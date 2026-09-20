#!/usr/bin/env python3
"""
Overhead — local server + proxy for the adsb.lol community ADS-B API.

Why the OpenSky version was retired:
OpenSky deliberately drops traffic from cloud/hosting IP ranges (Render, AWS, ...),
so a hosted proxy just sees "connect timed out". adsb.lol speaks the ADSBExchange
v2 JSON format and is meant to be called from apps, so this file fetches from it
instead and converts each aircraft into the same 17-slot
"state vector" array OpenSky used. squawk.html therefore keeps reading
s[0]=icao24, s[1]=callsign, s[5]=lon, s[6]=lat, s[7]=alt (m), s[8]=on_ground,
s[9]=speed (m/s), s[10]=heading, s[11]=vertical rate (m/s), s[14]=squawk.
Two extra slots are added: s[17]=registration, s[18]=aircraft type (when known).

Endpoints:
    /proxy/states?region=eu|na|asia|world   -> sampled busy hubs for a region (250 nm each)
    /proxy/states?lamin=..&lomin=..&lamax=..&lomax=..
                                            -> one radius query around the bbox centre
    /proxy/states?callsign=BAW249,AAL100    -> those callsigns, if airborne (tracked list)
    /proxy/states                           -> one random busy hub (trending chips)
    /proxy/track?icao24=XXXXXX              -> live state for ONE aircraft (detail page)
    /proxy/flight?callsign=XXX              -> airborne / scheduled / not_found resolver
    /proxy/health                           -> provider status, handy on Render

Important limits vs. OpenSky (these are properties of the data sources):
  * No "whole planet in one call". Radius queries are capped at 250 nautical miles,
    so region views are built from a handful of hub queries, not full coverage.
  * No historical /flights/all, so "recently landed" only works if the optional
    AeroDataBox schedule key below is configured.

Configuration (environment variables, all optional):
    ADSB_PROVIDERS      comma-separated base URLs of ADSBExchange-v2-compatible APIs,
                        tried in order with failover. default: https://api.adsb.lol
    ADSB_MIN_INTERVAL   seconds between calls to the same provider (default 1.1;
                        keep it at or above 1 to be a polite client)
    ADSB_USER_AGENT     optional, e.g. "overhead/2.0 (+https://your-site.example)" so a
                        provider can contact you if something misbehaves
    SCHEDULE_API_KEY / SCHEDULE_API_HOST   AeroDataBox via RapidAPI (schedule + landed)

Attribution: adsb.lol data is ODbL-licensed; keep the credit in the page footer.

Usage:
    python3 server.py
    then open http://127.0.0.1:8000/squawk.html in your browser

No third-party packages required -- standard library only.
"""
import http.server
import urllib.request
import urllib.error
import urllib.parse
import json
import time
import threading
import os
import re
import math
import random
from datetime import datetime, timezone

PORT = int(os.environ.get("PORT", 8000))

# ---------------------------------------------------------------------------
# ADS-B providers (ADSBExchange v2 compatible)
# ---------------------------------------------------------------------------
PROVIDER_BASES = [
    b.strip() for b in os.environ.get(
        "ADSB_PROVIDERS", "https://api.adsb.lol"
    ).split(",") if b.strip()
]
USER_AGENT = os.environ.get("ADSB_USER_AGENT", "overhead-flight-tracker/2.0")

MIN_REQUEST_INTERVAL = float(os.environ.get("ADSB_MIN_INTERVAL", "1.1"))
REQUEST_TIMEOUT = 8            # seconds; keep short so a dead provider fails fast
LIVE_CACHE_TTL = 12            # radius / callsign results are this fresh
TRACK_CACHE_TTL = 5            # single-aircraft polling on the detail page
RATE_LIMIT_BACKOFF = 15        # provider cool-down after HTTP 429 (or its Retry-After)
ERROR_BACKOFF = 30             # cool-down after 5xx / 403 / bad JSON
UNREACHABLE_BACKOFF = 45       # cool-down after connect/read timeouts
MAX_RADIUS_NM = 250
TRACKED_MAX = 8                # tracked-list lookups per refresh (one request each)
TRACKED_CACHE_TTL = 20

# ---- optional schedule API: AeroDataBox via RapidAPI free tier (600 units/month) ----
SCHEDULE_API_HOST = os.environ.get("SCHEDULE_API_HOST", "aerodatabox.p.rapidapi.com")
SCHEDULE_API_KEY = os.environ.get("SCHEDULE_API_KEY", "")
SCHEDULE_CACHE_TTL = 300  # 5 minutes -- the free tier is small, don't burn it
_schedule_cache = {}
_schedule_cache_lock = threading.Lock()

# ---------------------------------------------------------------------------
# Busy hubs used to sample a region (each is queried with a 250 nm radius)
# ---------------------------------------------------------------------------
REGION_HUBS = {
    "eu": [(51.47, -0.45), (50.03, 8.56), (40.49, -3.57), (41.80, 12.24), (41.28, 28.75)],
    "na": [(40.64, -73.78), (33.64, -84.43), (41.97, -87.91), (32.90, -97.04), (33.94, -118.41)],
    "asia": [(35.55, 139.78), (37.46, 126.44), (31.14, 121.81), (22.31, 113.92), (40.08, 116.60)],
    "world": [(51.47, -0.45), (40.64, -73.78), (25.25, 55.37), (1.36, 103.99),
              (33.94, -118.41), (6.58, 3.32), (-26.14, 28.25)],
}

# ---------------------------------------------------------------------------
# Provider bookkeeping (per-host pacing, cool-downs, last error for /proxy/health)
# ---------------------------------------------------------------------------
class Provider:
    def __init__(self, base):
        self.base = base.rstrip("/")
        self.name = urllib.parse.urlparse(self.base).netloc or self.base
        self._lock = threading.Lock()
        self.last_call = 0.0
        self.down_until = 0.0
        self.last_status = None
        self.last_error = None
        self.last_ok_at = None  # wall-clock

    def usable(self):
        return time.monotonic() >= self.down_until

    def pace(self):
        with self._lock:
            wait = MIN_REQUEST_INTERVAL - (time.monotonic() - self.last_call)
            if wait > 0:
                time.sleep(wait)
            self.last_call = time.monotonic()

    def mark_ok(self, status=200):
        self.last_status = status
        self.last_error = None
        self.last_ok_at = time.time()

    def mark_fail(self, status, error, message, backoff):
        self.last_status = status
        self.last_error = message
        self.down_until = time.monotonic() + backoff
        print(f"[adsb] {self.name}: {message} (cooling down {backoff:.0f}s)")
        return status, {"error": error, "message": f"{self.name}: {message}"}, True


PROVIDERS = [Provider(b) for b in PROVIDER_BASES]

_cache = {}  # path -> (expires_at_monotonic, data)
_cache_lock = threading.Lock()


def _cache_get(key):
    with _cache_lock:
        hit = _cache.get(key)
    if hit and time.monotonic() <= hit[0]:
        return hit[1]
    return None


def _cache_put(key, data, ttl):
    with _cache_lock:
        _cache[key] = (time.monotonic() + ttl, data)
        if len(_cache) > 400:  # crude bound so a long-running server can't grow forever
            now = time.monotonic()
            for k in [k for k, v in _cache.items() if v[0] < now]:
                _cache.pop(k, None)


def _try_provider(p, path):
    """One request to one provider. Returns (status, payload, retryable).
    retryable=True means "this provider is unhealthy right now -- try the next one"."""
    p.pace()
    try:
        req = urllib.request.Request(
            p.base + path,
            headers={"User-Agent": USER_AGENT, "Accept": "application/json"},
        )
        with urllib.request.urlopen(req, timeout=REQUEST_TIMEOUT) as resp:
            raw = resp.read()
        try:
            data = json.loads(raw.decode("utf-8"))
        except ValueError:
            return p.mark_fail(502, "bad_response", "returned something that isn't JSON", ERROR_BACKOFF)
        p.mark_ok(200)
        return 200, data, False
    except urllib.error.HTTPError as e:
        if e.code == 429:
            try:
                delay = float(e.headers.get("Retry-After") or RATE_LIMIT_BACKOFF)
            except ValueError:
                delay = RATE_LIMIT_BACKOFF
            return p.mark_fail(429, "rate_limited", "rate limited (HTTP 429)", min(max(delay, 5), 120))
        if e.code in (401, 403):
            return p.mark_fail(502, "provider_refused",
                               f"refused the request (HTTP {e.code}) - it may be blocking this server's IP", ERROR_BACKOFF)
        if e.code >= 500:
            return p.mark_fail(502, "provider_error", f"server error (HTTP {e.code})", ERROR_BACKOFF)
        # 404 / 400 etc: the provider is reachable, the query itself was rejected
        p.mark_ok(e.code)
        return e.code, {"error": "http_%d" % e.code, "message": f"{p.name}: HTTP {e.code} for {path}"}, False
    except (urllib.error.URLError, TimeoutError, OSError) as e:
        reason = getattr(e, "reason", e)
        return p.mark_fail(504, "upstream_unreachable", f"unreachable ({reason})", UNREACHABLE_BACKOFF)


def _adsb_request(path):
    """Try each provider in order. Returns (status, payload)."""
    last = None
    for p in PROVIDERS:
        if not p.usable():
            continue
        status, payload, retryable = _try_provider(p, path)
        if not retryable:
            return status, payload
        last = (status, payload)
    if last is not None:
        return last
    cooling = ", ".join(p.name for p in PROVIDERS) or "none configured"
    return 504, {"error": "upstream_unreachable",
                 "message": f"All ADS-B providers are cooling down after errors ({cooling}). Retrying shortly."}


def _cached_adsb(path, ttl):
    hit = _cache_get(path)
    if hit is not None:
        return 200, hit
    status, payload = _adsb_request(path)
    if status == 200:
        _cache_put(path, payload, ttl)
    return status, payload


# ---------------------------------------------------------------------------
# ADSBExchange-v2 aircraft  ->  OpenSky-style state vector
# ---------------------------------------------------------------------------
FT_TO_M = 0.3048
KT_TO_MS = 0.514444
FPM_TO_MS = 1 / 196.85


def _num(x):
    return x if isinstance(x, (int, float)) and not isinstance(x, bool) else None


def ac_to_state(ac, now_s=None):
    """Returns a 19-element list (17 OpenSky slots + registration + type) or None
    if the aircraft has no usable position / identity."""
    lat, lon = _num(ac.get("lat")), _num(ac.get("lon"))
    hex_ = (ac.get("hex") or "").strip().lower()
    if lat is None or lon is None or not hex_ or hex_.startswith("~"):
        return None  # "~" = non-ICAO (TIS-B) targets: no stable id, skip them
    now_s = now_s or int(time.time())

    alt_baro = ac.get("alt_baro")
    on_ground = alt_baro == "ground"
    if on_ground:
        alt_m = 0.0
    else:
        alt_ft = _num(alt_baro)
        alt_m = round(alt_ft * FT_TO_M, 1) if alt_ft is not None else None
    geo_ft = _num(ac.get("alt_geom"))
    geo_m = round(geo_ft * FT_TO_M, 1) if geo_ft is not None else None

    gs = _num(ac.get("gs"))
    vel = round(gs * KT_TO_MS, 2) if gs is not None else None
    track = _num(ac.get("track"))
    rate = _num(ac.get("baro_rate"))
    if rate is None:
        rate = _num(ac.get("geom_rate"))
    vrate = round(rate * FPM_TO_MS, 2) if rate is not None else None

    seen_pos = _num(ac.get("seen_pos"))
    seen = _num(ac.get("seen"))
    callsign = (ac.get("flight") or "").strip() or None
    squawk = ac.get("squawk") or None

    return [
        hex_,                                                   # 0  icao24
        callsign,                                               # 1  callsign
        None,                                                   # 2  origin country (not provided)
        int(now_s - seen_pos) if seen_pos is not None else now_s,  # 3  time_position
        int(now_s - seen) if seen is not None else now_s,       # 4  last_contact
        lon,                                                    # 5
        lat,                                                    # 6
        alt_m,                                                  # 7  baro altitude (m)
        on_ground,                                              # 8
        vel,                                                    # 9  m/s
        track,                                                  # 10 true track
        vrate,                                                  # 11 m/s
        None,                                                   # 12 sensors
        geo_m,                                                  # 13 geo altitude (m)
        squawk,                                                 # 14
        bool(ac.get("spi")),                                    # 15
        0,                                                      # 16 position source
        (ac.get("r") or None),                                  # 17 registration
        (ac.get("t") or None),                                  # 18 aircraft type
    ]


def _ac_list(payload):
    if not isinstance(payload, dict):
        return []
    lst = payload.get("ac")
    if lst is None:
        lst = payload.get("aircraft")
    return lst if isinstance(lst, list) else []


def states_from_payload(payload):
    now_s = int(time.time())
    out = []
    for ac in _ac_list(payload):
        if isinstance(ac, dict):
            s = ac_to_state(ac, now_s)
            if s:
                out.append(s)
    return out


# ---------------------------------------------------------------------------
# geometry helpers
# ---------------------------------------------------------------------------
def _haversine_nm(lat1, lon1, lat2, lon2):
    R_NM = 3440.065
    dlat, dlon = math.radians(lat2 - lat1), math.radians(lon2 - lon1)
    a = math.sin(dlat / 2) ** 2 + math.cos(math.radians(lat1)) * math.cos(math.radians(lat2)) * math.sin(dlon / 2) ** 2
    return 2 * R_NM * math.asin(math.sqrt(a))


def bbox_to_point(lamin, lomin, lamax, lomax):
    lat, lon = (lamin + lamax) / 2, (lomin + lomax) / 2
    r = max(_haversine_nm(lat, lon, la, lo) for la in (lamin, lamax) for lo in (lomin, lomax))
    return lat, lon, int(min(max(r, 5), MAX_RADIUS_NM))


def _in_bbox(state, bbox):
    if not bbox:
        return True
    lamin, lomin, lamax, lomax = bbox
    return lamin <= state[6] <= lamax and lomin <= state[5] <= lomax


def _parse_bbox(qs):
    try:
        vals = [float(qs[k][0]) for k in ("lamin", "lomin", "lamax", "lomax")]
    except (KeyError, ValueError, IndexError):
        return None
    return tuple(vals)


def fetch_point(lat, lon, radius_nm):
    radius = int(min(max(radius_nm, 1), MAX_RADIUS_NM))
    return _cached_adsb(f"/v2/point/{lat:.3f}/{lon:.3f}/{radius}", LIVE_CACHE_TTL)


def collect_states(points, bbox=None):
    """Query several (lat, lon, radius) points, merge + dedupe. Returns (status, body_dict)."""
    merged, last_err, failures = {}, None, 0
    for lat, lon, radius in points:
        status, payload = fetch_point(lat, lon, radius)
        if status != 200:
            last_err, failures = (status, payload), failures + 1
            continue
        for s in states_from_payload(payload):
            if _in_bbox(s, bbox):
                merged[s[0]] = s
    if not merged and last_err is not None:
        return last_err
    body = {"time": int(time.time()), "states": list(merged.values())}
    if failures:
        body["partial"] = True
    return 200, body


class Handler(http.server.SimpleHTTPRequestHandler):
    def do_GET(self):
        parsed = urllib.parse.urlparse(self.path)
        qs = urllib.parse.parse_qs(parsed.query)
        if parsed.path == "/":
            self.send_response(302)
            self.send_header("Location", "/squawk.html")
            self.end_headers()
        elif parsed.path == "/proxy/states":
            self.proxy_states(qs)
        elif parsed.path == "/proxy/track":
            self.proxy_track(qs)
        elif parsed.path == "/proxy/flight":
            self.proxy_flight(qs)
        elif parsed.path == "/proxy/health":
            self.proxy_health()
        elif parsed.path == "/favicon.ico":
            self.send_response(204)
            self.end_headers()
        else:
            super().do_GET()

    # ---------------- region / bbox / callsign-list / trending ----------------
    def proxy_states(self, qs):
        raw_calls = (qs.get("callsign", [""])[0] or "").upper()
        region = (qs.get("region", [""])[0] or "").lower()
        bbox = _parse_bbox(qs)

        if raw_calls:
            calls = [c for c in re.sub(r"[^A-Z0-9,]", "", raw_calls).split(",") if c][:25]
            if not calls:
                self._send_json(400, json.dumps({"error": "callsign required"}).encode())
                return
            found, failures, last_err = {}, 0, None
            for call in calls[:TRACKED_MAX]:
                status, payload = _cached_adsb("/v2/callsign/" + call, TRACKED_CACHE_TTL)
                if status != 200:
                    failures, last_err = failures + 1, (status, payload)
                    continue
                for s in states_from_payload(payload):
                    found[s[0]] = s
            if failures and not found and last_err is not None:
                self._send_upstream_error(*last_err)
                return
            self._send_json(200, json.dumps({"time": int(time.time()),
                                             "states": list(found.values())}).encode())
            return

        if region in REGION_HUBS:
            points = [(la, lo, MAX_RADIUS_NM) for la, lo in REGION_HUBS[region]]
        elif bbox:
            points = [bbox_to_point(*bbox)]
        else:
            la, lo = random.choice(REGION_HUBS["world"])
            points = [(la, lo, MAX_RADIUS_NM)]

        status, body = collect_states(points, bbox if region in REGION_HUBS else None)
        if status != 200:
            self._send_upstream_error(status, body)
            return
        self._send_json(200, json.dumps(body).encode())

    # ---------------- single aircraft, for the live detail-page map ----------------
    def proxy_track(self, qs):
        icao24 = re.sub(r"[^0-9a-f]", "", (qs.get("icao24", [""])[0] or "").strip().lower())
        if not icao24:
            self._send_json(400, json.dumps({"error": "icao24 required"}).encode())
            return
        status, payload = _cached_adsb("/v2/hex/" + icao24, TRACK_CACHE_TTL)
        if status != 200:
            self._send_upstream_error(status, payload)
            return
        self._send_json(200, json.dumps({"time": int(time.time()),
                                         "states": states_from_payload(payload)}).encode())

    # ---------------- callsign -> airborne / scheduled / not_found resolver ----------------
    def proxy_flight(self, qs):
        prefix = re.sub(r"[^A-Z0-9]", "", (qs.get("callsign", [""])[0] or "").strip().upper())
        # The flight number as the user typed it ("BA249"); AeroDataBox wants that form.
        flight_number_hint = (qs.get("flightnumber", [""])[0] or "").strip().upper()
        if not prefix:
            self._send_json(400, json.dumps({"error": "callsign required"}).encode())
            return

        # 1) is it broadcasting right now? (exact callsign match, e.g. BAW249)
        status, payload = _cached_adsb("/v2/callsign/" + urllib.parse.quote(prefix), LIVE_CACHE_TTL)
        if status != 200:
            self._send_upstream_error(status, payload)
            return
        for s in states_from_payload(payload):
            if (s[1] or "").upper().startswith(prefix):
                self._send_json(200, json.dumps({"status": "airborne", "state": s}).encode())
                return

        # 2) not live -- optional schedule API, if a key is configured
        sched = self._try_schedule_api(prefix, flight_number_hint)
        if sched is not None:
            self._send_json(200, json.dumps(sched).encode())
            return

        # 3) nothing. There is no historical feed in this data source, so we can't
        # say whether it recently landed -- searched_hours=0 tells the UI that.
        self._send_json(200, json.dumps({"status": "not_found", "searched_hours": 0}).encode())

    def proxy_health(self):
        now = time.monotonic()
        info = [{
            "provider": p.name,
            "usable": p.usable(),
            "cooldown_seconds": max(0, round(p.down_until - now)),
            "last_status": p.last_status,
            "last_error": p.last_error,
            "last_ok_seconds_ago": round(time.time() - p.last_ok_at) if p.last_ok_at else None,
        } for p in PROVIDERS]
        self._send_json(200, json.dumps({"providers": info}, indent=2).encode())

    def _send_upstream_error(self, status, payload):
        code = 429 if status == 429 else (504 if status == 504 else 502)
        if not isinstance(payload, dict) or "error" not in payload:
            payload = {"error": "upstream_error", "message": "Unexpected response from the ADS-B provider."}
        self._send_json(code, json.dumps(payload).encode())

    def _try_schedule_api(self, prefix, flight_number_hint):
        """Ask AeroDataBox for this flight's schedule/status. Returns a dict shaped
        like the client expects ({"status": "scheduled"/"landed", "flight": {...}}),
        or None to fall through (no key configured, no record, or the lookup failed)."""
        if not SCHEDULE_API_KEY or not SCHEDULE_API_HOST:
            return None

        raw_number = flight_number_hint or prefix
        number = re.sub(r"[^A-Z0-9]", "", raw_number.upper())
        if not number:
            return None

        cache_key = "adb:" + number
        with _schedule_cache_lock:
            hit = _schedule_cache.get(cache_key)
        if hit and time.monotonic() < hit[0]:
            flights = hit[1]
        else:
            url = f"https://{SCHEDULE_API_HOST}/flights/number/{urllib.parse.quote(number)}"
            headers = {
                "X-RapidAPI-Key": SCHEDULE_API_KEY,
                "X-RapidAPI-Host": SCHEDULE_API_HOST,
            }
            try:
                req = urllib.request.Request(url, headers=headers)
                with urllib.request.urlopen(req, timeout=REQUEST_TIMEOUT) as resp:
                    flights = json.loads(resp.read().decode("utf-8"))
            except urllib.error.HTTPError as e:
                print(f"[aerodatabox] HTTP {e.code} for {number}: {e.read()[:200]}")
                flights = None
            except Exception as e:
                print(f"[aerodatabox] request failed for {number}: {e}")
                flights = None
            with _schedule_cache_lock:
                _schedule_cache[cache_key] = (time.monotonic() + SCHEDULE_CACHE_TTL, flights)

        if not flights or not isinstance(flights, list):
            return None

        today = datetime.now(timezone.utc).date()
        chosen = None
        for f in flights:
            sched_utc = ((f.get("departure") or {}).get("scheduledTime") or {}).get("utc")
            parsed = self._parse_adb_time(sched_utc) if sched_utc else None
            if parsed and parsed.date() == today:
                chosen = f
                break
        if chosen is None:
            chosen = flights[0]

        dep = chosen.get("departure") or {}
        arr = chosen.get("arrival") or {}
        dep_airport = ((dep.get("airport") or {}).get("icao")
                       or (dep.get("airport") or {}).get("iata") or "")
        arr_airport = ((arr.get("airport") or {}).get("icao")
                       or (arr.get("airport") or {}).get("iata") or "")
        status = (chosen.get("status") or "").strip()
        callsign = chosen.get("callSign") or chosen.get("number") or number

        dep_actual = self._epoch(((dep.get("actualTime") or dep.get("runwayTime") or {}).get("utc")))
        dep_sched = self._epoch((dep.get("scheduledTime") or {}).get("utc"))
        arr_actual = self._epoch(((arr.get("actualTime") or arr.get("runwayTime") or {}).get("utc")))
        arr_sched = self._epoch((arr.get("scheduledTime") or {}).get("utc"))

        if status == "Landed":
            return {
                "status": "landed",
                "flight": {
                    "estDepartureAirport": dep_airport,
                    "estArrivalAirport": arr_airport,
                    "firstSeen": dep_actual or dep_sched,
                    "lastSeen": arr_actual or arr_sched,
                    "callsign": callsign,
                },
            }
        return {
            "status": "scheduled",
            "flight": {
                "departureAirport": dep_airport,
                "arrivalAirport": arr_airport,
                "departureTime": dep_sched,
                "statusLabel": status or None,
            },
        }

    @staticmethod
    def _parse_adb_time(iso_str):
        """AeroDataBox timestamps look like '2026-09-20T14:35Z' or '...T14:35:00Z'."""
        if not iso_str:
            return None
        s = iso_str.strip()
        if s.endswith("Z"):
            s = s[:-1] + "+00:00"
        if "T" in s and len(s.split("T", 1)[1].split("+")[0].split("-")[0]) == 5:
            head, tail = s.split("T", 1)
            time_part, _, offset = tail.partition("+")
            if len(time_part) == 5:
                tail = time_part + ":00+" + offset if offset else time_part + ":00"
            s = head + "T" + tail
        try:
            return datetime.fromisoformat(s)
        except ValueError:
            return None

    @classmethod
    def _epoch(cls, iso_str):
        dt = cls._parse_adb_time(iso_str)
        return int(dt.timestamp()) if dt else None

    def _send_json(self, status, data_bytes):
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Access-Control-Allow-Origin", "*")
        self.end_headers()
        self.wfile.write(data_bytes)

    def log_message(self, fmt, *args):
        try:
            if args and "/proxy/" in str(args[0]):
                print("[proxy]", *args)
        except Exception:
            pass


def _startup_probe():
    """Log once at boot whether each provider is reachable from THIS machine --
    the first thing to check in Render's logs if the app shows no aircraft."""
    for p in PROVIDERS:
        status, payload, _ = _try_provider(p, "/v2/point/51.47/-0.45/5")
        if status == 200:
            print(f"[startup] {p.name}: reachable (HTTP 200, {len(_ac_list(payload))} aircraft near LHR)")
        else:
            print(f"[startup] {p.name}: PROBLEM - {payload.get('message') if isinstance(payload, dict) else status}")


if __name__ == "__main__":
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    host = "0.0.0.0" if os.environ.get("PORT") else "127.0.0.1"
    httpd = http.server.ThreadingHTTPServer((host, PORT), Handler)
    print(f"Overhead running -> http://{host}:{PORT}/squawk.html")
    print("ADS-B providers:", ", ".join(p.name for p in PROVIDERS) or "NONE (set ADSB_PROVIDERS)")
    if not SCHEDULE_API_KEY:
        print("Tip: set SCHEDULE_API_KEY (AeroDataBox) to get scheduled / recently-landed status.")
    threading.Thread(target=_startup_probe, daemon=True).start()
    print("Press Ctrl+C to stop.")
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        pass