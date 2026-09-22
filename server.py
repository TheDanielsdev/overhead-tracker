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
Three extra slots are added: s[17]=registration, s[18]=aircraft type (ICAO code),
s[19]=aircraft type, human-readable (e.g. "Airbus A320", or None if unrecognized).

Endpoints:
    /proxy/states?region=eu|na|asia|world   -> sampled busy hubs for a region (250 nm each)
    /proxy/states?lamin=..&lomin=..&lamax=..&lomax=..
                                            -> one radius query around the bbox centre
    /proxy/states?callsign=BAW249,AAL100    -> those callsigns, if airborne (tracked list)
    /proxy/states                           -> one random busy hub (trending chips)
    /proxy/track?icao24=XXXXXX              -> live state for ONE aircraft (detail page)
    /proxy/flight?callsign=XXX              -> airborne / scheduled / not_found resolver
    /proxy/route?callsign=XXX&lat=..&lon=.. -> departure / destination airports for a flight
                                               (hexdb.io; community flight-plan data)
    /proxy/photo?icao24=XXXXXX              -> a representative photo of that airframe
                                               (planespotters.net public API)
    /proxy/health                           -> provider + circuit-breaker status, handy on Render

Important limits vs. OpenSky (these are properties of the data sources):
  * No "whole planet in one call". Radius queries are capped at 250 nautical miles,
    so region views are built from a handful of hub queries, not full coverage.
  * No historical /flights/all, so "recently landed" only works if the optional
    AeroDataBox schedule key below is configured.

Resilience:
  * Every upstream dependency (ADS-B providers, hexdb.io routes, planespotters.net
    photos, AeroDataBox schedule) goes through a shared CircuitBreaker (see below):
    a 429's Retry-After header is honored as a floor on the next wait, repeated
    failures back off exponentially (capped), and a run of consecutive failures
    trips the breaker fully open for a guaranteed cool-down so a struggling
    dependency stops getting hammered instead of being retried on every request.

Configuration (environment variables, all optional):
    ADSB_PROVIDERS      comma-separated base URLs of ADSBExchange-v2-compatible APIs,
                        tried in order with failover. default: https://api.adsb.lol
    ADSB_MIN_INTERVAL   seconds between calls to the same provider (default 1.1;
                        keep it at or above 1 to be a polite client)
    ADSB_USER_AGENT     optional, e.g. "overhead/2.0 (+https://your-site.example)" so a
                        provider can contact you if something misbehaves
    ROUTE_API_URL       hexdb.io base URL used for departure/destination airport lookups
                        (default https://hexdb.io; set to empty to disable)
    PHOTO_API_URL       planespotters.net base URL used for aircraft photos
                        (default https://api.planespotters.net/pub/photos/hex; set to
                        empty to disable)
    SCHEDULE_API_KEY / SCHEDULE_API_HOST   AeroDataBox via RapidAPI (schedule + landed)

Attribution: adsb.lol data is ODbL-licensed; planespotters.net photos carry a
photographer credit; both are kept in the UI. Keep the credit in the page footer.

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
# Shared resilience primitive: exponential backoff + circuit breaker
# ---------------------------------------------------------------------------
class CircuitBreaker:
    """Tracks the health of one upstream dependency.

    - usable() gates every request: while the breaker is cooling down, callers
      should skip the request entirely rather than firing it and eating another
      failure. That's the "halt repeated requests" part.
    - Each failure doubles the wait (exponential backoff), capped at max_backoff,
      so a flaky dependency gets progressively less traffic instead of being
      retried at a constant rate.
    - A 429's Retry-After header (or any other server-supplied hint) is honored
      as a floor: the breaker never waits less than what the server asked for,
      even if the exponential schedule alone would allow an earlier retry.
    - After `failure_threshold` consecutive failures, the breaker trips fully
      "open": the cool-down is forced up to at least `open_seconds`, regardless
      of how small the exponential/retry-after value was, because a long streak
      of failures usually means the dependency itself is down, not just slow.
    - Once the cool-down expires the breaker goes "half_open" and lets exactly
      one probe request through; success closes it again, failure reopens it
      (extending the cool-down further).
    """

    def __init__(self, name, base_backoff=5, max_backoff=300, failure_threshold=5, open_seconds=180):
        self.name = name
        self.base_backoff = base_backoff
        self.max_backoff = max_backoff
        self.failure_threshold = failure_threshold
        self.open_seconds = open_seconds
        self._lock = threading.Lock()
        self.consecutive_failures = 0
        self.down_until = 0.0
        self.state = "closed"          # closed | open | half_open
        self.last_error = None
        self.last_ok_at = None         # wall-clock, for /proxy/health

    def usable(self):
        with self._lock:
            now = time.monotonic()
            if now < self.down_until:
                return False
            if self.state == "open":
                self.state = "half_open"   # exactly one probe request allowed through
            return True

    def ok(self):
        with self._lock:
            self.consecutive_failures = 0
            self.state = "closed"
            self.last_error = None
            self.last_ok_at = time.time()

    def fail(self, message, retry_after=None):
        """Record a failure and return the backoff (seconds) applied."""
        with self._lock:
            self.consecutive_failures += 1
            backoff = min(self.base_backoff * (2 ** (self.consecutive_failures - 1)), self.max_backoff)
            if retry_after:
                backoff = max(backoff, min(float(retry_after), self.max_backoff))
            tripped = self.consecutive_failures >= self.failure_threshold
            if tripped or self.state != "closed":
                # Either this run of failures just crossed the threshold, or a
                # half-open probe failed -- in both cases, force the circuit open.
                self.state = "open"
                backoff = max(backoff, self.open_seconds)
            self.last_error = message
            self.down_until = time.monotonic() + backoff
            print(f"[{self.name}] {message} — backing off {backoff:.0f}s "
                  f"(circuit={self.state}, consecutive_failures={self.consecutive_failures})")
            return backoff

    def status(self):
        with self._lock:
            now = time.monotonic()
            return {
                "circuit": self.state,
                "consecutive_failures": self.consecutive_failures,
                "cooldown_seconds": max(0, round(self.down_until - now)),
                "last_error": self.last_error,
                "last_ok_seconds_ago": round(time.time() - self.last_ok_at) if self.last_ok_at else None,
            }


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
RATE_LIMIT_MIN_WAIT = 15       # floor used if a 429 has no (usable) Retry-After
MAX_RADIUS_NM = 250
TRACKED_MAX = 8                # tracked-list lookups per refresh (one request each)
TRACKED_CACHE_TTL = 20

# Route (departure/destination) lookups. Routes don't change mid-flight, so hits are
# cached for hours; misses for a shorter time; failures go through the breaker below.
ROUTE_API_URL = os.environ.get("ROUTE_API_URL", "https://hexdb.io").strip()  # hexdb.io: simple, documented, GET-only
ROUTE_TIMEOUT = 6
ROUTE_HIT_TTL = 6 * 3600
ROUTE_MISS_TTL = 30 * 60
AIRPORT_INFO_TTL = 30 * 24 * 3600  # airport lat/lon/name basically never changes

# Aircraft photos (planespotters.net public API -- no key needed, but be a polite
# client: cache aggressively and keep a photographer credit + link in the UI).
PHOTO_API_URL = os.environ.get("PHOTO_API_URL", "https://api.planespotters.net/pub/photos/hex").strip()
PHOTO_TIMEOUT = 6
PHOTO_HIT_TTL = 24 * 3600
PHOTO_MISS_TTL = 2 * 3600

# ---- optional schedule API: AeroDataBox via RapidAPI free tier (600 units/month) ----
SCHEDULE_API_HOST = os.environ.get("SCHEDULE_API_HOST", "aerodatabox.p.rapidapi.com")
SCHEDULE_API_KEY = os.environ.get("SCHEDULE_API_KEY", "")
SCHEDULE_CACHE_TTL = 300  # 5 minutes -- the free tier is small, don't burn it
_schedule_cache = {}
_schedule_cache_lock = threading.Lock()
schedule_breaker = CircuitBreaker("schedule", base_backoff=10, max_backoff=300,
                                   failure_threshold=4, open_seconds=180)

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
# Readable aircraft types: ICAO type designator -> human-friendly name.
# Not exhaustive -- covers the airframes that show up on commercial routes most
# often. Anything not in this table just falls back to showing the raw code.
# ---------------------------------------------------------------------------
AIRCRAFT_TYPES = {
    # Airbus narrowbody
    "A318": "Airbus A318", "A319": "Airbus A319", "A19N": "Airbus A319neo",
    "A320": "Airbus A320", "A20N": "Airbus A320neo",
    "A321": "Airbus A321", "A21N": "Airbus A321neo",
    # Airbus widebody
    "A306": "Airbus A300-600", "A310": "Airbus A310",
    "A332": "Airbus A330-200", "A333": "Airbus A330-300",
    "A338": "Airbus A330-800neo", "A339": "Airbus A330-900neo",
    "A342": "Airbus A340-200", "A343": "Airbus A340-300",
    "A345": "Airbus A340-500", "A346": "Airbus A340-600",
    "A359": "Airbus A350-900", "A35K": "Airbus A350-1000",
    "A388": "Airbus A380-800",
    # Boeing narrowbody
    "B712": "Boeing 717-200",
    "B731": "Boeing 737-100", "B732": "Boeing 737-200", "B733": "Boeing 737-300",
    "B734": "Boeing 737-400", "B735": "Boeing 737-500",
    "B736": "Boeing 737-600", "B737": "Boeing 737-700", "B738": "Boeing 737-800", "B739": "Boeing 737-900",
    "B37M": "Boeing 737 MAX 7", "B38M": "Boeing 737 MAX 8", "B39M": "Boeing 737 MAX 9", "B3XM": "Boeing 737 MAX 10",
    # Boeing widebody
    "B742": "Boeing 747-200", "B744": "Boeing 747-400", "B748": "Boeing 747-8",
    "B752": "Boeing 757-200", "B753": "Boeing 757-300",
    "B762": "Boeing 767-200", "B763": "Boeing 767-300", "B764": "Boeing 767-400",
    "B772": "Boeing 777-200", "B77L": "Boeing 777-200LR", "B773": "Boeing 777-300", "B77W": "Boeing 777-300ER",
    "B778": "Boeing 777-8", "B779": "Boeing 777-9",
    "B788": "Boeing 787-8 Dreamliner", "B789": "Boeing 787-9 Dreamliner", "B78X": "Boeing 787-10 Dreamliner",
    "MD11": "McDonnell Douglas MD-11", "MD80": "McDonnell Douglas MD-80", "MD82": "McDonnell Douglas MD-82",
    "MD83": "McDonnell Douglas MD-83", "MD88": "McDonnell Douglas MD-88", "MD90": "McDonnell Douglas MD-90",
    # Embraer
    "E135": "Embraer ERJ 135", "E145": "Embraer ERJ 145", "E170": "Embraer E170",
    "E75L": "Embraer E175", "E75S": "Embraer E175", "E190": "Embraer E190", "E195": "Embraer E195",
    "E290": "Embraer E190-E2", "E295": "Embraer E195-E2",
    # Bombardier / De Havilland
    "CRJ1": "Bombardier CRJ100", "CRJ2": "Bombardier CRJ200", "CRJ7": "Bombardier CRJ700",
    "CRJ9": "Bombardier CRJ900", "CRJX": "Bombardier CRJ1000",
    "CL30": "Bombardier Challenger 300", "CL60": "Bombardier Challenger 600",
    "GLEX": "Bombardier Global Express", "GL5T": "Bombardier Global 5000",
    "DH8A": "De Havilland Dash 8-100", "DH8B": "De Havilland Dash 8-200",
    "DH8C": "De Havilland Dash 8-300", "DH8D": "De Havilland Dash 8-400 (Q400)",
    # ATR / regional turboprops
    "AT43": "ATR 42-300", "AT45": "ATR 42-500", "AT72": "ATR 72", "AT76": "ATR 72-600",
    "SF34": "Saab 340", "F50": "Fokker 50", "F70": "Fokker 70", "F100": "Fokker 100",
    "DHC6": "De Havilland Twin Otter", "B350": "Beechcraft King Air 350",
    # Russian / Ukrainian
    "SU95": "Sukhoi Superjet 100", "A148": "Antonov An-148", "IL96": "Ilyushin Il-96",
    "TU95": "Tupolev Tu-95", "TU204": "Tupolev Tu-204",
    # Cargo / other widebody
    "A124": "Antonov An-124", "A225": "Antonov An-225",
    # Business jets
    "GLF4": "Gulfstream G450", "GLF5": "Gulfstream G550", "GLF6": "Gulfstream G650",
    "C25A": "Cessna Citation CJ2", "C25B": "Cessna Citation CJ3", "C25C": "Cessna Citation CJ4",
    "C56X": "Cessna Citation Excel", "C680": "Cessna Citation Sovereign", "C750": "Cessna Citation X",
    "LJ35": "Learjet 35", "LJ60": "Learjet 60", "FA7X": "Dassault Falcon 7X", "F2TH": "Dassault Falcon 2000",
    "PC12": "Pilatus PC-12", "TBM9": "Daher TBM 900",
    # Light aircraft / GA
    "C172": "Cessna 172 Skyhawk", "C182": "Cessna 182 Skylane", "C208": "Cessna 208 Caravan",
    "PA28": "Piper PA-28 Cherokee", "PA34": "Piper PA-34 Seneca", "SR22": "Cirrus SR22",
    # Military / other (occasionally seen on ADS-B)
    "C130": "Lockheed C-130 Hercules", "C17": "Boeing C-17 Globemaster III", "A400": "Airbus A400M Atlas",
    "KC35": "Boeing KC-135 Stratotanker", "E3TF": "Boeing E-3 Sentry (AWACS)",
    "H60": "Sikorsky UH-60 Black Hawk", "EC35": "Eurocopter EC135", "AS50": "Eurocopter AS350",
}


def readable_aircraft_type(icao_type_code):
    if not icao_type_code:
        return None
    return AIRCRAFT_TYPES.get(icao_type_code.strip().upper())


# ---------------------------------------------------------------------------
# Provider bookkeeping (per-host pacing + shared CircuitBreaker)
# ---------------------------------------------------------------------------
class Provider:
    def __init__(self, base):
        self.base = base.rstrip("/")
        self.name = urllib.parse.urlparse(self.base).netloc or self.base
        self._pace_lock = threading.Lock()
        self.last_call = 0.0
        self.last_status = None
        self.breaker = CircuitBreaker(self.name, base_backoff=5, max_backoff=300,
                                       failure_threshold=5, open_seconds=180)

    def usable(self):
        return self.breaker.usable()

    def pace(self):
        with self._pace_lock:
            wait = MIN_REQUEST_INTERVAL - (time.monotonic() - self.last_call)
            if wait > 0:
                time.sleep(wait)
            self.last_call = time.monotonic()

    def mark_ok(self, status=200):
        self.last_status = status
        self.breaker.ok()

    def mark_fail(self, status, error, message, retry_after=None):
        self.last_status = status
        backoff = self.breaker.fail(message, retry_after=retry_after)
        full_message = f"{message} (retrying in ~{backoff:.0f}s)"
        return status, {"error": error, "message": f"{self.name}: {full_message}"}, True


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
            return p.mark_fail(502, "bad_response", "returned something that isn't JSON")
        p.mark_ok(200)
        return 200, data, False
    except urllib.error.HTTPError as e:
        if e.code == 429:
            retry_after = None
            try:
                retry_after = float(e.headers.get("Retry-After"))
            except (TypeError, ValueError):
                retry_after = None
            # Retry-After is a floor, not the whole story -- mark_fail() combines it
            # with the exponential schedule and takes whichever is longer.
            return p.mark_fail(429, "rate_limited",
                               "rate limited (HTTP 429)" + (f", server asked for {retry_after:.0f}s" if retry_after else ""),
                               retry_after=retry_after or RATE_LIMIT_MIN_WAIT)
        if e.code in (401, 403):
            return p.mark_fail(502, "provider_refused",
                               f"refused the request (HTTP {e.code}) - it may be blocking this server's IP")
        if e.code >= 500:
            return p.mark_fail(502, "provider_error", f"server error (HTTP {e.code})")
        # 404 / 400 etc: the provider is reachable, the query itself was rejected
        p.mark_ok(e.code)
        return e.code, {"error": "http_%d" % e.code, "message": f"{p.name}: HTTP {e.code} for {path}"}, False
    except (urllib.error.URLError, TimeoutError, OSError) as e:
        reason = getattr(e, "reason", e)
        return p.mark_fail(504, "upstream_unreachable", f"unreachable ({reason})")


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
    cooling = ", ".join(f"{p.name} ({p.breaker.status()['circuit']})" for p in PROVIDERS) or "none configured"
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
    """Returns a 20-element list (17 OpenSky slots + registration, ICAO type code,
    and human-readable type) or None if the aircraft has no usable position / identity."""
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
    type_code = (ac.get("t") or None)

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
        type_code,                                              # 18 aircraft type (ICAO code)
        readable_aircraft_type(type_code),                      # 19 aircraft type (human-readable)
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


# ---------------------------------------------------------------------------
# Routes: departure / destination airports (hexdb.io)
#   GET /api/v1/route/icao/{callsign} -> {"flight","route":"DEP-ARR","updatetime"}
#     or 404 {"status":"404","error":"Route not found."} for an unknown callsign
#   GET /api/v1/airport/icao/{icao}   -> {"airport","iata","icao","latitude",
#     "longitude","country_code","region_name"} or 404 if unknown
# Two requests per fresh lookup (route, then each airport -- airports are cached
# separately and much longer, since they basically never change). The data is
# community-maintained, so it can be wrong, stale, or missing for less common
# routes -- the UI already labels results as approximate.
# ---------------------------------------------------------------------------
_route_cache = {}            # CALLSIGN -> (expires_at_monotonic, route_or_None)
_airport_cache = {}          # ICAO -> (expires_at_monotonic, airport_dict_or_None)
_route_lock = threading.Lock()
_airport_lock = threading.Lock()
_route_pace_lock = threading.Lock()
_route_last_call = [0.0]
route_breaker = CircuitBreaker("route", base_backoff=10, max_backoff=300,
                                failure_threshold=4, open_seconds=180)


def _route_store(key, route, ttl):
    with _route_lock:
        _route_cache[key] = (time.monotonic() + ttl, route)
        if len(_route_cache) > 500:
            now = time.monotonic()
            for k in [k for k, v in _route_cache.items() if v[0] < now]:
                _route_cache.pop(k, None)


def _polite_pace(pace_lock, last_call_box):
    with pace_lock:
        wait = MIN_REQUEST_INTERVAL - (time.monotonic() - last_call_box[0])
        if wait > 0:
            time.sleep(wait)
        last_call_box[0] = time.monotonic()


def _http_get_json(base_url, path, timeout, user_agent=USER_AGENT):
    """GET path from base_url. Returns (status, parsed_json_or_None, retry_after_or_None,
    error_message_or_None). status 404 is reported cleanly (not an error -- "not found")."""
    req = urllib.request.Request(
        base_url + path,
        headers={"Accept": "application/json", "User-Agent": user_agent},
    )
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            raw = resp.read()
    except urllib.error.HTTPError as e:
        if e.code == 404:
            return 404, None, None, None
        retry_after = None
        if e.code == 429:
            try:
                retry_after = float(e.headers.get("Retry-After"))
            except (TypeError, ValueError):
                retry_after = None
        if e.code == 429 or e.code >= 500:
            body_preview = e.read()[:200].decode("utf-8", errors="replace")
            return e.code, None, retry_after, f"HTTP {e.code}. Body preview: {body_preview!r}"
        return e.code, None, None, f"HTTP {e.code}"
    except (urllib.error.URLError, TimeoutError, OSError) as e:
        return 0, None, None, str(getattr(e, "reason", e))
    try:
        return 200, json.loads(raw.decode("utf-8", errors="replace")), None, None
    except ValueError as e:
        preview = raw[:200].decode("utf-8", errors="replace") if raw else "(empty body)"
        return 200, None, None, f"response wasn't JSON ({e}). Body preview: {preview!r}"


def _lookup_airport(icao):
    """ICAO code -> {"icao","iata","city","name","lat","lon","country"} or None (unknown).
    Cached for a long time -- airport locations don't move."""
    if not icao:
        return None
    icao = icao.upper()
    with _airport_lock:
        hit = _airport_cache.get(icao)
    if hit and time.monotonic() <= hit[0]:
        return hit[1]
    if not route_breaker.usable():
        return None

    _polite_pace(_route_pace_lock, _route_last_call)
    status, data, retry_after, err = _http_get_json(ROUTE_API_URL, "/api/v1/airport/icao/" + urllib.parse.quote(icao), ROUTE_TIMEOUT)
    airport = None
    if status == 200 and isinstance(data, dict) and data.get("icao"):
        route_breaker.ok()
        airport = {
            "icao": (data.get("icao") or "").upper() or None,
            "iata": (data.get("iata") or "").upper() or None,
            "city": data.get("airport") or None,   # hexdb calls the airport's display name "airport"
            "name": data.get("airport") or None,
            "lat": _num(data.get("latitude")),
            "lon": _num(data.get("longitude")),
            "country": data.get("country_code") or None,
        }
    elif status == 404:
        route_breaker.ok()
    elif err:
        route_breaker.fail(f"airport lookup for {icao} failed: {err}", retry_after=retry_after)
    with _airport_lock:
        _airport_cache[icao] = (time.monotonic() + AIRPORT_INFO_TTL, airport)
    return airport


def lookup_route(callsign, lat, lon):
    """Returns (status, route). status is "ok" (route found), "none" (no route known for
    this callsign) or "unavailable" (lookup disabled / breaker open / failing right now).
    lat/lon are accepted for API-compatibility with the old adsb.lol lookup but
    unused -- hexdb.io's route data isn't position-checked, so there's no
    "plausible" flag here; the client already treats that as optional."""
    if not ROUTE_API_URL:
        return "unavailable", None
    key = callsign.upper()
    with _route_lock:
        hit = _route_cache.get(key)
    if hit and time.monotonic() <= hit[0]:
        return ("ok" if hit[1] else "none"), hit[1]
    if not route_breaker.usable():
        return "unavailable", None

    _polite_pace(_route_pace_lock, _route_last_call)
    status, data, retry_after, err = _http_get_json(ROUTE_API_URL, "/api/v1/route/icao/" + urllib.parse.quote(key), ROUTE_TIMEOUT)
    if status == 404:
        route_breaker.ok()
        _route_store(key, None, ROUTE_MISS_TTL)
        return "none", None
    if err:
        route_breaker.fail(f"route lookup for {key} failed: {err}", retry_after=retry_after)
        return "unavailable", None
    if not isinstance(data, dict) or "-" not in (data.get("route") or ""):
        route_breaker.ok()
        _route_store(key, None, ROUTE_MISS_TTL)
        return "none", None

    dep_icao, _, arr_icao = data["route"].partition("-")
    origin = _lookup_airport(dep_icao.strip())
    destination = _lookup_airport(arr_icao.strip())
    if not origin or not destination:
        # Route string exists but one of the two airports isn't in hexdb's airport
        # table (rare, but happens for small/regional fields) -- no coordinates to
        # draw with, so treat it as unknown rather than showing a half-empty route.
        _route_store(key, None, ROUTE_MISS_TTL)
        return "none", None

    route_breaker.ok()
    route = {"origin": origin, "destination": destination, "via": [], "plausible": None}
    _route_store(key, route, ROUTE_HIT_TTL)
    return "ok", route


# ---------------------------------------------------------------------------
# Aircraft photos (planespotters.net public API)
#   GET /pub/photos/hex/{icao24} -> {"photos":[{"thumbnail_large":{"src":...,
#     "size":{"width":...,"height":...}},"link":...,"photographer":...}, ...]}
#   404 / empty "photos" -> no photo on file for this airframe
# planespotters.net asks that a credit + link back to the photographer accompany
# any use of a photo; the client renders both next to the image.
# ---------------------------------------------------------------------------
_photo_cache = {}
_photo_lock = threading.Lock()
_photo_pace_lock = threading.Lock()
_photo_last_call = [0.0]
photo_breaker = CircuitBreaker("photo", base_backoff=10, max_backoff=300,
                                failure_threshold=4, open_seconds=180)


def lookup_photo(icao24):
    """Returns (status, photo). status is "ok", "none", or "unavailable"."""
    if not PHOTO_API_URL or not icao24:
        return "unavailable", None
    icao24 = icao24.lower()
    with _photo_lock:
        hit = _photo_cache.get(icao24)
    if hit and time.monotonic() <= hit[0]:
        return ("ok" if hit[1] else "none"), hit[1]
    if not photo_breaker.usable():
        return "unavailable", None

    _polite_pace(_photo_pace_lock, _photo_last_call)
    status, data, retry_after, err = _http_get_json(PHOTO_API_URL, "/" + urllib.parse.quote(icao24), PHOTO_TIMEOUT)
    if status == 404:
        photo_breaker.ok()
        with _photo_lock:
            _photo_cache[icao24] = (time.monotonic() + PHOTO_MISS_TTL, None)
        return "none", None
    if err:
        photo_breaker.fail(f"photo lookup for {icao24} failed: {err}", retry_after=retry_after)
        return "unavailable", None

    photo_breaker.ok()
    photos = (data or {}).get("photos") or []
    if not photos:
        with _photo_lock:
            _photo_cache[icao24] = (time.monotonic() + PHOTO_MISS_TTL, None)
        return "none", None

    p0 = photos[0]
    thumb = p0.get("thumbnail_large") or p0.get("thumbnail") or {}
    size = thumb.get("size") if isinstance(thumb.get("size"), dict) else {}
    photo = {
        "url": thumb.get("src"),
        "width": size.get("width"),
        "height": size.get("height"),
        "photographer": p0.get("photographer"),
        "link": p0.get("link"),
    }
    with _photo_lock:
        _photo_cache[icao24] = (time.monotonic() + PHOTO_HIT_TTL, photo)
    return "ok", photo


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
        elif parsed.path == "/proxy/route":
            self.proxy_route(qs)
        elif parsed.path == "/proxy/photo":
            self.proxy_photo(qs)
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

    # ---------------- departure / destination airports ----------------
    def proxy_route(self, qs):
        callsign = re.sub(r"[^A-Z0-9]", "", (qs.get("callsign", [""])[0] or "").upper())
        try:
            lat, lon = float(qs["lat"][0]), float(qs["lon"][0])
        except (KeyError, ValueError, IndexError):
            lat = lon = float("nan")
        if not callsign or not (-90 <= lat <= 90 and -180 <= lon <= 180):
            self._send_json(400, json.dumps({"error": "callsign, lat and lon required"}).encode())
            return
        status, route = lookup_route(callsign, lat, lon)
        self._send_json(200, json.dumps({"status": status, "route": route,
                                         "source": "hexdb.io"}).encode())

    # ---------------- aircraft photo ----------------
    def proxy_photo(self, qs):
        icao24 = re.sub(r"[^0-9a-fA-F]", "", (qs.get("icao24", [""])[0] or "").strip())
        if not icao24:
            self._send_json(400, json.dumps({"error": "icao24 required"}).encode())
            return
        status, photo = lookup_photo(icao24)
        self._send_json(200, json.dumps({"status": status, "photo": photo,
                                         "source": "planespotters.net"}).encode())

    def proxy_health(self):
        info = [{"provider": p.name, **p.breaker.status()} for p in PROVIDERS]
        self._send_json(200, json.dumps({
            "providers": info,
            "route_lookup": {"enabled": bool(ROUTE_API_URL), **route_breaker.status()},
            "photo_lookup": {"enabled": bool(PHOTO_API_URL), **photo_breaker.status()},
            "schedule_lookup": {"enabled": bool(SCHEDULE_API_KEY), **schedule_breaker.status()},
        }, indent=2).encode())

    def _send_upstream_error(self, status, payload):
        code = 429 if status == 429 else (504 if status == 504 else 502)
        if not isinstance(payload, dict) or "error" not in payload:
            payload = {"error": "upstream_error", "message": "Unexpected response from the ADS-B provider."}
        self._send_json(code, json.dumps(payload).encode())

    def _try_schedule_api(self, prefix, flight_number_hint):
        """Ask AeroDataBox for this flight's schedule/status. Returns a dict shaped
        like the client expects ({"status": "scheduled"/"landed", "flight": {...}}),
        or None to fall through (no key configured, breaker open, no record, or the
        lookup failed)."""
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
        elif not schedule_breaker.usable():
            return None
        else:
            url = f"https://{SCHEDULE_API_HOST}/flights/number/{urllib.parse.quote(number)}"
            headers = {
                "X-RapidAPI-Key": SCHEDULE_API_KEY,
                "X-RapidAPI-Host": SCHEDULE_API_HOST,
            }
            flights = None
            try:
                req = urllib.request.Request(url, headers=headers)
                with urllib.request.urlopen(req, timeout=REQUEST_TIMEOUT) as resp:
                    flights = json.loads(resp.read().decode("utf-8"))
                schedule_breaker.ok()
            except urllib.error.HTTPError as e:
                retry_after = None
                if e.code == 429:
                    try:
                        retry_after = float(e.headers.get("Retry-After"))
                    except (TypeError, ValueError):
                        retry_after = None
                schedule_breaker.fail(f"HTTP {e.code} for {number}", retry_after=retry_after)
            except Exception as e:
                schedule_breaker.fail(f"request failed for {number}: {e}")
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