#!/usr/bin/env python3
"""
Overhead — local server + CORS proxy for the OpenSky Network API.

Why this exists:
OpenSky's API responds with `Access-Control-Allow-Origin: https://opensky-network.org`
only -- browsers block any other origin (including localhost) from reading the
response, and there is no client-side fix for that. This script fetches OpenSky
SERVER-SIDE (CORS is a browser rule, not a server-to-server rule) and re-serves
the JSON from the same origin squawk.html is loaded from, which the browser
is happy to accept.

Endpoints:
    /proxy/states                  -> raw OpenSky /states/all (optionally bbox-filtered)
    /proxy/track?icao24=XXXXXX     -> live state for ONE aircraft (used by the detail page)
    /proxy/flight?callsign=XXX     -> "where is this flight right now" resolver. Checks the
                                       live feed first; if the flight isn't airborne it looks
                                       back through OpenSky's historical /flights/all endpoint
                                       to say whether it looks recently LANDED, or whether we
                                       simply have no record (could mean it hasn't departed yet,
                                       is sitting at the gate not squawking, or the number was
                                       wrong -- OpenSky is ADS-B only, it has no schedule data,
                                       so we can never positively confirm "scheduled, not yet
                                       departed" -- only rule out "currently airborne" and
                                       "recently landed").

AUTHENTICATION -- read this if you're seeing 401s/429s:
OpenSky now EXCLUSIVELY supports OAuth2 client-credentials auth. The old
username/password Basic-auth scheme has been retired -- if you're on a version
of this script that still asks for OPENSKY_USERNAME/OPENSKY_PASSWORD, it will
silently fail to authenticate (or get a 401 from OpenSky) even with correct
credentials, because Basic auth is no longer accepted at all.

To authenticate:
  1. Log in to your OpenSky account -> Account page.
  2. Create an API client there and copy its client_id and client_secret.
  3. Paste them into OPENSKY_CLIENT_ID / OPENSKY_CLIENT_SECRET below.
This script then exchanges them for a short-lived (30 min) Bearer access token
automatically, and refreshes it before it expires or whenever OpenSky returns
401. Authenticated ("Standard user") access gets a much higher daily credit
quota than anonymous access, which is the real fix for persistent 429s.

Left blank, the proxy still runs anonymously (heavily rate limited).

Honesty note: there is no free, keyless source of airline SCHEDULE data (gate, boarding time,
departure time before wheels-up). If you get a free API key from a schedule provider
(AeroDataBox on RapidAPI, AviationStack, FlightAware AeroAPI, etc.) you can wire it into
SCHEDULE_API_* below and /proxy/flight will use it to give a real "scheduled, departs 14:20"
answer instead of the best-effort fallback. Left blank, the app is upfront with users that it
can't see pre-departure schedule info.

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
from datetime import datetime, timezone

PORT = int(os.environ.get("PORT", 8000))
STATES_URL = "https://opensky-network.org/api/states/all"
FLIGHTS_ALL_URL = "https://opensky-network.org/api/flights/all"
TOKEN_URL = (
    "https://auth.opensky-network.org/auth/realms/opensky-network"
    "/protocol/openid-connect/token"
)

# ---- OAuth2 client credentials (OpenSky no longer accepts username/password). ----
# Account page -> API clients -> create one -> paste the id/secret here.
# ---- OAuth2 client credentials (OpenSky no longer accepts username/password). ----
# Account page -> API clients -> create one -> paste the id/secret here for local
# use. When hosted (e.g. on Render), set OPENSKY_CLIENT_ID / OPENSKY_CLIENT_SECRET
# as environment variables in the dashboard instead -- keeps secrets out of your
# public GitHub repo, and env vars always win if both are set.
OPENSKY_CLIENT_ID = os.environ.get("OPENSKY_CLIENT_ID", "")
OPENSKY_CLIENT_SECRET = os.environ.get("OPENSKY_CLIENT_SECRET", "")

# How many seconds before a token's reported expiry to proactively refresh it.
TOKEN_REFRESH_MARGIN = 30

# ---- schedule API: AeroDataBox via RapidAPI free tier (600 units/month) ----
# RapidAPI -> AeroDataBox -> Endpoints tab -> copy the X-RapidAPI-Key shown in the
# code snippet (or Account -> My Apps -> your app -> Security tab). For hosted
# use, set SCHEDULE_API_KEY as an environment variable instead of pasting it here.
SCHEDULE_API_HOST = os.environ.get("SCHEDULE_API_HOST", "aerodatabox.p.rapidapi.com")
SCHEDULE_API_KEY = os.environ.get("SCHEDULE_API_KEY", "")

# Cache AeroDataBox lookups for a while -- the free tier is only 600 units/month,
# so we do not want every "Full check" click or tracked-flight refresh to burn one.
SCHEDULE_CACHE_TTL = 300  # 5 minutes

_schedule_cache = {}
_schedule_cache_lock = threading.Lock()

# How far back (hours) to search OpenSky's historical /flights/all when a flight
# isn't currently airborne, looking for a recent landing. Each hour costs one more
# upstream request (OpenSky anonymous access caps a single /flights/all call at a
# 2-hour window), so keep this modest -- it directly trades off against your rate limit.
LOOKBACK_HOURS = 4
CHUNK_HOURS = 2

# ---- rate-limit protection ----
MIN_REQUEST_INTERVAL = 3.0      # seconds between any two outgoing OpenSky requests
LIVE_CACHE_TTL = 12             # states/all (and per-icao24 track) results are this fresh
HISTORY_CACHE_TTL = 3600 * 6    # /flights/all windows are in the past, so cache them longer
RETRY_ON_429_WAIT = 6.0         # seconds to back off once if OpenSky itself throttles us

_pacer_lock = threading.Lock()
_last_call = [0.0]
_cache = {}  # url -> (expires_at_monotonic, status, data_bytes)
_cache_lock = threading.Lock()


# ---------------------------------------------------------------------------
# OAuth2 token manager -- fetches + caches a Bearer token via the client
# credentials flow, refreshing it automatically before it expires.
# ---------------------------------------------------------------------------
class TokenManager:
    def __init__(self, client_id, client_secret):
        self.client_id = client_id
        self.client_secret = client_secret
        self.token = None
        self.expires_at = 0.0
        self._lock = threading.Lock()

    def enabled(self):
        return bool(self.client_id and self.client_secret)

    def get_token(self, force_refresh=False):
        if not self.enabled():
            return None
        with self._lock:
            if not force_refresh and self.token and time.monotonic() < self.expires_at:
                return self.token
            return self._refresh_locked()

    def _refresh_locked(self):
        body = urllib.parse.urlencode({
            "grant_type": "client_credentials",
            "client_id": self.client_id,
            "client_secret": self.client_secret,
        }).encode()
        req = urllib.request.Request(
            TOKEN_URL,
            data=body,
            headers={"Content-Type": "application/x-www-form-urlencoded"},
            method="POST",
        )
        try:
            with urllib.request.urlopen(req, timeout=15) as resp:
                data = json.loads(resp.read().decode("utf-8"))
        except urllib.error.HTTPError as e:
            print("[auth] token request failed:", e.code, e.read()[:300])
            self.token = None
            return None
        except Exception as e:
            print("[auth] token request failed:", e)
            self.token = None
            return None

        self.token = data.get("access_token")
        expires_in = data.get("expires_in", 1800)
        self.expires_at = time.monotonic() + max(expires_in - TOKEN_REFRESH_MARGIN, 5)
        return self.token


_tokens = TokenManager(OPENSKY_CLIENT_ID, OPENSKY_CLIENT_SECRET)


def _cache_get(url):
    with _cache_lock:
        hit = _cache.get(url)
    if not hit:
        return None
    expires_at, status, data = hit
    if time.monotonic() > expires_at:
        return None
    return status, data


def _cache_put(url, status, data, ttl):
    with _cache_lock:
        _cache[url] = (time.monotonic() + ttl, status, data)


def _paced_fetch(url):
    """Fetch a URL from OpenSky, enforcing a minimum gap since our last call,
    retrying once (after a short backoff) if OpenSky itself returns 429, and
    retrying once with a freshly-refreshed token if it returns 401."""
    attempted_token_refresh = False

    for attempt in range(3):
        headers = {"User-Agent": "overhead-local-proxy/1.0"}
        token = _tokens.get_token()
        if token:
            headers["Authorization"] = "Bearer " + token

        with _pacer_lock:
            wait = MIN_REQUEST_INTERVAL - (time.monotonic() - _last_call[0])
            if wait > 0:
                time.sleep(wait)
            _last_call[0] = time.monotonic()
        try:
            req = urllib.request.Request(url, headers=headers)
            with urllib.request.urlopen(req, timeout=15) as resp:
                return resp.status, resp.read()
        except urllib.error.HTTPError as e:
            if e.code == 401 and _tokens.enabled() and not attempted_token_refresh:
                # Token expired/invalid mid-flight -- force a refresh and retry once.
                attempted_token_refresh = True
                _tokens.get_token(force_refresh=True)
                continue
            if e.code == 429 and attempt < 2:
                retry_after = e.headers.get("Retry-After") or e.headers.get(
                    "X-Rate-Limit-Retry-After-Seconds"
                )
                try:
                    delay = float(retry_after) if retry_after else RETRY_ON_429_WAIT
                except ValueError:
                    delay = RETRY_ON_429_WAIT
                time.sleep(delay)
                continue
            return e.code, e.read()
    return 429, json.dumps({
        "error": "rate_limited",
        "message": "OpenSky is throttling requests right now. Wait a bit and try "
                    "again, or double-check OPENSKY_CLIENT_ID/OPENSKY_CLIENT_SECRET "
                    "in server.py for a higher authenticated quota.",
    }).encode()


class Handler(http.server.SimpleHTTPRequestHandler):
    def do_GET(self):
        parsed = urllib.parse.urlparse(self.path)
        qs = urllib.parse.parse_qs(parsed.query)
        if parsed.path == "/":
            self.send_response(302)
            self.send_header("Location", "/squawk.html")
            self.end_headers()
        elif parsed.path == "/proxy/states":
            self.proxy_states(parsed.query)
        elif parsed.path == "/proxy/track":
            self.proxy_track(qs)
        elif parsed.path == "/proxy/flight":
            self.proxy_flight(qs)
        elif parsed.path == "/favicon.ico":
            self.send_response(204)
            self.end_headers()
        else:
            super().do_GET()

    # ---------------- existing raw states proxy (bbox-filterable) ----------------
    def proxy_states(self, query):
        url = STATES_URL + ("?" + query if query else "")
        self._relay_cached(url, LIVE_CACHE_TTL)

    # ---------------- single aircraft, for the live detail-page map ----------------
    def proxy_track(self, qs):
        icao24 = (qs.get("icao24", [""])[0] or "").strip().lower()
        if not icao24:
            self._send_json(400, json.dumps({"error": "icao24 required"}).encode())
            return
        url = STATES_URL + "?icao24=" + urllib.parse.quote(icao24)
        self._relay_cached(url, LIVE_CACHE_TTL)

    # ---------------- callsign -> airborne / landed / not_found resolver ----------------
    def proxy_flight(self, qs):
        prefix = (qs.get("callsign", [""])[0] or "").strip().upper()
        # Optional: the flight number as the user actually typed it (e.g. "BA249").
        # OpenSky only speaks ICAO callsign prefixes ("BAW249"), but AeroDataBox's
        # schedule lookup wants the IATA-style flight number, so the client sends
        # both and we use whichever fits each provider.
        flight_number_hint = (qs.get("flightnumber", [""])[0] or "").strip().upper()
        if not prefix:
            self._send_json(400, json.dumps({"error": "callsign required"}).encode())
            return

        # 1) is it airborne / on the ground with a live transponder right now?
        # (shares the same cache + TTL as /proxy/states, so a search made right after
        # the page's own polling won't cost an extra upstream request)
        status, data = self._cached_fetch(STATES_URL, LIVE_CACHE_TTL)
        if status == 429:
            self._send_json(429, data)
            return
        if status != 200:
            self._send_json(502, json.dumps({"error": "live feed unreachable (HTTP %s)" % status}).encode())
            return
        try:
            states = json.loads(data.decode("utf-8"))
        except Exception as e:
            self._send_json(502, json.dumps({"error": "bad response from live feed: " + str(e)}).encode())
            return
        for s in states.get("states") or []:
            cs = (s[1] or "").strip().upper()
            if cs.startswith(prefix):
                self._send_json(200, json.dumps({"status": "airborne", "state": s}).encode())
                return

        # 2) not live -- optional schedule API, if the user wired one in
        sched = self._try_schedule_api(prefix, flight_number_hint)
        if sched is not None:
            self._send_json(200, json.dumps(sched).encode())
            return

        # 3) fall back to OpenSky historical flights, looking for a recent landing.
        # Past time windows never change, so these are cached for hours, not seconds.
        now = int(time.time())
        best = None
        hours_done = 0
        while hours_done < LOOKBACK_HOURS:
            end = now - hours_done * 3600
            begin = end - CHUNK_HOURS * 3600
            url = FLIGHTS_ALL_URL + f"?begin={begin}&end={end}"
            h_status, h_data = self._cached_fetch(url, HISTORY_CACHE_TTL)
            if h_status == 429:
                # Don't fail the whole lookup -- just stop searching further back and
                # report what we know (nothing yet), same as a clean "not found".
                break
            chunk = None
            if h_status == 200:
                try:
                    chunk = json.loads(h_data.decode("utf-8"))
                except Exception:
                    chunk = None
            if isinstance(chunk, list):
                for f in chunk:
                    cs = (f.get("callsign") or "").strip().upper()
                    if cs.startswith(prefix):
                        if best is None or (f.get("lastSeen") or 0) > (best.get("lastSeen") or 0):
                            best = f
            if best is not None:
                break
            hours_done += CHUNK_HOURS

        if best is not None:
            self._send_json(200, json.dumps({"status": "landed", "flight": best}).encode())
        else:
            self._send_json(
                200,
                json.dumps({
                    "status": "not_found",
                    "searched_hours": LOOKBACK_HOURS,
                }).encode(),
            )

    def _try_schedule_api(self, prefix, flight_number_hint):
        """Ask AeroDataBox for this flight's schedule/status. Returns a dict shaped
        like the client expects ({"status": "scheduled"/"landed", "flight": {...}}),
        or None to fall through to the OpenSky-only best-effort logic (no key
        configured, AeroDataBox has no record, or the lookup failed)."""
        if not SCHEDULE_API_KEY or not SCHEDULE_API_HOST:
            return None

        # AeroDataBox wants an IATA-style flight number ("BA249"), not OpenSky's
        # ICAO callsign prefix ("BAW249") -- prefer what the user actually typed.
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
                with urllib.request.urlopen(req, timeout=15) as resp:
                    flights = json.loads(resp.read().decode("utf-8"))
            except urllib.error.HTTPError as e:
                # 404 = AeroDataBox has never heard of this number; 401/403 = bad key;
                # 429 = out of free-tier credits for the month. None of these should
                # break the app -- just fall back to the OpenSky-only logic.
                print(f"[aerodatabox] HTTP {e.code} for {number}: {e.read()[:200]}")
                flights = None
            except Exception as e:
                print(f"[aerodatabox] request failed for {number}: {e}")
                flights = None
            with _schedule_cache_lock:
                _schedule_cache[cache_key] = (time.monotonic() + SCHEDULE_CACHE_TTL, flights)

        if not flights or not isinstance(flights, list):
            return None

        # The endpoint can return several flights (different days / codeshares).
        # Prefer one that's today in UTC; otherwise take the first result.
        today = datetime.now(timezone.utc).date()
        chosen = None
        for f in flights:
            sched_utc = ((f.get("departure") or {}).get("scheduledTime") or {}).get("utc")
            if sched_utc and self._parse_adb_time(sched_utc):
                if self._parse_adb_time(sched_utc).date() == today:
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

        # Everything else we can still meaningfully show (Expected, CheckIn,
        # Boarding, GateClosed, Delayed, Canceled, Diverted, Unknown) is reported
        # as "not departed yet" -- AeroDataBox's own status label is passed through
        # so the card can say e.g. "Delayed" instead of a flat "Not departed yet".
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
        """AeroDataBox timestamps look like '2026-09-20T14:35Z' or
        '2026-09-20T14:35:00Z'. Returns a timezone-aware datetime, or None."""
        if not iso_str:
            return None
        s = iso_str.strip()
        if s.endswith("Z"):
            s = s[:-1] + "+00:00"
        if "T" in s and len(s.split("T", 1)[1].split("+")[0].split("-")[0]) == 5:
            # "HH:MM" with no seconds -- pad so fromisoformat accepts it
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

    # ---------------- shared helpers ----------------
    def _cached_fetch(self, url, ttl):
        hit = _cache_get(url)
        if hit is not None:
            return hit
        status, data = _paced_fetch(url)
        # Don't cache errors (other than a 429, which we DO cache briefly so a burst
        # of client requests during a throttle doesn't each re-trigger the backoff).
        if status == 200 or status == 429:
            _cache_put(url, status, data, ttl if status == 200 else RETRY_ON_429_WAIT)
        return status, data

    def _relay_cached(self, url, ttl):
        status, data = self._cached_fetch(url, ttl)
        self._send_json(status, data)

    def _send_json(self, status, data_bytes):
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        # Wide open since this only ever runs on your own machine for your own use.
        self.send_header("Access-Control-Allow-Origin", "*")
        self.end_headers()
        self.wfile.write(data_bytes)

    def log_message(self, fmt, *args):
        # quieter console output; tolerate any arg types (HTTPStatus enums etc.)
        try:
            if args and "/proxy/" in str(args[0]):
                print("[proxy]", *args)
        except Exception:
            pass


if __name__ == "__main__":
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    host = "0.0.0.0" if os.environ.get("PORT") else "127.0.0.1"
    httpd = http.server.ThreadingHTTPServer((host, PORT), Handler)
    print(f"Overhead running -> http://{host}:{PORT}/squawk.html")
    if _tokens.enabled():
        print("Authenticating with OpenSky using OAuth2 client credentials...")
        if _tokens.get_token():
            print("Auth OK -- using the higher authenticated rate limit.")
        else:
            print("WARNING: token request failed -- check OPENSKY_CLIENT_ID/SECRET.")
            print("         Falling back to anonymous access for now.")
    else:
        print("Tip: running anonymously. If you see 429s, create an API client on your")
        print("     OpenSky account page and set OPENSKY_CLIENT_ID/OPENSKY_CLIENT_SECRET")
        print("     near the top of this file.")
    print("Press Ctrl+C to stop.")
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        pass