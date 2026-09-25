import asyncio
import aiohttp
import subprocess
import shutil
import logging
import random
import re
import os
import time
import json
from urllib.parse import urlparse, urljoin
from collections import defaultdict
import sys

# --- কনফিগারেশন ---
M3U_SOURCES = [
    "https://iptv-api.streamingscripts.xyz/adult/iptv/m3u8/playlist_xxx_m3u8.m3u",
    "https://iptv-api.streamingscripts.xyz/adult/iptv/player/playlist_xxx_http.m3u",
    "https://iptv-api.streamingscripts.xyz/cabletv/m3u8/playlist_cable_m3u8.m3u",
    "https://iptv-api.streamingscripts.xyz/cabletv/player/playlist_cable_http.m3u",
    "https://iptv-api.streamingscripts.xyz/sportsiptv/m3u8/playlist_sports_m3u8.m3u",
    "https://iptv-api.streamingscripts.xyz/worldiptv/m3u8/playlist_world_m3u8.m3u",
    "https://iptv-api.streamingscripts.xyz/worldiptv/mpd/playlist_world_mpd.m3u",
    "https://iptv-api.streamingscripts.xyz/worldiptv/player/playlist_world_http.m3u",
]

OUTPUT_PREFIX = "working_"
COMBINED_FILE = "working.m3u"

# Rate limiting / concurrency
CONCURRENCY_LIMIT = 30          # parallel stream checks
SOURCE_FETCH_CONCURRENCY = 3    # parallel playlist downloads
HTTP_TIMEOUT = 12
FFPROBE_TIMEOUT = 15
HEAD_REQUEST_TIMEOUT = 8

# Retry policy
MAX_RETRIES = 2
RETRY_BACKOFF = 2.0  # seconds

# Rate limit protection for source downloads
DOWNLOAD_RATE_LIMIT_DELAY = 1.0  # seconds between source fetches per domain

USER_AGENTS = [
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/16.6 Safari/605.1.15",
    "Mozilla/5.0 (X11; Linux x86_64; rv:109.0) Gecko/20100101 Firefox/115.0",
    "VLC/3.0.18 LibVLC/3.0.18",
    "Kodi/19.5 (Windows NT 10.0; Win64; x64) App_Bitness/64 Version/19.5-Matrix",
]

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[
        logging.FileHandler("checker.log", mode='w', encoding='utf-8'),
        logging.StreamHandler(),
    ],
)
logger = logging.getLogger(__name__)

# ---------- Header / directive parsing ----------

# Directives that belong to the *stream* itself (need to be preserved per-link)
STREAM_DIRECTIVES = (
    "#EXTVLCOPT:",
    "#KODIPROP:",
    "#EXTHTTP:",
    "#EXTVLCOPT",
    "#KODIPROP",
)

# Known header keys we translate into ffprobe/http options
VLC_HEADER_KEYS = {
    "http-origin": "Origin",
    "http-referer": "Referer",
    "http-user-agent": "User-Agent",
    "http-cookie": "Cookie",
    "http-host": "Host",
}

KODI_LICENSE_TYPES = {
    "inputstream.adaptive.license_type",
    "inputstream.adaptive.license_key",
    "inputstream.adaptive.manifest_type",
}


def parse_stream_directives(raw_lines):
    """
    Given a list of lines immediately preceding a URL, extract:
      - directives: list of raw directive lines (EXTVLCOPT / KODIPROP)
      - headers:    dict of HTTP headers (case-insensitive keys)
      - manifest_type, license_type, license_key (from KODIPROP)
    """
    directives = []
    headers = {}
    manifest_type = None
    license_type = None
    license_key = None

    for raw in raw_lines:
        line = raw.strip()
        if not line:
            continue
        if not line.startswith("#EXTVLCOPT") and not line.startswith("#KODIPROP"):
            continue

        directives.append(line)

        # --- EXTVLCOPT:http-xxx=value ---
        m = re.match(r"#EXTVLCOPT:http-([a-z0-9\-]+)\s*=\s*(.+)", line, re.IGNORECASE)
        if m:
            key = m.group(1).strip().lower()
            val = m.group(2).strip()
            hdr = VLC_HEADER_KEYS.get(key)
            if hdr:
                headers[hdr] = val
            continue

        # --- KODIPROP:inputstream.adaptive.xxx=value ---
        m = re.match(
            r"#KODIPROP:(inputstream\.adaptive\.[a-z0-9_\.]+)\s*=\s*(.*)",
            line,
            re.IGNORECASE,
        )
        if m:
            key = m.group(1).strip().lower()
            val = m.group(2).strip()
            if key.endswith(".manifest_type"):
                manifest_type = val
            elif key.endswith(".license_type"):
                license_type = val
            elif key.endswith(".license_key"):
                license_key = val

    return {
        "directives": directives,
        "headers": headers,
        "manifest_type": manifest_type,
        "license_type": license_type,
        "license_key": license_key,
    }


# ---------- Processor ----------

class M3UProcessor:
    def __init__(self):
        # per-source grouping: {source_url: {channel_name: [candidate_dict, ...]}}
        self.per_source_channels = defaultdict(lambda: defaultdict(list))
        self.per_source_working = defaultdict(list)
        self.per_source_dead = defaultdict(int)

    def get_random_ua(self):
        return random.choice(USER_AGENTS)

    def normalize_name(self, name):
        name = name.strip()
        name = re.sub(r"\s+", " ", name)
        return name.title()

    def standardize_data(self, line, url, source_url):
        parts = line.split(",", 1)
        channel_name = parts[1].strip() if len(parts) > 1 else "Unknown Channel"
        channel_name_lower = channel_name.lower()

        group_match = re.search(r'group-title="([^"]+)"', line, re.IGNORECASE)
        original_group = group_match.group(1).strip() if group_match else "Others"
        group_lower = original_group.lower()
        clean_group = original_group.title()

        url_lower = url.lower()
        parsed_url = urlparse(url_lower)
        url_path = parsed_url.path
        url_host = parsed_url.hostname or ""

        # VOD detection
        vod_extensions = (".mp4", ".mkv", ".avi", ".mov", ".wmv", ".webm", ".flv")
        is_vod_link = (
            url_path.endswith(vod_extensions)
            or "://vod" in url_lower
            or "vod." in url_host
            or "vods." in url_host
            or "/vod/" in url_path
            or "/vods/" in url_path
            or "/movie/" in url_path
            or "/series/" in url_path
        )
        is_vod_group = "vod" in group_lower or (
            "movie" in group_lower and not url_path.endswith(".m3u8")
        )

        if is_vod_link or is_vod_group:
            clean_group = "VOD / Movies"
        elif any(
            x in channel_name_lower
            for x in [
                "somoy", "jamuna", "ekattor", "ntv", "atn", "gtv", "gazi tv",
                "nagorik", "boishakhi", "channel i", "dbc", "independent",
                "rtv", "btv", "banglavision", "deepto", "dipto", "maasranga",
                "mohona", "my tv", "desh tv", "asian tv", "ekushey", "t sports", "toffee",
            ]
        ):
            clean_group = "Bangladesh"
        elif any(
            x in channel_name_lower
            for x in [
                "star ", "zee ", "colors", "sony ", "sun ", "asianet",
                "abp ", "ndtv", "republic", "aaj tak", "sports18", "jio ", "jalsha",
            ]
        ):
            clean_group = "India"
        else:
            if any(x in group_lower for x in ["bangladesh", "bangladeshi", "bangla", "bd"]):
                clean_group = "Bangladesh"
            elif any(x in group_lower for x in ["india", "indian", "hindi", "in"]):
                clean_group = "India"
            elif any(x in group_lower for x in ["sports", "sport", "cricket", "football", "khela"]):
                clean_group = "Sports"
            elif any(x in group_lower for x in ["news", "khobor", "newz"]):
                clean_group = "News"
            elif any(x in group_lower for x in ["kids", "cartoon", "children"]):
                clean_group = "Kids"
            elif any(x in group_lower for x in ["music", "song", "gaan"]):
                clean_group = "Music"
            elif any(x in group_lower for x in ["religious", "islamic", "quran", "islam"]):
                clean_group = "Religious"
            elif original_group == "Others":
                clean_group = "Others"
            else:
                clean_group = original_group.title()

        if group_match:
            new_line = line.replace(
                f'group-title="{original_group}"', f'group-title="{clean_group}"'
            )
        else:
            new_line = f'{parts[0]} group-title="{clean_group}",{parts[1]}'

        return new_line, clean_group, channel_name

    # ---------- Fetching ----------

    async def fetch_playlist(self, session, url, semaphore):
        """Fetch one source playlist. Rate-limited via shared semaphore + per-domain delay."""
        clean_url = url.split("|")[0]
        headers = {"User-Agent": self.get_random_ua()}

        async with semaphore:
            for attempt in range(MAX_RETRIES + 1):
                try:
                    async with session.get(clean_url, headers=headers, timeout=30) as response:
                        if response.status == 200:
                            text = await response.text(errors="ignore")
                            lines = text.splitlines()
                            self._parse_m3u_content(lines, clean_url)
                            logger.info(f"✅ Loaded: {clean_url}")
                            return
                        elif response.status in (429, 503):
                            wait = RETRY_BACKOFF * (attempt + 1) + random.uniform(0, 1)
                            logger.warning(
                                f"⏳ Rate limited ({response.status}) on {clean_url}; sleeping {wait:.1f}s"
                            )
                            await asyncio.sleep(wait)
                            continue
                        else:
                            logger.warning(f"⚠️ Failed ({response.status}): {clean_url}")
                            return
                except (aiohttp.ClientError, asyncio.TimeoutError) as e:
                    if attempt < MAX_RETRIES:
                        wait = RETRY_BACKOFF * (attempt + 1)
                        logger.warning(
                            f"↻ Retry {attempt + 1}/{MAX_RETRIES} for {clean_url}: {e}"
                        )
                        await asyncio.sleep(wait)
                    else:
                        logger.error(f"❌ Error fetching {clean_url}: {e}")
                except Exception as e:
                    logger.error(f"❌ Unexpected error on {clean_url}: {e}")
                    return
            # small delay to prevent hammering a single host across many sources
            await asyncio.sleep(DOWNLOAD_RATE_LIMIT_DELAY)

    def _parse_m3u_content(self, lines, source_url):
        """Parse raw M3U content preserving EXTVLCOPT / KODIPROP directives."""
        i = 0
        n = len(lines)
        pending_directives = []  # directives encountered since last #EXTINF

        while i < n:
            raw = lines[i]
            line = raw.strip()

            if not line:
                i += 1
                continue

            # Capture EXTVLCOPT / KODIPROP / EXTHTTP lines
            if line.upper().startswith(("#EXTVLCOPT", "#KODIPROP", "#EXTHTTP")):
                pending_directives.append(line)
                i += 1
                continue

            if line.startswith("#EXTINF"):
                # look ahead for URL, collecting any directives in between
                j = i + 1
                inline_directives = list(pending_directives)
                url = None
                while j < n:
                    nxt = lines[j].strip()
                    if not nxt:
                        j += 1
                        continue
                    if nxt.upper().startswith(("#EXTVLCOPT", "#KODIPROP", "#EXTHTTP")):
                        inline_directives.append(nxt)
                        j += 1
                        continue
                    if nxt.startswith("#"):
                        # other comment, skip
                        j += 1
                        continue
                    url = nxt
                    break

                if url and url.startswith("http"):
                    parsed = parse_stream_directives(inline_directives)
                    extinf_clean, group, name = self.standardize_data(line, url, source_url)
                    norm_name = self.normalize_name(name)

                    channel_data = {
                        "extinf": extinf_clean,
                        "group": group,
                        "name": norm_name,
                        "url": url,
                        "directives": parsed["directives"],  # raw lines
                        "headers": parsed["headers"],        # resolved http headers
                        "manifest_type": parsed["manifest_type"],
                        "license_type": parsed["license_type"],
                        "license_key": parsed["license_key"],
                        "source": source_url,
                    }

                    bucket = self.per_source_channels[source_url]
                    if not any(x["url"] == url for x in bucket[norm_name]):
                        bucket[norm_name].append(channel_data)

                pending_directives = []
                i = j + 1
                continue

            # Non-directive, non-EXTINF line — reset pending directives
            pending_directives = []
            i += 1

    # ---------- Validation ----------

    def _build_headers_for_url(self, channel_data, default_ua):
        """Merge per-channel headers with a default UA."""
        hdrs = {"User-Agent": default_ua}
        for k, v in (channel_data.get("headers") or {}).items():
            hdrs[k] = v
        return hdrs

    def _ffprobe_cmd(self, url, channel_data, default_ua):
        """Build ffprobe command including all headers + adaptive options."""
        hdrs = self._build_headers_for_url(channel_data, default_ua)

        cmd = ["ffprobe", "-v", "error"]

        # General http header option (works for http/https inputs)
        # Build a single CRLF-joined header block for -headers
        header_block = "".join(f"{k}: {v}\r\n" for k, v in hdrs.items())
        cmd += ["-headers", header_block]

        # Also pass user_agent explicitly (some ffprobe builds need it)
        cmd += ["-user_agent", hdrs.get("User-Agent", default_ua)]

        cmd += [
            "-rw_timeout", str(FFPROBE_TIMEOUT * 1_000_000),
            "-show_entries", "stream=codec_type",
            "-of", "default=noprint_wrappers=1:nokey=1",
            url,
        ]
        return cmd

    async def _http_probe(self, session, url, channel_data, default_ua):
        """Lightweight pre-check using HTTP HEAD/GET; respects per-channel headers."""
        hdrs = self._build_headers_for_url(channel_data, default_ua)
        try:
            async with session.head(
                url,
                headers=hdrs,
                timeout=HEAD_REQUEST_TIMEOUT,
                allow_redirects=True,
            ) as resp:
                # Many IPTV servers don't implement HEAD correctly → treat 4xx as "try GET"
                if resp.status in (200, 301, 302, 303, 307, 308):
                    return True
                if resp.status in (403, 404, 410):
                    return False
        except Exception:
            pass

        # Fallback GET with range to be gentle
        try:
            get_hdrs = dict(hdrs)
            get_hdrs["Range"] = "bytes=0-2048"
            async with session.get(
                url,
                headers=get_hdrs,
                timeout=HEAD_REQUEST_TIMEOUT,
                allow_redirects=True,
            ) as resp:
                return resp.status in (200, 206, 301, 302, 303, 307, 308)
        except Exception:
            return False

    async def validate_stream(self, session, channel_data):
        """Two-stage validation: HTTP probe + ffprobe. Requires BOTH to pass."""
        url = channel_data["url"]
        default_ua = self.get_random_ua()

        # Stage 1: HTTP reachability with headers
        ok_http = await self._http_probe(session, url, channel_data, default_ua)
        if not ok_http:
            return False, "http-fail"

        # Stage 2: ffprobe with headers
        cmd = self._ffprobe_cmd(url, channel_data, default_ua)
        try:
            process = await asyncio.create_subprocess_exec(
                *cmd,
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.PIPE,
            )
            try:
                stdout, stderr = await asyncio.wait_for(
                    process.communicate(), timeout=FFPROBE_TIMEOUT
                )
            except asyncio.TimeoutError:
                try:
                    process.kill()
                except Exception:
                    pass
                return False, "ffprobe-timeout"

            out = stdout.decode("utf-8", errors="ignore").strip()
            err = stderr.decode("utf-8", errors="ignore").strip()

            if process.returncode == 0 and ("video" in out or "audio" in out):
                return True, "ok"
            return False, f"ffprobe-rc{process.returncode}"
        except Exception as e:
            return False, f"ffprobe-exc:{e}"

    async def process_channel_group(self, session, semaphore, source_url, channel_name, candidates):
        async with semaphore:
            for data in candidates:
                ok, reason = await self.validate_stream(session, data)
                if ok:
                    self.per_source_working[source_url].append(data)
                    logger.info(
                        f"🟢 OK: [{data['group']}] {channel_name} → {data['url'][:80]}"
                    )
                    self.per_source_dead[source_url] += len(candidates) - 1
                    return
                else:
                    logger.debug(f"   ✗ {channel_name}: {reason}")

            self.per_source_dead[source_url] += len(candidates)
            logger.info(
                f"🔴 DEAD: [{candidates[0]['group']}] {channel_name} (all {len(candidates)} links failed)"
            )

    # ---------- Output ----------

    def _emit_channel(self, f, ch):
        f.write(ch["extinf"] + "\n")
        # re-emit directives exactly as parsed (order preserved)
        for d in ch.get("directives", []):
            f.write(d + "\n")
        f.write(ch["url"] + "\n")

    def save_outputs(self):
        logger.info("💾 Sorting and writing output playlists...")

        # Per-source outputs
        written_files = []
        for source_url, channels in self.per_source_working.items():
            # derive a safe filename from source url
            parsed = urlparse(source_url)
            slug = (parsed.path.strip("/") or "playlist").replace("/", "_")
            slug = re.sub(r"[^A-Za-z0-9_.\-]", "_", slug)
            if not slug.endswith(".m3u"):
                slug += ".m3u"
            filename = f"{OUTPUT_PREFIX}{slug}"

            sorted_channels = sorted(channels, key=lambda x: (x["group"], x["name"]))
            with open(filename, "w", encoding="utf-8") as f:
                f.write("#EXTM3U\n")
                for ch in sorted_channels:
                    self._emit_channel(f, ch)
            written_files.append((filename, len(sorted_channels), source_url))
            logger.info(f"   → {filename} ({len(sorted_channels)} channels)")

        # Combined output
        all_working = []
        seen_urls = set()
        for channels in self.per_source_working.values():
            for ch in channels:
                if ch["url"] not in seen_urls:
                    seen_urls.add(ch["url"])
                    all_working.append(ch)

        all_working.sort(key=lambda x: (x["group"], x["name"]))
        with open(COMBINED_FILE, "w", encoding="utf-8") as f:
            f.write("#EXTM3U\n")
            for ch in all_working:
                self._emit_channel(f, ch)
        logger.info(f"   → {COMBINED_FILE} (combined, {len(all_working)} channels)")

        return written_files

    # ---------- Main ----------

    async def run(self):
        if shutil.which("ffprobe") is None:
            logger.critical("❌ FFprobe not found in system PATH!")
            return

        logger.info("🚀 Starting Header-Aware M3U Checker...")

        # ---------- Stage 1: Fetch all sources (rate-limited) ----------
        source_semaphore = asyncio.Semaphore(SOURCE_FETCH_CONCURRENCY)
        fetch_conn = aiohttp.TCPConnector(
            limit=SOURCE_FETCH_CONCURRENCY, ssl=False, ttl_dns_cache=300
        )
        async with aiohttp.ClientSession(connector=fetch_conn) as session:
            fetch_tasks = [
                self.fetch_playlist(session, url, source_semaphore) for url in M3U_SOURCES
            ]
            await asyncio.gather(*fetch_tasks, return_exceptions=True)

        total_unique = sum(len(v) for v in self.per_source_channels.values())
        logger.info(
            f"✅ Loaded {len(self.per_source_channels)} source(s); "
            f"{total_unique} unique channel-names to validate."
        )

        # ---------- Stage 2: Validate streams (header-aware) ----------
        semaphore = asyncio.Semaphore(CONCURRENCY_LIMIT)
        conn = aiohttp.TCPConnector(
            limit=CONCURRENCY_LIMIT,
            ssl=False,
            ttl_dns_cache=300,
            enable_cleanup_closed=True,
        )
        timeout = aiohttp.ClientTimeout(total=HTTP_TIMEOUT)

        async with aiohttp.ClientSession(connector=conn, timeout=timeout) as session:
            tasks = []
            for source_url, channels in self.per_source_channels.items():
                for name, candidates in channels.items():
                    tasks.append(
                        asyncio.create_task(
                            self.process_channel_group(
                                session, semaphore, source_url, name, candidates
                            )
                        )
                    )

            # Process in chunks to keep memory bounded
            chunk_size = 500
            for i in range(0, len(tasks), chunk_size):
                chunk = tasks[i : i + chunk_size]
                await asyncio.gather(*chunk, return_exceptions=True)
                logger.info(
                    f"📊 Progress: {min(i + chunk_size, len(tasks))} / {len(tasks)} channels checked"
                )

        # ---------- Stage 3: Write outputs ----------
        written = self.save_outputs()

        total_working = sum(n for _, n, _ in written)
        total_dead = sum(self.per_source_dead.values())
        logger.info(
            f"🎉 Done! Working channels: {total_working} | Dead/discarded links: {total_dead}"
        )
        logger.info(f"📁 Files written: {', '.join(f for f, _, _ in written)}")


if __name__ == "__main__":
    if sys.platform == "win32":
        asyncio.set_event_loop_policy(asyncio.WindowsProactorEventLoopPolicy())
    processor = M3UProcessor()
    asyncio.run(processor.run())