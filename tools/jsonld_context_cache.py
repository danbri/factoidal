#!/usr/bin/env python3
"""Offline, URL-keyed cache of remote JSON-LD `@context` documents.

    third_party/jsonld-context-cache/<domain>/<sha256(url)>/v<N>.jsonld

Commands (all also reachable via tools/jsonld-context-cache.sh):

    add URL...        fetch and store; idempotent
    resolve URL       print the cached body -- THE READ PATH, no network
    refresh           re-fetch every known URL, minting vN only on change
    verify            re-hash every snapshot offline
    list              print the index

`resolve` is the operation consumers want: it is the shape of
`JSONLD.Loader.jsonld_load_document : string -> option string`, so an
OCaml/JS document loader (issue #275) can shell out to it or port
`resolve_body` below.

Importable:

    from jsonld_context_cache import resolve_body, normalize_url
    body = resolve_body(cache_dir, "https://www.w3.org/ns/did/v1")  # str|None

Design rules, each with a reason:

* The cache key is the NORMALIZED REQUESTED url, never the redirect
  target. A document citing an IRI must resolve under that IRI.
* A new v<N> appears only when bytes change, so history survives an
  upstream revision -- a signed document was signed against whichever
  revision was live at the time.
* Writes are atomic (tmp + os.replace) and the index is written under an
  exclusive lock, so a crash or a concurrent run cannot publish a
  truncated snapshot or a half-updated index.
* A body that is not parseable JSON is refused: an unparseable cached
  context poisons every consumer that resolves it.
"""
from __future__ import annotations

import argparse
import datetime
import errno
import fcntl
import hashlib
import json
import os
import re
import subprocess
import sys
import time
import urllib.parse

# Transient conditions worth a retry. 429/5xx are server-side and often
# clear; curl 6/7/28/35/52/56 are DNS, connect, timeout and TLS/read
# failures. A 404 is NOT retried -- it is an answer, not a hiccup.
RETRY_HTTP = {408, 429, 500, 502, 503, 504}
RETRY_CURL = {6, 7, 28, 35, 52, 56}
RETRY_DELAYS = (2, 4, 8)

# A domain becomes a directory name, so it is validated rather than
# trusted: host[:port] only, no separators, no traversal.
SAFE_DOMAIN = re.compile(r"^[a-z0-9.\-]+(?::[0-9]{1,5})?$")

JSONISH = ("application/ld+json", "application/json", "+json", "text/json")


# --------------------------------------------------------------------
# URL normalization
# --------------------------------------------------------------------

def normalize_url(url: str) -> str:
    """Canonical cache key for `url`.

    Only transformations that cannot change which document is served:
    scheme and host are case-insensitive per RFC 3986 and are lowercased;
    the default port is redundant and is dropped; a fragment is never
    sent to the server so it cannot select a document. Path and query
    are left EXACTLY alone -- they are case-sensitive and percent-
    encoding is meaningful, so touching them could silently alias two
    different resources onto one cache entry.
    """
    parts = urllib.parse.urlsplit(url.strip())
    if parts.scheme.lower() not in ("http", "https"):
        raise ValueError(f"only http/https URLs can be cached: {url!r}")
    if not parts.hostname:
        raise ValueError(f"URL has no host: {url!r}")

    host = parts.hostname.lower()
    port = parts.port
    if port is not None and not (
        (parts.scheme.lower() == "http" and port == 80)
        or (parts.scheme.lower() == "https" and port == 443)
    ):
        host = f"{host}:{port}"

    if parts.username or parts.password:
        raise ValueError(f"refusing to cache a URL with credentials: {url!r}")

    return urllib.parse.urlunsplit(
        (parts.scheme.lower(), host, parts.path, parts.query, "")
    )


def url_key(url: str) -> str:
    return hashlib.sha256(url.encode("utf-8")).hexdigest()


def domain_of(url: str) -> str:
    domain = urllib.parse.urlsplit(url).netloc.lower()
    if not SAFE_DOMAIN.match(domain):
        raise ValueError(f"unsafe domain for a directory name: {domain!r}")
    return domain


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


# --------------------------------------------------------------------
# Index I/O
# --------------------------------------------------------------------

def index_path(cache: str) -> str:
    return os.path.join(cache, "index.json")


class IndexLock:
    """Exclusive lock around a read-modify-write of index.json.

    Two `add` runs in parallel would otherwise race: both read the same
    index, both append, and the second write loses the first's entry.
    """

    def __init__(self, cache: str):
        self.path = os.path.join(cache, ".index.lock")
        self.fh = None

    def __enter__(self):
        os.makedirs(os.path.dirname(self.path) or ".", exist_ok=True)
        self.fh = open(self.path, "w", encoding="utf-8")
        fcntl.flock(self.fh, fcntl.LOCK_EX)
        return self

    def __exit__(self, *exc):
        fcntl.flock(self.fh, fcntl.LOCK_UN)
        self.fh.close()
        return False


def load_index(cache: str) -> dict:
    path = index_path(cache)
    if not os.path.exists(path):
        return {"contexts": {}}
    with open(path, encoding="utf-8") as fh:
        return json.load(fh)


def save_index(cache: str, data: dict) -> None:
    """Atomic: a crash mid-write must not leave an unparseable index."""
    path = index_path(cache)
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as fh:
        json.dump(data, fh, indent=2, sort_keys=True)
        fh.write("\n")
        fh.flush()
        os.fsync(fh.fileno())
    os.replace(tmp, path)


def write_atomic(path: str, raw: bytes) -> None:
    tmp = path + ".tmp"
    with open(tmp, "wb") as fh:
        fh.write(raw)
        fh.flush()
        os.fsync(fh.fileno())
    os.replace(tmp, path)


# --------------------------------------------------------------------
# The read path
# --------------------------------------------------------------------

def resolve_entry(cache: str, url: str, version: int | None = None):
    """Return (version_record, absolute_path) for `url`, or (None, None)."""
    try:
        key = normalize_url(url)
    except ValueError:
        return None, None
    entry = load_index(cache)["contexts"].get(key)
    if not entry or not entry["versions"]:
        return None, None
    if version is None:
        rec = entry["versions"][-1]
    else:
        matches = [v for v in entry["versions"] if v["version"] == version]
        if not matches:
            return None, None
        rec = matches[0]
    return rec, os.path.join(cache, rec["path"])


def resolve_body(cache: str, url: str, version: int | None = None,
                 check_digest: bool = True) -> str | None:
    """Cached body for `url`, or None. No network, ever.

    This is the function a documentLoader wants. With `check_digest`
    (the default) the bytes are re-hashed against the index before being
    handed back, so a corrupted snapshot fails closed rather than
    silently feeding a wrong context into expansion.
    """
    rec, path = resolve_entry(cache, url, version)
    if rec is None or not os.path.exists(path):
        return None
    with open(path, "rb") as fh:
        raw = fh.read()
    if check_digest and sha256_bytes(raw) != rec["content_sha256"]:
        return None
    return raw.decode("utf-8")


# --------------------------------------------------------------------
# Fetch
# --------------------------------------------------------------------

def fetch(url: str, timeout: int = 30) -> tuple[bytes, str, str]:
    """Fetch `url`, retrying transient failures. Returns (body, ct, final).

    Raises RuntimeError with a specific message on permanent failure, so
    a caller can report which URL failed and why rather than a bare
    non-zero exit (anti-pattern #14 -- never swallow a failed fetch).
    """
    last = "no attempt made"
    for attempt, delay in enumerate([0, *RETRY_DELAYS]):
        if delay:
            time.sleep(delay)
        tmp = None
        try:
            import tempfile
            fd, tmp = tempfile.mkstemp(prefix="jsonld-ctx-")
            os.close(fd)
            proc = subprocess.run(
                ["curl", "-sS", "-L", "--max-time", str(timeout),
                 "-H", "Accept: application/ld+json, application/json;q=0.9",
                 "-w", "%{http_code}\t%{content_type}\t%{url_effective}",
                 "--proto", "=https", "--proto-redir", "=https",
                 "-o", tmp, url],
                capture_output=True, text=True, check=False,
            )
            if proc.returncode != 0:
                last = f"curl exit {proc.returncode}: {proc.stderr.strip()[:200]}"
                if proc.returncode in RETRY_CURL and attempt < len(RETRY_DELAYS):
                    continue
                raise RuntimeError(last)

            code_s, ctype, final = (proc.stdout.split("\t") + ["", "", ""])[:3]
            code = int(code_s) if code_s.isdigit() else 0
            if code != 200:
                last = f"HTTP {code}"
                if code in RETRY_HTTP and attempt < len(RETRY_DELAYS):
                    continue
                raise RuntimeError(last)

            with open(tmp, "rb") as fh:
                return fh.read(), ctype.strip(), final.strip()
        finally:
            if tmp and os.path.exists(tmp):
                os.unlink(tmp)
    raise RuntimeError(last)


def store(cache: str, url: str, raw: bytes, ctype: str, final: str) -> str:
    """Store `raw` under `url`. Returns a one-line human status."""
    key = normalize_url(url)
    domain = domain_of(key)
    digest = url_key(key)

    try:
        json.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise RuntimeError(f"body is not valid JSON ({exc})") from exc

    content_sha = sha256_bytes(raw)
    with IndexLock(cache):
        data = load_index(cache)
        entry = data["contexts"].setdefault(
            key, {"domain": domain, "url_sha256": digest, "versions": []})
        versions = entry["versions"]
        if versions and versions[-1]["content_sha256"] == content_sha:
            return f"unchanged  v{versions[-1]['version']}  {key}"

        # The url hash names a FOLDER, and each snapshot is a plain
        # v<N>.jsonld inside it. Every version of one URL therefore sits
        # together, `ls` of a domain lists URLs rather than a flat wall of
        # hash-dot-version filenames, and a whole URL is removed by
        # deleting one directory.
        version = (versions[-1]["version"] + 1) if versions else 1
        rel = os.path.join(domain, digest, f"v{version}.jsonld")
        os.makedirs(os.path.join(cache, domain, digest), exist_ok=True)
        write_atomic(os.path.join(cache, rel), raw)
        versions.append({
            "version": version,
            "path": rel,
            "content_sha256": content_sha,
            "bytes": len(raw),
            "retrieved": datetime.datetime.now(datetime.timezone.utc)
                                 .strftime("%Y-%m-%d"),
            "final_url": final,
            "content_type": ctype,
        })
        save_index(cache, data)

    note = ""
    if not any(j in ctype.lower() for j in JSONISH):
        note = f"  [warn: content-type {ctype!r} is not JSON-ish]"
    if final and final != key:
        note += f"  [via {final}]"
    return f"stored     v{version}  {key}  ({len(raw)} bytes){note}"


# --------------------------------------------------------------------
# Commands
# --------------------------------------------------------------------

def cmd_add(args) -> int:
    failures = 0
    for url in args.urls:
        try:
            # Validate BEFORE the network call, never after. curl happily
            # dereferences file:// (local file read) and ftp://, so handing
            # it an unvalidated URL is a local-file-disclosure hole and a
            # way to hang the tool on a protocol we never cache. Fail fast.
            key = normalize_url(url)
            domain_of(key)
            raw, ctype, final = fetch(key, args.timeout)
            print(store(args.cache, key, raw, ctype, final))
        except (RuntimeError, ValueError) as exc:
            # Continue: one dead URL must not abandon the rest of a batch.
            print(f"FAILED     {url}: {exc}", file=sys.stderr)
            failures += 1
    if failures:
        print(f"{failures} of {len(args.urls)} URL(s) failed", file=sys.stderr)
    return 1 if failures else 0


def cmd_refresh(args) -> int:
    urls = sorted(load_index(args.cache)["contexts"])
    if not urls:
        print("cache is empty")
        return 0
    args.urls = urls
    return cmd_add(args)


def cmd_resolve(args) -> int:
    body = resolve_body(args.cache, args.url, args.version)
    if body is None:
        # Distinguish absent from corrupt. Reporting a digest mismatch as
        # "not cached" would send someone off to re-fetch a URL whose real
        # problem is a tampered or truncated file on disk -- the same
        # message-conflation defect we flagged in the JSON-LD loader.
        rec, path = resolve_entry(args.cache, args.url, args.version)
        if rec is None:
            print(f"not cached: {args.url}", file=sys.stderr)
        elif not os.path.exists(path):
            print(f"indexed but MISSING on disk: {rec['path']} "
                  f"({args.url}) — run verify", file=sys.stderr)
        else:
            print(f"CORRUPT: {rec['path']} does not match its recorded "
                  f"sha256 ({args.url}) — run verify", file=sys.stderr)
        return 1
    if args.path_only:
        _, path = resolve_entry(args.cache, args.url, args.version)
        print(path)
    else:
        sys.stdout.write(body)
    return 0


def cmd_verify(args) -> int:
    data = load_index(args.cache)
    bad = total = 0
    for url, entry in sorted(data["contexts"].items()):
        if url_key(url) != entry["url_sha256"]:
            print(f"BAD url hash: {url}")
            bad += 1
        if url != normalize_url(url):
            print(f"BAD key (not normalized): {url}")
            bad += 1
        for ver in entry["versions"]:
            total += 1
            path = os.path.join(args.cache, ver["path"])
            if not os.path.exists(path):
                print(f"MISSING {ver['path']}")
                bad += 1
                continue
            with open(path, "rb") as fh:
                raw = fh.read()
            if sha256_bytes(raw) != ver["content_sha256"]:
                print(f"BAD content hash: {ver['path']}")
                bad += 1
            elif len(raw) != ver["bytes"]:
                print(f"BAD byte count: {ver['path']}")
                bad += 1
    # An orphan file is a real defect: something wrote into the cache
    # without going through this tool.
    indexed = {os.path.join(args.cache, v["path"])
               for e in data["contexts"].values() for v in e["versions"]}
    for root, _dirs, files in os.walk(args.cache):
        for name in files:
            full = os.path.join(root, name)
            if name.endswith(".jsonld") and full not in indexed:
                print(f"ORPHAN (on disk, not in index): "
                      f"{os.path.relpath(full, args.cache)}")
                bad += 1
    print(f"verify: {total - bad} of {total} snapshot(s) intact, "
          f"{len(data['contexts'])} url(s)")
    return 1 if bad else 0


def cmd_list(args) -> int:
    data = load_index(args.cache)
    if not data["contexts"]:
        print("cache is empty")
        return 0
    for url, entry in sorted(data["contexts"].items()):
        newest = entry["versions"][-1]
        print(url)
        print(f"    domain     {entry['domain']}")
        print(f"    url sha256 {entry['url_sha256']}")
        for ver in entry["versions"]:
            mark = "*" if ver is newest else " "
            print(f"  {mark} v{ver['version']}  {ver['bytes']:>6} bytes  "
                  f"{ver['retrieved']}  {ver['content_sha256'][:16]}…")
            if ver["final_url"] and ver["final_url"] != url:
                print(f"        via {ver['final_url']}")
    return 0


def default_cache() -> str:
    here = os.path.dirname(os.path.abspath(__file__))
    return os.path.join(os.path.dirname(here),
                        "third_party", "jsonld-context-cache")


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Offline URL-keyed JSON-LD @context cache.")
    ap.add_argument("--cache", default=default_cache())
    sub = ap.add_subparsers(dest="cmd", required=True)

    p = sub.add_parser("add", help="fetch and store (idempotent)")
    p.add_argument("urls", nargs="+")
    p.add_argument("--timeout", type=int, default=30)
    p.set_defaults(fn=cmd_add)

    p = sub.add_parser("refresh", help="re-fetch every known URL")
    p.add_argument("--timeout", type=int, default=30)
    p.set_defaults(fn=cmd_refresh)

    p = sub.add_parser("resolve", help="print the cached body (no network)")
    p.add_argument("url")
    p.add_argument("--version", type=int, default=None)
    p.add_argument("--path-only", action="store_true")
    p.set_defaults(fn=cmd_resolve)

    for name, fn, helptext in (
        ("verify", cmd_verify, "re-hash every snapshot offline"),
        ("list", cmd_list, "print the index"),
    ):
        p = sub.add_parser(name, help=helptext)
        p.set_defaults(fn=fn)

    args = ap.parse_args()
    os.makedirs(args.cache, exist_ok=True)
    try:
        return args.fn(args)
    except BrokenPipeError:          # `… resolve URL | head` is not an error
        try:
            sys.stdout.close()
        except OSError as exc:
            if exc.errno != errno.EPIPE:
                raise
        return 0


if __name__ == "__main__":
    sys.exit(main())
