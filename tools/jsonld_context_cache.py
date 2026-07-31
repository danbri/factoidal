#!/usr/bin/env python3
"""Index maintenance for third_party/jsonld-context-cache/.

Layout, per the cache README:

    <cache>/<domain>/<sha256(requested-url)>.v<N>.jsonld

The cache key is the sha256 of the REQUESTED url, and the folder is that
url's host. Both are properties of what a document cites, not of where
the bytes came from -- w3id.org redirects to w3c.github.io, and a
document citing the w3id.org IRI must resolve under the w3id.org key.

A new v<N> is minted only when the fetched bytes differ from the newest
stored snapshot. Re-running `add` on an unchanged upstream is therefore
a no-op, and a changed upstream is preserved as history rather than
overwriting what earlier documents were signed against.

Every entry is self-authenticating: `verify` re-hashes each file on disk
and re-derives each url hash, so a corrupted or hand-edited snapshot is
detected without a network fetch.
"""
from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import os
import sys


def load(index_path: str) -> dict:
    if not os.path.exists(index_path):
        return {"contexts": {}}
    with open(index_path, encoding="utf-8") as fh:
        return json.load(fh)


def save(index_path: str, data: dict) -> None:
    with open(index_path, "w", encoding="utf-8") as fh:
        json.dump(data, fh, indent=2, sort_keys=True)
        fh.write("\n")


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def cmd_store(args: argparse.Namespace) -> int:
    index_path = os.path.join(args.cache, "index.json")
    data = load(index_path)

    with open(args.body, "rb") as fh:
        raw = fh.read()
    content_sha = sha256_bytes(raw)

    # The url hash is recomputed here rather than trusted from the shell,
    # so the index can never disagree with its own key.
    derived = sha256_bytes(args.url.encode("utf-8"))
    if derived != args.url_sha:
        print(f"url-hash mismatch: shell said {args.url_sha}, derived {derived}",
              file=sys.stderr)
        return 1

    entry = data["contexts"].setdefault(
        args.url, {"domain": args.domain, "url_sha256": derived, "versions": []}
    )
    versions = entry["versions"]

    if versions and versions[-1]["content_sha256"] == content_sha:
        print(f"unchanged  v{versions[-1]['version']}  {args.url}")
        return 0

    version = (versions[-1]["version"] + 1) if versions else 1
    rel = os.path.join(args.domain, f"{derived}.v{version}.jsonld")
    with open(os.path.join(args.cache, rel), "wb") as fh:
        fh.write(raw)

    # A context that is not parseable JSON is a cache-poisoning risk for
    # every consumer, so refuse to record one.
    try:
        json.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        os.unlink(os.path.join(args.cache, rel))
        print(f"REFUSED (not valid JSON): {args.url}: {exc}", file=sys.stderr)
        return 1

    versions.append({
        "version": version,
        "path": rel,
        "content_sha256": content_sha,
        "bytes": len(raw),
        "retrieved": datetime.datetime.now(datetime.timezone.utc)
                             .strftime("%Y-%m-%d"),
        "final_url": args.final_url,
        "content_type": args.content_type,
    })
    save(index_path, data)
    print(f"stored     v{version}  {args.url}  ({len(raw)} bytes, {rel})")
    return 0


def cmd_verify(args: argparse.Namespace) -> int:
    data = load(os.path.join(args.cache, "index.json"))
    bad = 0
    total = 0
    for url, entry in sorted(data["contexts"].items()):
        if sha256_bytes(url.encode("utf-8")) != entry["url_sha256"]:
            print(f"BAD url hash: {url}")
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
    print(f"verify: {total - bad} of {total} snapshot(s) intact, "
          f"{len(data['contexts'])} url(s)")
    return 1 if bad else 0


def cmd_list(args: argparse.Namespace) -> int:
    data = load(os.path.join(args.cache, "index.json"))
    if not data["contexts"]:
        print("cache is empty")
        return 0
    for url, entry in sorted(data["contexts"].items()):
        newest = entry["versions"][-1]
        print(f"{url}")
        print(f"    domain     {entry['domain']}")
        print(f"    url sha256 {entry['url_sha256']}")
        for ver in entry["versions"]:
            mark = "*" if ver is newest else " "
            print(f"  {mark} v{ver['version']}  {ver['bytes']:>6} bytes  "
                  f"{ver['retrieved']}  {ver['content_sha256'][:16]}…")
            if ver["final_url"] != url:
                print(f"        via {ver['final_url']}")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    sub = ap.add_subparsers(dest="cmd", required=True)

    p = sub.add_parser("store")
    p.add_argument("--cache", required=True)
    p.add_argument("--url", required=True)
    p.add_argument("--domain", required=True)
    p.add_argument("--url-sha", required=True)
    p.add_argument("--body", required=True)
    p.add_argument("--content-type", default="")
    p.add_argument("--final-url", default="")
    p.set_defaults(fn=cmd_store)

    for name, fn in (("verify", cmd_verify), ("list", cmd_list)):
        p = sub.add_parser(name)
        p.add_argument("--cache", required=True)
        p.set_defaults(fn=fn)

    args = ap.parse_args()
    return args.fn(args)


if __name__ == "__main__":
    sys.exit(main())
