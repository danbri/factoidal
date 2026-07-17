#!/usr/bin/env python3
"""Generate third_party/testing/xslt1-xalan/manifest.json from the vendored
Apache Xalan conformance submodule.

For every conf/<category>/<name>.xsl that has a matching <name>.xml source
and a conf-gold/<category>/<name>.out gold file, emit one manifest entry in
the {name, category, stylesheet, source, expected, description} schema the
xslt_runner consumes (paths relative to the manifest's directory). Idempotent;
run after bumping the submodule pin. No upstream files are modified.
"""
import os
import re
import json

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
CORPUS = os.path.join(ROOT, "third_party", "testing", "xslt1-xalan")
SUB = os.path.join(CORPUS, "xalan-test-src")
CONF = os.path.join(SUB, "tests", "conf")
GOLD = os.path.join(SUB, "tests", "conf-gold")


def main():
    if not os.path.isdir(CONF) or not os.path.isdir(GOLD):
        raise SystemExit(
            "xalan-test submodule not populated; run tools/ensure-test-env.sh first")
    entries = []
    for cat in sorted(os.listdir(CONF)):
        cdir = os.path.join(CONF, cat)
        gdir = os.path.join(GOLD, cat)
        if not os.path.isdir(cdir) or not os.path.isdir(gdir):
            continue
        for f in sorted(os.listdir(cdir)):
            if not f.endswith(".xsl"):
                continue
            base = f[:-4]
            xsl = os.path.join(cdir, f)
            xml = os.path.join(cdir, base + ".xml")
            out = os.path.join(gdir, base + ".out")
            if not (os.path.isfile(xml) and os.path.isfile(out)):
                continue
            desc = ""
            try:
                with open(xsl, "r", errors="replace") as fh:
                    m = re.search(r"Purpose:\s*(.*)", fh.read(4000))
                    if m:
                        desc = m.group(1).strip().split("-->")[0].strip()[:200]
            except OSError:
                pass
            rel = lambda p: os.path.relpath(p, CORPUS)
            entries.append({
                "name": f"{cat}-{base}",
                "category": cat,
                "stylesheet": rel(xsl),
                "source": rel(xml),
                "expected": rel(out),
                "description": desc,
            })
    with open(os.path.join(CORPUS, "manifest.json"), "w") as fh:
        json.dump(entries, fh, indent=2)
        fh.write("\n")
    print(f"wrote {len(entries)} entries across "
          f"{len({e['category'] for e in entries})} categories")


if __name__ == "__main__":
    main()
