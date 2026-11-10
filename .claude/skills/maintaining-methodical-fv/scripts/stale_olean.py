#!/usr/bin/env python3
"""List Lean build artifacts that must not be trusted after a capped or killed build.

usage: stale_olean.py --src SRC_ROOT --build LIB_ROOT [--since EPOCH | --marker FILE]

SRC_ROOT holds the sources (A/B.lean). LIB_ROOT holds the artifacts in the
same layout (A/B.olean, A/B.ilean), for example `.lake/build/lib/lean` in Lake.

Flags, one line each:
  STALE   artifact older than its source
  ORPHAN  artifact whose source is missing
  AFTER   artifact written at or after --since / the --marker file's mtime
          (use the start time of the failed or killed job: anything it wrote
          is suspect)

Exit codes: 0 nothing flagged, 1 something flagged, 2 usage error (missing
directory, no artifact found, bad --since or --marker).

Limits: file mtimes only. It does not read Lake trace hashes and does not
follow imports, so a module whose own source is unchanged but whose
dependency changed is NOT flagged. A clean result is "no mtime evidence of
staleness", not "the build is sound". After a killed build, a clean rebuild
(or a reviewer's cold rebuild in a fresh copy) is still the stronger check.
"""
import argparse
import os
import sys

EXTS = (".olean", ".ilean")


def main(argv):
    p = argparse.ArgumentParser(add_help=True)
    p.add_argument("--src", required=True)
    p.add_argument("--build", required=True)
    g = p.add_mutually_exclusive_group()
    g.add_argument("--since", type=float)
    g.add_argument("--marker")
    try:
        a = p.parse_args(argv)
    except SystemExit:
        return 2
    for d in (a.src, a.build):
        if not os.path.isdir(d):
            print(f"stale_olean: not a directory: {d}", file=sys.stderr)
            return 2
    since = a.since
    if a.marker is not None:
        try:
            since = os.stat(a.marker).st_mtime
        except OSError as e:
            print(f"stale_olean: bad marker: {e}", file=sys.stderr)
            return 2
    seen = 0
    flagged = 0
    for root, _dirs, files in os.walk(a.build):
        for fn in sorted(files):
            if not fn.endswith(EXTS):
                continue
            seen += 1
            art = os.path.join(root, fn)
            rel = os.path.relpath(art, a.build)
            src = os.path.join(a.src, os.path.splitext(rel)[0] + ".lean")
            amt = os.stat(art).st_mtime
            reasons = []
            if not os.path.exists(src):
                reasons.append("ORPHAN")
            elif os.stat(src).st_mtime > amt:
                reasons.append("STALE")
            if since is not None and amt >= since:
                reasons.append("AFTER")
            for r in reasons:
                print(f"{r}\t{rel}")
            if reasons:
                flagged += 1
    if seen == 0:
        print(f"stale_olean: no .olean/.ilean under {a.build}", file=sys.stderr)
        return 2
    print(f"SUMMARY artifacts={seen} flagged={flagged}")
    return 1 if flagged else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
