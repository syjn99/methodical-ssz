#!/usr/bin/env python3
"""Classify the outputs of gen/prysm-tests.sh against the known failures.

Usage: prysm_tests_classify.py <out-dir> <result.json>
Known failures (cited from the prysm-fv-pin-smoke run, REPORT section 6; GENERATOR-FINDINGS 2 and 3):
- KNOWN_SUBTESTS: three error-text subtests of consensus-types/blocks (cause: generator 280b752),
  in the mainnet runs that include that package.
- KNOWN_MINIMAL: under -tags minimal, consensus-types/blocks test files do not build and
  encoding/ssz/detect TestByState panics (same on the committed baseline files).
Every other failure (a test, a build, a package-level FAIL line or a panic not explained by a known
failure of that run), a missing run output, or a known failure that is gone, is "unexpected".
Exit status 0 only if nothing is unexpected. Python 3 standard library only. Run with python3 -I.
"""
import json
import re
import sys

KNOWN_SUBTESTS = {"TestMarshalPartsMetadata/available_too_large", "TestMarshalPartsMetadata/requests_too_large",
                  "TestPartialDataColumn_PartsMetadata/marshal_error_due_max_bitlist_size"}
KNOWN_PARENTS = {"TestMarshalPartsMetadata", "TestPartialDataColumn_PartsMetadata"}
# the one panic of the known minimal detect TestByState failure (no other panic is masked)
KNOWN_PANIC = "panic: runtime error: index out of range [64] with length 64 [recovered, repanicked]"


def main():
    out_dir, res_path = sys.argv[1:3]
    runs = []
    for line in open(f"{out_dir}/summary.txt"):
        m = re.match(r"t(\d+) rc=(\d+) tags=\[(.*?)\] run=\[(.*?)\] pkgs=(.*)$", line.strip())
        n = int(m.group(1))
        txt = open(f"{out_dir}/t{n:02d}.out").read()
        runs.append({"run": n, "rc": int(m.group(2)), "tags": m.group(3), "filter": m.group(4), "pkgs": m.group(5).split(),
                     "failed_tests": sorted(set(re.findall(r"^\s*--- FAIL: (\S+)", txt, re.M))),
                     "failed_pkgs": sorted(set(re.findall(r"^FAIL[ \t]+(\S+)", txt, re.M))),
                     "build_failed": sorted(set(re.findall(r"^FAIL[ \t]+(\S+) \[build failed\]", txt, re.M))),
                     "panics": re.findall(r"^panic:.*$", txt, re.M),
                     "ok_pkgs": sorted(set(re.findall(r"^ok[ \t]+(\S+)", txt, re.M)))})
    unexpected = []
    seen_known = set()
    for r in runs:
        blocks = any(p.endswith("consensus-types/blocks") for p in r["pkgs"])
        for t in r["failed_tests"]:
            if t in KNOWN_SUBTESTS and r["tags"] == "" and blocks:
                seen_known.add(t)
            elif t in KNOWN_PARENTS and r["tags"] == "" and blocks:
                pass
            elif t == "TestByState" and r["tags"] == "minimal" and any(p.endswith("encoding/ssz/detect") for p in r["pkgs"]):
                seen_known.add("minimal:detect:TestByState")
            else:
                unexpected.append(f"t{r['run']}: failed test {t}")
        for p in r["build_failed"]:
            if p.endswith("consensus-types/blocks") and r["tags"] == "minimal":
                seen_known.add("minimal:blocks:build")
            else:
                unexpected.append(f"t{r['run']}: build failed {p}")
        if r["rc"] != 0 and not (r["failed_tests"] or r["build_failed"]):
            unexpected.append(f"t{r['run']}: rc {r['rc']} without a failed test or build")
        # package-level FAIL lines and panics must be explained by a known failure of that run
        known_blocks = r["tags"] == "" and bool(set(r["failed_tests"]) & KNOWN_SUBTESTS)
        known_detect = r["tags"] == "minimal" and "TestByState" in r["failed_tests"]
        for p in r["failed_pkgs"]:
            if p.endswith("consensus-types/blocks") and (known_blocks or (r["tags"] == "minimal" and p in r["build_failed"])):
                continue
            if p.endswith("encoding/ssz/detect") and known_detect:
                continue
            unexpected.append(f"t{r['run']}: package FAIL {p}")
        allowed = [KNOWN_PANIC] if known_detect else []
        if r["panics"] and r["panics"] != allowed:
            unexpected.append(f"t{r['run']}: panics {r['panics']} other than the one known minimal detect TestByState panic")
    want = KNOWN_SUBTESTS | {"minimal:blocks:build", "minimal:detect:TestByState"}
    for k in sorted(want - seen_known):
        unexpected.append(f"known failure not seen: {k}")
    res = {"schema": "fvphase1c.prysm-tests/4", "runs": runs, "known_seen": sorted(seen_known), "unexpected": unexpected,
           "verdict": "only known failures" if not unexpected else "UNEXPECTED"}
    json.dump(res, open(res_path, "w"), indent=1)
    print(json.dumps({"verdict": res["verdict"], "unexpected": unexpected, "known_seen": sorted(seen_known)}, indent=1))
    return 0 if not unexpected else 1


if __name__ == "__main__":
    sys.exit(main())
