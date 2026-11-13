"""Print the theorem line range of every negative case. No Lean.

usage (from the repository root):
  python3 -I -B fv/kraken/gen/restructure/tools/negative_case_ranges.py <case file>...

A case file path is relative to fv/kraken (for example gen/checks/negative-cases-checkpoint-and-attestation-data.json).
A case file is a JSON list of cases, or an object with the key "cases".
Each output line is: case file, case id, first line, last line, number of lines.
The ranges come from `cut` of fv/kraken/gen/checks/negative.py, the function that the negative runner uses.
Run it before and after a step. A rename changes no line count, so the two outputs must be equal.
Exit 1 if a case does not resolve to one theorem.
"""
import json
import pathlib
import subprocess
import sys

if len(sys.argv) < 2:
    sys.exit(__doc__)
REPO = pathlib.Path(subprocess.run(["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True,
                                   check=True).stdout.strip())
KRAKEN = REPO / "fv" / "kraken"
sys.path.insert(0, str(KRAKEN / "gen" / "checks"))
import negative  # noqa: E402

failures = 0
for rel in sys.argv[1:]:
    data = json.loads((KRAKEN / rel).read_text())
    cases = data["cases"] if isinstance(data, dict) else data
    for case in cases:
        try:
            _, first, last = negative.cut((KRAKEN / "lean" / case["module"]).read_text(), case["theorem"])
        except (SystemExit, Exception) as e:  # negative.cut stops with SystemExit on a missing theorem
            print(rel, case.get("id"), "ERROR", repr(e)[:200])
            failures += 1
            continue
        print(rel, case.get("id"), first, last, last - first)
sys.exit(1 if failures else 0)
