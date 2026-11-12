#!/usr/bin/env python3
"""ENC round trip: the prysm-e2e axioms gate (`axioms_gate.py`, not changed) over E2e, E2eAd, E2eScal, E2eList, E2eEnc
AND E2eDec. Imports `encaxioms_gate.py` (which widens ROOTS / LISTS for E2eList and E2eEnc) and widens them again:
ROOTS gets "E2eDec", LISTS gets `gen/e2e/AxiomsEnc2.lean`. Usage as `encaxioms_gate.py`. Python 3 stdlib only.
"""
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import encaxioms_gate  # noqa: E402,F401
import axioms_gate as g  # noqa: E402

g.ROOTS = g.ROOTS + ["E2eDec"]
g.LISTS = g.LISTS + [HERE / "AxiomsEnc2.lean"]

if __name__ == "__main__":
    a = sys.argv[1:]
    if a[:1] == ["check"] and len(a) == 3:
        sys.exit(g.cmd_check(a[1], a[2]))
    if a[:1] == ["run"] and len(a) >= 3:
        xp, xm, rest = [], [], a[3:]
        while rest:
            if rest[0] == "--extra-lean-path":
                xp.append(rest[1])
            elif rest[0] == "--extra-module":
                xm.append(rest[1])
            else:
                sys.exit(__doc__)
            rest = rest[2:]
        sys.exit(g.cmd_run(a[1], a[2], xp, xm))
    sys.exit(__doc__)
