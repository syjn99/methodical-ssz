"""Forwarder to gen/checks/axioms_gate.py, kept only for the CI workflow.

The workflow file .github/workflows/fv-lean.yaml names this path (`sys.path.insert(0, '../gen/e2e')` and
`python3 -B fv/kraken/gen/e2e/axioms_gate.py run ...`). The workflow file cannot be changed with the access of this
session. When the workflow names gen/checks/axioms_gate.py (the two-line change is recorded in gen/path-names.tsv),
delete this file and its directory.
"""
import importlib.util
import pathlib
import sys

_spec = importlib.util.spec_from_file_location(
    "axioms_gate_checks", pathlib.Path(__file__).resolve().parent.parent / "checks" / "axioms_gate.py")
_gate = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_gate)
globals().update({k: v for k, v in vars(_gate).items() if not k.startswith("__")})

if __name__ == "__main__":
    sys.exit(_gate.main(sys.argv[1:]))
