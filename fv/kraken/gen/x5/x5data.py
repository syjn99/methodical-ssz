#!/usr/bin/env python3
"""X5 data items of the Go 1.26.10 namespace, written with link/data.py's code and format.

Usage: x5data.py <outdir>     (the X5 link dir; writes <outdir>/data/*.data)
The items are the two data operands of the Go 1.26.10 v1alpha1.Checkpoint decoder (the makeslice element
type word and the ssz.ErrSize global, address only). No X5 proof reads them yet (the X5 size proofs read
no data); they are here so that link/check.py (f) compares real Go 1.26.10 data with the ELF and so that
(d), which runs after (f), runs. Python 3 standard library only.
"""
import importlib.util
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
LINK = HERE.parent.parent / "link"
spec = importlib.util.spec_from_file_location("data", LINK / "data.py")
data = importlib.util.module_from_spec(spec)
spec.loader.exec_module(data)

out = pathlib.Path(sys.argv[1])
cp = (out / "norm" / "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ.S").read_text()
ins = [l.strip() for l in cp.split("\n")]
i = ins.index("callq runtime.makeslice")
off = int(re.fullmatch(r"lea type__\+(\d+)\(%rip\),%rax", next(x for x in reversed(ins[:i]) if x.startswith("lea type__")))[1])
data.ITEMS = [("x5CpElemType", "type__", off, 48, data.ABI_TYPE_WORDS), ("x5ErrSize", "ssz.ErrSize", 0, 0, [])]
data.main(out)
