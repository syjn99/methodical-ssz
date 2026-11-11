#!/usr/bin/env python3
"""Generator tests for the SG-1 extension of `scalgen.py p2dec` (offset-0 form). Tests that can fail.

usage: p2dec_test.py <work-dir> <result.json>      (run from anywhere; one gated job; Python 3 stdlib + git)
exit 0 = every case has its expected exit code and output; 1 = a case differs; 2 = usage

Cases (all on the committed Eth1Data `.S` and IR; mutants are written to <work-dir>, nothing in the repo):
 - old-gen: the frozen generator (git blob OLD_BLOB, method freeze 56dfc27) on Eth1Data: exit 2, 0 bytes on
   stdout, stderr = the committed record line of `prysm/go1.26.10/e2e/e1/gen-e1dec.raw.txt` (historical record).
 - new-gen: the working-tree generator on Eth1Data: exit 0, both fields (DepositRoot offset-0 form,
   BlockHash add form), stdout = the committed `lean/E2eScal/GenE1Dec.lean`, two runs byte-identical.
 - mutants of the `.S` (one line changed or removed, found by exact text at a 1-based line):
   wrong length, missing memmove, an add on another register, offset-0 form with a wrong destination,
   offset-0 form at a non-zero SSZ offset, broken head of the first field, unrecognised directive in place
   of the add. Expected exit 2 (no field matches) or 3 (some fields match), and 0 bytes on stdout always.
 - partial: one mutant again with `--partial-out`: the file starts with `/-! PARTIAL OUTPUT` and names the
   missing field; stdout stays empty.
"""
import json
import pathlib
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent
KR = HERE.parent.parent
OLD_BLOB = "78e3339bc0ff3f20b6daa9a28582c97d7df9f712"
S = "prysm/go1.26.10/e2e/e1/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ.S"
RECORD = "prysm/go1.26.10/e2e/e1/gen-e1dec.raw.txt"
COMMITTED = "lean/E2eScal/GenE1Dec.lean"
ARGS = ["--const", "E1Unmarshal", "--ir", "prysm/ir/ir-mainnet.json", "--type", "v1alpha1.Eth1Data",
        "--prefix", "e1_dec", "--imports", "E2eScal.P2Dec,E2eScal.P2DecZ,E2eScal.E1Code", "--open", "E2eScal.E1Code"]
OLD_ARGS = ["--const", "E1Unmarshal", "--ir", "prysm/ir/ir-mainnet.json", "--type", "v1alpha1.Eth1Data",
            "--prefix", "e1_dec", "--imports", "E2eScal.P2Dec,E2eScal.E1Code", "--open", "E2eScal.E1Code"]

# (id, what, 1-based line, old text, new text or None = delete, expected exit, expected MATCH fields)
MUTANTS = [
    ("m-len", "wrong length: memmove count 0x10 in the offset-0 DepositRoot block", 31,
     "  mov $0x20,%ecx", "  mov $0x10,%ecx", 3, ["BlockHash"]),
    ("m-nomemmove", "missing memmove: the DepositRoot memmove call removed", 32,
     "  callq runtime.memmove", None, 3, ["BlockHash"]),
    ("m-addreg", "an add with a different register: BlockHash `add $0x28,%rsi`", 68,
     "  add $0x28,%rbx", "  add $0x28,%rsi", 3, ["DepositRoot"]),
    ("m-z-dest", "offset-0 form with a wrong destination: DepositRoot pointer stored at 0x10(%rdx)", 29,
     "  mov %rax,0x8(%rdx)", "  mov %rax,0x10(%rdx)", 3, ["BlockHash"]),
    ("m-z-nonzero", "offset-0 form at SSZ offset 40: the BlockHash add removed", 68,
     "  add $0x28,%rbx", None, 3, ["DepositRoot"]),
    ("m-both", "both fields broken: DepositRoot length and the BlockHash add register", None,
     None, None, 2, []),
    ("m-z-srcreg", "offset-0 form with the buffer reloaded into rsi (not the memmove source register)", 30,
     "  mov 0x38(%rsp),%rbx", "  mov 0x38(%rsp),%rsi", 3, ["BlockHash"]),
]


def run(argv, cwd):
    p = subprocess.run(argv, cwd=cwd, capture_output=True)
    return p.returncode, p.stdout, p.stderr.decode("utf-8", "replace")


def mutate(lines, line, old, new):
    if lines[line - 1] != old:
        raise SystemExit(f"mutant base mismatch at line {line}: {lines[line - 1]!r} != {old!r}")
    return lines[:line - 1] + ([] if new is None else [new]) + lines[line:]


def main(work, out):
    work.mkdir(parents=True, exist_ok=True)
    res, bad = [], 0
    old = work / "scalgen_old.py"
    old.write_bytes(subprocess.run(["git", "cat-file", "-p", OLD_BLOB], cwd=KR, capture_output=True, check=True).stdout)
    new = KR / "gen" / "scal" / "scalgen.py"

    # old generator, historical record
    rc, so, se = run(["python3", "-I", str(old), "p2dec", "--S", S] + OLD_ARGS, KR)
    rec = [l for l in (KR / RECORD).read_text().split("\n") if l.startswith("scalgen p2dec:")]
    ok = rc == 2 and so == b"" and rec and se.strip() == rec[0]
    res.append(dict(id="old-gen", expect="exit 2, 0 bytes, stderr = record", exit=rc, stdout_bytes=len(so),
                    stderr=se.strip(), ok=bool(ok)))
    bad |= not ok

    # new generator, two runs, committed output
    outs = []
    for _ in range(2):
        rc, so, se = run(["python3", "-I", str(new), "p2dec", "--S", S] + ARGS, KR)
        outs.append((rc, so, se))
    com = (KR / COMMITTED).read_bytes() if (KR / COMMITTED).exists() else None
    ok = all(r == 0 for r, _, _ in outs) and outs[0][1] == outs[1][1] and outs[0][1] == com
    t = outs[0][1].decode()
    res.append(dict(id="new-gen", expect="exit 0 twice, identical, = committed GenE1Dec.lean", exit=[r for r, _, _ in outs],
                    stdout_bytes=len(outs[0][1]), deterministic=outs[0][1] == outs[1][1], equals_committed=outs[0][1] == com,
                    theorems=[l.split()[1] for l in t.split("\n") if l.startswith("theorem ")], ok=bool(ok)))
    bad |= not ok

    base = (KR / S).read_text().split("\n")
    for (mid, what, line, o, n, want, match) in MUTANTS:
        if mid == "m-both":
            lines = mutate(mutate(base, 31, "  mov $0x20,%ecx", "  mov $0x10,%ecx"), 68, "  add $0x28,%rbx", "  add $0x28,%rsi")
        else:
            lines = mutate(base, line, o, n)
        f = work / f"{mid}.S"
        f.write_text("\n".join(lines))
        rc, so, se = run(["python3", "-I", str(new), "p2dec", "--S", str(f)] + ARGS, KR)
        got = sorted(l.split()[2].rstrip(":") for l in se.split("\n") if ": MATCH form" in l)
        ok = rc == want and so == b"" and (want == 2 or got == sorted(match))
        res.append(dict(id=mid, what=what, expect=f"exit {want}, 0 bytes" + (f", MATCH {match}" if want == 3 else ""),
                        exit=rc, stdout_bytes=len(so), matched=got, stderr=se.strip().split("\n"), ok=bool(ok)))
        bad |= not ok

    # partial output on request
    f = work / "m-addreg.S"
    po = work / "partial.lean"
    if po.exists():
        po.unlink()
    rc, so, se = run(["python3", "-I", str(new), "p2dec", "--S", str(f), "--partial-out", str(po)] + ARGS, KR)
    pt = po.read_text() if po.exists() else ""
    ok = (rc == 3 and so == b"" and pt.startswith("/-! PARTIAL OUTPUT") and "NOT generated: BlockHash" in pt.split("\n")[0]
          and "theorem e1_dec_DepositRoot_seg " in pt and "e1_dec_BlockHash_seg" not in pt)
    res.append(dict(id="partial", expect="exit 3, 0 bytes on stdout, --partial-out file marked PARTIAL, DepositRoot only",
                    exit=rc, stdout_bytes=len(so), partial_first_line=pt.split("\n")[0], ok=bool(ok)))
    bad |= not ok

    out.write_text(json.dumps(dict(cases=res, passed=sum(r["ok"] for r in res), total=len(res)), indent=1) + "\n")
    print(f"p2dec_test: {sum(r['ok'] for r in res)}/{len(res)} as expected")
    for r in res:
        print(("OK  " if r["ok"] else "BAD ") + r["id"], "exit", r["exit"], "stdout", r["stdout_bytes"])
    return 1 if bad else 0


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print(__doc__)
        sys.exit(2)
    sys.exit(main(pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2])))
