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

GEN2 cases (unit G2-G, `p2dec --gen2`; ids `g2-*`; mutated `.S` and IR copies in <work-dir> only):
 - g2-compat-*: the default mode (no `--gen2`) on BlobIdentifier / DepositMessage still prints the committed
   H3 files `GenBiDec.lean` / `GenDmDec.lean` byte for byte.
 - g2-new-*: `--gen2` on Eth1Data, BlobIdentifier, DepositMessage: exit 0 twice, identical, = the committed
   raw files `Gen2E1Dec.lean`, `Gen2BiDec.lean`, `Gen2DmDec.lean`, with every field covered.
 - adversarial `.S` / IR mutants: wrong size immediates, a size other than 32 / 48 / 96, mismatched registers
   in the uint64 triple, base register not rsp / rdx, a scratch register outside the lemma's list, wrong
   displacement against the IR, truncated `.S`, swapped field order (IR and code), a delegated overlay
   field (real BeaconBlockHeader). Expected: the field is "not covered" (no theorem with its name, exit 3) or
   exit 2; 0 bytes on stdout whenever the exit code is not 0; the `--summary` JSON agrees with the exit code.
 - g2-syn48-add: a synthetic `.S` / IR where DepositMessage.WithdrawalCredentials is a 48-byte add-form field
   (no development site has one): the theorem text has the add-form 48 shape and the parameters of the
   synthetic code. Text check only (no Lean code constant for a synthetic `.S`: not kernel-checked).
 - g2-partial: a mutant with `--partial-out`: the file is marked PARTIAL and `kindcheck.py` rejects it.
 - g2c-*: `--compose` = the committed `Gen2BiAccept.lean` / `Gen2DmAccept.lean` / `Gen2E1Accept.lean` (two runs,
   identical; kindcheck PASS "identity-checked"); without `--same-as` the run warns on stderr and kindcheck
   rejects the file (no statement check); a field not covered, a tail store from another register and a
   shifted epilogue give exit 2 and 0 bytes.
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


H3N = "prysm/go1.26.10/e2e/h3/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1."
E1S = S
IR = "prysm/ir/ir-mainnet.json"
G2 = {
    "E1": dict(S=E1S, type="v1alpha1.Eth1Data", committed="lean/E2eScal/Gen2E1Dec.lean",
               args=["--const", "E1Unmarshal", "--prefix", "e1_g2dec", "--imports",
                     "E2eScal.P2Dec,E2eScal.P2DecZ,E2eScal.U64Inline,E2eScal.E1Code", "--open", "E2eScal.E1Code"],
               fields=["DepositRoot", "DepositCount", "BlockHash"]),
    "BI": dict(S=H3N + "BlobIdentifier.UnmarshalSSZ.S", type="v1alpha1.BlobIdentifier",
               committed="lean/E2eScal/Gen2BiDec.lean", old="lean/E2eScal/GenBiDec.lean",
               args=["--const", "BiUnmarshal", "--prefix", "bi_g2dec", "--imports",
                     "E2eScal.P2Dec,E2eScal.P2DecZ,E2eScal.U64Inline,E2eScal.H3Code", "--open", "E2eScal.H3Code"],
               old_args=["--const", "BiUnmarshal", "--prefix", "bi_dec", "--imports",
                         "E2eScal.P2Dec,E2eScal.P2DecZ,E2eScal.H3Code", "--open", "E2eScal.H3Code"],
               fields=["BlockRoot", "Index"]),
    "DM": dict(S=H3N + "DepositMessage.UnmarshalSSZ.S", type="v1alpha1.DepositMessage",
               committed="lean/E2eScal/Gen2DmDec.lean", old="lean/E2eScal/GenDmDec.lean",
               args=["--const", "DmUnmarshal", "--prefix", "dm_g2dec", "--imports",
                     "E2eScal.P2Dec,E2eScal.SegN,E2eScal.U64Inline,E2eScal.H3Code", "--open", "E2eScal.H3Code"],
               old_args=["--const", "DmUnmarshal", "--prefix", "dm_dec", "--imports",
                         "E2eScal.P2Dec,E2eScal.P2DecZ,E2eScal.H3Code", "--open", "E2eScal.H3Code"],
               fields=["PublicKey", "WithdrawalCredentials", "Amount"]),
    "BH": dict(S="prysm/go1.26.10/e2e/bh/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1."
                 "BeaconBlockHeader.UnmarshalSSZ.S", type="v1alpha1.BeaconBlockHeader",
               args=["--const", "BhUnmarshal", "--prefix", "bh_g2dec", "--imports",
                     "E2eScal.P2Dec,E2eScal.BhCode", "--open", "E2eScal.BhCode"],
               fields=["Slot", "ProposerIndex", "ParentRoot", "StateRoot", "BodyRoot"]),
}


def ir_edit(ir, tname, fn):
    """A copy of the IR with the field list of type `tname` (package suffix + name) changed by `fn`."""
    d = json.loads(ir)
    pkg, name = tname.rsplit(".", 1)
    for c in d["configs"]:
        for t in c.get("types", []):
            if t.get("name") == name and t.get("package", "").endswith("/" + pkg):
                fn(t)
    return json.dumps(d)


def ir_size(field, size):
    def fn(t):
        for f in t["ir"]["fields"]:
            if f["key"] == field:
                f["v"]["size"] = size
                f["v"]["fixed_size"] = size
    return fn


def ir_swap(a, b):
    def fn(t):
        fs = t["ir"]["fields"]
        i, j = [k for k, f in enumerate(fs) if f["key"] in (a, b)]
        fs[i], fs[j] = fs[j], fs[i]
    return fn


def edits(lines, eds):
    """Apply (1-based line, old text, new text or None = delete) edits, highest line first."""
    for line, old, new in sorted(eds, key=lambda e: -e[0]):
        lines = mutate(lines, line, old, new)
    return lines


# (id, what, type key, .S edits or a function of the lines, IR edit or None, expected exit, expected covered)
G2_MUT = [
    ("g2-size-imm-head", "PublicKey makeslice size immediate 0x20 instead of 0x30 (IR 48)", "DM",
     [(16, "  mov $0x30,%ecx", "  mov $0x20,%ecx")], None, 3, ["WithdrawalCredentials", "Amount"]),
    ("g2-size-imm-memmove", "PublicKey memmove count 0x20 instead of 0x30 (offset-0 form)", "DM",
     [(31, "  mov $0x30,%ecx", "  mov $0x20,%ecx")], None, 3, ["WithdrawalCredentials", "Amount"]),
    ("g2-size-imm-len", "PublicKey len store 0x20 instead of 0x30 after memmove", "DM",
     [(34, "  movq $0x30,0x8(%rdx)", "  movq $0x20,0x8(%rdx)")], None, 3, ["WithdrawalCredentials", "Amount"]),
    ("g2-size-64", "PublicKey of 64 bytes in IR and code (size outside 32/48/96)", "DM",
     [(16, "  mov $0x30,%ecx", "  mov $0x40,%ecx"), (20, "  movq $0x30,0x10(%rdx)", "  movq $0x40,0x10(%rdx)"),
      (31, "  mov $0x30,%ecx", "  mov $0x40,%ecx"), (34, "  movq $0x30,0x8(%rdx)", "  movq $0x40,0x8(%rdx)"),
      (35, "  movq $0x30,0x10(%rdx)", "  movq $0x40,0x10(%rdx)")], ir_size("PublicKey", 64), 2, []),
    ("g2-size-20-ir", "PublicKey declared 20 bytes in the IR, code unchanged", "DM", [], ir_size("PublicKey", 20), 2, []),
    ("g2-u64-reg-mismatch-load", "Amount: `mov 0x50(%rcx),%rsi` (load into another register)", "DM",
     [(85, "  mov 0x50(%rcx),%rcx", "  mov 0x50(%rcx),%rsi")], None, 3, ["PublicKey", "WithdrawalCredentials"]),
    ("g2-u64-reg-mismatch-store", "Amount: `mov %rsi,0x30(%rdx)` (store from another register)", "DM",
     [(86, "  mov %rcx,0x30(%rdx)", "  mov %rsi,0x30(%rdx)")], None, 3, ["PublicKey", "WithdrawalCredentials"]),
    ("g2-u64-reg-mismatch-reload", "Amount: buffer reloaded into rdi, read through rcx", "DM",
     [(84, "  mov 0x38(%rsp),%rcx", "  mov 0x38(%rsp),%rdi")], None, 3, ["PublicKey", "WithdrawalCredentials"]),
    ("g2-u64-base-not-rsp", "Amount: buffer reload from 0x38(%rbp)", "DM",
     [(84, "  mov 0x38(%rsp),%rcx", "  mov 0x38(%rbp),%rcx")], None, 3, ["PublicKey", "WithdrawalCredentials"]),
    ("g2-u64-base-not-rdx", "Amount: store to 0x30(%rax) (receiver not in rdx)", "DM",
     [(86, "  mov %rcx,0x30(%rdx)", "  mov %rcx,0x30(%rax)")], None, 3, ["PublicKey", "WithdrawalCredentials"]),
    ("g2-u64-reg-rbp", "Amount: scratch register rbp (not in U64InlineReg)", "DM",
     [(84, "  mov 0x38(%rsp),%rcx", "  mov 0x38(%rsp),%rbp"), (85, "  mov 0x50(%rcx),%rcx", "  mov 0x50(%rbp),%rbp"),
      (86, "  mov %rcx,0x30(%rdx)", "  mov %rbp,0x30(%rdx)")], None, 3, ["PublicKey", "WithdrawalCredentials"]),
    ("g2-u64-src-disp", "Amount: source displacement 0x48 against IR SSZ offset 80", "DM",
     [(85, "  mov 0x50(%rcx),%rcx", "  mov 0x48(%rcx),%rcx")], None, 3, ["PublicKey", "WithdrawalCredentials"]),
    ("g2-u64-dst-disp", "Amount: receiver displacement 0x38 against IR Go offset 48", "DM",
     [(86, "  mov %rcx,0x30(%rdx)", "  mov %rcx,0x38(%rdx)")], None, 3, ["PublicKey", "WithdrawalCredentials"]),
    ("g2-u64-32bit", "Index: 32-bit register form `mov 0x20(%rcx),%ecx`", "BI",
     [(49, "  mov 0x20(%rcx),%rcx", "  mov 0x20(%rcx),%ecx")], None, 3, ["BlockRoot"]),
    ("g2-truncated-after-wc", "DepositMessage `.S` cut after directive 83 (Amount read missing)", "DM",
     lambda L: L[:84], None, 3, ["PublicKey", "WithdrawalCredentials"]),
    ("g2-truncated-in-pk", "DepositMessage `.S` cut inside the PublicKey segment (line 30)", "DM",
     lambda L: L[:30], None, 2, []),
    ("g2-ir-order-swap", "IR field order PublicKey / WithdrawalCredentials swapped (SSZ offsets move)", "DM",
     [], ir_swap("PublicKey", "WithdrawalCredentials"), 3, ["Amount"]),
    ("g2-code-order-swap", "Eth1Data code: the DepositCount read moved after the BlockHash segment", "E1",
     lambda L: L[:47] + L[50:86] + L[47:50] + L[86:], None, 2, []),
    ("g2-overlay", "real BeaconBlockHeader: Slot / ProposerIndex are delegated overlay fields", "BH",
     [], None, 3, ["ParentRoot", "StateRoot", "BodyRoot"]),
]


def gen2_cases(work, new):
    res, bad = [], 0
    irt = (KR / IR).read_text()
    # compatibility: default mode = committed H3 files
    for key in ("BI", "DM"):
        c = G2[key]
        rc, so, se = run(["python3", "-I", str(new), "p2dec", "--S", c["S"], "--ir", IR, "--type", c["type"]]
                         + c["old_args"], KR)
        ok = rc == 0 and so == (KR / c["old"]).read_bytes()
        res.append(dict(id=f"g2-compat-{key}", expect=f"default mode exit 0, stdout = {c['old']}", exit=rc,
                        stdout_bytes=len(so), ok=bool(ok)))
        bad |= not ok
    # GEN2 runs, twice, = committed raw output
    for key in ("E1", "BI", "DM"):
        c = G2[key]
        outs = []
        for i in range(2):
            sm = work / f"g2-new-{key}-{i}.json"
            rc, so, se = run(["python3", "-I", str(new), "p2dec", "--gen2", "--summary", str(sm), "--S", c["S"],
                              "--ir", IR, "--type", c["type"]] + c["args"], KR)
            outs.append((rc, so, json.loads(sm.read_text())))
        com = (KR / c["committed"]).read_bytes() if (KR / c["committed"]).exists() else None
        sm = outs[0][2]
        cov = [f["field"] for f in sm["fields"] if f["status"] == "covered"]
        ok = (all(r == 0 for r, _, _ in outs) and outs[0][1] == outs[1][1] and outs[0][1] == com
              and cov == c["fields"] and sm["exit"] == 0)
        res.append(dict(id=f"g2-new-{key}", expect=f"exit 0 twice, identical, = {c['committed']}, covered {c['fields']}",
                        exit=[r for r, _, _ in outs], stdout_bytes=len(outs[0][1]), deterministic=outs[0][1] == outs[1][1],
                        equals_committed=outs[0][1] == com, covered=cov, ok=bool(ok)))
        bad |= not ok
    # adversarial mutants
    for (mid, what, key, eds, iredit, want, cov_want) in G2_MUT:
        c = G2[key]
        base = (KR / c["S"]).read_text().split("\n")
        lines = eds(base) if callable(eds) else edits(base, eds)
        f = work / f"{mid}.S"
        f.write_text("\n".join(lines))
        irp = IR
        if iredit:
            irf = work / f"{mid}.ir.json"
            irf.write_text(ir_edit(irt, c["type"], iredit))
            irp = str(irf)
        sm = work / f"{mid}.summary.json"
        if sm.exists():
            sm.unlink()
        rc, so, se = run(["python3", "-I", str(new), "p2dec", "--gen2", "--summary", str(sm), "--S", str(f),
                          "--ir", irp, "--type", c["type"]] + c["args"], KR)
        s = json.loads(sm.read_text()) if sm.exists() else {}
        cov = [x["field"] for x in s.get("fields", []) if x.get("status") == "covered"]
        reasons = {x["field"]: x.get("reason") for x in s.get("fields", []) if x.get("status") != "covered"}
        ok = rc == want and so == b"" and s.get("exit") == rc and (want == 2 or cov == cov_want)
        res.append(dict(id=mid, what=what, expect=f"exit {want}, 0 bytes" + (f", covered {cov_want}" if want == 3 else ""),
                        exit=rc, stdout_bytes=len(so), covered=cov, not_covered=reasons,
                        stderr=se.strip().split("\n")[-6:], ok=bool(ok)))
        bad |= not ok
    # synthetic 48-byte add-form field (no development site)
    c = G2["DM"]
    base = (KR / c["S"]).read_text().split("\n")
    lines = edits(base, [(50, "  mov $0x20,%ecx", "  mov $0x30,%ecx"), (54, "  movq $0x20,0x28(%rdx)", "  movq $0x30,0x28(%rdx)"),
                         (67, "  mov $0x20,%ecx", "  mov $0x30,%ecx"), (70, "  movq $0x20,0x20(%rdx)", "  movq $0x30,0x20(%rdx)"),
                         (71, "  movq $0x20,0x28(%rdx)", "  movq $0x30,0x28(%rdx)"),
                         (85, "  mov 0x50(%rcx),%rcx", "  mov 0x60(%rcx),%rcx")])
    f = work / "g2-syn48-add.S"
    f.write_text("\n".join(lines))
    irf = work / "g2-syn48-add.ir.json"
    irf.write_text(ir_edit(irt, c["type"], ir_size("WithdrawalCredentials", 48)))
    rc, so, se = run(["python3", "-I", str(new), "p2dec", "--gen2", "--S", str(f), "--ir", str(irf), "--type", c["type"]]
                     + c["args"], KR)
    t = so.decode()
    want = ["@E2eScal.bytesDecSegKind h 48 DmUnmarshal 47 61 48 56 24 24 32 40 48 := by",
            "with_reducible exact E2eScal.bytesdec_seg 48 (Or.inr (Or.inl rfl)) _ _ _ _ _ _ _ _ _ (k + 47) (k + 61) hA hB hl",
            "(hroot : root.length = 48)", "(hav : 48 ≤ avail)", "⋆ Heap (avail - 48)", "Eq ((Int.toBytes 8 48).At aL)",
            "Eq ((Int.toBytes 8 48).At aC)", "(hSrc : bf + (48 : Int64).toBitVec = aSrc)",
            "@E2eScal.u64DecInlineSegKind h DmUnmarshal 83 56 96 48 := by"]
    miss = [w for w in want if w not in t]
    ok = rc == 0 and not miss and "length = 32" not in t.split("dm_g2dec_WithdrawalCredentials_seg")[1].split("theorem")[0]
    res.append(dict(id="g2-syn48-add", what="synthetic 48-byte add-form field (text check only, not kernel-checked)",
                    expect="exit 0; add-form 48 shape with the synthetic parameters", exit=rc, stdout_bytes=len(so),
                    missing=miss, ok=bool(ok)))
    bad |= not ok
    # partial output on request, then kindcheck must reject it
    f = work / "g2-u64-src-disp.S"
    po = work / "g2-partial.lean"
    if po.exists():
        po.unlink()
    rc, so, se = run(["python3", "-I", str(new), "p2dec", "--gen2", "--S", str(f), "--partial-out", str(po), "--ir", IR,
                      "--type", c["type"]] + c["args"], KR)
    pt = po.read_text() if po.exists() else ""
    kc = subprocess.run(["python3", "-I", str(HERE / "kindcheck.py"), str(po)], capture_output=True, text=True)
    ok = (rc == 3 and so == b"" and pt.startswith("/-! PARTIAL OUTPUT") and "NOT generated: Amount" in pt.split("\n")[0]
          and "dm_g2dec_Amount_seg" not in pt and kc.returncode == 1)
    res.append(dict(id="g2-partial", expect="exit 3, PARTIAL file without Amount, kindcheck exit 1", exit=rc,
                    stdout_bytes=len(so), partial_first_line=pt.split("\n")[0], kindcheck_exit=kc.returncode, ok=bool(ok)))
    bad |= not ok
    # composition (`--compose`)
    CP = {"BI": ("bi_e2e_accept_main_gc", "E2eScal.Bi.bi_e2e_accept_main", "lean/E2eScal/Gen2BiAccept.lean",
                 "E2eScal.Compose,E2eScal.Gen2BiDec,E2eScal.BiAccept"),
          "DM": ("dm_e2e_accept_main_gc", "E2eScal.Dm.dm_e2e_accept_main", "lean/E2eScal/Gen2DmAccept.lean",
                 "E2eScal.Compose,E2eScal.Gen2DmDec,E2eScal.DmAccept"),
          "E1": ("e1_e2e_accept_main_gc", "E2eScal.E1.e1_e2e_accept_main", "lean/E2eScal/Gen2E1Accept.lean",
                 "E2eScal.Compose,E2eScal.Gen2E1Dec,E2eScal.E1Accept")}

    def cargs(key, same=True):
        c = G2[key]
        nm, ha, _, imps = CP[key]
        a = list(c["args"])
        a[a.index("--imports") + 1] = imps
        return (["p2dec", "--gen2", "--compose", "--name", nm] + (["--same-as", ha] if same else [])
                + ["--ir", IR, "--type", c["type"]] + a)

    for key in ("BI", "DM", "E1"):
        outs = [run(["python3", "-I", str(new)] + cargs(key) + ["--S", G2[key]["S"]], KR) for _ in range(2)]
        com = (KR / CP[key][2]).read_bytes() if (KR / CP[key][2]).exists() else None
        tf = work / f"g2c-{key}.lean"
        tf.write_bytes(outs[0][1])
        kc = subprocess.run(["python3", "-I", str(HERE / "kindcheck.py"), str(tf)], capture_output=True, text=True)
        ok = (outs[0][0] == 0 and outs[1][0] == 0 and outs[0][1] == outs[1][1] == com and kc.returncode == 0
              and "identity-checked" in kc.stdout)
        res.append(dict(id=f"g2c-new-{key}", expect=f"exit 0 twice, identical, = {CP[key][2]}, kindcheck identity PASS",
                        exit=[o[0] for o in outs], stdout_bytes=len(outs[0][1]), equals_committed=outs[0][1] == com,
                        kindcheck_exit=kc.returncode, ok=bool(ok)))
        bad |= not ok
    rc, so, se = run(["python3", "-I", str(new)] + cargs("BI", same=False) + ["--S", G2["BI"]["S"]], KR)
    tf = work / "g2c-nosame.lean"
    tf.write_bytes(so)
    kc = subprocess.run(["python3", "-I", str(HERE / "kindcheck.py"), str(tf)], capture_output=True, text=True)
    ok = rc == 0 and "NOT checked" in se and "NO statement check" in so.decode() and kc.returncode == 1
    res.append(dict(id="g2c-no-same-as", expect="exit 0, stderr says NOT checked, kindcheck exit 1", exit=rc,
                    stdout_bytes=len(so), kindcheck_exit=kc.returncode, ok=bool(ok)))
    bad |= not ok
    base = (KR / G2["DM"]["S"]).read_text().split("\n")
    for (mid, what, eds) in [
            ("g2c-not-covered", "Amount not covered (source displacement 0x48)", [(85, "  mov 0x50(%rcx),%rcx", "  mov 0x48(%rcx),%rcx")]),
            ("g2c-tail-reg", "PublicKey tail store from rsi instead of rdi", [(47, "  mov %rdi,(%rdx)", "  mov %rsi,(%rdx)")]),
            ("g2c-epilogue", "epilogue frame 0x28", [(89, "  add $0x20,%rsp", "  add $0x28,%rsp")])]:
        f = work / f"{mid}.S"
        f.write_text("\n".join(edits(base, eds)))
        rc, so, se = run(["python3", "-I", str(new)] + cargs("DM") + ["--S", str(f)], KR)
        ok = rc == 2 and so == b""
        res.append(dict(id=mid, what=what, expect="exit 2, 0 bytes", exit=rc, stdout_bytes=len(so),
                        stderr=se.strip().split("\n")[-1:], ok=bool(ok)))
        bad |= not ok
    return res, bad


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
        got = sorted(l.split()[3].rstrip(":") for l in se.split("\n") if ": MATCH form" in l)
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

    r2, b2 = gen2_cases(work, new)
    res += r2
    bad |= b2

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
