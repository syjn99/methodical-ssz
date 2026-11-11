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

Unit G2-F cases (review g2g-r1; ids `g2f-*`):
 - g2-partial (changed): the `--gen2 --partial-out` file is a Lean module: imports first, then the PARTIAL header
   with an `UNCOVERED-JSON:` line; `kindcheck.py` exit 1 by default, exit 3 with `--partial`.
 - g2f-bh-partial: real BeaconBlockHeader (Slot, ProposerIndex are delegated overlay fields): exit 3, 0 bytes on
   stdout, partial file = the committed `lean/E2eScal/Gen2BhDecPartial.lean`, two runs identical, kindcheck
   default exit 1, `--partial` exit 3 with `PARTIAL 3/5 fields`.
 - g2f-compose-*: `--compose` refusals, exit 2, 0 bytes, no partial file even with `--partial-out`: partial
   coverage (BeaconBlockHeader), frame 0x28, a non-contiguous field (a `nop` between two fields), uint64 first
   field (IR order of BlobIdentifier swapped: displacement 0, not covered).
 - g2f-no-same-as-marker: `--compose` without `--same-as` still exits 0; the theorem line carries
   `-- UNCHECKED STATEMENT` and the header says the statement is checked by nobody; kindcheck exit 1.
 - g2f-same-as-generated: `--same-as E2eScal.Gen.bi_e2e_accept_main_gc` (a generated theorem): exit 0, kindcheck
   exit 1 (review g2g-r1 case (ii)).
 - g2f-same-as-prop: `--same-as-prop E2eScal.Fx.biStmt`: exit 0, the Prop identity line, kindcheck PASS; the
   test fixture `g2f-bi-prop-fixture.lean` (the output with a scratch `abbrev` equal to the type of
   `Bi.bi_e2e_accept_main`) is written to <work-dir> for a separate gated `lake env lean`.

GEN3 cases (unit G3-G, `p2dec --gen3`; ids `g3-*`; mutated `.S` / IR copies in <work-dir> only):
 - g3-new-*: `--gen3` on PendingPartialWithdrawal, Deposit_Data, BeaconBlockHeader: exit 0 twice, identical,
   every field covered, = the committed raw files `Gen3PwDec.lean`, `Gen3DdDec.lean`, `Gen3BhDec.lean` when they
   exist; AttestationData: exit 3, Slot / CommitteeIndex / BeaconBlockRoot covered, Source / Target not
   (nested containers), partial file = committed `Gen3AdDecPartial.lean` when it exists; `kindcheck.py` PASS
   (`--partial`: exit 3).
 - adversarial `.S` / IR mutants per GEN3 shape: wrong callee symbol, callee without a proved spec (IR),
   `test` / `je` missing, `je` to a missing or an earlier label, set-up with an extra or a missing move, `nop` in
   an unobserved position (between `add` and `mov $0x8,%ecx`, after the `callq`, before `memmove`, before
   `mov $n,%ecx`, in the offset-0 form), two `nop`s, the two-directive read with swapped registers, wrong
   displacements against the IR, rdx as its register (clobbers the `lea` set-up), `lea` displacements against
   the IR, a reload set-up with another rdi constant or register, IR order swapped (SSZ offset of a first-form
   callee field not 0). Expected: the field is not covered (exit 3; no theorem whose name has the field) or
   exit 2; 0 bytes on stdout whenever the exit code is not 0; `--summary` agrees.
 - g3-compose-*: `--gen3 --compose` refuses callee / two-directive types (PendingPartialWithdrawal,
   BeaconBlockHeader: exit 2, 0 bytes); Deposit_Data composes (exit 0) with the `decAcceptKind` `_kind` line
   and the identity with `H4.dd_accept_stmt`; kindcheck PASS; = committed `Gen3DdAccept2.lean` when it exists.

GEN4 cases (unit G4-G, `p2dec --gen4`; ids `g4-*`; mutated `.S` / IR copies in <work-dir> only):
 - g4-new-*: `--gen4` on the 10 development types: exit 0 twice (AttestationData: 3), identical, the expected
   covered fields, `kindcheck.py` PASS (`--partial`: exit 3), = the committed raw file `Gen4*.lean` when it exists.
 - g4-compose-refuse: `--gen4 --compose` exits 2 with the reason, 0 bytes, no file.
 - adversarial inputs for the dataflow (SyncCommitteeMessage, PendingConsolidation, PendingPartialWithdrawal,
   Eth1Data): a receiver / argument register clobbered between set-up and block, set-up moves in another VALID order
   (covered) and in an invalid order (refused), an extra harmless move and a fall-through label (covered), `nop` at
   start / middle / end / doubled (covered), a `nop` replaced by `cld` (one byte, no step lemma: refused),
   displacements off by 8 against the IR (refused), source / destination registers swapped at the call (refused),
   an unknown callee in the code or in the IR (refused), a label inside a call / segment window (refused), field order
   wrong in the IR or the code (refused), a receiver register outside the lemma's set, a reload from another slot,
   the buffer slot overwritten, a store through an unknown base, an indexed / rip operand, an immediate store, an rsp
   change. Expected: exit 0 with every field covered, or exit 3 with the stated covered fields (no theorem of an
   uncovered field: `kindcheck.py --partial` exit 3 on the partial file), 0 bytes on stdout unless exit 0; the
   summary's miss class is checked where stated. A covered mutant is a text result only (no Lean constant exists for
   mutated code): its theorems carry the mutated code's indices, never a parameter of the unmutated code.
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
    kc = subprocess.run(["python3", "-I", "-B", str(HERE / "kindcheck.py"), str(po)], capture_output=True, text=True)
    kp = subprocess.run(["python3", "-I", "-B", str(HERE / "kindcheck.py"), "--partial", str(po)], capture_output=True, text=True)
    ph = [l for l in pt.split("\n") if "PARTIAL OUTPUT" in l]
    uj = [json.loads(l.split(": ", 1)[1]) for l in pt.split("\n") if l.startswith("UNCOVERED-JSON: ")]
    ok = (rc == 3 and so == b"" and pt.startswith("import ") and len(ph) == 1 and "NOT generated: Amount" in ph[0]
          and uj and [u["field"] for u in uj[0]] == ["Amount"] and "dm_g2dec_Amount_seg" not in pt
          and kc.returncode == 1 and kp.returncode == 3 and "PARTIAL 2/3 fields" in kp.stdout)
    res.append(dict(id="g2-partial", expect="exit 3, Lean-module PARTIAL file without Amount, kindcheck exit 1, --partial exit 3",
                    exit=rc, stdout_bytes=len(so), partial_header=ph, kindcheck_exit=kc.returncode,
                    kindcheck_partial_exit=kp.returncode, ok=bool(ok)))
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
              and f"identity against {CP[key][1]} — statement evidence only if" in kc.stdout)
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
    r2, b2 = g2f_cases(work, new, cargs, CP, irt)
    return res + r2, bad | b2


GEN2_BH_PARTIAL = "lean/E2eScal/Gen2BhDecPartial.lean"


def g2f_cases(work, new, cargs, CP, irt):
    """Unit G2-F (review g2g-r1): partial output as a Lean module, compose refusals, statement markers."""
    res, bad = [], 0
    KC = ["python3", "-I", "-B", str(HERE / "kindcheck.py")]
    c = G2["BH"]
    outs = []
    for i in range(2):
        po = work / f"g2f-bh-partial-{i}.lean"
        if po.exists():
            po.unlink()
        rc, so, se = run(["python3", "-I", "-B", str(new), "p2dec", "--gen2", "--partial-out", str(po), "--S", c["S"],
                          "--ir", IR, "--type", c["type"]] + c["args"], KR)
        outs.append((rc, so, po.read_bytes() if po.exists() else b""))
    po = work / "g2f-bh-partial-0.lean"
    kc = subprocess.run(KC + [str(po)], capture_output=True, text=True)
    kp = subprocess.run(KC + ["--partial", str(po)], capture_output=True, text=True)
    com = (KR / GEN2_BH_PARTIAL).read_bytes() if (KR / GEN2_BH_PARTIAL).exists() else None
    pt = outs[0][2].decode()
    uj = [json.loads(l.split(": ", 1)[1]) for l in pt.split("\n") if l.startswith("UNCOVERED-JSON: ")]
    ok = (all(o[0] == 3 and o[1] == b"" for o in outs) and outs[0][2] == outs[1][2] and outs[0][2] == com
          and uj and [u["field"] for u in uj[0]] == ["Slot", "ProposerIndex"]
          and all("delegated overlay" in u["reason"] for u in uj[0])
          and kc.returncode == 1 and kp.returncode == 3 and "PARTIAL 3/5 fields" in kp.stdout)
    res.append(dict(id="g2f-bh-partial", expect=f"exit 3 twice, 0 bytes, file = {GEN2_BH_PARTIAL}, kindcheck 1, --partial 3",
                    exit=[o[0] for o in outs], stdout_bytes=len(outs[0][1]), equals_committed=outs[0][2] == com,
                    uncovered=uj, kindcheck_exit=kc.returncode, kindcheck_partial_exit=kp.returncode, ok=bool(ok)))
    bad |= not ok
    # --compose refusals
    dm = (KR / G2["DM"]["S"]).read_text().split("\n")
    bia = ["p2dec", "--gen2", "--compose", "--name", "bi_e2e_accept_main_gc", "--same-as", "E2eScal.Bi.bi_e2e_accept_main"]
    for (mid, what, base_args, S_text, ir_text) in [
            ("g2f-compose-partial-bh", "partial coverage: real BeaconBlockHeader (3 of 5 fields)",
             ["p2dec", "--gen2", "--compose", "--name", "bh_e2e_accept_main_gc", "--ir", IR, "--type", c["type"]] + c["args"],
             None, None),
            ("g2f-compose-frame-0x28", "DepositMessage frame 0x28 (prologue and epilogue)", cargs("DM"),
             "\n".join(edits(dm, [(7, "  sub $0x20,%rsp", "  sub $0x28,%rsp"), (89, "  add $0x20,%rsp", "  add $0x28,%rsp")])), None),
            ("g2f-compose-not-contiguous", "DepositMessage: a nop between the PublicKey tail and WithdrawalCredentials",
             cargs("DM"), "\n".join(edits(dm, [(47, "  mov %rdi,(%rdx)", "  mov %rdi,(%rdx)\n  nop")])), None),
            ("g2f-compose-u64-first", "BlobIdentifier IR order swapped: uint64 Index first (displacement 0)",
             cargs("BI"), None, ir_edit(irt, G2["BI"]["type"], ir_swap("BlockRoot", "Index")))]:
        a = list(base_args)
        S = c["S"] if mid == "g2f-compose-partial-bh" else (G2["DM"]["S"] if mid != "g2f-compose-u64-first" else G2["BI"]["S"])
        if S_text is not None:
            f = work / f"{mid}.S"
            f.write_text(S_text)
            S = str(f)
        if ir_text is not None:
            f = work / f"{mid}.ir.json"
            f.write_text(ir_text)
            a[a.index("--ir") + 1] = str(f)
        po = work / f"{mid}.partial.lean"
        if po.exists():
            po.unlink()
        rc, so, se = run(["python3", "-I", "-B", str(new)] + a + ["--S", S, "--partial-out", str(po)], KR)
        ok = rc == 2 and so == b"" and not po.exists() and "no template match" in se
        res.append(dict(id=mid, what=what, expect="exit 2, 0 bytes, no partial file", exit=rc, stdout_bytes=len(so),
                        partial_file=po.exists(), stderr=se.strip().split("\n")[-1:], ok=bool(ok)))
        bad |= not ok
    # --compose without --same-as: marker
    rc, so, se = run(["python3", "-I", "-B", str(new)] + cargs("BI", same=False) + ["--S", G2["BI"]["S"]], KR)
    tf = work / "g2f-nosame.lean"
    tf.write_bytes(so)
    kc = subprocess.run(KC + [str(tf)], capture_output=True, text=True)
    th = [l for l in so.decode().split("\n") if l.startswith("theorem ")]
    ok = (rc == 0 and th and th[0].endswith("-- UNCHECKED STATEMENT: checked by nobody") and len(th) == 1
          and "checked by nobody" in so.decode().split("-/")[0] and kc.returncode == 1)
    res.append(dict(id="g2f-no-same-as-marker", expect="exit 0, UNCHECKED STATEMENT on the theorem line, kindcheck 1",
                    exit=rc, stdout_bytes=len(so), theorem_line_end=th[0][-45:] if th else None,
                    kindcheck_exit=kc.returncode, ok=bool(ok)))
    bad |= not ok
    # --same-as a generated theorem (review g2g-r1 case (ii))
    a = cargs("BI")
    a[a.index("--same-as") + 1] = "E2eScal.Gen.bi_e2e_accept_main_gc"
    a[a.index("--name") + 1] = "bi_selfgen_gc"  # the reviewer's case: another name, right-hand side generated
    rc, so, se = run(["python3", "-I", "-B", str(new)] + a + ["--S", G2["BI"]["S"]], KR)
    tf = work / "g2f-same-as-generated.lean"
    tf.write_bytes(so)
    kc = subprocess.run(KC + [str(tf)], capture_output=True, text=True)
    ok = rc == 0 and kc.returncode == 1 and "is a generated name" in kc.stdout
    res.append(dict(id="g2f-same-as-generated", expect="exit 0, kindcheck exit 1 (generated right-hand side)", exit=rc,
                    stdout_bytes=len(so), kindcheck_exit=kc.returncode, ok=bool(ok)))
    bad |= not ok
    # --same-as-prop
    a = cargs("BI")
    a[a.index("--same-as"):a.index("--same-as") + 2] = ["--same-as-prop", "E2eScal.Fx.biStmt"]
    rc, so, se = run(["python3", "-I", "-B", str(new)] + a + ["--S", G2["BI"]["S"]], KR)
    t = so.decode()
    tf = work / "g2f-same-as-prop.lean"
    tf.write_bytes(so)
    kc = subprocess.run(KC + [str(tf)], capture_output=True, text=True)
    line = "    type_of% (@bi_e2e_accept_main_gc h) = @E2eScal.Fx.biStmt h := by"
    com = (KR / CP["BI"][2]).read_text()
    ok = (rc == 0 and line in t and kc.returncode == 0 and "identity against E2eScal.Fx.biStmt" in kc.stdout
          and t.split("\n/-- Statement check")[0].replace("E2eScal.Fx.biStmt", "E2eScal.Bi.bi_e2e_accept_main")
          == com.split("\n/-- Statement check")[0])
    imps, rest = t.split("\n\n", 1)
    (work / "g2f-bi-prop-fixture.lean").write_text(
        imps + "\n\n-- TEST FIXTURE (scratch, not in the library): a Prop-valued abbrev equal to the type of the hand\n"
        "-- theorem `E2eScal.Bi.bi_e2e_accept_main`.\n"
        "abbrev E2eScal.Fx.biStmt [h : Host] : Prop := type_of% (@E2eScal.Bi.bi_e2e_accept_main h)\n\n" + rest)
    res.append(dict(id="g2f-same-as-prop", expect="exit 0, Prop identity line, kindcheck PASS; fixture written",
                    exit=rc, stdout_bytes=len(so), kindcheck_exit=kc.returncode, ok=bool(ok)))
    bad |= not ok
    return res, bad


H4N = "prysm/go1.26.10/e2e/h4/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1."
G3 = {
    "PW": dict(S=H4N + "PendingPartialWithdrawal.UnmarshalSSZ.S", type="v1alpha1.PendingPartialWithdrawal",
               committed="lean/E2eScal/Gen3PwDec.lean",
               args=["--const", "PwUnmarshal", "--prefix", "pw_g3dec", "--imports", "E2eScal.H4Code", "--open", "E2eScal.H4Code"],
               fields=["Index", "Amount", "WithdrawableEpoch"]),
    "DD": dict(S=H4N + "Deposit_Data.UnmarshalSSZ.S", type="v1alpha1.Deposit_Data", committed="lean/E2eScal/Gen3DdDec.lean",
               args=["--const", "DdUnmarshal", "--prefix", "dd_g3dec", "--imports",
                     "E2eScal.P2Dec,E2eScal.P2DecZ,E2eScal.SegN,E2eScal.SegNPad,E2eScal.U64Inline,E2eScal.H4Code",
                     "--open", "E2eScal.H4Code"],
               fields=["PublicKey", "WithdrawalCredentials", "Amount", "Signature"]),
    "BH": dict(S=G2["BH"]["S"], type="v1alpha1.BeaconBlockHeader", committed="lean/E2eScal/Gen3BhDec.lean",
               args=["--const", "BhUnmarshal", "--prefix", "bh_g3dec", "--imports", "E2eScal.P2Dec,E2eScal.BhCode",
                     "--open", "E2eScal.BhCode"],
               fields=["Slot", "ProposerIndex", "ParentRoot", "StateRoot", "BodyRoot"]),
    "AD": dict(S="prysm/go1.26.10/e2e/ad/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1."
                 "AttestationData.UnmarshalSSZ.S", type="v1alpha1.AttestationData",
               committed="lean/E2eScal/Gen3AdDecPartial.lean",
               args=["--const", "AdUnmarshal", "--prefix", "ad_g3dec", "--imports", "E2eScal.P2Dec,E2eAd.Code",
                     "--open", "E2eAd.Code"],
               fields=["Slot", "CommitteeIndex", "BeaconBlockRoot", "Source", "Target"]),
}
PWL = "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ_"
PRIM = "github.com_OffchainLabs_prysm_v7_consensus_types_primitives."


def ir_overlay_name(field, name):
    def fn(t):
        for f in t["ir"]["fields"]:
            if f["key"] == field:
                f["v"]["name"] = name
                f["v"]["delegated_to"]["name"] = name
    return fn


# (id, what, type key, .S edits (1-based line, old, new or None) or a function of the lines, IR edit, exit, covered)
G3_MUT = [
    ("g3-wrong-callee", "Index: call to Epoch.UnmarshalSSZ (IR ValidatorIndex)", "PW",
     [(18, f"  callq {PRIM}ValidatorIndex.UnmarshalSSZ", f"  callq {PRIM}Epoch.UnmarshalSSZ")], None, 3,
     ["Amount", "WithdrawableEpoch"]),
    ("g3-callee-no-spec", "Index: callee Gwei.UnmarshalSSZ in code and IR (no proved callee spec)", "PW",
     [(18, f"  callq {PRIM}ValidatorIndex.UnmarshalSSZ", f"  callq {PRIM}Gwei.UnmarshalSSZ")], ir_overlay_name("Index", "Gwei"), 3,
     ["Amount", "WithdrawableEpoch"]),
    ("g3-test-missing", "Index: `test %rax,%rax` after the call removed", "PW", [(19, "  test %rax,%rax", None)], None, 3,
     ["Amount", "WithdrawableEpoch"]),
    ("g3-je-missing", "Index: `je` after the test replaced by `jne`", "PW",
     [(20, f"  je {PWL}b9", f"  jne {PWL}b9")], None, 3, ["Amount", "WithdrawableEpoch"]),
    ("g3-je-no-label", "Index: `je` to a label that does not exist", "PW",
     [(20, f"  je {PWL}b9", f"  je {PWL}zz")], None, 3, ["Amount", "WithdrawableEpoch"]),
    ("g3-je-earlier-label", "Index: `je` to the entry label (before the call)", "PW",
     [(20, f"  je {PWL}b9", f"  je {PWL}0")], None, 3, ["Amount", "WithdrawableEpoch"]),
    ("g3-setup-extra-move", "Index: `mov %rax,%rdx` between `add` and `mov $0x8,%ecx`", "PW",
     [(17, "  mov $0x8,%ecx", "  mov %rax,%rdx\n  mov $0x8,%ecx")], None, 3, ["Amount", "WithdrawableEpoch"]),
    ("g3-setup-missing-move", "Index: `mov $0x8,%ecx` removed", "PW", [(17, "  mov $0x8,%ecx", None)], None, 3,
     ["Amount", "WithdrawableEpoch"]),
    ("g3-setup-nop-between", "Index: `nop` between `add $0x8,%rax` and `mov $0x8,%ecx` (unobserved position)", "PW",
     [(17, "  mov $0x8,%ecx", "  nop\n  mov $0x8,%ecx")], None, 3, ["Amount", "WithdrawableEpoch"]),
    ("g3-nop-after-call", "Index: `nop` between the `callq` and `test`", "PW",
     [(19, "  test %rax,%rax", "  nop\n  test %rax,%rax")], None, 3, ["Amount", "WithdrawableEpoch"]),
    ("g3-first-add-other-reg", "Index: `add $0x8,%rbx` instead of rax", "PW", [(16, "  add $0x8,%rax", "  add $0x8,%rbx")], None, 3,
     ["Amount", "WithdrawableEpoch"]),
    ("g3-rr-swapped", "Amount: `mov 0x8(%rax),%r8; mov %r8,0x10(%rbx)` (bases swapped)", "PW",
     [(55, "  mov 0x8(%rbx),%r8", "  mov 0x8(%rax),%r8"), (56, "  mov %r8,0x10(%rax)", "  mov %r8,0x10(%rbx)")], None, 3, ["Index"]),
    ("g3-rr-two-regs", "Amount: `mov 0x8(%rbx),%r8; mov %r9,0x10(%rax)`", "PW",
     [(56, "  mov %r8,0x10(%rax)", "  mov %r9,0x10(%rax)")], None, 3, ["Index"]),
    ("g3-rr-src-disp", "Amount: source displacement 0x10 against IR SSZ offset 8", "PW",
     [(55, "  mov 0x8(%rbx),%r8", "  mov 0x10(%rbx),%r8")], None, 3, ["Index"]),
    ("g3-rr-dst-disp", "Amount: receiver displacement 0x18 against IR Go offset 16", "PW",
     [(56, "  mov %r8,0x10(%rax)", "  mov %r8,0x18(%rax)")], None, 3, ["Index"]),
    ("g3-rr-reg-rdx", "Amount read through rdx (clobbers the `lea` set-up register)", "PW",
     [(55, "  mov 0x8(%rbx),%r8", "  mov 0x8(%rbx),%rdx"), (56, "  mov %r8,0x10(%rax)", "  mov %rdx,0x10(%rax)")], None, 3,
     ["Index", "Amount"]),
    ("g3-rr-reg-rbp", "Amount read through rbp (not in U64RRReg)", "PW",
     [(55, "  mov 0x8(%rbx),%r8", "  mov 0x8(%rbx),%rbp"), (56, "  mov %r8,0x10(%rax)", "  mov %rbp,0x10(%rax)")], None, 3,
     ["Index"]),
    ("g3-lea-src-disp", "WithdrawableEpoch: `lea 0x18(%rbx),%rdx` against IR SSZ offset 16", "PW",
     [(50, "  lea 0x10(%rbx),%rdx", "  lea 0x18(%rbx),%rdx")], None, 3, ["Index", "Amount"]),
    ("g3-lea-f-disp", "WithdrawableEpoch: `lea 0x20(%rax),%rsi` against IR Go offset 24", "PW",
     [(54, "  lea 0x18(%rax),%rsi", "  lea 0x20(%rax),%rsi")], None, 3, ["Index", "Amount"]),
    ("g3-lea-extra-move", "WithdrawableEpoch: an extra `mov %rdx,%rcx` before `mov %rsi,%rax`", "PW",
     [(57, "  mov %rsi,%rax", "  mov %rdx,%rcx\n  mov %rsi,%rax")], None, 3, ["Index", "Amount"]),
    ("g3-ir-swap-index-amount", "IR order Index / Amount swapped (Index at SSZ offset 8, Amount at 0)", "PW",
     [], ir_swap("Index", "Amount"), 2, []),
    ("g3-reload-c", "ProposerIndex: `add $-0x10,%rdi` (observed: minus the SSZ offset 8)", "BH",
     [(51, "  add $-0x8,%rdi", "  add $-0x10,%rdi")], None, 3, ["Slot", "ParentRoot", "StateRoot", "BodyRoot"]),
    ("g3-reload-reg", "ProposerIndex: buffer reloaded into rcx", "BH",
     [(48, "  mov 0x78(%rsp),%rbx", "  mov 0x78(%rsp),%rcx")], None, 3, ["Slot", "ParentRoot", "StateRoot", "BodyRoot"]),
    ("g3-two-nops-setup", "ProposerIndex: two `nop`s before the call", "BH",
     [(55, "  nop", "  nop\n  nop")], None, 3, ["Slot", "ParentRoot", "StateRoot", "BodyRoot"]),
    ("g3-reload-src-disp", "ProposerIndex: `add $0x10,%rbx` against IR SSZ offset 8", "BH",
     [(49, "  add $0x8,%rbx", "  add $0x10,%rbx")], None, 3, ["Slot", "ParentRoot", "StateRoot", "BodyRoot"]),
    ("g3-pad-two-nops", "WithdrawalCredentials: two `nop`s before makeslice", "DD",
     [(51, "  nop", "  nop\n  nop")], None, 3, ["PublicKey", "Amount", "Signature"]),
    ("g3-pad-before-memmove", "WithdrawalCredentials: `nop` before `callq runtime.memmove`", "DD",
     [(68, "  callq runtime.memmove", "  nop\n  callq runtime.memmove")], None, 3, ["PublicKey", "Amount", "Signature"]),
    ("g3-pad-before-size", "WithdrawalCredentials: `nop` before `mov $0x20,%ecx` (moved)", "DD",
     [(50, "  mov $0x20,%ecx", "  nop"), (51, "  nop", "  mov $0x20,%ecx")], None, 3, ["PublicKey", "Amount", "Signature"]),
    ("g3-pad-offset0", "PublicKey (offset-0 form): `nop` before makeslice", "DD",
     [(17, "  callq runtime.makeslice", "  nop\n  callq runtime.makeslice")], None, 3,
     ["WithdrawalCredentials", "Amount", "Signature"]),
]


def g3_cases(work, new):
    """Unit G3-G: the GEN3 shapes, their adversarial inputs and the compose refusals / DD composition."""
    res, bad = [], 0
    irt = (KR / IR).read_text()
    KC = ["python3", "-I", "-B", str(HERE / "kindcheck.py")]
    G = ["python3", "-I", "-B", str(new), "p2dec", "--gen3"]
    for key in ("PW", "DD", "BH", "AD"):
        c = G3[key]
        outs = []
        for i in range(2):
            po, su = work / f"g3-new-{key}-{i}.partial.lean", work / f"g3-new-{key}-{i}.json"
            for q in (po, su):
                if q.exists():
                    q.unlink()
            rc, so, se = run(G + ["--S", c["S"], "--ir", IR, "--type", c["type"], "--summary", str(su),
                                  "--partial-out", str(po)] + c["args"], KR)
            outs.append((rc, so, po.read_bytes() if po.exists() else b"", json.loads(su.read_text())))
        rc, so, pt, sm = outs[0]
        cov = [f["field"] for f in sm["fields"] if f["status"] == "covered"]
        text = so if key != "AD" else pt
        f = work / f"g3-new-{key}.lean"
        f.write_bytes(text)
        kc = subprocess.run(KC + (["--partial"] if key == "AD" else []) + [str(f)], capture_output=True, text=True)
        com = (KR / c["committed"]).read_bytes() if (KR / c["committed"]).exists() else None
        want_cov = c["fields"][:3] if key == "AD" else c["fields"]
        ok = (rc == (3 if key == "AD" else 0) and outs[0][:3] == outs[1][:3] and cov == want_cov
              and kc.returncode == (3 if key == "AD" else 0) and (com is None or com == text)
              and (key != "AD" or so == b""))
        res.append(dict(id=f"g3-new-{key}", expect=f"exit {3 if key == 'AD' else 0} twice, identical, covered {want_cov}, "
                        f"kindcheck PASS, = committed if present", exit=rc, stdout_bytes=len(so), covered=cov,
                        kindcheck_exit=kc.returncode, committed_present=com is not None,
                        equals_committed=(com == text) if com is not None else None, ok=bool(ok)))
        bad |= not ok
    for (mid, what, key, eds, irf, want, covw) in G3_MUT:
        c = G3[key]
        base = (KR / c["S"]).read_text().split("\n")
        lines = eds(base) if callable(eds) else edits(base, eds)
        fS = work / f"{mid}.S"
        fS.write_text("\n".join(lines))
        irp = KR / IR
        if irf:
            irp = work / f"{mid}.ir.json"
            irp.write_text(ir_edit(irt, c["type"], irf))
        po, su = work / f"{mid}.partial.lean", work / f"{mid}.json"
        for q in (po, su):
            if q.exists():
                q.unlink()
        rc, so, se = run(G + ["--S", str(fS), "--ir", str(irp), "--type", c["type"], "--summary", str(su),
                              "--partial-out", str(po)] + c["args"], KR)
        sm = json.loads(su.read_text()) if su.exists() else {}
        cov = [f["field"] for f in sm.get("fields", []) if f.get("status") == "covered"] if rc != 2 else []
        pt = po.read_text() if po.exists() else ""
        thm = [l.split()[1] for l in pt.split("\n") if l.startswith("theorem ")]
        unc = [f for f in c["fields"] if f not in covw]
        leak = [n for n in thm if any(f"_{u}_" in n for u in unc)]
        ok = (rc == want and so == b"" and sm.get("exit") == want and (want == 2 or cov == covw) and not leak
              and (want != 2 or not po.exists()))
        res.append(dict(id=mid, what=what, expect=f"exit {want}, 0 bytes" + (f", covered {covw}" if want == 3 else ""),
                        exit=rc, stdout_bytes=len(so), covered=cov, theorems_for_uncovered=leak,
                        reasons=[f.get("reason") for f in sm.get("fields", []) if f.get("status") != "covered"],
                        ok=bool(ok)))
        bad |= not ok
    # compose: refusals for callee / two-directive types, Deposit_Data composed with decAcceptKind
    for key in ("PW", "BH"):
        c = G3[key]
        po = work / f"g3-compose-{key}.partial.lean"
        if po.exists():
            po.unlink()
        rc, so, se = run(G + ["--compose", "--name", "x_g3", "--S", c["S"], "--ir", IR, "--type", c["type"],
                              "--partial-out", str(po)] + c["args"], KR)
        ok = rc == 2 and so == b"" and not po.exists() and "no composition" in se
        res.append(dict(id=f"g3-compose-refuse-{key}", expect="exit 2, 0 bytes, no file", exit=rc, stdout_bytes=len(so),
                        stderr=se.strip()[:300], ok=bool(ok)))
        bad |= not ok
    c = G3["DD"]
    outs = [run(G + ["--compose", "--name", "dd_e2e_accept_main_g3", "--same-as-prop", "E2eScal.H4.dd_accept_stmt",
                     "--S", c["S"], "--ir", IR, "--type", c["type"], "--const", "DdUnmarshal", "--prefix", "dd_g3dec",
                     "--imports", "E2eScal.Compose,E2eScal.Gen3DdDec,E2eScal.H4Stmt", "--open", "E2eScal.H4Code"], KR)
            for _ in range(2)]
    rc, so, se = outs[0]
    f = work / "g3-compose-DD.lean"
    f.write_bytes(so)
    kc = subprocess.run(KC + [str(f)], capture_output=True, text=True)
    com = KR / "lean/E2eScal/Gen3DdAccept2.lean"
    com = com.read_bytes() if com.exists() else None
    t = so.decode()
    ok = (rc == 0 and outs[0] == outs[1] and kc.returncode == 0 and "decAcceptKind" in kc.stdout
          and "@E2eScal.decAcceptKind h DdUnmarshal true [.bytes 48, .bytes 32, .u64, .bytes 96] 106 := by" in t
          and "set_option maxHeartbeats 200000 in\ntheorem dd_e2e_accept_main_g3_kind" in t
          and "UNCHECKED" not in t and (com is None or com == so))
    res.append(dict(id="g3-compose-DD", expect="exit 0 twice, identical, decAcceptKind line + Prop identity, kindcheck PASS",
                    exit=rc, stdout_bytes=len(so), kindcheck_exit=kc.returncode, committed_present=com is not None,
                    ok=bool(ok)))
    bad |= not ok
    # --gen3 without a GEN3 shape (Eth1Data) covers what --gen2 covers, with the same theorem text
    c2 = G2["E1"]
    rc, so, se = run(G + ["--S", c2["S"], "--ir", IR, "--type", c2["type"]] + c2["args"], KR)
    com = (KR / c2["committed"]).read_text()
    body = lambda s: s.split("namespace E2eScal.Gen\n", 1)[1]
    ok = rc == 0 and body(so.decode()) == body(com)
    res.append(dict(id="g3-e1-same-theorems-as-gen2", expect="exit 0, theorem text = committed Gen2E1Dec.lean body",
                    exit=rc, stdout_bytes=len(so), ok=bool(ok)))
    bad |= not ok
    return res, bad


H5N = "prysm/go1.26.10/e2e/h5/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1."
PN = "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1."


def g4c(sdir, tname, const, mod, pre, out, fields, cov=None):
    return dict(S=f"prysm/go1.26.10/e2e/{sdir}/{PN}{tname}.UnmarshalSSZ.S", type=f"v1alpha1.{tname}",
                committed=f"lean/E2eScal/{out}.lean", args=["--const", const, "--prefix", f"{pre}_g4dec", "--imports", mod,
                                                             "--open", mod],
                fields=fields, cov=fields if cov is None else cov)


G4 = {
    "CP": g4c("link/norm", "Checkpoint", "CpUnmarshal", "E2e.Code", "cp", "Gen4CpDec", ["Epoch", "Root"]),
    "AD": g4c("ad/link/norm", "AttestationData", "AdUnmarshal", "E2eAd.Code", "ad", "Gen4AdDecPartial",
              ["Slot", "CommitteeIndex", "BeaconBlockRoot", "Source", "Target"], ["Slot", "CommitteeIndex", "BeaconBlockRoot"]),
    "BH": g4c("bh/link/norm", "BeaconBlockHeader", "BhUnmarshal", "E2eScal.BhCode", "bh", "Gen4BhDec",
              ["Slot", "ProposerIndex", "ParentRoot", "StateRoot", "BodyRoot"]),
    "E1": g4c("e1/link/norm", "Eth1Data", "E1Unmarshal", "E2eScal.E1Code", "e1", "Gen4E1Dec",
              ["DepositRoot", "DepositCount", "BlockHash"]),
    "BI": g4c("h3/link/norm", "BlobIdentifier", "BiUnmarshal", "E2eScal.H3Code", "bi", "Gen4BiDec", ["BlockRoot", "Index"]),
    "DM": g4c("h3/link/norm", "DepositMessage", "DmUnmarshal", "E2eScal.H3Code", "dm", "Gen4DmDec",
              ["PublicKey", "WithdrawalCredentials", "Amount"]),
    "DD": g4c("h4/link/norm", "Deposit_Data", "DdUnmarshal", "E2eScal.H4Code", "dd", "Gen4DdDec",
              ["PublicKey", "WithdrawalCredentials", "Amount", "Signature"]),
    "PW": g4c("h4/link/norm", "PendingPartialWithdrawal", "PwUnmarshal", "E2eScal.H4Code", "pw", "Gen4PwDec",
              ["Index", "Amount", "WithdrawableEpoch"]),
    "SM": g4c("h5/link/norm", "SyncCommitteeMessage", "SmUnmarshal", "E2eScal.H5Code", "sm", "Gen4SmDec",
              ["Slot", "BlockRoot", "ValidatorIndex", "Signature"]),
    "PC": g4c("h5/link/norm", "PendingConsolidation", "PcUnmarshal", "E2eScal.H5Code", "pc", "Gen4PcDec",
              ["SourceIndex", "TargetIndex"]),
}
SMF, PCF, PWF = G4["SM"]["fields"], G4["PC"]["fields"], G4["PW"]["fields"]
SML = "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_"


def sm_vi(new):
    """SyncCommitteeMessage.ValidatorIndex set-up (lines 83–88) replaced by the lines `new`."""
    old = ["  mov 0x78(%rsp),%rbx", "  add $0x28,%rbx", "  mov 0x88(%rsp),%rdi", "  add $-0x28,%rdi", "  add $0x28,%rax",
           "  mov $0x8,%ecx"]

    def fn(L):
        assert L[82:88] == old, L[82:88]
        return L[:82] + new + L[88:]
    return fn


VI = ["  mov 0x78(%rsp),%rbx", "  add $0x28,%rbx", "  mov 0x88(%rsp),%rdi", "  add $-0x28,%rdi", "  add $0x28,%rax",
      "  mov $0x8,%ecx"]
# (id, what, type key, .S edits or function, IR edit, exit, covered, miss class of the first uncovered field or None)
G4_MUT = [
    ("g4-clobber-rax", "ValidatorIndex: `mov %rdx,%rax` after `add $0x28,%rax` (receiver clobbered before the call)", "SM",
     sm_vi(VI[:5] + ["  mov %rdx,%rax"] + VI[5:]), None, 3, SMF[:2], "register"),
    ("g4-clobber-rbx-callee-arg", "ValidatorIndex: `mov 0x88(%rsp),%rbx` after the rbx set-up (source register clobbered)", "SM",
     sm_vi(VI[:2] + ["  mov 0x88(%rsp),%rbx"] + VI[2:]), None, 3, SMF[:2], None),
    ("g4-order-valid", "ValidatorIndex: `add $0x28,%rax` first, then the rbx / rdi set-up (another valid order)", "SM",
     sm_vi([VI[4]] + VI[:4] + [VI[5]]), None, 0, SMF, None),
    ("g4-order-valid-ecx-first", "ValidatorIndex: `mov $0x8,%ecx` first (another valid order)", "SM",
     sm_vi([VI[5]] + VI[:5]), None, 0, SMF, None),
    ("g4-order-invalid", "ValidatorIndex: `add $0x28,%rbx` before `mov 0x78(%rsp),%rbx` (the load overwrites the add)", "SM",
     sm_vi([VI[1], VI[0]] + VI[2:]), None, 3, SMF[:2], "set-up order"),
    ("g4-extra-harmless", "ValidatorIndex: an extra `mov %rdi,%rsi` in the set-up", "SM",
     sm_vi(VI[:4] + ["  mov %rdi,%rsi"] + VI[4:]), None, 0, SMF, None),
    ("g4-label-fallthrough", "ValidatorIndex: a fall-through label between two set-up moves (label step)", "SM",
     sm_vi(VI[:2] + [f"{SML}zz:"] + VI[2:]), None, 0, SMF, None),
    ("g4-nop-start", "ValidatorIndex: `nop` before the first set-up move", "SM", sm_vi(["  nop"] + VI), None, 0, SMF, None),
    ("g4-nop-middle", "ValidatorIndex: `nop` between `add $0x28,%rbx` and `mov 0x88(%rsp),%rdi`", "SM",
     sm_vi(VI[:2] + ["  nop"] + VI[2:]), None, 0, SMF, None),
    ("g4-nop-end", "ValidatorIndex: `nop` between `mov $0x8,%ecx` and the `callq`", "SM", sm_vi(VI + ["  nop"]), None, 0, SMF, None),
    ("g4-nop-doubled-after-call", "ValidatorIndex: two `nop`s between the `callq` and `test`", "SM",
     [(90, "  test %rax,%rax", "  nop\n  nop\n  test %rax,%rax")], None, 0, SMF, None),
    ("g4-nop-in-segment", "Signature: `nop` before `callq runtime.memmove` and two before makeslice", "SM",
     [(141, "  callq runtime.memmove", "  nop\n  callq runtime.memmove"), (124, "  nop", "  nop\n  nop")], None, 0, SMF, None),
    ("g4-cld-for-nop-seg", "Signature: the `nop` before makeslice replaced by `cld` (one byte, no step lemma)", "SM",
     [(124, "  nop", "  cld")], None, 3, SMF[:3], "new directive form"),
    ("g4-cld-for-nop-call", "TargetIndex: the `nop` after the `callq` replaced by `cld`", "PC",
     [(57, "  nop", "  cld")], None, 3, PCF[:1], "new directive form"),
    ("g4-cld-in-setup", "TargetIndex: `cld` in the set-up (no step lemma)", "PC",
     [(53, "  mov 0x58(%rsp),%rax", "  cld\n  mov 0x58(%rsp),%rax")], None, 3, PCF[:1], "new directive form"),
    ("g4-disp-f-off8", "ValidatorIndex: `add $0x30,%rax` (Go offset 0x28 in the IR)", "SM",
     sm_vi(VI[:4] + ["  add $0x30,%rax"] + VI[5:]), None, 3, SMF[:2], "other"),
    ("g4-disp-src-off8", "ValidatorIndex: `add $0x30,%rbx` (SSZ offset 0x28 in the IR)", "SM",
     sm_vi([VI[0], "  add $0x30,%rbx"] + VI[2:]), None, 3, SMF[:2], None),
    ("g4-swapped-call-regs", "WithdrawableEpoch: `mov %rsi,%rbx; mov %rdx,%rax` (source / destination swapped)", "PW",
     [(57, "  mov %rsi,%rax", "  mov %rsi,%rbx"), (58, "  mov %rdx,%rbx", "  mov %rdx,%rax")], None, 3, PWF[:2], "register"),
    ("g4-unknown-callee-code", "TargetIndex: `callq …Gwei.UnmarshalSSZ` in the code (IR ValidatorIndex)", "PC",
     [(56, f"  callq {PRIM}ValidatorIndex.UnmarshalSSZ", f"  callq {PRIM}Gwei.UnmarshalSSZ")], None, 3, PCF[:1], None),
    ("g4-unknown-callee-ir", "TargetIndex: callee Gwei.UnmarshalSSZ in code and IR (no proved spec)", "PC",
     [(56, f"  callq {PRIM}ValidatorIndex.UnmarshalSSZ", f"  callq {PRIM}Gwei.UnmarshalSSZ")],
     ir_overlay_name("TargetIndex", "Gwei"), 3, PCF[:1], "new field kind"),
    ("g4-label-in-call-window", "TargetIndex: the `nop` after the `callq` replaced by a label (inside the call window)", "PC",
     [(57, "  nop", "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.UnmarshalSSZ_zz:")],
     None, 3, PCF[:1], "other"),
    ("g4-label-in-seg-window", "Signature: a label between `xor %ebx,%ebx` and `mov $0x60,%ecx` (inside the segment window)", "SM",
     [(123, "  mov $0x60,%ecx", f"{SML}zz:\n  mov $0x60,%ecx")], None, 3, SMF[:3], "other"),
    ("g4-ir-order-swap", "IR order Amount / WithdrawableEpoch swapped (wrong field order)", "PW",
     [], ir_swap("Amount", "WithdrawableEpoch"), 3, PWF[:1], "set-up order"),
    ("g4-code-order-swap", "Eth1Data code: the DepositCount read moved after the BlockHash segment", "E1",
     lambda L: L[:47] + L[50:86] + L[47:50] + L[86:], None, 3, ["DepositRoot"], "set-up order"),
    ("g4-ry-rbx", "BlockRoot: receiver reloaded into rbx after memmove (not in the lemma's set)", "SM",
     [(68, "  mov 0x70(%rsp),%rax", "  mov 0x70(%rsp),%rbx"), (69, "  movq $0x20,0x18(%rax)", "  movq $0x20,0x18(%rbx)"),
      (70, "  movq $0x20,0x20(%rax)", "  movq $0x20,0x20(%rbx)")], None, 3, SMF[:1], "register"),
    ("g4-reload-other-slot", "BlockRoot: second receiver reload from 0x68(%rsp)", "SM",
     [(68, "  mov 0x70(%rsp),%rax", "  mov 0x68(%rsp),%rax")], None, 3, SMF[:1], "other"),
    ("g4-buffer-slot-overwritten", "Signature: `mov %rax,0x78(%rsp)` before the segment (buffer slot overwritten)", "SM",
     [(119, "  mov %rbx,0x30(%rsp)", "  mov %rbx,0x30(%rsp)\n  mov %rax,0x78(%rsp)")], None, 3, SMF[:3], "register"),
    ("g4-store-unknown-base", "ValidatorIndex: `mov %rax,0x8(%rcx)` in the set-up (store through an unknown base)", "SM",
     sm_vi(VI[:2] + ["  mov %rax,0x8(%rcx)"] + VI[2:]), None, 3, SMF[:2], "register"),
    ("g4-indexed-operand", "Amount: `mov 0x8(%rbx,%rcx,1),%r8` (index operand)", "PW",
     [(55, "  mov 0x8(%rbx),%r8", "  mov 0x8(%rbx,%rcx,1),%r8")], None, 3, PWF[:1], "new directive form"),
    ("g4-imm-store", "TargetIndex: `movq $0x0,0x40(%rsp)` in the set-up (immediate store)", "PC",
     [(53, "  mov 0x58(%rsp),%rax", "  movq $0x0,0x40(%rsp)\n  mov 0x58(%rsp),%rax")], None, 3, PCF[:1], "new directive form"),
    ("g4-rip-load", "TargetIndex: `mov ssz.ErrSize(%rip),%rdi` in the set-up", "PC",
     [(53, "  mov 0x58(%rsp),%rax", "  mov ssz.ErrSize(%rip),%rdi\n  mov 0x58(%rsp),%rax")], None, 3, PCF[:1], "new directive form"),
    ("g4-rsp-change", "TargetIndex: `add $0x8,%rsp` in the set-up", "PC",
     [(53, "  mov 0x58(%rsp),%rax", "  add $0x8,%rsp\n  mov 0x58(%rsp),%rax")], None, 3, PCF[:1], None),
    ("g4-movi-len-16", "TargetIndex: `mov $0x10,%ecx` (rcx = 16 at the call)", "PC",
     [(55, "  mov $0x8,%ecx", "  mov $0x10,%ecx")], None, 3, PCF[:1], None),
    ("g4-u64-src-disp", "Amount: `mov 0x10(%rbx),%r8` (SSZ offset 8 in the IR)", "PW",
     [(55, "  mov 0x8(%rbx),%r8", "  mov 0x10(%rbx),%r8")], None, 3, PWF[:1], "other"),
    ("g4-u64-dst-disp", "Amount: store to 0x18(%rax), the Go offset of WithdrawableEpoch", "PW",
     [(56, "  mov %r8,0x10(%rax)", "  mov %r8,0x18(%rax)")], None, 3, PWF[:1], "set-up order"),
]


def g4_cases(work, new):
    """Unit G4-G: `--gen4` on the development types, compose refusal, dataflow adversarial inputs."""
    res, bad = [], 0
    irt = (KR / IR).read_text()
    KC = ["python3", "-I", "-B", str(HERE / "kindcheck.py")]
    G = ["python3", "-I", "-B", str(new), "p2dec", "--gen4"]
    for key, c in G4.items():
        outs = []
        for i in range(2):
            po, su = work / f"g4-new-{key}-{i}.partial.lean", work / f"g4-new-{key}-{i}.json"
            for q in (po, su):
                if q.exists():
                    q.unlink()
            rc, so, se = run(G + ["--S", c["S"], "--ir", IR, "--type", c["type"], "--summary", str(su),
                                  "--partial-out", str(po)] + c["args"], KR)
            outs.append((rc, so, po.read_bytes() if po.exists() else b"", json.loads(su.read_text())))
        rc, so, pt, sm = outs[0]
        part = c["cov"] != c["fields"]
        cov = [f["field"] for f in sm["fields"] if f["status"] == "covered"]
        text = pt if part else so
        f = work / f"g4-new-{key}.lean"
        f.write_bytes(text)
        kc = subprocess.run(KC + (["--partial"] if part else []) + [str(f)], capture_output=True, text=True)
        com = (KR / c["committed"]).read_bytes() if (KR / c["committed"]).exists() else None
        ok = (rc == (3 if part else 0) and outs[0][:3] == outs[1][:3] and cov == c["cov"]
              and kc.returncode == (3 if part else 0) and (com is None or com == text) and (not part or so == b""))
        res.append(dict(id=f"g4-new-{key}", expect=f"exit {3 if part else 0} twice, identical, covered {c['cov']}, "
                        f"kindcheck PASS, = committed if present", exit=rc, stdout_bytes=len(so), covered=cov,
                        kindcheck_exit=kc.returncode, committed_present=com is not None,
                        equals_committed=(com == text) if com is not None else None, ok=bool(ok)))
        bad |= not ok
    c = G4["SM"]
    po = work / "g4-compose.partial.lean"
    if po.exists():
        po.unlink()
    rc, so, se = run(G + ["--compose", "--name", "x_g4", "--S", c["S"], "--ir", IR, "--type", c["type"],
                          "--partial-out", str(po)] + c["args"], KR)
    ok = rc == 2 and so == b"" and not po.exists() and "--gen4 --compose: refused" in se
    res.append(dict(id="g4-compose-refuse", expect="exit 2, 0 bytes, no file, reason", exit=rc, stdout_bytes=len(so),
                    stderr=se.strip()[:300], ok=bool(ok)))
    bad |= not ok
    for (mid, what, key, eds, irf, want, covw, mcls) in G4_MUT:
        c = G4[key]
        base = (KR / c["S"]).read_text().split("\n")
        lines = eds(base) if callable(eds) else edits(base, eds)
        fS = work / f"{mid}.S"
        fS.write_text("\n".join(lines))
        irp = KR / IR
        if irf:
            irp = work / f"{mid}.ir.json"
            irp.write_text(ir_edit(irt, c["type"], irf))
        po, su = work / f"{mid}.partial.lean", work / f"{mid}.json"
        for q in (po, su):
            if q.exists():
                q.unlink()
        rc, so, se = run(G + ["--S", str(fS), "--ir", str(irp), "--type", c["type"], "--summary", str(su),
                              "--partial-out", str(po)] + c["args"], KR)
        sm = json.loads(su.read_text()) if su.exists() else {}
        cov = [f["field"] for f in sm.get("fields", []) if f.get("status") == "covered"] if rc != 2 else []
        unc = [f for f in sm.get("fields", []) if f.get("status") != "covered"]
        kcr = None
        if rc == 3:
            kcr = subprocess.run(KC + ["--partial", str(po)], capture_output=True, text=True).returncode
        elif rc == 0:
            fo = work / f"{mid}.lean"
            fo.write_bytes(so)
            kcr = subprocess.run(KC + [str(fo)], capture_output=True, text=True).returncode
        ok = (rc == want and (so == b"") == (want != 0) and sm.get("exit") == want and cov == covw
              and kcr == (3 if want == 3 else 0) and (mcls is None or (unc and unc[0].get("miss_class") == mcls)))
        res.append(dict(id=mid, what=what, expect=f"exit {want}, covered {covw}" + (f", miss class {mcls}" if mcls else ""),
                        exit=rc, stdout_bytes=len(so), covered=cov, kindcheck_exit=kcr,
                        uncovered=[(f["field"], f.get("miss_class"), f.get("reason")) for f in unc], ok=bool(ok)))
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
    r3, b3 = g3_cases(work, new)
    res += r3
    bad |= b3
    r4, b4 = g4_cases(work, new)
    res += r4
    bad |= b4

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
