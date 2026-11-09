#!/usr/bin/env python3
"""phase1c X4: statements and proofs for a fixed-size container of uint/bool fields, from its Desc.

Usage:
  x4gen.py --desccheck-result R.json --desc-dir D --type pkg.T --out-lean lean/Gen1cX4/<T>.lean
           [--code-ns Fk.Code] [--mutant-S FILE --mutant-name NAME]

Inputs:
- the Desc of the type, accepted only through gen/gen1c/emit.accept (checker result, sha256, SPEC);
- the Go layout of the receiver (gen/wit/src/layout.json: unsafe.Offsetof/Sizeof, Go 1.26.3 amd64);
- the normalised machine code fv/kraken/link/out/norm/target.<T>.<M>.S (directive list; labels
  count as directives, as in `include_x64_rt`).
Output: one Lean module in the Gen1cX4 library with, per obligation, `def <obl>_stmt [Host] : Prop`
(the statement, built from the Desc and the layout) and `theorem <obl> [Host] : <obl>_stmt` (the
proof, built from the directive list of the path: one tactic block per directive kind).
The generator never writes into lean/Fk. With --mutant-S, the module also includes the mutated
code as `<NAME> : Program := include_x64_rt "<FILE>"` and states the obligations for it (negative
test: the proof must fail inside the designated theorem).
Python 3 standard library only. Run with python3 -I -B.
"""
import argparse
import json
import os
import re
import sys

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
KRAKEN = os.path.normpath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, os.path.join(KRAKEN, "gen", "gen1c"))
import emit  # noqa: E402

NORM = os.path.join(KRAKEN, "link", "out", "norm")
LAYOUT = json.load(open(os.path.join(KRAKEN, "gen", "wit", "src", "layout.json")))
FK = os.path.realpath(os.path.join(KRAKEN, "lean", "Fk"))
W = {1: (8, "zx8"), 2: (16, "zx16"), 4: (32, "zx32"), 8: (64, None)}


def directives(path):
    """(index, kind, text) for every directive of a normalised .S file; index 0 is the function label."""
    out = []
    for line in open(path):
        t = line.strip()
        if not t:
            continue
        out.append((len(out), "label" if t.endswith(":") else "instr", t.rstrip(":")))
    return out


class Fields:
    def __init__(self, desc, layout):
        self.f = []
        for df, lf in zip(desc["fields"], layout["fields"]):
            assert df["name"] == lf["name"] and df["kind"] in ("uint", "bool"), (df, lf)
            self.f.append({"name": df["name"], "kind": df["kind"], "w": df["width"], "ssz": df["offset"], "go": lf["offset"]})
        self.size = desc["fixed_size"]


def plus(base, off):
    return base if off == 0 else f"({base} + {off})"


# ---------------------------------------------------------------- statements

def size_stmt(code, n):
    return f"""def size_stmt [Host] : Prop :=
  ∀ (k : Nat) (hk : {code}.IsInfixAt Host.prog k) (s : MachineData) (ra : UInt64)
    (R : DataMem → Prop) (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec) ⋆ R),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = {n} ∧ st.data.regs.rsp = s.regs.rsp + 8
        ∧ st.data.regs.r14 = s.regs.r14 ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf k⟩
"""


def accept_stmt(code, F, labels):
    n = len(F.f)
    bs = " ".join(f"b{i}" for i in range(n))
    cs = " ".join(f"c{i}" for i in range(n))
    hb = " ".join(f"(h{i}l : b{i}.length = {f['w']})" for i, f in enumerate(F.f))
    hc = " ".join(f"(g{i} : c{i}.length = {f['w']})" for i, f in enumerate(F.f))
    inp = "\n      ⋆ ".join(f"Eq (b{i}.At {plus('s.regs.rbx.toBitVec', f['ssz'])})" for i, f in enumerate(F.f))
    rcv = "\n      ⋆ ".join(f"Eq (c{i}.At {plus('s.regs.rax.toBitVec', f['go'])})" for i, f in enumerate(F.f))
    hl = "\n    ".join(f"(hL{l}f : ∀ i < k, Host.prog[i]? ≠ some (.label \"{lab}\"))" for l, lab in labels)
    hbool = " ".join(f"(hb{i} : b{i} = [0] ∨ b{i} = [1])" for i, f in enumerate(F.f) if f["kind"] == "bool")
    out = "\n          ⋆ ".join(f"Eq (b{i}.At {plus('s.regs.rax.toBitVec', f['go'])})" for i, f in enumerate(F.f))
    inp2 = "\n          ⋆ ".join(f"Eq (b{i}.At {plus('s.regs.rbx.toBitVec', f['ssz'])})" for i, f in enumerate(F.f))
    return f"""def accept_stmt [Host] : Prop :=
  ∀ (k : Nat) (hk : {code}.IsInfixAt Host.prog k)
    (s : MachineData) (ra : UInt64) (slot {bs} {cs} : List UInt8)
    (hsl : slot.length = 8) {hb}
    {hc}
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16))
      ⋆ {inp}
      ⋆ {rcv} ⋆ R)
    {hl}
    (hlen : s.regs.rcx = {F.size}) {hbool},
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.r14 = s.regs.r14
        ∧ ({out}
          ⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ {inp2} ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩
"""


def reject_size_stmt(code, F, lab, err):
    return f"""def reject_size_stmt [Host] : Prop :=
  ∀ (k : Nat) (hk : {code}.IsInfixAt Host.prog k)
    (hLf : ∀ i < k, Host.prog[i]? ≠ some (.label "{lab}"))
    (s : MachineData) (ra e0 e1 : UInt64) (slot : List UInt8) (hsl : slot.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec) ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16#64))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "{err}").toBitVec) ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "{err}" + 8).toBitVec) ⋆ R)
    (hlen : s.regs.rcx ≠ {F.size}),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1)
      ⟨s, Host.addrOf k⟩
"""


def reject_bool_stmt(code, F, labels, err):
    bi = [i for i, f in enumerate(F.f) if f["kind"] == "bool"][0]
    pre = [i for i in range(len(F.f)) if i != bi]
    bs = " ".join(f"b{i}" for i in pre)
    cs = " ".join(f"c{i}" for i in range(len(F.f)))
    hb = " ".join(f"(h{i}l : b{i}.length = {F.f[i]['w']})" for i in pre)
    hc = " ".join(f"(g{i} : c{i}.length = {F.f[i]['w']})" for i in pre)
    def inp(i):
        return f"Eq ([e].At {plus('s.regs.rbx.toBitVec', F.f[i]['ssz'])})" if i == bi else f"Eq (b{i}.At {plus('s.regs.rbx.toBitVec', F.f[i]['ssz'])})"
    ins = "\n      ⋆ ".join(inp(i) for i in range(len(F.f)))
    rcv = "\n      ⋆ ".join(f"Eq (c{i}.At {plus('s.regs.rax.toBitVec', f['go'])})" for i, f in enumerate(F.f))
    hl = "\n    ".join(f"(hL{l}f : ∀ i < k, Host.prog[i]? ≠ some (.label \"{lab}\"))" for l, lab in labels)
    outw = "\n          ⋆ ".join([f"Eq (b{i}.At {plus('s.regs.rax.toBitVec', F.f[i]['go'])})" for i in pre] +
                                 [f"Eq (c{bi}.At {plus('s.regs.rax.toBitVec', F.f[bi]['go'])})"])
    ins2 = "\n          ⋆ ".join(inp(i) for i in range(len(F.f)))
    return f"""def reject_bool_stmt [Host] : Prop :=
  ∀ (k : Nat) (hk : {code}.IsInfixAt Host.prog k)
    (s : MachineData) (ra e0 e1 : UInt64) (slot {bs} {cs} : List UInt8) (e : UInt8)
    (he : 1 < e.toNat)
    (hsl : slot.length = 8) {hb}
    {hc}
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16))
      ⋆ {ins}
      ⋆ {rcv}
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "{err}").toBitVec)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "{err}" + 8).toBitVec) ⋆ R)
    {hl}
    (hlen : s.regs.rcx = {F.size}),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.r14 = s.regs.r14
        ∧ ({outw}
          ⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ {ins2}
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "{err}").toBitVec)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "{err}" + 8).toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩
"""


# ---------------------------------------------------------------- proofs

def step(d):
    return [f"apply estep (isInfixAt_drop hk {d})", "kunfold"]


def size_proof(D):
    L = ["intro k hk s ra R h_mem",
         "obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s",
         "simp only at h_mem ⊢"]
    for d, kind, t in D:
        L += step(d)
        if t.startswith("retq"):
            L += ["apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)",
                  "kunfold", "apply Eventually.done",
                  "refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl | (apply UInt64.toBitVec_inj.mp; simp)"]
            break
    return L


MEM = re.compile(r"^(?P<op>\w+)\s+(?P<a>[^,]+),(?P<b>.+)$")


def disp(m):
    """(displacement, base register) of an operand like 0x7(%rbx), (%rax), 0x10(%rsp)."""
    mm = re.fullmatch(r"(0x[0-9a-f]+)?\(%(\w+)\)", m.strip())
    return (int(mm[1], 16) if mm[1] else 0, mm[2]) if mm else None


def jump_cond(D, d):
    """(immediate, register) of the cmp that sets the flags of the jump at d (jumps keep the flags)."""
    j = d - 1
    while D[j][2].split()[0].startswith("j") and D[j][2].split()[0] != "jmp":
        j -= 1
    mm = re.match(r"cmp \$0x([0-9a-f]+),%(\w+)", D[j][2])
    assert mm, f"no cmp before {D[d][2]}"
    return int(mm[1], 16), mm[2]


TAKE = {"jne": lambda v, i: v != i, "je": lambda v, i: v == i, "ja": lambda v, i: v > i,
        "jae": lambda v, i: v >= i, "jb": lambda v, i: v < i, "jbe": lambda v, i: v <= i}
# proof of the impossible branch when the compared value is a known constant
NOT_TAKEN = ["· rename_i h; exact absurd h (by decide)"]
TAKEN = ["case isFalse h => exact absurd h (by decide)"]
# jne taken on `hlen : s.regs.rcx ≠ N` (pattern of Fk/FvSmall.lean fv_reject_size_main)
TAKEN_LEN_NE = ["case isFalse h =>",
                "  exfalso; simp [CondCode.interp, StatusFlags.from_result] at h",
                "  apply hlen; apply UInt64.toBitVec_inj.mp; apply BitVec.eq_of_toNat_eq",
                "  have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this ⊢; omega"]
# ja taken on a loaded byte `[e]` with `he : 1 < e.toNat` (pattern of Fk/ScRejectBool.lean)
TAKEN_BYTE_GT = ["case isFalse h =>",
                 "  exfalso; apply h",
                 "  have hb : {imm} < e.toBitVec.toNat := he",
                 "  have hl := e.toNat_lt",
                 "  simp only [Gen1cX4.ofBytes1]",
                 "  have hx : BitVec.extractLsb' 0 8 (BitVec.setWidth 64 e.toBitVec) = e.toBitVec := by",
                 "    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]",
                 "  simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, hx] at hb ⊢",
                 "  refine ⟨by omega, ?_⟩",
                 "  intro h0; have := congrArg BitVec.toNat h0; simp at this; omega"]


def walk(D, F, mode, bool_case=None):
    """Tactic lines for one path through the decoder, from directive 1 to its retq.

    mode "accept": length = fixed size, bool byte = bool_case[i] (0 or 1);
    mode "reject_size": length != fixed size (hlen); mode "reject_bool": length = fixed size,
    the bool byte is `[e]` with 1 < e. The jump outcomes follow from the mode; the impossible
    branch of each jump is closed by the snippet for its kind of condition."""
    by_ssz = {f["ssz"]: i for i, f in enumerate(F.f)}
    by_go = {f["go"]: i for i, f in enumerate(F.f)}
    lab_index = {t: d for d, k, t in D if k == "label"}
    L, m, d, last_load, seen, errs = [], 0, 1, None, set(), 0
    while True:
        assert d not in seen, f"loop at directive {d}"
        seen.add(d)
        _, kind, t = D[d]
        if kind == "label":
            L += step(d)
            d += 1
            continue
        op = t.split()[0]
        mm = MEM.match(t)
        a, b = (mm["a"].strip(), mm["b"].strip()) if mm else (None, None)
        if op == "retq":
            L += step(d)
            L += ["apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)",
                  "kunfold", "apply Eventually.done"]
            return L, m
        if op == "mov" and a and re.fullmatch(r"ssz\.\w+(\+8)?\(%rip\)", a):
            L += step(d) + [f"apply load_step _ _ _ _ (Int.toBytes 8 e{errs}.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)",
                            "kunfold"]
            errs += 1
        elif op in ("mov", "movb", "movw", "movl", "movq") and b and disp(b) and disp(b)[1] == "rsp":
            L += step(d) + ["apply store_step _ _ _ _ _ slot _ _ (by ecancel) (by exact hsl)", f"intro m{m} H{m}", "simp only [Effects.All]"]
            m += 1
        elif op in ("movzbl", "movzwl", "mov") and a and disp(a) and disp(a)[1] == "rbx":
            i = by_ssz[disp(a)[0]]
            if mode == "reject_bool" and F.f[i]["kind"] == "bool":
                L += step(d) + ["apply load_step _ _ _ _ [e] _ _ (by ecancel) (by rfl)", "kunfold"]
            else:
                L += step(d) + [f"apply load_step _ _ _ _ b{i} _ _ (by ecancel) (by exact h{i}l)", "kunfold"]
            last_load = i
        elif op in ("mov", "movb") and b and disp(b) and disp(b)[1] == "rax":
            i = by_go[disp(b)[0]]
            L += step(d) + [f"apply store_step _ _ _ _ _ c{i} _ _ (by ecancel) (by exact g{i})", f"intro m{m} H{m}", "kunfold"]
            m += 1
        elif op == "cmp":
            L += step(d)
        elif op.startswith("j"):
            target = t.split()[1]
            if op == "jmp":
                L += step(d) + [f"rw [hL{target.rsplit('_', 1)[1]}]"]
                d = lab_index[target]
                continue
            imm, reg = jump_cond(D, d)
            if reg == "rcx":
                taken = TAKE[op](F.size, imm) if mode != "reject_size" else op == "jne"
                proof = TAKEN_LEN_NE if mode == "reject_size" else (TAKEN if taken else NOT_TAKEN)
            elif mode == "reject_bool":
                assert op == "ja", f"reject_bool template expects ja, got {op}"
                taken, proof = True, [x.replace("{imm}", str(imm)) for x in TAKEN_BYTE_GT]
            else:
                taken = TAKE[op](bool_case[last_load], imm)
                proof = TAKEN if taken else NOT_TAKEN
            L += step(d) + ["split"] + proof + ["simp only [Effects.All]"]
            if taken:
                L.append(f"rw [hL{target.rsplit('_', 1)[1]}]")
                d = lab_index[target]
                continue
        elif op in ("xor",):
            L += step(d) + ["intro _"]
        elif op == "nop":
            L += step(d)
        else:
            raise SystemExit(f"directive {d} `{t}`: no tactic template")
        d += 1


def accept_proof(D, F, labels, bool_case):
    return walk(D, F, "accept", bool_case)[0]


def path_labels(L, D):
    lab_by_suf = {t.rsplit("_", 1)[1]: t for _, k, t in D if k == "label" and "_" in t}
    labs = []
    for x in L:
        mm = re.match(r"rw \[hL(\w+)\]", x)
        if mm and mm[1] not in labs:
            labs.append(mm[1])
    return sorted([(s, lab_by_suf[s]) for s in labs], key=lambda p: [d for d, k, t in D if t == p[1]][0])


def accept_finish(F):
    simps = []
    for i, f in enumerate(F.f):
        if f["kind"] == "uint":
            bits, _ = W[f["w"]]
            simps.append(f"toBytes_ofInt_ofBytes {bits} {f['w']} rfl b{i} h{i}l")
    return ["simp only [Width.bytes, zx8, zx16, zx32, " + ", ".join(simps) + ",",
            "  show Int.toBytes 1 (BitVec.truncate 8 (0 : BitVec 64)).toInt = [0] by decide,",
            "  show Int.toBytes 1 (BitVec.truncate 8 (1 : BitVec 64)).toInt = [1] by decide] at H{last}",
            "refine ⟨?_, ?_, ?_, ?_, rfl, ?_⟩",
            "· simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl] <;> rfl",
            "· simp", "· simp",
            "· apply UInt64.toBitVec_inj.mp; simp",
            "· dsimp only; (try simp only [BitVec.ofNat_eq_ofNat] at H{last} ⊢); simp only [Std.ExtHashMap.sep_emp, Width.bits, Width.bytes] at H{last}",
            "  ecancel"]


def accept_full(D, F, labels):
    n = len(F.f)
    bools = [i for i, f in enumerate(F.f) if f["kind"] == "bool"]
    assert len(bools) == 1, "template: exactly one bool field"
    bi = bools[0]
    intro = "intro k hk s ra slot " + " ".join(f"b{i}" for i in range(n)) + " " + " ".join(f"c{i}" for i in range(n)) + \
        " hsl " + " ".join(f"h{i}l" for i in range(n)) + " " + " ".join(f"g{i}" for i in range(n)) + " R h_mem " + \
        " ".join(f"hL{l}f" for l, _ in labels) + f" hlen hb{bi}"
    L = [intro]
    lab_index = {t: d for d, k, t in D if k == "label"}
    for l, lab in labels:
        L.append(f"have hL{l} := label_in_fragment hk (j := {lab_index[lab]}) (by decide) (by decide) hL{l}f")
    L += ["obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s",
          "simp only at h_mem hlen ⊢", "subst hlen"] + step(0)
    # common prefix up to the jump that depends on the bool byte value, then one branch per value
    p0 = accept_proof(D, F, labels, {bi: 0})
    p1 = accept_proof(D, F, labels, {bi: 1})
    k = 0
    while k < min(len(p0), len(p1)) and p0[k] == p1[k]:
        k += 1
    # split before the estep of the first jump whose outcome depends on the value
    k = max(i for i in range(k) if p0[i].startswith("apply estep"))
    # the not-taken jump before the split works for both values: prove its absurd case by cases
    pre = [x.replace("exact absurd h (by decide)", f"exact absurd h (by subst_vars; rcases hb{bi} with rfl | rfl <;> decide)") for x in p0[:k]]
    nstores = lambda p: sum(1 for x in p if x.startswith("intro m"))
    last0, last1 = nstores(p0) - 1, nstores(p1) - 1
    f0 = [x.replace("{last}", str(last0)) for x in accept_finish(F)]
    f1 = [x.replace("{last}", str(last1)) for x in accept_finish(F)]
    L += pre + [f"rcases hb{bi} with rfl | rfl"]
    L += ["· -- bool byte 0"] + ["  " + x for x in p0[k:] + f0]
    L += ["· -- bool byte 1"] + ["  " + x for x in p1[k:] + f1]
    return L


def reject_size_full(D, F):
    L, _ = walk(D, F, "reject_size")
    [(l, lab)] = path_labels(L, D)
    lab_index = {t: d for d, k, t in D if k == "label"}
    return ["intro k hk hLf s ra e0 e1 slot hsl R h_mem hlen",
            f"have hL{l} := label_in_fragment hk (j := {lab_index[lab]}) (by decide) (by decide) hLf",
            "obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s",
            "simp only at h_mem hlen ⊢",
            # the statement writes the slot offset as 16#64; the steps produce the OfNat literal
            "try simp only [BitVec.ofNat_eq_ofNat] at h_mem",
            "have := rcx.toNat_lt_size; simp only [UInt64.size] at *"] + step(0) + L + [
            "simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]",
            "refine ⟨?_, ?_, ?_⟩ <;> first | trivial | rfl | (apply UInt64.toBitVec_inj.mp; simp)"], (l, lab)


def reject_bool_full(D, F):
    L, m = walk(D, F, "reject_bool")
    labels = path_labels(L, D)
    lab_index = {t: d for d, k, t in D if k == "label"}
    bi = [i for i, f in enumerate(F.f) if f["kind"] == "bool"][0]
    pre = [i for i in range(len(F.f)) if i != bi]
    intro = ("intro k hk s ra e0 e1 slot " + " ".join(f"b{i}" for i in pre) + " " + " ".join(f"c{i}" for i in range(len(F.f))) +
             " e he hsl " + " ".join(f"h{i}l" for i in pre) + " " + " ".join(f"g{i}" for i in pre) + " R h_mem " +
             " ".join(f"hL{l}f" for l, _ in labels) + " hlen")
    simps = [f"toBytes_ofInt_ofBytes {W[F.f[i]['w']][0]} {F.f[i]['w']} rfl b{i} h{i}l" for i in pre]
    last = m - 1
    return [intro] + [f"have hL{l} := label_in_fragment hk (j := {lab_index[lab]}) (by decide) (by decide) hL{l}f" for l, lab in labels] + [
        "obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s",
        "simp only at h_mem hlen ⊢", "subst hlen"] + step(0) + L + [
        "simp only [Width.bytes, zx8, zx16, zx32, " + ", ".join(simps) + f"] at H{last}",
        "refine ⟨?_, ?_, ?_, ?_, rfl, ?_⟩",
        "· simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl] <;> rfl",
        "· apply UInt64.toBitVec_inj.mp; simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]",
        "· apply UInt64.toBitVec_inj.mp; simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]",
        "· apply UInt64.toBitVec_inj.mp; simp",
        f"· dsimp only at H{last} ⊢; (try simp only [BitVec.ofNat_eq_ofNat] at H{last} ⊢)",
        "  simp only [Std.ExtHashMap.sep_emp, Width.bits, Width.bytes, Int64.toBitVec_add, Int64.toBitVec_ofNat,",
        f"    BitVec.ofNat_eq_ofNat] at H{last} ⊢",
        "  ecancel"], labels


def err_label(D, d_from):
    for d, k, t in D[d_from:]:
        mm = re.match(r"mov (ssz\.\w+)\(%rip\)", t)
        if mm:
            return mm[1]


def accept_labels(D, F):
    """Jump targets on the accept paths (both bool values), in directive order."""
    labs = set()
    for v in (0, 1):
        bi = [i for i, f in enumerate(F.f) if f["kind"] == "bool"][0]
        for x in accept_proof(D, F, [], {bi: v}):
            mm = re.match(r"rw \[hL(\w+)\]", x)
            if mm:
                labs.add(mm[1])
    lab_by_suf = {t.rsplit("_", 1)[1]: t for _, k, t in D if k == "label" and "_" in t}
    return [(s, lab_by_suf[s]) for s in sorted(labs, key=lambda s: [d for d, k, t in D if t == lab_by_suf[s]][0])]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--desccheck-result", required=True)
    ap.add_argument("--desc-dir", required=True)
    ap.add_argument("--type", required=True)
    ap.add_argument("--out-lean", required=True)
    ap.add_argument("--only", default="size,accept,reject_bool,reject_size",
                    help="obligations to emit (a failing one must not be in the library module)")
    ap.add_argument("--ns", default=None, help="namespace (default Gen1cX4.<T>)")
    ap.add_argument("--mutant", default=None,
                    help="M=FILE: state and prove the obligations of method M against the code in FILE "
                         "(the proof is still generated from the original code: a negative test)")
    ap.add_argument("--theorems", default=os.path.join(KRAKEN, "gen", "frozen", "THEOREMS.json"))
    a = ap.parse_args()
    out = os.path.realpath(a.out_lean)
    if out.startswith(FK + os.sep):
        raise SystemExit(f"refusing to write into {FK}")
    th = json.load(open(a.theorems))
    [(key, desc, _p, dsha, _r)] = emit.accept(a.desccheck_result, a.desc_dir, [a.type], "hand_case", th)
    t = key[1]
    F = Fields(desc, LAYOUT["types"][t])
    ns = a.ns or f"Gen1cX4.{t}"
    only = a.only.split(",")
    code = {m: f"{t}{m}" for m in ("SizeSSZ", "UnmarshalSSZ")}
    head = ["import Fk.Step", "import Fk.Bytes", "import Fk.Labels", "import Gen1cX4.Support"]
    pre = []
    if a.mutant:
        m, f = a.mutant.split("=", 1)
        head.append("import Fk.Include")
        code[m] = f"{t}{m}Mut"
        pre = [f'def {code[m]} : Program := include_x64_rt "{os.path.realpath(f)}"', ""]
    Dsz = directives(os.path.join(NORM, f"target.{t}.SizeSSZ.S"))
    Dun = directives(os.path.join(NORM, f"target.{t}.UnmarshalSSZ.S"))
    body = [f"-- Generated by fv/kraken/gen/x4/x4gen.py from the Desc of {key[0]}.{t} (sha256 {dsha}).",
            "-- Statements from the Desc and the Go layout; proofs from the directive list. Do not edit.",
            *head, "", f"namespace {ns}", "open Fk Fk.Code", "", *pre]
    if "size" in only:
        body += [size_stmt(code["SizeSSZ"], F.size),
                 "theorem size [Host] : size_stmt := by", *["  " + x for x in size_proof(Dsz)], ""]
    if "accept" in only:
        labels = accept_labels(Dun, F)
        body += [accept_stmt(code["UnmarshalSSZ"], F, labels), "set_option maxHeartbeats 2000000 in",
                 "theorem accept [Host] : accept_stmt := by", *["  " + x for x in accept_full(Dun, F, labels)], ""]
    if "reject_size" in only:
        rs_proof, rs_lab = reject_size_full(Dun, F)
        body += [reject_size_stmt(code["UnmarshalSSZ"], F, rs_lab[1], err_label(Dun, [d for d, k, x in Dun if x == rs_lab[1]][0])),
                 "theorem reject_size [Host] : reject_size_stmt := by", *["  " + x for x in rs_proof], ""]
    if "reject_bool" in only:
        rb_proof, rb_labels = reject_bool_full(Dun, F)
        body += [reject_bool_stmt(code["UnmarshalSSZ"], F, rb_labels, err_label(Dun, [d for d, k, x in Dun if x == rb_labels[0][1]][0])),
                 "set_option maxHeartbeats 2000000 in",
                 "theorem reject_bool [Host] : reject_bool_stmt := by", *["  " + x for x in rb_proof], ""]
    body += [f"end {ns}", ""]
    os.makedirs(os.path.dirname(out), exist_ok=True)
    open(out, "w").write("\n".join(body))
    print(json.dumps({"type": t, "out": a.out_lean, "only": only, "mutant": a.mutant, "desc_sha256": dsha}))


if __name__ == "__main__":
    main()
