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
import include_adapter  # noqa: E402

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
        self.t = desc["type"]


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



# ---------------------------------------------------------------- marshal (fast path, no growslice)
# Patterns of Fk/ScMarshal.lean (sc_marshal_main): stack-guard check, frame push, spills, one
# load-compare-append block per field, the bool appended by value, frame pop and return.

STACK_NOT_TAKEN = ["· rename_i h; exfalso",
                   "  simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h",
                   "  have := guard.toNat_lt_size; have := rsp.toNat_lt_size",
                   "  simp only [UInt64.size] at *",
                   "  rcases h with h | h",
                   "  · apply h; omega",
                   "  · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega"]
CAP_TAKEN = ["case isFalse h =>",
             "  exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega"]


def marshal_stmt(code, F):
    bi = [i for i, f in enumerate(F.f) if f["kind"] == "bool"][0]
    cn = [f"c{f['name']}" for f in F.f]
    n = len(F.f)
    hc = " ".join(f"(h{f['name']} : c{f['name']}.length = {f['w']})" for i, f in enumerate(F.f) if i != bi)
    hd = " ".join(f"(hd{i} : d{i}.length = {f['w']})" for i, f in enumerate(F.f))
    rcv = lambda base: "\n      ⋆ ".join(f"Eq ({cn[i]}.At {plus(base, f['go'])})" for i, f in enumerate(F.f))
    dst = "\n      ⋆ ".join(f"Eq (d{i}.At {plus('s.regs.rbx.toBitVec + s.regs.rcx.toBitVec', f['ssz']).replace('(s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + ', '(s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + ') if f['ssz'] else '(s.regs.rbx.toBitVec + s.regs.rcx.toBitVec)'})" for i, f in enumerate(F.f))
    outd = "\n          ⋆ ".join(f"Eq ({cn[i]}.At {('(s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + ' + str(f['ssz']) + ')') if f['ssz'] else '(s.regs.rbx.toBitVec + s.regs.rcx.toBitVec)'})" for i, f in enumerate(F.f))
    outc = "\n          ⋆ ".join(f"Eq ({cn[i]}.At {plus('s.regs.rax.toBitVec', f['go'])})" for i, f in enumerate(F.f))
    return f"""def marshal_stmt [Host] : Prop :=
  ∀ (k : Nat) (hk : {code}.IsInfixAt Host.prog k)
    (hf : LabelsFresh {code} k)
    (s : MachineData) (ra guard : UInt64) (fp sp1 sp2 {' '.join(cn)} {' '.join(f'd{i}' for i in range(n))} pre : List UInt8)
    (hfp : fp.length = 8) (hs1 : sp1.length = 8) (hs2 : sp2.length = 8)
    {hc}
    {hd}
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (sp1.At (s.regs.rsp.toBitVec + 8)) ⋆ Eq (sp2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ {rcv('s.regs.rax.toBitVec')}
      ⋆ {dst}
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + {F.size} ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (h{F.f[bi]['name']} : c{F.f[bi]['name']} = [0] ∨ c{F.f[bi]['name']} = [1]),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx = s.regs.rcx + {F.size} ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ ({outd}
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ {outc}
          ⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩
"""


def marshal_walk(D, F, code, bval):
    """Fast path of MarshalSSZTo for bool value bval; returns (lines, last store index)."""
    by_go = {f["go"]: i for i, f in enumerate(F.f)}
    lab_index = {t: d for d, k, t in D if k == "label"}
    kat = lambda d: f"kat hk {code} {d}"
    L, m, d, seen = [], 1, 1, set()
    rdx, field, frame = None, None, None
    while True:
        assert d not in seen, f"loop at {d}"
        seen.add(d)
        _, kind, t = D[d]
        if kind == "label":
            L.append(kat(d)); d += 1; continue
        op = t.split()[0]
        args = t[len(op):].strip()
        if op == "cmp" and args.startswith("0x10(%r14)"):
            L += [kat(d), "apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)", "kunfold"]
        elif op == "jbe":
            L += [kat(d), "split"] + STACK_NOT_TAKEN + ["simp only [Effects.All]"]
        elif op == "push":
            L += [kat(d), "apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)",
                  f"intro m{m} H{m}", f"simp only [Width.bytes, Width.bits] at H{m}", "kunfold"]
            m += 1
        elif op == "sub" and args.endswith("%rsp"):
            frame = int(args.split(",")[0][1:], 16)
            L.append(kat(d))
        elif op == "mov" and re.fullmatch(r"%r[ab]x,0x[0-9a-f]+\(%rsp\)", args):
            off = int(re.search(r"0x([0-9a-f]+)\(", args)[1], 16) - frame - 8
            ch, hy = {8: ("sp1", "hs1"), 16: ("sp2", "hs2")}[off]
            L += [kat(d), f"apply store_step_at _ _ (rsp.toBitVec + {off}) _ _ _ {ch} _ _ (by bv_omega) (by ecancel) (by exact {hy})",
                  f"intro m{m} H{m}", f"simp only [Width.bytes, Width.bits] at H{m}", "kunfold"]
            m += 1
        elif op == "lea" and args == "0x1(%rcx),%rdx":
            rdx = "rcx.toBitVec + 1"; L.append(kat(d))
        elif op in ("movzbl", "movzwl", "mov") and re.fullmatch(r"(0x[0-9a-f]+)?\(%rax\),%r8\w*", args):
            off = disp(args.split(",")[0])[0]
            field = by_go[off]
            fn = F.f[field]["name"]
            addr = "(rax.toBitVec)" if off == 0 else f"(rax.toBitVec + {off})"
            L += [kat(d), f"apply load_step_at _ _ {addr} _ _ c{fn} _ _ (by bv_omega) (by ecancel) (by exact h{fn})", "kunfold"]
        elif op == "cmpb" and re.fullmatch(r"\$0x0,0x[0-9a-f]+\(%rax\)", args):
            off = int(args.split(",")[1].split("(")[0], 16)
            field = by_go[off]
            fn = F.f[field]["name"]
            L += [kat(d), f"apply load_step_at _ _ (rax.toBitVec + {off}) _ _ c{fn} _ _ (by bv_omega) (by ecancel) (by rcases h{fn} with rfl | rfl <;> rfl)",
                  "kunfold", f"rcases h{fn} with rfl | rfl"] if False else \
                 [kat(d), f"apply load_step_at _ _ (rax.toBitVec + {off}) _ _ c{fn} _ _ (by bv_omega) (by ecancel) (by rfl)", "kunfold"]
        elif op == "cmp" and args == "%rdx,%rdi":
            L.append(kat(d))
        elif op == "jae":
            target = args
            L += [kat(d), "split"] + CAP_TAKEN + ["simp only [Effects.All]", f"klabel hk hf {code} {lab_index[target]}"]
            d = lab_index[target]; continue
        elif op == "je":
            target = args
            if bval == 0:
                L += [kat(d), "split", "case isFalse h => exact absurd h (by decide)", "simp only [Effects.All]",
                      f"klabel hk hf {code} {lab_index[target]}"]
                d = lab_index[target]; continue
            L += [kat(d), "split", "case isTrue h => exact absurd h (by decide)", "simp only [Effects.All]"]
        elif op == "jmp":
            target = args
            L += [kat(d), f"klabel hk hf {code} {lab_index[target]}"]
            d = lab_index[target]; continue
        elif op in ("mov", "movb") and re.fullmatch(r"(%r8\w*|\$0x[01]),-0x([0-9a-f]+)\(%rdx,%rbx,1\)", args):
            w = int(re.search(r"-0x([0-9a-f]+)\(", args)[1], 16)
            i = field if not args.startswith("$") else [j for j, f in enumerate(F.f) if f["kind"] == "bool"][0]
            off = F.f[i]["ssz"]
            rhs = "rbx.toBitVec + rcx.toBitVec" + (f" + {off}" if off else "")
            L += [kat(d), f"rw [show {rdx} + rbx.toBitVec * 1#64 + -{w} = {rhs} by bv_omega]",
                  f"apply store_step _ _ _ _ _ d{i} _ _ (by ecancel) (by exact hd{i})",
                  f"intro m{m} H{m}", f"simp only [Width.bytes, Width.bits] at H{m}", "kunfold"]
            m += 1
        elif op == "add" and args.endswith(",%rdx"):
            rdx = f"{int(args.split(',')[0][1:], 16)} + ({rdx})"; L.append(kat(d))
        elif op == "inc" and args == "%rdx":
            rdx = f"{rdx} + 1"; L.append(kat(d))
        elif op == "xor":
            L += [kat(d), "intro _"]
        elif op == "add" and args.endswith(",%rsp"):
            L.append(kat(d))
        elif op == "pop" and args == "%rbp":
            L += [kat(d), f"rw [show {frame} + (rsp.toBitVec - 8#64 - {frame}) = rsp.toBitVec - 8 by bv_omega]",
                  f"obtain ⟨F{m}, H{m}⟩ : ∃ F, (Eq ((Int.toBytes 8 rbp.toBitVec.toInt).At (rsp.toBitVec - 8)) ⋆ F) m{m - 1} := ⟨_, by ecancel⟩",
                  f"apply load_step _ _ _ _ _ F{m} _ H{m} (by exact Int.toBytes_length 8 _)", "kunfold"]
        elif op == "retq":
            L += [kat(d), "rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]",
                  "apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)",
                  "kunfold", "apply Eventually.done"]
            return L, m - 1
        elif op == "mov" and re.fullmatch(r"%r\w+,%r\w+", args):
            L.append(kat(d))
        else:
            raise SystemExit(f"marshal directive {d} `{t}`: no tactic template")
        d += 1


def marshal_full(D, F, code):
    bi = [i for i, f in enumerate(F.f) if f["kind"] == "bool"][0]
    bn = F.f[bi]["name"]
    cn = [f"c{f['name']}" for f in F.f]
    n = len(F.f)
    intro = ("intro k hk hf s ra guard fp sp1 sp2 " + " ".join(cn) + " " + " ".join(f"d{i}" for i in range(n)) +
             " pre hfp hs1 hs2 " + " ".join(f"h{f['name']}" for i, f in enumerate(F.f) if i != bi) + " " +
             " ".join(f"hd{i}" for i in range(n)) + f" R h_mem hguard hcap hcap63 h{bn}")
    L = [intro,
         "obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s",
         "simp only at h_mem hguard hcap hcap63 ⊢",
         "have := rcx.toNat_lt_size; have := rdi.toNat_lt_size; have := rsp.toNat_lt_size",
         "have := guard.toNat_lt_size; simp only [UInt64.size] at *",
         f"kat hk {code} 0"]
    p0, l0 = marshal_walk(D, F, code, 0)
    p1, l1 = marshal_walk(D, F, code, 1)
    k = 0
    while p0[k] == p1[k]:
        k += 1
    k = max(i for i in range(k) if p0[i].startswith("kat "))   # split before the `je` on the bool
    simps = ", ".join(f"toBytes_ofInt_ofBytes {W[f['w']][0]} {f['w']} rfl c{f['name']} h{f['name']}" for i, f in enumerate(F.f) if i != bi)
    def fin(last):
        return ["simp only [Width.bytes, zx8, zx16, zx32, " + simps + ",",
                "  show Int.toBytes 1 (BitVec.truncate 8 (0 : BitVec 64)).toInt = [0] by decide,",
                f"  show Int.toBytes 1 (BitVec.truncate 8 (1 : BitVec 64)).toInt = [1] by decide] at H{last}",
                "simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]",
                "refine ⟨trivial, trivial, ?_, trivial, ?_, ?_, ?_, trivial, trivial, ?_⟩",
                "· apply UInt64.toBitVec_inj.mp; simp; generalize rcx.toBitVec = x; apply BitVec.eq_of_toNat_eq; simp; omega",
                "· apply UInt64.toBitVec_inj.mp; simp", "· apply UInt64.toBitVec_inj.mp; simp", "· apply UInt64.toBitVec_inj.mp; simp",
                f"· (try simp only [BitVec.ofNat_eq_ofNat] at H{last} ⊢); ecancel"]
    # the bool chunk is loaded before the split with a symbolic value: its length proof needs the cases
    pre = [x.replace("(by rfl)", f"(by rcases h{bn} with rfl | rfl <;> rfl)") for x in p0[:k]]
    L += pre + [f"rcases h{bn} with rfl | rfl", f"· -- {bn} = false"] + ["  " + x for x in p0[k:] + fin(l0)]
    L += [f"· -- {bn} = true"] + ["  " + x for x in p1[k:] + fin(l1)]
    return L


# ---------------------------------------------------------------- compose (decode, then marshal)
# Shape of Fk/ComposeSc.lean (sc_unmarshal_then_marshal); the proof uses the generated
# `accept` and `marshal` of this module, not the hand theorems.

def compose_stmt(F, labels):
    n = len(F.f)
    bi = [i for i, f in enumerate(F.f) if f["kind"] == "bool"][0]
    bs, cs, ds = (" ".join(f"{x}{i}" for i in range(n)) for x in "bcd")
    hb = " ".join(f"(h{i}l : b{i}.length = {f['w']})" for i, f in enumerate(F.f))
    hc = " ".join(f"(g{i} : c{i}.length = {f['w']})" for i, f in enumerate(F.f))
    hd = " ".join(f"(hd{i} : d{i}.length = {f['w']})" for i, f in enumerate(F.f))
    inp = lambda: "\n      ⋆ ".join(f"Eq (b{i}.At {plus('s.regs.rbx.toBitVec', f['ssz'])})" for i, f in enumerate(F.f))
    rcv = "\n      ⋆ ".join(f"Eq (c{i}.At {plus('s.regs.rax.toBitVec', f['go'])})" for i, f in enumerate(F.f))
    D = "dptr.toBitVec + dlen.toBitVec"
    dst = "\n        ⋆ ".join(f"Eq (d{i}.At {('(' + D + ' + ' + str(f['ssz']) + ')') if f['ssz'] else '(' + D + ')'})" for i, f in enumerate(F.f))
    outd = "\n                ⋆ ".join(f"Eq (b{i}.At {('(' + D + ' + ' + str(f['ssz']) + ')') if f['ssz'] else '(' + D + ')'})" for i, f in enumerate(F.f))
    outa = "\n                ⋆ ".join(f"Eq (b{i}.At {plus('s.regs.rax.toBitVec', f['go'])})" for i, f in enumerate(F.f))
    outb = "\n                ⋆ ".join(f"Eq (b{i}.At {plus('s.regs.rbx.toBitVec', f['ssz'])})" for i, f in enumerate(F.f))
    hl = "\n    ".join(f"(hL{l}f : ∀ i < kd, Host.prog[i]? ≠ some (.label \"{lab}\"))" for l, lab in labels)
    return f"""def compose_stmt [Host] : Prop :=
  ∀ (kd : Nat) (hkd : {F.t}UnmarshalSSZ.IsInfixAt Host.prog kd)
    (km : Nat) (hkm : {F.t}MarshalSSZTo.IsInfixAt Host.prog km) (hfm : LabelsFresh {F.t}MarshalSSZTo km)
    (s : MachineData) (ra ra2 guard : UInt64) (slot {bs} {cs} fp sp1 {ds} pre : List UInt8)
    (hsl : slot.length = 8) {hb}
    {hc}
    (hfp : fp.length = 8) (hs1 : sp1.length = 8)
    {hd}
    (dptr dlen cap : UInt64) (hpre : pre.length = dlen.toNat)
    (hcap2 : dlen.toNat + {F.size} ≤ cap.toNat) (hcap2' : cap.toNat < 2 ^ 63)
    (R0 : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16))
      ⋆ {inp()}
      ⋆ {rcv}
      ⋆ (Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (sp1.At (s.regs.rsp.toBitVec + 8))
        ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
        ⋆ Eq (pre.At dptr.toBitVec) ⋆ {dst} ⋆ R0))
    {hl}
    (hlen : s.regs.rcx = {F.size}) (hb{bi} : b{bi} = [0] ∨ b{bi} = [1]) (hguard : guard.toNat < s.regs.rsp.toNat),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧
        ∀ (m2 : DataMem) (zm : RegZmms) (fl : StatusFlags),
          (∀ F : DataMem → Prop, (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec) ⋆ F) st.data.dmem →
            (Eq ((Int.toBytes 8 ra2.toBitVec.toInt).At s.regs.rsp.toBitVec) ⋆ F) m2) →
          Eventually (step1 Host.exe)
            (fun st' => st'.pc = Int64.ofBitVec ra2.toBitVec ∧ st'.data.regs.rax = dptr
              ∧ st'.data.regs.rbx = dlen + {F.size} ∧
              ({outd} ⋆ Eq (pre.At dptr.toBitVec)
                ⋆ {outa}
                ⋆ {outb} ⋆ R0 ⋆ fun _ => True) st'.data.dmem)
            ⟨⟨{{ st.data.regs with rax := s.regs.rax, rbx := dptr, rcx := dlen, rdi := cap, rsp := s.regs.rsp }},
              zm, fl, m2⟩, Host.addrOf km⟩)
      ⟨s, Host.addrOf kd⟩
"""


def compose_full(F, labels):
    n = len(F.f)
    bi = [i for i, f in enumerate(F.f) if f["kind"] == "bool"][0]
    seq = lambda x: " ".join(f"{x}{i}" for i in range(n))
    intro = (f"intro kd hkd km hkm hfm s ra ra2 guard slot {seq('b')} {seq('c')} fp sp1 {seq('d')} pre hsl "
             f"{' '.join(f'h{i}l' for i in range(n))} {' '.join(f'g{i}' for i in range(n))} hfp hs1 {' '.join(f'hd{i}' for i in range(n))} "
             f"dptr dlen cap hpre hcap2 hcap2' R0 h_mem {' '.join(f'hL{l}f' for l, _ in labels)} hlen hb{bi} hguard")
    pre_l = " ".join(f"h{i}l" for i in range(n) if i != bi)
    return [intro,
            f"refine eventually_trans _ _ _ _ (accept kd hkd s ra slot {seq('b')} {seq('c')} hsl {' '.join(f'h{i}l' for i in range(n))}",
            f"  {' '.join(f'g{i}' for i in range(n))} _ h_mem {' '.join(f'hL{l}f' for l, _ in labels)} hlen hb{bi}) ?_",
            "rintro ⟨d', pc⟩ ⟨hpc, hrax, -, -, hr14, hm⟩",
            "refine Eventually.done _ ⟨hpc, hrax, fun m2 zm fl hupd => ?_⟩",
            "have hm2 := hupd _ (by ecancel)",
            f"have hb' : b{bi} = [0] ∨ b{bi} = [1] := hb{bi}",
            f"refine eventually_trans _ _ _ _ (marshal km hkm hfm _ ra2 guard fp sp1 (Int.toBytes 8 s.regs.rbx.toBitVec.toInt)",
            f"  {seq('b')} {seq('d')} pre hfp hs1 (Int.toBytes_length 8 _) {pre_l} {' '.join(f'hd{i}' for i in range(n))} _",
            "  (by dsimp only; rw [hr14]; ecancel)",
            "  (by dsimp only; exact hguard) (by dsimp only; omega) (by dsimp only; exact hcap2') hb') ?_",
            "intro st' hh",
            "obtain ⟨e1, e2, e3, -, -, -, -, -, -, hm'⟩ := hh",
            "dsimp only at e2 e3 hm'",
            "exact Eventually.done _ ⟨e1, e2, e3, sep_true (by ecancel)⟩"]


# ---------------------------------------------------------------- reject_size, design 2
# The first design (walk() with store_step) failed three times (logs/66, 68, 69). Design 2 follows
# Fk/ScReject.lean: reorder h_mem by hand (h_mem'), store the spill with Mem.storeInt_sep, step with
# sym/kstep, and give each rip load and the return its own separated-frame hypothesis.

def reject_size_full2(D, F, code):
    lab_index = {t: d for d, k, t in D if k == "label"}
    # path: 0 label, 1 spill, 2 cmp $size,%rcx, 3 jne L, L: label, 2 rip loads, retq
    assert D[1][2] == "mov %rbx,0x10(%rsp)" and D[2][2] == f"cmp ${hex(F.size)},%rcx" and D[3][2].startswith("jne "), D[:4]
    lab = D[3][2].split()[1]
    j = lab_index[lab]
    err = re.match(r"mov (ssz\.\w+)\(%rip\),%rax", D[j + 1][2])[1]
    assert D[j + 2][2] == f"mov {err}+8(%rip),%rbx" and D[j + 3][2] == "retq", D[j:j + 4]
    E0 = f'Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "{err}").toBitVec)'
    E1 = f'Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "{err}" + 8).toBitVec)'
    RA = "Eq ((Int.toBytes 8 ra.toBitVec.toInt).At rsp.toBitVec)"
    SP = "Eq ((Int.toBytes 8 rbx.toBitVec.toInt).At (rsp.toBitVec + 16#64))"
    MEM = "(Mem.storeInt mem (rsp.toBitVec + 16#64) 8 rbx.toBitVec.toInt)"
    suf = lab.rsplit("_", 1)[1]
    return ["intro k hk hLf s ra e0 e1 slot hsl R h_mem hlen",
            f"have hL := label_in_fragment hk (j := {j}) (by decide) (by decide) hLf",
            "have h0 := hk",
            f"simp only [{code}] at h0",
            "apply estep h0",
            "simp [Directive.interp]",
            "apply estep h0.cons.2",
            "obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s",
            "simp only at h_mem hlen ⊢",
            f"have h_mem' : (Eq (slot.At (rsp.toBitVec + 16#64)) ⋆ ({RA}",
            f"    ⋆ {E0} ⋆ {E1} ⋆ R)) mem := by",
            "  ecancel",
            "have h_mem1 := Mem.storeInt_sep (rsp.toBitVec + 16#64) 8 slot _ mem ⟨h_mem', hsl⟩ rbx.toBitVec.toInt",
            "sym =>", "kstep",
            "case h_mem => tactic => simp; exact h_mem'",
            "case h_len => exact hsl",
            "tactic =>",
            "simp only [Effects.All_require_write_access, Effects.All]",
            "apply estep h0.cons.2.cons.2",
            "sym =>", "kstep", "tactic =>",
            "apply estep h0.cons.2.cons.2.cons.2",
            "sym =>", "kstep", "tactic =>",
            "rename_i v status",
            "have hv : ¬ (v = 0#64) := by grind",
            "have hc : (!v == BitVec.zero 64) = true := by simpa using hv",
            "simp only [hc, ↓reduceIte, Effects.All]",
            "rw [hL]",
            f"have hj := isInfixAt_drop hk {j}",
            f"simp only [{code}, List.drop] at hj",
            "apply estep hj",
            "simp [Directive.interp]",
            f"have hE0 : ({E0} ⋆", f"    ({SP} ⋆ {RA}", f"      ⋆ {E1} ⋆ R))", f"    {MEM} := by ecancel",
            "apply estep hj.cons.2",
            "sym =>", "kstep",
            "case h_mem => tactic => simp [rip_addr']; exact hE0",
            "case h_len => exact Int.toBytes_length 8 _",
            "tactic =>",
            "simp only [Effects.All_require_read_access, Effects.All]",
            f"have hE1 : ({E1} ⋆", f"    ({SP} ⋆ {RA}", f"      ⋆ {E0} ⋆ R))", f"    {MEM} := by ecancel",
            "apply estep hj.cons.2.cons.2",
            "simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,",
            "  AddrExpr.interp, ConstExpr.interp, Effects.All]",
            "simp only [Width.bits, Int.add_zero, rip_addr, BitVec.setWidth_eq]",
            "rw [load_sep _ _ _ _ _ _ hE1 (Int.toBytes_length 8 _)]",
            "simp only [Effects.All_require_read_access, MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,",
            "  Effects.All, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]",
            f"have hRA : ({RA} ⋆", f"    ({SP}", f"      ⋆ {E0}", f"      ⋆ {E1} ⋆ R))", f"    {MEM} := by ecancel",
            "apply estep hj.cons.2.cons.2.cons.2",
            "simp only [Directive.interp, Instr.interp, Operation.interp, Effects.All, Reg64s.get64]",
            "rw [load_sep _ _ _ _ _ _ hRA (Int.toBytes_length 8 _)]",
            "simp only [Effects.All_require_read_access, Effects.All, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]",
            "exact Eventually.done _ ⟨rfl, rfl, rfl⟩"], (suf, lab)


# ---------------------------------------------------------------- one list[uint] field (ListU64 shape)
# Patterns of Fk/LuMarshal.lean (lu_size_main) and Fk/LuReject.lean (lu_reject_short_main,
# lu_reject_offset_main): stack guard through r12, frame push, one spill, length and first-offset
# checks, error epilogue (rip loads, frame pop, return).

class ListField:
    def __init__(self, desc, layout):
        [f] = desc["fields"]
        assert f["kind"] == "list" and f["variable"] and desc["fixed_part_size"] == 4, f
        lf = layout["fields"][0]
        assert lf["kind"] == "slice", lf
        self.t, self.esz, self.limit, self.goff = desc["type"], f["elem_size"], f["limit"], lf["offset"]
        self.shift = {1: 0, 2: 1, 4: 2, 8: 3}[self.esz]


def lu_size_stmt(code, L):
    return f"""def size_stmt [Host] : Prop :=
  ∀ (k : Nat) (hk : {code}.IsInfixAt Host.prog k) (s : MachineData) (ra : UInt64)
    (n : Nat) (hn : n < 2 ^ 60) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 n).toInt).At (s.regs.rax.toBitVec + {L.goff + 8})) ⋆ R),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax.toNat = 4 + {L.esz} * n
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf k⟩
"""


def lu_size_proof(D, L, code):
    assert [x[2] for x in D[1:]] == [f"mov {hex(L.goff + 8)}(%rax),%rax", f"shl ${hex(L.shift)},%rax", "add $0x4,%rax", "retq"], D
    return ["intro k hk s ra n hn R h_mem",
            "obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s",
            "simp only at h_mem ⊢",
            f"kat hk {code} 0", f"kat hk {code} 1",
            "apply load_step _ _ _ _ (Int.toBytes 8 (BitVec.ofNat 64 n).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)",
            "kunfold", f"kat hk {code} 2", f"kshl64 {L.shift}", f"kat hk {code} 3", f"kat hk {code} 4",
            "apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)",
            "kunfold", "apply Eventually.done", "simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]",
            "refine ⟨trivial, ?_, ?_, trivial⟩",
            f"· show (4 + BitVec.ofNat 64 n <<< {L.shift}).toNat = _",
            "  simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega",
            "· apply UInt64.toBitVec_inj.mp; simp"]


def lu_rej_stmt(name, code, err, mode):
    o4 = "\n    (o4 : List UInt8) (ho4 : o4.length = 4) (hoff : Int.ofBytes o4 ≠ 4)" if mode == "offset" else ""
    o4m = "\n      ⋆ Eq (o4.At s.regs.rbx.toBitVec)" if mode == "offset" else ""
    hlen = "(hlen : s.regs.rcx.toNat < 4)" if mode == "short" else "(hlen : 4 ≤ s.regs.rcx.toNat)"
    return f"""def {name}_stmt [Host] : Prop :=
  ∀ (k : Nat) (hk : {code}.IsInfixAt Host.prog k)
    (hf : LabelsFresh {code} k)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp slot : List UInt8) (hfp : fp.length = 8) (hsl : slot.length = 8){o4}
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16)){o4m}
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "{err}").toBitVec)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "{err}" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat - 8) (hsp : 8 ≤ s.regs.rsp.toNat) {hlen},
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩
"""


def lu_rej_proof(D, code, mode):
    lab_index = {t: d for d, k, t in D if k == "label"}
    kat = lambda d: f"kat hk {code} {d}"
    intro = "intro k hk hf s ra guard e0 e1 fp slot hfp hsl " + ("o4 ho4 hoff " if mode == "offset" else "") + "R h_mem hguard hsp hlen"
    L = [intro,
         "obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s",
         "simp only at h_mem hguard hsp hlen ⊢",
         "have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; simp only [UInt64.size] at *"]
    d, frame, err, seen = 0, None, None, set()
    while True:
        assert d not in seen
        seen.add(d)
        _, kind, t = D[d]
        if kind == "label":
            L.append(kat(d)); d += 1; continue
        op = t.split()[0]
        a = t[len(op):].strip()
        if op == "lea" and a == "-0x8(%rsp),%r12" or op == "nop" or (op == "mov" and a == "%rsp,%rbp"):
            L.append(kat(d))
        elif op == "cmp" and a == "0x10(%r14),%r12":
            L += [kat(d), "apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)", "kunfold"]
        elif op == "jbe":
            L += [kat(d), "split", "case isTrue h =>", "  exfalso",
                  "  rw [cmp_be_false _ _ _ _ (by rw [toNat_add_neg8 _ (by simpa using hsp)]; simpa using hguard)] at h",
                  "  exact absurd h (by simp)", "simp only [Effects.All]"]
        elif op == "push":
            L += [kat(d), "apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by kaddr) (by ecancel) (by exact hfp)",
                  "intro m1 H1", "simp only [Width.bytes, Width.bits] at H1", "kunfold"]
        elif op == "add" and a.endswith(",%rsp"):
            assert a.startswith("$-"), a
            frame = -int(a.split(",")[0][1:], 16)
            L.append(kat(d))
        elif op == "mov" and a.startswith("%rbx,") and a.endswith("(%rsp)"):
            off = int(a.split(",")[1].split("(")[0], 16) - frame - 8
            assert off == 16, a
            L += [kat(d), f"apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ slot _ _ (by bv_omega) (by ecancel) (by exact hsl)",
                  "intro m2 H2", "simp only [Width.bytes, Width.bits] at H2", "kunfold"]
        elif op == "cmp" and a == "$0x4,%rcx":
            L.append(kat(d))
        elif op == "jb":
            L += [kat(d), "split"]
            if mode == "short":
                L += ["case isFalse h =>", "  exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega",
                      "simp only [Effects.All]", f"klabel hk hf {code} {lab_index[a]}"]
                d = lab_index[a]; continue
            L += ["case isTrue h =>", "  exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega",
                  "simp only [Effects.All]"]
        elif op == "mov" and a == "(%rbx),%edx":
            L += [kat(d), "apply load_step_at _ _ rbx.toBitVec _ _ o4 _ _ (by bv_omega) (by ecancel) (by exact ho4)", "kunfold"]
        elif op == "cmp" and a == "$0x4,%rdx":
            L.append(kat(d))
        elif op == "jne" and mode == "offset":
            L += [kat(d), "split", "case isFalse h =>", "  exfalso; simp [CondCode.interp, StatusFlags.from_result] at h",
                  "  exact hoff (Gen1cX4.off4 o4 ho4 h)", "simp only [Effects.All]", f"klabel hk hf {code} {lab_index[a]}"]
            d = lab_index[a]; continue
        elif op == "mov" and re.fullmatch(r"ssz\.\w+(\+8)?\(%rip\),%r[ab]x", a):
            e = "e1" if "+8" in a else "e0"
            L += [kat(d), f"apply load_step _ _ _ _ (Int.toBytes 8 {e}.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)", "kunfold"]
        elif op == "sub" and a.endswith(",%rsp"):
            L.append(kat(d))
        elif op == "pop":
            L += [kat(d), f"rw [show -{frame} + (rsp.toBitVec - 8#64) - -{frame} = rsp.toBitVec - 8 by bv_omega]",
                  "apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)", "kunfold"]
        elif op == "retq":
            L += [kat(d), "rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]",
                  "apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)",
                  "kunfold", "apply Eventually.done", "simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]",
                  "refine ⟨trivial, ?_, ?_, ?_, ?_, ?_⟩",
                  "· first | trivial | rfl | (apply UInt64.toBitVec_inj.mp; simp)",
                  "· first | trivial | rfl | (apply UInt64.toBitVec_inj.mp; simp)",
                  "· apply UInt64.toBitVec_inj.mp; simp", "· first | trivial | rfl",
                  "· have : (R ⋆ fun _ => True) m2 := sep_true (by ecancel)", "  exact this"]
            return L
        else:
            raise SystemExit(f"list reject directive {d} `{t}`: no tactic template")
        d += 1


def lu_err(D, mode):
    """Error global of the path's first error label (short: jb target, offset: jne target)."""
    lab_index = {t: d for d, k, t in D if k == "label"}
    op = "jb" if mode == "short" else "jne"
    tgt = next(t.split()[1] for _, k, t in D if k == "instr" and t.split()[0] == op)
    return re.match(r"mov (ssz\.\w+)\(%rip\)", D[lab_index[tgt] + 1][2])[1]


# ---------------------------------------------------------------- ListU64 reject paths through fmt.errorf
# Pattern of Fk/LuRejectCall.lean (lu_reject_toobig_main, lu_reject_misaligned_main): the length
# checks pass up to the failing one, then a 4-word argument array (two `any`) is built in the frame
# with two `movups %xmm15`, `runtime.convT64` boxes the count (contract ConvT64C), the type word of
# `int` and the error global's itab/data words fill the array, `fmt.errorf` with a `%d ... %w` format
# (contract FmtErrorfDWC) returns a non-nil error and the epilogue returns it. Per-directive steps,
# label numbers, frame/argument offsets, call sites, data items and the arithmetic lemmas are
# generated from the directive list; the contract application blocks are hand text with these
# values substituted (README section 2).

class CallPath:
    """Values of one fmt.errorf reject path, read from the directive list (refuses anything else)."""
    def __init__(self, D, mode):
        lab_index = {t: d for d, k, t in D if k == "label"}
        ins = [(d, t) for d, k, t in D if k == "instr"]
        self.frame = next(-int(t.split()[1].split(",")[0][1:], 16) for d, t in ins if re.fullmatch(r"add \$-0x[0-9a-f]+,%rsp", t))
        test7 = next(d for d, t in ins if t == "test $0x7,%rcx")
        assert D[test7 + 1][2].startswith("jne "), D[test7 + 1]
        if mode == "misaligned":
            self.start = lab_index[D[test7 + 1][2].split()[1]]
        else:
            jg = next(d for d, t in ins if d > test7 and t.startswith("jg "))
            assert [D[jg - 2][2], D[jg - 1][2]] == ["shr $0x3,%rcx", "cmp $0x10,%rcx"], (D[jg - 2], D[jg - 1])
            self.start = lab_index[D[jg][2].split()[1]]
        d = self.start + 1
        m = re.fullmatch(r"lea (0x[0-9a-f]+)\(%rsp\),%rdx", D[d][2])
        assert m, D[d]
        self.argoff = int(m[1], 16)
        calls = [i for i in range(d, len(D)) if D[i][2].startswith("callq ")]
        self.c1, self.c2 = calls[0], calls[1]
        assert D[self.c1][2] == "callq runtime.convT64" and D[self.c2][2] == "callq fmt.errorf", (D[self.c1], D[self.c2])
        m = re.fullmatch(r"lea type__\+(\d+)\(%rip\),%rcx", D[self.c1 + 1][2])
        assert m, D[self.c1 + 1]
        self.tw = tw_item(int(m[1]))
        self.err = next(re.fullmatch(r"mov (ssz\.\w+)\(%rip\),%rcx", D[i][2])[1] for i in range(self.c1, self.c2)
                        if re.fullmatch(r"mov ssz\.\w+\(%rip\),%rcx", D[i][2]))
        fs = [re.fullmatch(r"lea go_string\._\+(\d+)\(%rip\),%rax", D[i][2]) for i in range(self.c1, self.c2)]
        [fs] = [x for x in fs if x]
        ln = next(int(re.fullmatch(r"mov \$(0x[0-9a-f]+),%ebx", D[i][2])[1], 16) for i in range(self.c1, self.c2)
                  if re.fullmatch(r"mov \$0x[0-9a-f]+,%ebx", D[i][2]))
        fid, api_id = include_adapter.rodata_id(None, include_adapter.RODATA_LABEL, int(fs[1]), ln)
        assert api_id, f"format string go_string._+{fs[1]} ({ln} bytes) is not an include API item"
        self.fmt, self.fmtlen = fid, ln
        assert D[self.c2 + 1][2] == "test %rax,%rax" and D[self.c2 + 2][2].startswith("jne "), D[self.c2 + 1:self.c2 + 3]
        self.end = lab_index[D[self.c2 + 2][2].split()[1]]
        C = self.frame + 16                    # call slot rsp - C (return address of a call)
        self.C = C
        self.P1 = 8 + self.frame - self.argoff  # argument array at rsp - P1 (16 bytes) and rsp - P2
        self.P2 = self.P1 - 16
        assert self.P2 - 8 > 8 and self.argoff >= 40, "argument array must lie above the 40-byte spill area"
        self.budget = ln + 20 + 8192 + 8        # FmtErrorfDWC budget + the convT64 box


def tw_item(off):
    api = include_adapter.check_api()
    hits = [it["id"] for it in api["items"] if it.get("label") == "type__" and it.get("offset") == off]
    assert hits == ["intType"], f"type word type__+{off} is not the include API item intType ({hits})"
    return "intType"


def lu_call_lemmas(P):
    """Arithmetic lemmas of one call path with the path's numbers (generated, proved by bv_omega)."""
    F, A, C, P1, P2 = P.frame, P.argoff, P.C, P.P1, P.P2
    u = "simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega"
    L = {f"ar_a{P1}": f"(x : BitVec 64) : -{F} + (x - 8#64) + {A} = x - {P1} := by bv_omega",
         f"ar_a{P2}": f"(x : BitVec 64) : x - {P1} + 16 = x - {P2} := by bv_omega",
         f"ar_slot{C}": f"(x : BitVec 64) : -{F} + (x - 8#64) - 8#64 = x - {C} := by bv_omega",
         f"ar_d{P1}": f"(x : BitVec 64) : x - {P1} + 8 = x - {P1 - 8} := by bv_omega",
         f"ar_d{P2}": f"(x : BitVec 64) : x - {P2} + 8 = x - {P2 - 8} := by bv_omega",
         f"ar_b{C}": f"(x o : BitVec 64) : ({{ toBitVec := x - {C} }} + 8 : UInt64).toBitVec + o = x - {C - 8} + o := by\n  {u}",
         f"ar_p{F}": f"(x : BitVec 64) : ({{ toBitVec := x - {C} }} + 8 : UInt64).toBitVec - -{F} = x - 8 := by\n  {u}",
         f"ar_c{C}": f"(x : BitVec 64) : ({{ toBitVec := x - {C} }} + 8 : UInt64).toBitVec - 8#64 = x - {C} := by\n  {u}"}
    for j in range(4):
        L[f"ar_c{C - 8}_{A + 8 * j}"] = f"(x : BitVec 64) : x - {C - 8} + {A + 8 * j} = x - {P1 - 8 * j} := by bv_omega"
    return L


def lu_call_stmt(name, code, mode, P):
    fb, fa = include_adapter.bytes_name(P.fmt), include_adapter.addr_name(P.fmt)
    nn = "\n    (n : Nat) (hn : 16 < n)" if mode == "toobig" else ""
    box = "BitVec.ofNat 64 n" if mode == "toobig" else "s.regs.rcx.toBitVec - 4"
    hlen = ("(hlen : s.regs.rcx.toNat = 4 + 8 * n)" if mode == "toobig"
            else "(hlen : 4 ≤ s.regs.rcx.toNat) (hmis : (s.regs.rcx.toNat - 4) % 8 ≠ 0)")
    return f"""def {name}_stmt [Host] : Prop :=
  ∀ (k : Nat) (hk : {code}.IsInfixAt Host.prog k)
    (hf : LabelsFresh {code} k){nn}
    (s : MachineData) (ra guard e0 e1 t8 : UInt64) (he0 : e0 ≠ 0)
    (hei : e0.toBitVec = (label "go_itab._errors.errorString_error").toBitVec) (esp : BitVec 64) (msg : List UInt8)
    (fp slot a0 a1 rslot : List UInt8) (hfp : fp.length = 8) (hsl : slot.length = 8)
    (ha0 : a0.length = 16) (ha1 : a1.length = 16) (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch spl : List UInt8) (hsc : scratch.length = S)
    (hspl : spl.length = 40)
    (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 8 ≤ avail) (hbud : msg.length + {P.budget} ≤ avail)
    (h_mem : s.dmem =⋆ Eq (spl.At (s.regs.rsp.toBitVec - {P.C - 8})) ⋆ Eq ({fb}.At {fa}) ⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (a0.At (s.regs.rsp.toBitVec - {P.P1})) ⋆ Eq (a1.At (s.regs.rsp.toBitVec - {P.P2}))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - {P.C})) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - {P.C} - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq ([4, 0, 0, 0].At s.regs.rbx.toBitVec)
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "{P.err}").toBitVec)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "{P.err}" + 8).toBitVec)
      ⋆ Eq ((Int.toBytes 8 t8.toBitVec.toInt).At (e0.toBitVec + 8)) ⋆ ErrStr e1.toBitVec esp msg ⋆ StaticBox ({box}) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat - 8) (hsp : {P.C} ≤ s.regs.rsp.toNat)
    {hlen}
    (hcv : ConvT64C Heap S) (hfe : FmtErrorfDWC Heap {fb} {include_adapter.addr_name(P.tw)} S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax ≠ 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩
"""


def lu_call_proof(D, code, mode, P):
    """Proof of one fmt.errorf reject path: walk the directives from the entry to the failing check,
    then from the path label through both calls to `retq`."""
    lab_index = {t: d for d, k, t in D if k == "label"}
    kat = lambda d: f"kat hk {code} {d}"
    F, A, C, P1, P2 = P.frame, P.argoff, P.C, P.P1, P.P2
    hyps = "hlen hmis" if mode == "misaligned" else "hlen"
    intro = ("intro k hk hf " + ("n hn " if mode == "toobig" else "") + "s ra guard e0 e1 t8 he0 hei esp msg "
             "fp slot a0 a1 rslot hfp hsl ha0 ha1 hrs R S scratch spl hsc hspl Heap avail hav hbud h_mem hguard hsp "
             f"{hyps} hcv hfe")
    L = [intro,
         "obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s",
         f"simp only at h_mem hguard hsp {hyps} ⊢"]
    if mode == "misaligned":
        L += ["generalize hSB : StaticBox (rcx.toBitVec - 4) = SB at h_mem"]
    L += ["have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size",
          "simp only [UInt64.size] at *",
          f"have hfl : {include_adapter.bytes_name(P.fmt)}.length = {P.fmtlen} := by rfl"]
    xmm = "(Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt)"
    d, seen, done_c1 = 0, set(), False
    while True:
        if d in seen:
            raise SystemExit(f"call path {mode}: directive {d} visited twice")
        seen.add(d)
        _, kind, t = D[d]
        if kind == "label":
            L.append(kat(d)); d += 1; continue
        op = t.split()[0]
        a = t[len(op):].strip()
        if (op == "lea" and a == "-0x8(%rsp),%r12") or op == "nop" or (op == "mov" and a in ("%rsp,%rbp", "%rdx,%rsi", "%rcx,%rax", "%rax,%rbx", "%rdi,%rsi")):
            L.append(kat(d))
        elif op == "cmp" and a == "0x10(%r14),%r12":
            L += [kat(d), "apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)", "kunfold"]
        elif op == "jbe":
            L += [kat(d), "split", "case isTrue h =>", "  exfalso",
                  "  rw [cmp_be_false _ _ _ _ (by rw [toNat_add_neg8 _ (by simp; omega)]; simpa using hguard)] at h",
                  "  exact absurd h (by simp)", "simp only [Effects.All]"]
        elif op == "push":
            L += [kat(d), "apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by kaddr) (by ecancel) (by exact hfp)",
                  "intro m1 H1", "simp only [Width.bytes, Width.bits] at H1", "kunfold"]
        elif op == "add" and a == f"$-{hex(F)},%rsp":
            L.append(kat(d))
        elif op == "mov" and a == f"%rbx,{hex(F + 24)}(%rsp)":
            L += [kat(d), "apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ slot _ _ (by bv_omega) (by ecancel) (by exact hsl)",
                  "intro m2 H2", "simp only [Width.bytes, Width.bits] at H2", "kunfold"]
        elif op == "cmp" and a in ("$0x4,%rcx", "$0x4,%rdx", "$0x10,%rcx"):
            L.append(kat(d))
        elif op == "jb":
            L += [kat(d), "split", "case isTrue h =>",
                  "  exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega", "simp only [Effects.All]"]
        elif op == "mov" and a == "(%rbx),%edx":
            L += [kat(d), "apply load_step_at _ _ rbx.toBitVec _ _ [4, 0, 0, 0] _ _ (by bv_omega) (by ecancel) (by simp)",
                  "simp only [show Int.ofBytes [4, 0, 0, 0] = 4 by simp [Int.ofBytes]]", "kunfold"]
        elif op == "jne" and D[d - 1][2] == "cmp $0x4,%rdx":
            L += [kat(d), "split", "case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h",
                  "simp only [Effects.All]"]
        elif op == "lea" and a == "-0x4(%rdi),%rdx" or op == "neg" and a == "%rdx" or op == "add" and a in ("$-0x4,%rcx", "%rbx,%rdx"):
            L.append(kat(d))
        elif op == "sar" and a == "$0x3f,%rdx":
            L += [kat(d), "kshl64 63"]
        elif (op == "and" and a == "$0x4,%edx") or op == "test":
            L += [kat(d), "intro _"]
        elif op == "jne" and D[d - 1][2] == "test $0x7,%rcx":
            L += [kat(d), "split"]
            if mode == "misaligned":
                L += ["case isFalse h =>", "  exfalso; simp [CondCode.interp, StatusFlags.from_result] at h",
                      "  exact Gen1cX4.and7_ne rcx.toBitVec (by simpa using hlen) (by simpa using hmis) h",
                      "simp only [Effects.All]", f"klabel hk hf {code} {P.start}"]
                d = P.start; continue
            L += ["case isTrue h =>", "  exfalso; rw [Gen1cX4.and7_zero' rcx.toBitVec n (by simpa using hlen)] at h",
                  "  simp [CondCode.interp, StatusFlags.from_result] at h", "simp only [Effects.All]"]
        elif op == "shr" and a == "$0x3,%rcx":
            L += [kat(d), "kshl64 3"]
        elif op == "jg":
            assert mode == "toobig", t
            L += [kat(d), "have hnN := Gen1cX4.shr3_toNat' rcx.toBitVec n (by simpa using hlen)",
                  "generalize BitVec.ushiftRight (-4 + rcx.toBitVec) 3 = nV at hnN ⊢",
                  "rw [Gen1cX4.jg16_true nV _ (by omega) (by omega)]", "simp only [↓reduceIte, Effects.All]",
                  f"klabel hk hf {code} {P.start}"]
            d = P.start; continue
        elif op == "lea" and a in (f"{hex(A)}(%rsp),%rdx", f"{hex(A)}(%rsp),%rcx"):
            L.append(kat(d))
        elif op == "movups" and a in ("%xmm15,(%rdx)", "%xmm15,0x10(%rdx)"):
            first = a.endswith(",(%rdx)")
            L += [kat(d), "simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]", "kunfold",
                  f"rw [ar_a{P1 if first else P2}]",
                  f"apply Gen1cX4.store_avx_step _ _ _ _ {'a0' if first else 'a1'} _ _ (by ecancel) (by exact {'ha0' if first else 'ha1'}) (by decide)",
                  f"intro m{3 if first else 4} H{3 if first else 4}", "kunfold"]
        elif op == "callq" and d == P.c1:
            box = ("rw [hA, Gen1cX4.staticBox_congr (y := BitVec.ofNat 64 n) ?hv]" if mode == "toobig"
                   else "rw [hA, Gen1cX4.staticBox_congr (y := rcx.toBitVec - 4) ?hv, hSB]")
            hv = ("first | bv_omega | (apply BitVec.eq_of_toNat_eq; rw [Gen1cX4.shr3_toNat' _ _ hlen]; simp; omega)"
                  if mode == "toobig" else "rw [BitVec.add_comm, ← BitVec.sub_eq_add_neg]")
            L += [kat(d), f"apply store_step_at _ _ (rsp.toBitVec - {C}) _ _ _ rslot _ _ (ar_slot{C} _) (by ecancel) (by exact hrs)",
                  "intro m5 H5", "simp only [Width.bytes, Width.bits] at H5", "kunfold", f"rw [ar_slot{C}] at *",
                  f"have hA : rsp.toBitVec - {C} + 8 = rsp.toBitVec - {C - 8} := by bv_omega",
                  f"rw [← List.take_append_drop 8 spl, at_app (spl.take 8) (spl.drop 8) (a := rsp.toBitVec - {C - 8})",
                  f"  (b := rsp.toBitVec - {C - 16}) (by simp [hspl]; bv_omega) (by simp [hspl])] at H5",
                  f"refine eventually_trans _ _ _ _ (hcv _ (Host.addrOf (k + {d} + 1)) avail scratch (spl.take 8) _ hav hsc",
                  "  (by simp [hspl]) (by", "    try dsimp only", f"    {box}", "    · ecancel", f"    · {hv})) ?_",
                  "rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hr141, stk1, sp1, hb1, av1, hstk1, hsp1, hbox1, hav1, hav1', Hm1⟩",
                  "dsimp only at hpc1 hrsp1 Hm1"]
            if mode == "misaligned":
                L += ["have hv4 : -4 + rcx.toBitVec = rcx.toBitVec - 4 := by rw [BitVec.add_comm, ← BitVec.sub_eq_add_neg]",
                      "rw [hv4] at hbox1", "rw [Gen1cX4.staticBox_congr hv4, hSB] at Hm1"]
            L += ["subst hpc1",
                  "obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩,",
                  "  zmms1, flags1, mem1⟩ := d1",
                  "simp only at hrsp1 Hm1", "rw [hA] at Hm1", "subst hrsp1",
                  f"rw [Gen1cX4.lr_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - {P1}), Gen1cX4.lr_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - {P2})] at Hm1",
                  f"rw [ar_d{P1}, ar_d{P2}] at Hm1"]
            done_c1 = True
        elif op == "lea" and re.fullmatch(r"(type__|go_string\._|go_itab\.\w+)\+?\d*\(%rip\),%r[a-z]x", a):
            L.append(kat(d))
        elif op == "mov" and re.fullmatch(r"%r[a-d]x,(0x[0-9a-f]+)\(%rsp\)", a) and done_c1:
            o = int(re.fullmatch(r"%r[a-d]x,(0x[0-9a-f]+)\(%rsp\)", a)[1], 16)
            assert A <= o < A + 32 and o % 8 == 0, t
            j = (o - A) // 8
            half = "take" if j % 2 == 0 else "drop"
            hn = {0: 6, 1: 7, 2: 8, 3: 9}[j]
            L += [kat(d), f"rw [ar_b{C}, ar_c{C - 8}_{o}]",
                  f"apply store_step _ _ _ _ _ ({xmm}.{half} 8) _ _ (by ecancel) (by simp [Int.toBytes_length])",
                  f"intro m{hn} H{hn}", f"simp only [Width.bytes, Width.bits] at H{hn}", "kunfold"]
        elif op == "mov" and a == f"{P.err}(%rip),%rcx":
            L += [kat(d), "apply load_step _ _ _ _ (Int.toBytes 8 e0.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)", "kunfold"]
        elif op == "mov" and a == f"{P.err}+8(%rip),%rdx":
            L += [kat(d), "apply load_step _ _ _ _ (Int.toBytes 8 e1.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)", "kunfold"]
        elif op == "je" and D[d - 1][2] == "test %rcx,%rcx":
            L += [kat(d), "split", "case isTrue h =>", "  exfalso; simp [CondCode.interp, StatusFlags.from_result] at h",
                  "  exact he0 (UInt64.toBitVec_inj.mp (by simpa using h))", "simp only [Effects.All]"]
        elif op == "mov" and a == "0x8(%rcx),%rcx":
            L += [kat(d), "apply load_step _ _ _ _ (Int.toBytes 8 t8.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)", "kunfold"]
        elif op == "mov" and re.fullmatch(r"\$0x[0-9a-f]+,%e[bd]i?x?", a):
            L.append(kat(d))
        elif op == "callq" and d == P.c2:
            L += [kat(d), f"apply store_step_at _ _ (rsp.toBitVec - {C}) _ _ _ (Int.toBytes 8 (Host.addrOf (k + {P.c1} + 1)).toBitVec.toInt) _ _",
                  f"  (ar_c{C} _) (by ecancel) (by exact Int.toBytes_length 8 _)",
                  "intro m10 H10", "simp only [Width.bytes, Width.bits] at H10", "kunfold",
                  f"rw [ar_c{C}] at *", "rw [← hA] at H10",
                  f"refine eventually_trans _ _ _ _ (hfe _ (Host.addrOf (k + {d} + 1)) av1",
                  "  (Int.toBytes 8 t8.toBitVec.toInt) msg hb1 stk1 (sp1 ++ spl.drop 8) rax1.toBitVec _ e1.toBitVec esp _",
                  "  (by rw [hfl]; rfl) (by first | rfl | decide) (by first | rfl | decide)",
                  "  (Int.toBytes_length 8 _) hbox1 hstk1 (by simp [hsp1, hspl]) (by rw [hfl]; omega)",
                  "  (by dsimp only",
                  "      rw [← hei" + (", hSB]" if mode == "misaligned" else "]"),
                  f"      simp only [{include_adapter.addr_name(P.tw)}]",
                  "      simp only [List.append_assoc]",
                  f"      try simp only [ar_b{C}, ar_c{C - 8}_{A}]",
                  f"      rw [at_app sp1 (spl.drop 8) (b := rsp.toBitVec - {C - 16}) (by rw [hsp1]; bv_omega) (by simp [hsp1, hspl]),",
                  f"        Gen1cX4.join4 (rsp.toBitVec - {P1}) (rsp.toBitVec - {P1 - 8}) (rsp.toBitVec - {P2}) (rsp.toBitVec - {P2 - 8}) _ _ _ _ (Int.toBytes_length 8 _)",
                  "          (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) (by bv_omega) (by bv_omega) (by bv_omega)]",
                  "      ecancel)) ?_",
                  "rintro ⟨d2, pc2⟩ ⟨hpc2, hrsp2, hr142, hrax2, stk2, sp2, av2, hstk2, hsp2, hav2, Hm2⟩",
                  "dsimp only at hpc2 hrsp2 hrax2 Hm2", "subst hpc2",
                  "obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,",
                  "  zmms2, flags2, mem2⟩ := d2",
                  "simp only at hrsp2 hrax2 Hm2", "subst hrsp2"]
        elif op == "jne" and D[d - 1][2] == "test %rax,%rax":
            L += [kat(d), "split", "case isFalse h =>", "  exfalso; simp [CondCode.interp, StatusFlags.from_result] at h",
                  "  exact hrax2 (UInt64.toBitVec_inj.mp (by simpa using h))", "simp only [Effects.All]",
                  f"klabel hk hf {code} {P.end}"]
            d = P.end; continue
        elif op == "sub" and a == f"$-{hex(F)},%rsp":
            L.append(kat(d))
        elif op == "pop" and d > P.end:
            L += [kat(d), f"rw [ar_p{F}]",
                  "apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)", "kunfold"]
        elif op == "retq" and d > P.end:
            L += [kat(d), "rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]",
                  "apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)",
                  "kunfold", "apply Eventually.done", "simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]",
                  "refine ⟨trivial, hrax2, ?_, ?_, ?_⟩", "· apply UInt64.toBitVec_inj.mp; simp", "· first | trivial | rfl",
                  "· have : (R ⋆ fun _ => True) mem2 := sep_true (by ecancel)", "  exact this"]
            return L
        else:
            raise SystemExit(f"call path {mode}: directive {d} `{t}`: no tactic template")
        d += 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--desccheck-result", required=True)
    ap.add_argument("--desc-dir", required=True)
    ap.add_argument("--type", required=True)
    ap.add_argument("--out-lean", required=True)
    ap.add_argument("--only", default="size,accept,reject_bool,reject_size,marshal,compose",
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
    try:
        if any(f["kind"] == "list" for f in desc["fields"]):
            return main_list(a, key, desc, dsha)
        F = Fields(desc, LAYOUT["types"][t])
        check_offsets(F, directives(os.path.join(NORM, f"target.{t}.UnmarshalSSZ.S")))
    except (KeyError, AssertionError, IndexError, StopIteration) as e:   # review r5 S5: classified refusal
        raise SystemExit(f"x4gen: refused {key[0]}.{t}: template does not fit the Desc/layout/code "
                         f"({type(e).__name__}: {e})")
    ns = a.ns or f"Gen1cX4.{t}"
    only = a.only.split(",")
    code = {m: f"{t}{m}" for m in ("SizeSSZ", "UnmarshalSSZ", "MarshalSSZTo")}
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
        rs_proof, rs_lab = reject_size_full2(Dun, F, code["UnmarshalSSZ"])
        body += [reject_size_stmt(code["UnmarshalSSZ"], F, rs_lab[1], err_label(Dun, [d for d, k, x in Dun if x == rs_lab[1]][0])),
                 "theorem reject_size [Host] : reject_size_stmt := by", *["  " + x for x in rs_proof], ""]
    if "reject_bool" in only:
        rb_proof, rb_labels = reject_bool_full(Dun, F)
        body += [reject_bool_stmt(code["UnmarshalSSZ"], F, rb_labels, err_label(Dun, [d for d, k, x in Dun if x == rb_labels[0][1]][0])),
                 "set_option maxHeartbeats 2000000 in",
                 "theorem reject_bool [Host] : reject_bool_stmt := by", *["  " + x for x in rb_proof], ""]
    if "marshal" in only:
        Dma = directives(os.path.join(NORM, f"target.{t}.MarshalSSZTo.S"))
        body += [marshal_stmt(code["MarshalSSZTo"], F), "set_option maxHeartbeats 4000000 in", "set_option maxRecDepth 100000 in",
                 "theorem marshal [Host] : marshal_stmt := by", *["  " + x for x in marshal_full(Dma, F, code["MarshalSSZTo"])], ""]
    if "compose" in only:
        assert "accept" in only and "marshal" in only, "compose uses the generated accept and marshal"
        body += [compose_stmt(F, accept_labels(Dun, F)), "set_option maxHeartbeats 16000000 in", "set_option maxRecDepth 100000 in",
                 "theorem compose [Host] : compose_stmt := by", *["  " + x for x in compose_full(F, accept_labels(Dun, F))], ""]
    body += [f"end {ns}", ""]
    os.makedirs(os.path.dirname(out), exist_ok=True)
    open(out, "w").write("\n".join(body))
    print(json.dumps({"type": t, "out": a.out_lean, "only": only, "mutant": a.mutant, "desc_sha256": dsha}))



def check_offsets(F, D):
    """Every input load (rbx) and receiver store (rax) of the decoder must hit a field of the Desc
    (SSZ offset) and of the Go layout (Go offset); otherwise the Desc does not describe this code."""
    ssz = {f["ssz"] for f in F.f}
    go = {f["go"] for f in F.f}
    for d, k, t in D:
        mm = MEM.match(t) if k == "instr" else None
        if not mm:
            continue
        a, b = disp(mm["a"]), disp(mm["b"])
        if t.split()[0] in ("movzbl", "movzwl", "mov") and a and a[1] == "rbx" and a[0] not in ssz:
            raise SystemExit(f"x4gen: refused {F.t}: directive {d} `{t}` loads input offset {a[0]}, not a field offset of the Desc {sorted(ssz)}")
        if t.split()[0] in ("mov", "movb") and b and b[1] == "rax" and b[0] not in go:
            raise SystemExit(f"x4gen: refused {F.t}: directive {d} `{t}` stores receiver offset {b[0]}, not a Go field offset {sorted(go)}")


def main_list(a, key, desc, dsha):
    t = key[1]
    L = ListField(desc, LAYOUT["types"][t])
    ns = a.ns or f"Gen1cX4.{t}"
    LIST_OBL = ("size", "reject_short", "reject_offset", "reject_misaligned", "reject_toobig")
    only = [x for x in a.only.split(",") if x in LIST_OBL] if a.only != ap_default() else list(LIST_OBL)
    code = {m: f"{t}{m}" for m in ("SizeSSZ", "UnmarshalSSZ", "MarshalSSZTo")}
    head = ["import Fk.Step", "import Fk.Bytes", "import Fk.Labels", "import Fk.Flags", "import Gen1cX4.Support"]
    if any(x in only for x in ("reject_misaligned", "reject_toobig")):
        head += ["import Fk.Contracts", "import Fk.Frame"]
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
        body += [lu_size_stmt(code["SizeSSZ"], L), "theorem size [Host] : size_stmt := by",
                 *["  " + x for x in lu_size_proof(Dsz, L, code["SizeSSZ"])], ""]
    for mode in ("short", "offset"):
        if f"reject_{mode}" in only:
            body += [lu_rej_stmt(f"reject_{mode}", code["UnmarshalSSZ"], lu_err(Dun, mode), mode),
                     "set_option maxHeartbeats 4000000 in", "set_option maxRecDepth 100000 in",
                     f"theorem reject_{mode} [Host] : reject_{mode}_stmt := by",
                     *["  " + x for x in lu_rej_proof(Dun, code["UnmarshalSSZ"], mode)], ""]
    calls = [m for m in ("misaligned", "toobig") if f"reject_{m}" in only]
    if calls:
        if (L.esz, L.limit) != (8, 16):
            raise SystemExit(f"x4gen: refused {key[0]}.{t}: the fmt.errorf reject template is for 8-byte elements "
                             f"and limit 16 (Support lemmas and7_*, shr3_toNat', jg16_true), not {L.esz}/{L.limit}")
        try:
            Ps = {m: CallPath(Dun, m) for m in calls}
        except (KeyError, AssertionError, IndexError, StopIteration, ValueError, TypeError) as e:
            raise SystemExit(f"x4gen: refused {key[0]}.{t}: fmt.errorf reject template does not fit the code "
                             f"({type(e).__name__}: {e})")
        lem = {}
        for m in calls:
            lem.update(lu_call_lemmas(Ps[m]))
        body += ["-- arithmetic lemmas of the fmt.errorf reject paths (generated with the paths' frame and argument offsets)"]
        body += [f"theorem {n} {v}" for n, v in sorted(lem.items())] + [""]
        for m in calls:
            body += [lu_call_stmt(f"reject_{m}", code["UnmarshalSSZ"], m, Ps[m]),
                     "set_option maxHeartbeats 8000000 in", "set_option maxRecDepth 100000 in",
                     f"theorem reject_{m} [Host] : reject_{m}_stmt := by",
                     *["  " + x for x in lu_call_proof(Dun, code["UnmarshalSSZ"], m, Ps[m])], ""]
    body += [f"end {ns}", ""]
    out = os.path.realpath(a.out_lean)
    os.makedirs(os.path.dirname(out), exist_ok=True)
    open(out, "w").write("\n".join(body))
    print(json.dumps({"type": t, "out": a.out_lean, "only": only, "mutant": a.mutant, "desc_sha256": dsha}))


def ap_default():
    return "size,accept,reject_bool,reject_size,marshal,compose"


if __name__ == "__main__":
    main()
