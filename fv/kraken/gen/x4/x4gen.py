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
        self.shift = {1: 0, 2: 1, 4: 2, 8: 3}.get(self.esz)   # None for a list of containers


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


def guard_size(D):
    """Stack-guard distance G of the prologue `lea -G(%rsp),%r12; cmp 0x10(%r14),%r12; jbe`."""
    m = re.fullmatch(r"lea -(0x[0-9a-f]+)\(%rsp\),%r12", D[2][2])
    assert m and D[3][2] == "cmp 0x10(%r14),%r12", D[2:4]
    return int(m[1], 16)


def lu_rej_stmt(name, code, err, mode, G=8):
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
    {"(hguard : guard.toNat < s.regs.rsp.toNat - 8) (hsp : 8 ≤ s.regs.rsp.toNat)" if G == 8 else f"(hguard : guard.toNat + {G} < s.regs.rsp.toNat)"} {hlen},
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩
"""


def lu_rej_proof(D, code, mode, G=8):
    """G: stack-guard distance. G = 8 (ListU64) keeps the hsp premise; a larger guard (ListC: 0x60)
    has the premise `guard + G < rsp` and a generated `ar_neg{G}` lemma."""
    lab_index = {t: d for d, k, t in D if k == "label"}
    kat = lambda d: f"kat hk {code} {d}"
    hsp = "hsp " if G == 8 else ""
    intro = "intro k hk hf s ra guard e0 e1 fp slot hfp hsl " + ("o4 ho4 hoff " if mode == "offset" else "") + f"R h_mem hguard {hsp}hlen"
    L = [intro,
         "obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s",
         f"simp only at h_mem hguard {hsp}hlen ⊢",
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
        if op == "lea" and a == f"-{hex(G)}(%rsp),%r12" or op == "nop" or (op == "mov" and a == "%rsp,%rbp"):
            L.append(kat(d))
        elif op == "cmp" and a == "0x10(%r14),%r12":
            L += [kat(d), "apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)", "kunfold"]
        elif op == "jbe" and G == 8:
            L += [kat(d), "split", "case isTrue h =>", "  exfalso",
                  "  rw [cmp_be_false _ _ _ _ (by rw [toNat_add_neg8 _ (by simpa using hsp)]; simpa using hguard)] at h",
                  "  exact absurd h (by simp)", "simp only [Effects.All]"]
        elif op == "jbe":
            L += [kat(d), "split", "case isTrue h =>", "  exfalso",
                  f"  rw [cmp_be_false _ _ _ _ (by rw [ar_neg{G} _ (by simp; omega)]; simp; omega)] at h",
                  "  exact absurd h (by simp)", "simp only [Effects.All]"]
        elif op == "sub" and re.fullmatch(r"\$0x[0-9a-f]+,%rsp", a) and frame is None:
            frame = ("sub", int(a.split(",")[0][1:], 16))
            L.append(kat(d))
        elif op == "push":
            L += [kat(d), "apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by kaddr) (by ecancel) (by exact hfp)",
                  "intro m1 H1", "simp only [Width.bytes, Width.bits] at H1", "kunfold"]
        elif op == "add" and a.endswith(",%rsp") and not isinstance(frame, tuple):
            assert a.startswith("$-"), a
            frame = -int(a.split(",")[0][1:], 16)
            L.append(kat(d))
        elif op == "mov" and a.startswith("%rbx,") and a.endswith("(%rsp)"):
            F = frame[1] if isinstance(frame, tuple) else frame
            raw = int(a.split(",")[1].split("(")[0], 16)
            off = raw - F - 8
            assert off == 16, a
            pf = f"(ar_s{raw} _)" if isinstance(frame, tuple) else "(by bv_omega)"
            L += [kat(d), f"apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ slot _ _ {pf} (by ecancel) (by exact hsl)",
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
        elif op == "sub" and a.endswith(",%rsp") or (op == "add" and a.endswith(",%rsp") and isinstance(frame, tuple)):
            L.append(kat(d))
        elif op == "pop" and isinstance(frame, tuple):
            L += [kat(d), f"rw [ar_m{frame[1] + 8}]",
                  "apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)", "kunfold"]
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



# ---------------------------------------------------------------- ListU64 accept: makeslice + element loop
# Pattern of Fk/LuLoop.lean (lu_iter, lu_exit, lu_loop) and Fk/LuAccept.lean (lu_accept_main). The loop
# lemmas are generated into the module (loop_iter, loop_exit, loop) from the loop's directives; the
# accept proof walks the entry, the makeslice call (contract MakesliceC), the slice-header stores,
# the write-barrier test, the loop and the epilogue. Branch-closing and contract blocks are hand text
# with the path's values (README section 2).

class LoopShape:
    """Loop head H, body label B, exit label X of the decoder's element loop (refuses other shapes)."""
    def __init__(self, D):
        lab_index = {t: d for d, k, t in D if k == "label"}
        jg = next(d for d, k, t in D if k == "instr" and t.startswith("jge "))
        assert D[jg - 1][2] == "cmp %rdx,%rax" and D[jg - 2][1] == "label", D[jg - 2:jg]
        self.H, self.X = jg - 2, lab_index[D[jg][2].split()[1]]
        jbs = [d for d in range(jg, self.X) if D[d][2].startswith("jb ") and D[d - 1][2] == "cmp %r8,%r10"]
        [jb] = jbs
        self.B = lab_index[D[jb][2].split()[1]]
        want = ["mov (%rsi),%r8", "mov %r11,(%r8,%r10,8)", "mov %r9,%rax", "nop"]
        assert [D[self.B + 1 + i][2] for i in range(4)] == want and self.B + 5 == self.H, D[self.B:self.H]
        assert [D[self.X + 1][2], D[self.X + 2][2]] == ["xor %eax,%eax", "xor %ebx,%ebx"], D[self.X:self.X + 3]


def lu_loop_lemmas(D, code, LS):
    """loop_iter (one element), loop_exit (i = n), loop (induction): generated from the loop directives."""
    H, B, X = LS.H, LS.B, LS.X
    kat = lambda d: f"  kat hk {code} {d}"
    lab_index = {t: d for d, k, t in D if k == "label"}
    pre = f"""set_option maxHeartbeats 4000000 in
theorem loop_iter [Host] (k : Nat) (hk : {code}.IsInfixAt Host.prog k)
    (hf : LabelsFresh {code} k)
    (bs : List UInt8) (n i : Nat) (hbs : bs.length = 8 * n) (hn : n ≤ 16) (hi : i < n)
    (d c p nb : BitVec 64) (hnb : nb.toNat = n) (R : DataMem → Prop) (s : MachineData)
    (hrax : s.regs.rax.toNat = i) (hrdx : s.regs.rdx.toNat = n) (hrcx : 8 * n ≤ s.regs.rcx.toNat)
    (hrdi : s.regs.rdi.toBitVec = d) (hrsi : s.regs.rsi.toBitVec = c)
    (sp bp r14v : UInt64) (hrsp : s.regs.rsp = sp) (hrbp : s.regs.rbp = bp) (hr14 : s.regs.r14 = r14v)
    (h_mem : s.dmem =⋆ Eq (bs.At d) ⋆ Eq ((Int.toBytes 8 p.toInt).At c) ⋆ Eq ((Int.toBytes 8 nb.toInt).At (c + 8))
      ⋆ Eq ((bs.take (8 * i) ++ List.replicate (8 * (n - i)) 0).At p) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + {H}) ∧ st.data.regs.rax.toNat = i + 1 ∧ st.data.regs.rdx.toNat = n
        ∧ 8 * n ≤ st.data.regs.rcx.toNat ∧ st.data.regs.rdi.toBitVec = d ∧ st.data.regs.rsi.toBitVec = c
        ∧ st.data.regs.rsp = sp ∧ st.data.regs.rbp = bp ∧ st.data.regs.r14 = r14v
        ∧ (Eq (bs.At d) ⋆ Eq ((Int.toBytes 8 p.toInt).At c) ⋆ Eq ((Int.toBytes 8 nb.toInt).At (c + 8))
          ⋆ Eq ((bs.take (8 * (i + 1)) ++ List.replicate (8 * (n - (i + 1))) 0).At p) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + {H})⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hrax hrdx hrcx hrdi hrsi hrsp hrbp hr14 ⊢
  subst hrdi hrsi hrsp hrbp hr14
  have := rax.toNat_lt_size; have := rdx.toNat_lt_size; have := rcx.toNat_lt_size
  simp only [UInt64.size] at *
  have hlen : bs.length < 2 ^ 64 := by omega
  rw [block_split bs rdi.toBitVec (8 * i) (by omega) hlen, out_next bs n i hbs hi,
    Mem.At_append_sep _ _ _ (by simp; omega), Mem.At_append_sep _ _ _ (by simp; omega)] at h_mem
  simp only [List.length_take, List.length_replicate, hbs, Nat.min_eq_left (show 8 * i ≤ 8 * n by omega)] at h_mem"""
    L = [pre]
    d, seen = H, set()
    while True:
        if d in seen:
            break
        seen.add(d)
        _, kind, t = D[d]
        if kind == "label":
            if d == H and len(seen) > 1:
                break
            L.append(kat(d)); d += 1; continue
        op = t.split()[0]
        a = t[len(op):].strip()
        if t in ("cmp %rdx,%rax", "lea 0x1(%rax),%r8", "mov %r8,%r9", "cmp %rcx,%r8", "mov %rax,%r10", "nop",
                 "cmp %rax,%r8", "cmp %r8,%r10", "mov %r9,%rax"):
            L.append(kat(d))
        elif op == "jge":
            L += [kat(d), "  split", "  case isTrue h =>",
                  "    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.signed] at h",
                  "    exact jge_false _ _ (by simp; omega) (by simp; omega) h", "  simp only [Effects.All]"]
        elif op == "shl" and a in ("$0x3,%r8", "$0x3,%rax"):
            L += [kat(d), "  kshl64 3"]
        elif op == "ja":
            L += [kat(d), "  split", "  case isTrue h =>",
                  "    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h",
                  "    (try simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Int.shiftLeft_eq] at h)",
                  "    obtain ⟨h1, h2⟩ := h; apply h2; apply BitVec.eq_of_toNat_eq",
                  "    simp [BitVec.toNat_sub, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_add]; omega",
                  "  simp only [Effects.All]"]
        elif op == "jb" and D[d - 1][2] == "cmp %rax,%r8":
            L += [kat(d), "  split", "  case isTrue h =>",
                  "    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h",
                  "    (try simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Int.shiftLeft_eq] at h); omega",
                  "  simp only [Effects.All]"]
        elif t == "mov 0x8(%rsi),%r8":
            L += [kat(d), "  apply load_step_at _ _ (rsi.toBitVec + 8) _ _ (Int.toBytes 8 nb.toInt) _ _ (by bv_omega) (by ecancel) (by exact Int.toBytes_length 8 _)",
                  "  kunfold"]
        elif t == "mov (%rdi,%r10,8),%r11":
            L += [kat(d), "  rw [show rdi.toBitVec + rax.toBitVec * 8#64 = rdi.toBitVec + BitVec.ofNat 64 (8 * i) by",
                  "    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_mul]; omega]",
                  "  apply load_step _ _ _ _ ((bs.drop (8 * i)).take 8) _ _ (by ecancel) (by simp; omega)", "  kunfold"]
        elif op == "jb" and D[d - 1][2] == "cmp %r8,%r10":
            L += [kat(d), "  split", "  case isFalse h =>",
                  "    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega",
                  "  simp only [Effects.All]", f"  klabel hk hf {code} {B}"]
            d = B; continue
        elif t == "mov (%rsi),%r8":
            L += [kat(d), "  apply load_step_at _ _ rsi.toBitVec _ _ (Int.toBytes 8 p.toInt) _ _ (by bv_omega) (by ecancel) (by exact Int.toBytes_length 8 _)",
                  "  kunfold"]
        elif t == "mov %r11,(%r8,%r10,8)":
            L += [kat(d), "  rw [show p + rax.toBitVec * 8#64 = p + BitVec.ofNat 64 (8 * i) by",
                  "    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_mul]; omega]",
                  "  apply store_step _ _ _ _ _ (List.replicate 8 0) _ _ (by ecancel) (by simp)",
                  "  intro m1 H1",
                  "  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl _ (show ((bs.drop (8 * i)).take 8).length = 8 by simp; omega)] at H1",
                  "  kunfold"]
        else:
            raise SystemExit(f"loop_iter: directive {d} `{t}`: no tactic template")
        d += 1
    L += ["  apply Eventually.done", "  refine ⟨rfl, ?_, hrdx, hrcx, rfl, rfl, rfl, rfl, rfl, ?_⟩",
          "  · show (rax.toBitVec + 1).toNat = i + 1; simp [BitVec.toNat_add]; omega",
          "  · dsimp only",
          "    rw [← out_step bs n i hbs hi, Mem.At_append_sep _ _ _ (by simp; omega), Mem.At_append_sep _ _ _ (by simp; omega),",
          "      block_split bs rdi.toBitVec (8 * i) (by omega) hlen]",
          "    simp only [List.length_take, List.length_replicate, List.length_drop, hbs,",
          "      Nat.min_eq_left (show 8 * i ≤ 8 * n by omega), Nat.min_eq_left (show 8 ≤ 8 * n - 8 * i by omega)]",
          "    (try simp only [BitVec.ofNat_eq_ofNat] at H1 ⊢)", "    ecancel", ""]
    assert D[H + 2][2].startswith("jge ")
    L.append(f"""set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem loop_exit [Host] (k : Nat) (hk : {code}.IsInfixAt Host.prog k)
    (hf : LabelsFresh {code} k)
    (bs : List UInt8) (n : Nat) (hbs : bs.length = 8 * n) (hn : n ≤ 16)
    (d c p nb : BitVec 64) (R : DataMem → Prop) (s : MachineData)
    (hrax : s.regs.rax.toNat = n) (hrdx : s.regs.rdx.toNat = n)
    (sp bp r14v : UInt64) (hrsp : s.regs.rsp = sp) (hrbp : s.regs.rbp = bp) (hr14 : s.regs.r14 = r14v)
    (h_mem : s.dmem =⋆ Eq (bs.At d) ⋆ Eq ((Int.toBytes 8 p.toInt).At c) ⋆ Eq ((Int.toBytes 8 nb.toInt).At (c + 8))
      ⋆ Eq ((bs.take (8 * n) ++ List.replicate (8 * (n - n)) 0).At p) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + {X}) ∧ st.data.regs.rsp = sp ∧ st.data.regs.rbp = bp ∧ st.data.regs.r14 = r14v
        ∧ (Eq (bs.At d) ⋆ Eq ((Int.toBytes 8 p.toInt).At c) ⋆ Eq ((Int.toBytes 8 nb.toInt).At (c + 8))
          ⋆ Eq (bs.At p) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + {H})⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hrax hrdx hrsp hrbp hr14 ⊢
  subst hrsp hrbp hr14
  have hrr : rax = rdx := UInt64.toNat_inj.mp (by omega)
  subst hrr
  kat hk {code} {H}
  kat hk {code} {H + 1}
  kat hk {code} {H + 2}
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
  simp only [Effects.All]
  klabel hk hf {code} {X}
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  rw [Nat.sub_self, Nat.mul_zero, List.replicate_zero, List.append_nil, List.take_of_length_le (by omega)] at h_mem
  exact h_mem

theorem loop [Host] (k : Nat) (hk : {code}.IsInfixAt Host.prog k)
    (hf : LabelsFresh {code} k)
    (bs : List UInt8) (n : Nat) (hbs : bs.length = 8 * n) (hn : n ≤ 16)
    (d c p nb : BitVec 64) (hnb : nb.toNat = n) (R : DataMem → Prop) (sp bp r14v : UInt64) :
    ∀ j i (s : MachineData), i + j = n →
    s.regs.rax.toNat = i → s.regs.rdx.toNat = n → 8 * n ≤ s.regs.rcx.toNat →
    s.regs.rdi.toBitVec = d → s.regs.rsi.toBitVec = c → s.regs.rsp = sp → s.regs.rbp = bp → s.regs.r14 = r14v →
    (s.dmem =⋆ Eq (bs.At d) ⋆ Eq ((Int.toBytes 8 p.toInt).At c) ⋆ Eq ((Int.toBytes 8 nb.toInt).At (c + 8))
      ⋆ Eq ((bs.take (8 * i) ++ List.replicate (8 * (n - i)) 0).At p) ⋆ R) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + {X}) ∧ st.data.regs.rsp = sp ∧ st.data.regs.rbp = bp ∧ st.data.regs.r14 = r14v
        ∧ (Eq (bs.At d) ⋆ Eq ((Int.toBytes 8 p.toInt).At c) ⋆ Eq ((Int.toBytes 8 nb.toInt).At (c + 8))
          ⋆ Eq (bs.At p) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + {H})⟩
  | 0, i, s, hij, hrax, hrdx, _, _, _, hrsp, hrbp, hr14, h_mem => by
    have hin : i = n := by omega
    rw [hin] at hrax h_mem
    exact loop_exit k hk hf bs n hbs hn d c p nb R s hrax hrdx sp bp r14v hrsp hrbp hr14 h_mem
  | j + 1, i, s, hij, hrax, hrdx, hrcx, hrdi, hrsi, hrsp, hrbp, hr14, h_mem => by
    refine eventually_trans _ _ _ _
      (loop_iter k hk hf bs n i hbs hn (by omega) d c p nb hnb R s hrax hrdx hrcx hrdi hrsi sp bp r14v hrsp hrbp hr14 h_mem) ?_
    rintro ⟨s', pc⟩ ⟨hpc, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    dsimp only at hpc; subst hpc
    exact loop k hk hf bs n hbs hn d c p nb hnb R sp bp r14v j (i + 1) s' (by omega) h1 h2 h3 h4 h5 h6 h7 h8 h9
""")
    return L


class AcceptShape:
    """Frame, spill slots, makeslice site and type word of the accept path (refuses other shapes)."""
    def __init__(self, D, Lf):
        ins = [(d, t) for d, k, t in D if k == "instr"]
        self.frame = next(-int(t.split()[1].split(",")[0][1:], 16) for d, t in ins if re.fullmatch(r"add \$-0x[0-9a-f]+,%rsp", t))
        self.ms = next(d for d, t in ins if t == "callq runtime.makeslice")
        m = re.fullmatch(r"lea type__\+(\d+)\(%rip\),%rax", D[self.ms - 2][2])
        assert m, D[self.ms - 2]
        self.ty = int(m[1])
        self.spills = {}                     # Go frame offset -> register stored before the call
        for d in range(self.ms - 8, self.ms):
            mm = re.fullmatch(r"mov %(r\w+),(0x[0-9a-f]+)\(%rsp\)", D[d][2])
            if mm:
                self.spills[int(mm[2], 16)] = (d, mm[1])
        assert sorted(self.spills) == [0x28, 0x30, 0x38, self.frame + 16], self.spills
        assert Lf.goff == 0, "receiver slice header must be the first field"

    def rel(self, off):
        """rsp-relative address (entry rsp) of frame offset `off` after push + add."""
        r = off - self.frame - 8
        return f"s.regs.rsp.toBitVec + {r}" if r > 0 else f"s.regs.rsp.toBitVec - {-r}"


def lu_accept_stmt(code, A):
    F = A.frame
    r = lambda off: A.rel(off)
    return f"""def accept_stmt [Host] : Prop :=
  ∀ (k : Nat) (hk : {code}.IsInfixAt Host.prog k)
    (hf : LabelsFresh {code} k)
    (bs : List UInt8) (n : Nat) (hbs : bs.length = 8 * n) (hn : n ≤ 16)
    (s : MachineData) (ra guard : UInt64)
    (fp s28 s30 s38 s90 s98 rslot cP cL cC : List UInt8)
    (hfp : fp.length = 8) (h28 : s28.length = 8) (h30 : s30.length = 8) (h38 : s38.length = 8)
    (h90 : s90.length = 8) (h98 : s98.length = 8) (hrs : rslot.length = 8)
    (hcP : cP.length = 8) (hcL : cL.length = 8) (hcC : cC.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch spm : List UInt8) (hsc : scratch.length = S) (hspm : spm.length = 24)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (spm.At (s.regs.rsp.toBitVec - {F + 8}))
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s28.At ({r(0x28)}))
      ⋆ Eq (s30.At ({r(0x30)})) ⋆ Eq (s38.At ({r(0x38)}))
      ⋆ Eq (s90.At ({r(F + 16)})) ⋆ Eq (s98.At ({r(F + 24)}))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - {F + 16})) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - {F + 16} - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq ([4, 0, 0, 0].At s.regs.rbx.toBitVec)
      ⋆ (Eq (bs.At (s.regs.rbx.toBitVec + 4))
        ⋆ Eq (cP.At s.regs.rax.toBitVec) ⋆ Eq (cL.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 16))
        ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R))
    (hguard : guard.toNat < s.regs.rsp.toNat - 8) (hsp : 8 ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rcx.toNat = 4 + 8 * n) (hcap : s.regs.rcx.toNat ≤ s.regs.rdi.toNat)
    (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hav : 8 * n ≤ avail)
    (hms : MakesliceC Heap (label "type__" + {A.ty}).toBitVec 8 S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0 ∧
        st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (p : BitVec 64) (fp' s28' s30' s38' s90' s98' rslot' scratch' spm' : List UInt8),
        fp'.length = 8 ∧ s28'.length = 8 ∧ s30'.length = 8 ∧ s38'.length = 8 ∧ s90'.length = 8 ∧
        s98'.length = 8 ∧ rslot'.length = 8 ∧ scratch'.length = S ∧ spm'.length = 24 ∧
        (Eq ((Int.toBytes 8 p.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 (n : Int)).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 (n : Int)).At (s.regs.rax.toBitVec + 16)) ⋆ Eq (bs.At p)
          ⋆ Heap (avail - 8 * n)
          ⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec) ⋆ Eq (spm'.At (s.regs.rsp.toBitVec - {F + 8}))
          ⋆ Eq (fp'.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s28'.At ({r(0x28)}))
          ⋆ Eq (s30'.At ({r(0x30)})) ⋆ Eq (s38'.At ({r(0x38)}))
          ⋆ Eq (s90'.At ({r(F + 16)})) ⋆ Eq (s98'.At ({r(F + 24)}))
          ⋆ Eq (rslot'.At (s.regs.rsp.toBitVec - {F + 16})) ⋆ Eq (scratch'.At (s.regs.rsp.toBitVec - {F + 16} - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ([4, 0, 0, 0].At s.regs.rbx.toBitVec) ⋆ Eq (bs.At (s.regs.rbx.toBitVec + 4))
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩
"""


def lu_accept_proof(D, code, A, LS):
    lab_index = {t: d for d, k, t in D if k == "label"}
    kat = lambda d: f"kat hk {code} {d}"
    F = A.frame
    loc = lambda off: (f"rsp.toBitVec + {off - F - 8}" if off - F - 8 > 0 else f"rsp.toBitVec - {F + 8 - off}")
    spill_val = {"rax": "rax.toBitVec", "rsi": "cV", "rdx": "dV", "rcx": "nV"}
    L = ["intro k hk hf bs n hbs hn s ra guard fp s28 s30 s38 s90 s98 rslot cP cL cC hfp h28 h30 h38 h90 h98 hrs hcP hcL hcC "
         "R S scratch spm hsc hspm Heap avail h_mem hguard hsp hlen hcap hcap63 hav hms",
         "obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s",
         "simp only at h_mem hguard hsp hlen hcap hcap63 ⊢",
         "have := rcx.toNat_lt_size; have := rdi.toNat_lt_size; have := rsp.toNat_lt_size",
         "have := guard.toNat_lt_size; simp only [UInt64.size] at *",
         "generalize hQ : (Eq (bs.At (rbx.toBitVec + 4))",
         "      ⋆ Eq (cP.At rax.toBitVec) ⋆ Eq (cL.At (rax.toBitVec + 8)) ⋆ Eq (cC.At (rax.toBitVec + 16))",
         "      ⋆ Eq ([0, 0, 0, 0].At (label \"runtime.writeBarrier\").toBitVec) ⋆ R) = Q at h_mem"]
    d, seen, after = 0, set(), False
    hn_ = {}
    while True:
        if d in seen:
            raise SystemExit(f"accept: directive {d} visited twice")
        seen.add(d)
        _, kind, t = D[d]
        if kind == "label":
            L.append(kat(d)); d += 1; continue
        op = t.split()[0]
        a = t[len(op):].strip()
        if (op == "lea" and a == "-0x8(%rsp),%r12") or op == "nop" or t in (
                "mov %rsp,%rbp", "cmp $0x4,%rcx", "cmp $0x4,%rdx", "lea -0x4(%rdi),%rdx", "mov %rdx,%rsi", "neg %rdx",
                "add $-0x4,%rcx", "add %rbx,%rdx", "cmp $0x10,%rcx", "mov %rcx,%rbx", f"add $-{hex(F)},%rsp") or \
                re.fullmatch(r"lea type__\+\d+\(%rip\),%rax", t):
            L.append(kat(d))
        elif t == "cmp 0x10(%r14),%r12":
            L += [kat(d), "apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)", "kunfold"]
        elif op == "jbe":
            L += [kat(d), "split", "case isTrue h =>", "  exfalso",
                  "  rw [cmp_be_false _ _ _ _ (by rw [toNat_add_neg8 _ (by simpa using hsp)]; simpa using hguard)] at h",
                  "  exact absurd h (by simp)", "simp only [Effects.All]"]
        elif op == "push":
            L += [kat(d), "apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by kaddr) (by ecancel) (by exact hfp)",
                  "intro m1 H1", "simp only [Width.bytes, Width.bits] at H1", "kunfold"]
        elif t == f"mov %rbx,{hex(F + 24)}(%rsp)":
            L += [kat(d), "apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s98 _ _ (by kaddr) (by ecancel) (by exact h98)",
                  "intro m2 H2", "simp only [Width.bytes, Width.bits] at H2", "kunfold"]
        elif op == "jb" and D[d - 1][2] == "cmp $0x4,%rcx":
            L += [kat(d), "split", "case isTrue h =>",
                  "  exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega", "simp only [Effects.All]"]
        elif t == "mov (%rbx),%edx":
            L += [kat(d), "apply load_step_at _ _ rbx.toBitVec _ _ [4, 0, 0, 0] _ _ (by bv_omega) (by ecancel) (by simp)",
                  "simp only [show Int.ofBytes [4, 0, 0, 0] = 4 by simp [Int.ofBytes]]", "kunfold"]
        elif op == "jne" and D[d - 1][2] == "cmp $0x4,%rdx":
            L += [kat(d), "split", "case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h", "simp only [Effects.All]"]
        elif t == "sar $0x3f,%rdx":
            L += [kat(d), "kshl64 63"]
        elif t in ("and $0x4,%edx", "test $0x7,%rcx"):
            L += [kat(d), "intro _"]
        elif op == "jne" and D[d - 1][2] == "test $0x7,%rcx":
            L += [kat(d), "split", "case isTrue h =>",
                  "  exfalso; rw [and7_zero rcx.toBitVec n hn (by simpa using hlen)] at h",
                  "  simp [CondCode.interp, StatusFlags.from_result] at h", "simp only [Effects.All]"]
        elif t == "shr $0x3,%rcx":
            L += [kat(d), "kshl64 3"]
        elif op == "jg":
            L += [kat(d), "split", "case isTrue h =>",
                  "  exfalso; rw [jg16_false _ _ (by rw [shr3_toNat rcx.toBitVec n hn (by simpa using hlen)]; omega)] at h",
                  "  simp at h", "simp only [Effects.All]",
                  "generalize hdV : rbx.toBitVec + BitVec.zeroExtend 64",
                  "    (BitVec.extractLsb' 0 32 (BitVec.sshiftRight (-(rdi.toBitVec + -4)) 63) &&& BitVec.truncate 32 4) = dV",
                  "generalize hnV : BitVec.ushiftRight (-4 + rcx.toBitVec) 3 = nV",
                  "generalize hcV : rdi.toBitVec + -4 = cV"]
        elif re.fullmatch(r"mov %r\w+,0x[0-9a-f]+\(%rsp\)", t) and d < A.ms:
            off = int(re.fullmatch(r"mov %r\w+,(0x[0-9a-f]+)\(%rsp\)", t)[1], 16)
            nm = "s90" if off == F + 16 else f"s{off:x}"
            hn_[off] = len(hn_) + 3
            i = hn_[off]
            L += [kat(d), f"apply store_step_at _ _ ({loc(off)}) _ _ _ {nm} _ _ (by kaddr) (by ecancel) (by exact h{nm[1:]})",
                  f"intro m{i} H{i}", f"simp only [Width.bytes, Width.bits] at H{i}", "kunfold"]
        elif d == A.ms:
            L += [kat(d), f"apply store_step_at _ _ (rsp.toBitVec - {F + 16}) _ _ _ rslot _ _ (call_slot _) (by ecancel) (by exact hrs)",
                  "intro m7 H7", "simp only [Width.bytes, Width.bits] at H7", "kunfold",
                  "rw [call_slot] at *",
                  "have hnN : nV.toNat = n := by rw [← hnV]; exact shr3_toNat rcx.toBitVec n hn (by simpa using hlen)",
                  f"have hspA : rsp.toBitVec - {F + 16} + 8 = rsp.toBitVec - {F + 8} := by bv_omega",
                  f"refine eventually_trans _ _ _ _ (hms _ (Host.addrOf (k + {d} + 1)) n avail scratch spm _ rfl (Nat.le_of_eq hnN) hnN hav",
                  "  (by unfold maxAlloc; omega) (by omega) hsc hspm (by dsimp only; rw [hspA]; ecancel)) ?_",
                  "rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hr141, -, stk1, spm1, hstk1, hspm1, Hm1⟩",
                  "dsimp only at hpc1 hrsp1 hr141 Hm1", "subst hpc1",
                  "obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩,",
                  "  zmms1, flags1, mem1⟩ := d1",
                  "simp only at hrsp1 hr141 Hm1", "subst hrsp1 hr141 hQ", "rw [hspA] at Hm1"]
            after = True
        elif after and re.fullmatch(r"mov (0x[0-9a-f]+)\(%rsp\),%r\w+", t):
            off = int(re.fullmatch(r"mov (0x[0-9a-f]+)\(%rsp\),%r\w+", t)[1], 16)
            v = spill_val[A.spills[off][1]]
            L += [kat(d), f"apply load_step_at _ _ ({loc(off)}) _ _ (Int.toBytes 8 {v}.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)", "kunfold"]
        elif t in ("mov %rdx,0x8(%rsi)", "mov %rdx,0x10(%rsi)"):
            o, nm, i = (8, "cL", 8) if "0x8(" in t else (16, "cC", 9)
            L += [kat(d), f"apply store_step_at _ _ (rax.toBitVec + {o}) _ _ _ {nm} _ _ (by kaddr) (by ecancel) (by exact h{nm})",
                  f"intro m{i} H{i}", f"simp only [Width.bytes, Width.bits] at H{i}", "kunfold"]
        elif t == "cmpl $0x0,runtime.writeBarrier(%rip)":
            L += [kat(d), "apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)",
                  "simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]", "kunfold"]
        elif op == "je" and D[d - 1][2].startswith("cmpl $0x0,runtime.writeBarrier"):
            tgt = lab_index[a]
            L += [kat(d), "split", "case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h",
                  "simp only [Effects.All]", f"klabel hk hf {code} {tgt}"]
            d = tgt; continue
        elif t == "mov %rax,(%rsi)":
            L += [kat(d), "apply store_step_at _ _ (rax.toBitVec) _ _ _ cP _ _ (by kaddr) (by ecancel) (by exact hcP)",
                  "intro m10 H10", "simp only [Width.bytes, Width.bits] at H10", "kunfold"]
        elif t == "xor %eax,%eax" and d < LS.H:
            L += [kat(d), "intro _"]
        elif op == "jmpq" and lab_index[a] == LS.H:
            L += [kat(d), f"klabel hk hf {code} {LS.H}",
                  "have hbsd : bs.At (rbx.toBitVec + 4) = bs.At dV := by",
                  "  rcases Nat.eq_zero_or_pos n with h0 | h0",
                  "  · subst h0; have hb0 : bs = [] := List.length_eq_zero_iff.mp (by simpa using hbs)",
                  "    subst hb0; simp [List.At]",
                  "  · rw [← hdV, dptr_buf rbx rdi n h0 (by simpa using hlen ▸ hcap) hcap63]",
                  "rw [hbsd] at H10",
                  "have hcN : 8 * n ≤ cV.toNat := by rw [← hcV]; exact cap_sub4 rdi n (by rw [← hlen]; exact hcap)",
                  "refine eventually_trans _ _ _ _ (loop k hk hf bs n hbs hn dV rax.toBitVec rax1.toBitVec nV hnN _ _ _ _ n 0 _",
                  "  (by omega) (by simp) hnN hcN rfl rfl rfl rfl rfl (by simp only [Nat.mul_zero, List.take_zero, List.nil_append, Nat.sub_zero]; ecancel)) ?_",
                  "rintro ⟨d2, pc2⟩ ⟨hpc2, hrsp2, -, hr142, Hm2⟩", "dsimp only at hpc2 hrsp2 Hm2", "subst hpc2",
                  "obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,",
                  "  zmms2, flags2, mem2⟩ := d2",
                  "simp only at hrsp2 hr142 Hm2", "subst hrsp2 hr142"]
            d = LS.X; continue
        elif t in ("xor %eax,%eax", "xor %ebx,%ebx"):
            L += [kat(d), "intro _"]
        elif t == f"sub $-{hex(F)},%rsp":
            L.append(kat(d))
        elif op == "pop":
            L += [kat(d), "apply load_step_at _ _ (rsp.toBitVec - 8) _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (pop_slot _) (by ecancel) (by exact Int.toBytes_length 8 _)",
                  "kunfold"]
        elif op == "retq":
            L += [kat(d), "rw [pop_slot, ret_slot]",
                  "apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)",
                  "kunfold", "apply Eventually.done",
                  "have hnI : nV.toInt = (n : Int) := by rw [BitVec.toInt_eq_toNat_of_lt (by omega), hnN]",
                  "rw [hnI] at Hm2",
                  "refine ⟨rfl, ?_, ?_, ?_, rfl, rax1.toBitVec, Int.toBytes 8 rbp.toBitVec.toInt, Int.toBytes 8 (n : Int),",
                  "  Int.toBytes 8 cV.toInt, Int.toBytes 8 dV.toInt, Int.toBytes 8 rax.toBitVec.toInt, Int.toBytes 8 rbx.toBitVec.toInt,",
                  f"  Int.toBytes 8 (Host.addrOf (k + {A.ms} + 1)).toBitVec.toInt, stk1, spm1,",
                  "  ?l1, ?l2, ?l3, ?l4, ?l5, ?l6, ?l7, ?l8, hspm1, ?mem⟩",
                  "· apply UInt64.toBitVec_inj.mp; simp", "· apply UInt64.toBitVec_inj.mp; simp", "· apply UInt64.toBitVec_inj.mp; simp",
                  "case mem =>", "  dsimp only", "  simp only [Std.ExtHashMap.sep_emp, Width.bits, Width.bytes] at Hm2",
                  "  rw [hbsd]", "  ecancel", "all_goals first | exact hstk1 | simp [Int.toBytes_length]"]
            return L
        else:
            raise SystemExit(f"accept: directive {d} `{t}`: no tactic template")
        d += 1



# ---------------------------------------------------------------- ListU64 marshal fast path + its loop
# Pattern of Fk/LuMarshal.lean (lum_iter, lum_exit, lum_loop, lu_marshal_main): the room check passes
# (no growslice), the offset 4 is written, the count check passes, the element loop copies 8n bytes,
# the epilogue returns (dst, len + 4 + 8n, cap, nil). Loop lemmas are generated into the module.

class MarshalShape:
    def __init__(self, D):
        lab_index = {t: d for d, k, t in D if k == "label"}
        ins = [(d, t) for d, k, t in D if k == "instr"]
        self.frame = next(int(t.split()[1].split(",")[0][1:], 16) for d, t in ins if re.fullmatch(r"sub \$0x[0-9a-f]+,%rsp", t))
        jge = next(d for d, t in ins if t.startswith("jge ") and D[d - 1][2] == "cmp %r8,%rax")
        assert D[jge - 2][1] == "label", D[jge - 2]
        self.H, self.X = jge - 2, lab_index[D[jge][2].split()[1]]
        jae = next(d for d in range(jge, self.X) if D[d][2].startswith("jae "))
        self.B = lab_index[D[jae][2].split()[1]]
        assert [D[self.B + 1][2], D[self.B + 2][2]] == ["mov %r10,-0x8(%rdx,%rbx,1)", "inc %rax"] and self.B + 3 == self.H
        jae0 = next(d for d, t in ins if t.startswith("jae ") and D[d - 1][2] == "cmp %rdx,%rdi")
        self.fast = lab_index[D[jae0][2].split()[1]]
        self.spills = {}
        for d in range(self.fast, self.H):
            mm = re.fullmatch(r"mov %(r\w+),(0x[0-9a-f]+)\(%rsp\)", D[d][2])
            if mm:
                self.spills[int(mm[2], 16)] = mm[1]
        assert sorted(self.spills.values()) == ["r8", "r9"], self.spills

    def rel(self, off):
        r = off - self.frame - 8
        return f"rsp.toBitVec + {r}" if r > 0 else f"rsp.toBitVec - {-r}"


def lu_mloop_lemmas(D, code, M):
    H, B, X = M.H, M.B, M.X
    kat = lambda d: f"  kat hk {code} {d}"
    L = [f"""set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem mloop_iter [Host] (k : Nat) (hk : {code}.IsInfixAt Host.prog k)
    (hf : LabelsFresh {code} k)
    (bs d : List UInt8) (n : Nat) (hn : n ≤ 16) (hbs : bs.length = 8 * n) (hd : d.length = 8 * n) (i : Nat) (hi : i < n)
    (b p : BitVec 64) (L cap : Nat) (hcap : L + 4 + 8 * n ≤ cap) (hcap63 : cap < 2 ^ 63)
    (R : DataMem → Prop) (s : MachineData)
    (hrax : s.regs.rax.toNat = i) (hrbx : s.regs.rbx.toBitVec = b) (hrdx : s.regs.rdx.toNat = L + 4 + 8 * i)
    (hrdi : s.regs.rdi.toNat = cap) (hr8 : s.regs.r8.toNat = n) (hr9 : s.regs.r9.toBitVec = p)
    (sp bp : UInt64) (hrsp : s.regs.rsp = sp) (hrbp : s.regs.rbp = bp)
    (h_mem : s.dmem =⋆ Eq (bs.At p) ⋆ Eq ((bs.take (8 * i) ++ d.drop (8 * i)).At (b + BitVec.ofNat 64 (L + 4))) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + {H}) ∧ st.data.regs.rax.toNat = i + 1 ∧ st.data.regs.rbx.toBitVec = b
        ∧ st.data.regs.rdx.toNat = L + 4 + 8 * (i + 1) ∧ st.data.regs.rdi.toNat = cap ∧ st.data.regs.r8.toNat = n
        ∧ st.data.regs.r9.toBitVec = p ∧ st.data.regs.rsp = sp ∧ st.data.regs.rbp = bp
        ∧ (Eq (bs.At p) ⋆ Eq ((bs.take (8 * (i + 1)) ++ d.drop (8 * (i + 1))).At (b + BitVec.ofNat 64 (L + 4))) ⋆ R)
          st.data.dmem)
      ⟨s, Host.addrOf (k + {H})⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hrax hrbx hrdx hrdi hr8 hr9 hrsp hrbp ⊢
  subst hrbx hr9 hrsp hrbp
  have := rax.toNat_lt_size; have := rdx.toNat_lt_size; have := rdi.toNat_lt_size; have := r8.toNat_lt_size
  simp only [UInt64.size] at *
  have hlen : bs.length < 2 ^ 64 := by omega
  rw [block_split bs r9.toBitVec (8 * i) (by omega) hlen, Gen1cX4.mix_split bs d i,
    Mem.At_append_sep _ _ _ (by simp; omega), Mem.At_append_sep _ _ _ (by simp; omega)] at h_mem
  simp only [List.length_take, List.length_drop, hbs, hd, Nat.min_eq_left (show 8 * i ≤ 8 * n by omega),
    Nat.min_eq_left (show 8 ≤ 8 * n - 8 * i by omega)] at h_mem"""]
    d, seen = H, set()
    while True:
        _, kind, t = D[d]
        if kind == "label":
            if d == H and d in seen:
                break
            seen.add(d); L.append(kat(d)); d += 1; continue
        if d in seen:
            raise SystemExit(f"mloop_iter: directive {d} visited twice")
        seen.add(d)
        if t in ("cmp %r8,%rax", "add $0x8,%rdx", "cmp %rdx,%rdi", "inc %rax"):
            L.append(kat(d))
        elif t.startswith("jge "):
            L += [kat(d), "  split", "  case isTrue h =>",
                  "    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.signed] at h",
                  "    exact jge_false rax.toBitVec r8.toBitVec (by simp; omega) (by simp; omega) (by simpa using h)",
                  "  simp only [Effects.All]"]
        elif t == "mov (%r9,%rax,8),%r10":
            L += [kat(d), "  rw [Gen1cX4.idx8' _ _ i (by simpa using hrax) (by omega)]",
                  "  apply load_step _ _ _ _ ((bs.drop (8 * i)).take 8) _ _ (by ecancel) (by simp; omega)", "  kunfold"]
        elif t.startswith("jae ") and D[d - 1][2] == "cmp %rdx,%rdi":
            L += [kat(d), "  split", "  case isFalse h =>",
                  "    exfalso; simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h",
                  "    have := Gen1cX4.lum_room rdx.toBitVec rdi.toBitVec L n i cap (by simpa using hrdx) hi (by simpa using hrdi) hcap hcap63",
                  "    simp at h; omega", "  simp only [Effects.All]", f"  klabel hk hf {code} {B}"]
            d = B; continue
        elif t == "mov %r10,-0x8(%rdx,%rbx,1)":
            L += [kat(d), "  rw [Gen1cX4.lum_addr _ _ L i (by simpa using hrdx) (by omega)]",
                  "  apply store_step _ _ _ _ _ ((d.drop (8 * i)).take 8) _ _ (by ecancel) (by simp; omega)",
                  "  intro m1 H1",
                  "  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl _ (show ((bs.drop (8 * i)).take 8).length = 8 by simp; omega)] at H1",
                  "  kunfold"]
        else:
            raise SystemExit(f"mloop_iter: directive {d} `{t}`: no tactic template")
        d += 1
    L += ["  apply Eventually.done", "  refine ⟨rfl, ?_, rfl, ?_, hrdi, hr8, rfl, rfl, rfl, ?_⟩",
          "  · exact Gen1cX4.inc_toNat16 _ i (by simpa using hrax) (by omega)",
          "  · exact Gen1cX4.lum_rdx _ L i (by simpa using hrdx) (by omega)",
          "  · dsimp only",
          "    rw [← Gen1cX4.mix_step bs d i, Mem.At_append_sep _ _ _ (by simp; omega), Mem.At_append_sep _ _ _ (by simp; omega),",
          "      block_split bs r9.toBitVec (8 * i) (by omega) hlen]",
          "    simp only [List.length_take, List.length_drop, hbs, hd, Nat.min_eq_left (show 8 * i ≤ 8 * n by omega),",
          "      Nat.min_eq_left (show 8 ≤ 8 * n - 8 * i by omega)]",
          "    (try simp only [BitVec.ofNat_eq_ofNat] at H1 ⊢)", "    ecancel", ""]
    L.append(f"""set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem mloop_exit [Host] (k : Nat) (hk : {code}.IsInfixAt Host.prog k)
    (hf : LabelsFresh {code} k) (P : MachineState → Prop) (s : MachineData)
    (hrr : s.regs.rax = s.regs.r8)
    (hP : ∀ f : StatusFlags, P ⟨⟨s.regs, s.zmms, f, s.dmem⟩, Host.addrOf (k + {X})⟩) :
    Eventually (step1 Host.exe) P ⟨s, Host.addrOf (k + {H})⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrr hP ⊢
  subst hrr
  kat hk {code} {H}
  kat hk {code} {H + 1}
  kat hk {code} {H + 2}
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
  simp only [Effects.All]
  klabel hk hf {code} {X}
  exact Eventually.done _ (hP _)

theorem mloop [Host] (k : Nat) (hk : {code}.IsInfixAt Host.prog k)
    (hf : LabelsFresh {code} k)
    (bs d : List UInt8) (n : Nat) (hn : n ≤ 16) (hbs : bs.length = 8 * n) (hd : d.length = 8 * n)
    (b p : BitVec 64) (L cap : Nat) (hcap : L + 4 + 8 * n ≤ cap) (hcap63 : cap < 2 ^ 63)
    (R : DataMem → Prop) (sp bp : UInt64) :
    ∀ j i (s : MachineData), i + j = n →
    s.regs.rax.toNat = i → s.regs.rbx.toBitVec = b → s.regs.rdx.toNat = L + 4 + 8 * i →
    s.regs.rdi.toNat = cap → s.regs.r8.toNat = n → s.regs.r9.toBitVec = p → s.regs.rsp = sp → s.regs.rbp = bp →
    (s.dmem =⋆ Eq (bs.At p) ⋆ Eq ((bs.take (8 * i) ++ d.drop (8 * i)).At (b + BitVec.ofNat 64 (L + 4))) ⋆ R) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + {X}) ∧ st.data.regs.rbx.toBitVec = b
        ∧ st.data.regs.rdx.toNat = L + 4 + 8 * n ∧ st.data.regs.rdi.toNat = cap
        ∧ st.data.regs.rsp = sp ∧ st.data.regs.rbp = bp
        ∧ (Eq (bs.At p) ⋆ Eq (bs.At (b + BitVec.ofNat 64 (L + 4))) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + {H})⟩
  | 0, i, s, hij, hrax, hrbx, hrdx, hrdi, hr8, _, hrsp, hrbp, h_mem => by
    have hin : i = n := by omega
    subst hin
    refine mloop_exit k hk hf _ s (UInt64.toNat_inj.mp (by omega)) fun _ => ⟨rfl, hrbx, hrdx, hrdi, hrsp, hrbp, ?_⟩
    rw [List.take_of_length_le (by omega), List.drop_of_length_le (by omega), List.append_nil] at h_mem
    exact h_mem
  | j + 1, i, s, hij, hrax, hrbx, hrdx, hrdi, hr8, hr9, hrsp, hrbp, h_mem => by
    refine eventually_trans _ _ _ _
      (mloop_iter k hk hf bs d n hn hbs hd i (by omega) b p L cap hcap hcap63 R s hrax hrbx hrdx hrdi hr8 hr9 sp bp hrsp hrbp h_mem) ?_
    rintro ⟨s', pc⟩ ⟨hpc, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    dsimp only at hpc; subst hpc
    exact mloop k hk hf bs d n hn hbs hd b p L cap hcap hcap63 R sp bp j (i + 1) s' (by omega) h1 h2 h3 h4 h5 h6 h7 h8 h9
""")
    return L


def lu_marshal_lemmas(M):
    F = M.frame
    out = {f"ar_m{F + 8}": f"(x : BitVec 64) : {F} + (x - 8#64 - {F}) = x - 8 := by bv_omega"}
    for off in [F + 24] + sorted(M.spills):
        r = off - F - 8
        rhs = f"x + {r}" if r > 0 else f"x - {-r}"
        out[f"ar_s{off}"] = f"(x : BitVec 64) : x - 8#64 - {F} + {off} = {rhs} := by bv_omega"
    return out


def lu_marshal_stmt(code, M):
    inv = {v: k for k, v in M.spills.items()}
    r = lambda off: M.rel(off).replace("rsp.toBitVec", "s.regs.rsp.toBitVec")
    return f"""def marshal_stmt [Host] : Prop :=
  ∀ (k : Nat) (hk : {code}.IsInfixAt Host.prog k)
    (hf : LabelsFresh {code} k)
    (bs pre o4 d : List UInt8) (n : Nat) (hn : n ≤ 16) (hbs : bs.length = 8 * n) (hd : d.length = 8 * n)
    (ho4 : o4.length = 4) (p : BitVec 64)
    (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp slot l1 l2 : List UInt8)
    (hfp : fp.length = 8) (hsl : slot.length = 8) (hl1 : l1.length = 8) (hl2 : l2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (slot.At ({r(M.frame + 24)}))
      ⋆ Eq (l1.At ({r(inv["r8"])})) ⋆ Eq (l2.At ({r(inv["r9"])}))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 p.toInt).At s.regs.rax.toBitVec) ⋆ Eq ((Int.toBytes 8 (n : Int)).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (bs.At p)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (o4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d.At (s.regs.rbx.toBitVec + BitVec.ofNat 64 (s.regs.rcx.toNat + 4))) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 8 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 4 + 8 * n ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 4 + 8 * n ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq ([4, 0, 0, 0].At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (bs.At (s.regs.rbx.toBitVec + BitVec.ofNat 64 (s.regs.rcx.toNat + 4)))
          ⋆ Eq (bs.At p) ⋆ R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩
"""


def lu_marshal_reject_stmt(code, M, err):
    inv = {v: k for k, v in M.spills.items()}
    r = lambda off: M.rel(off).replace("rsp.toBitVec", "s.regs.rsp.toBitVec")
    return f"""def marshal_reject_stmt [Host] : Prop :=
  ∀ (k : Nat) (hk : {code}.IsInfixAt Host.prog k)
    (hf : LabelsFresh {code} k)
    (pre o4 : List UInt8) (n : Nat) (hn : 16 < n) (hn63 : n < 2 ^ 59)
    (ho4 : o4.length = 4) (p e0 e1 : BitVec 64)
    (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp slot l1 l2 : List UInt8)
    (hfp : fp.length = 8) (hsl : slot.length = 8) (hl1 : l1.length = 8) (hl2 : l2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (slot.At ({r(M.frame + 24)}))
      ⋆ Eq (l1.At ({r(inv["r8"])})) ⋆ Eq (l2.At ({r(inv["r9"])}))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 p.toInt).At s.regs.rax.toBitVec) ⋆ Eq ((Int.toBytes 8 (n : Int)).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (o4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq ((Int.toBytes 8 e0.toInt).At (label "{err}").toBitVec)
      ⋆ Eq ((Int.toBytes 8 e1.toInt).At (label "{err}" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 8 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 4 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rcx = 0 ∧ st.data.regs.rdi.toBitVec = e0 ∧ st.data.regs.rsi.toBitVec = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (Eq (pre.At s.regs.rbx.toBitVec) ⋆ R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩
"""


def lu_marshal_err(D):
    lab_index = {t: d for d, k, t in D if k == "label"}
    jg = next(d for d, k, t in D if k == "instr" and t.startswith("jg "))
    return re.match(r"mov (ssz\.\w+)\(%rip\),%rdi", D[lab_index[D[jg][2].split()[1]] + 1][2])[1]


def lu_marshal_proof(D, code, M, mode="fast"):
    """mode fast: the room and count checks pass (lu_marshal_main); mode toobig: the count check
    fails and the error global is returned (lu_marshal_reject_main)."""
    lab_index = {t: d for d, k, t in D if k == "label"}
    kat = lambda d: f"kat hk {code} {d}"
    F = M.frame
    names = {"r8": ("l1", "hl1", 4), "r9": ("l2", "hl2", 5)}
    L = ["intro k hk hf bs pre o4 d n hn hbs hd ho4 p s ra guard hpre fp slot l1 l2 hfp hsl hl1 hl2 R h_mem hguard hsp hcap hcap63"
         if mode == "fast" else "intro k hk hf pre o4 n hn hn63 ho4 p e0 e1 s ra guard hpre fp slot l1 l2 hfp hsl hl1 hl2 R h_mem hguard hsp hcap hcap63",
         "obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s",
         "simp only at h_mem hguard hsp hcap hcap63 hpre ⊢",
         "have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; have := rdi.toNat_lt_size",
         "simp only [UInt64.size] at *",
         "have hnI : (n : Int) = (BitVec.ofNat 64 n).toInt := by",
         "  rw [BitVec.toInt_eq_toNat_of_lt (by simp; omega)]; simp; omega",
         "rw [hnI] at h_mem"]
    d, seen = 0, set()
    while True:
        if d in seen:
            raise SystemExit(f"marshal: directive {d} visited twice")
        seen.add(d)
        _, kind, t = D[d]
        if kind == "label":
            L.append(kat(d)); d += 1; continue
        op = t.split()[0]
        a = t[len(op):].strip()
        if t in ("mov %rsp,%rbp", f"sub {'$' + hex(F)},%rsp", "lea 0x4(%rcx),%rdx", "nop", "cmp %rdx,%rdi", "cmp $0x10,%r8",
                 "mov %rbx,%rax", "mov %rdx,%rbx", "mov %rdi,%rcx", f"add {'$' + hex(F)},%rsp"):
            L.append(kat(d))
        elif t == "cmp 0x10(%r14),%rsp":
            L += [kat(d), "apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)", "kunfold"]
        elif op == "jbe":
            L += [kat(d), "split", "· rename_i h; exfalso",
                  "  simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h",
                  "  rcases h with h | h", "  · apply h; omega",
                  "  · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega", "simp only [Effects.All]"]
        elif op == "push":
            L += [kat(d), "apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)",
                  "intro m1 H1", "simp only [Width.bytes, Width.bits] at H1", "kunfold"]
        elif t == f"mov %rbx,{hex(F + 24)}(%rsp)":
            L += [kat(d), f"apply store_step_at _ _ ({M.rel(F + 24)}) _ _ _ slot _ _ (ar_s{F + 24} _) (by ecancel) (by exact hsl)",
                  "intro m2 H2", "simp only [Width.bytes, Width.bits] at H2", "kunfold"]
        elif op == "jae" and lab_index[a] == M.fast:
            L += [kat(d), "split", "case isFalse h =>",
                  "  exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega",
                  "simp only [Effects.All]", f"klabel hk hf {code} {M.fast}"]
            d = M.fast; continue
        elif t == "movl $0x4,-0x4(%rdx,%rbx,1)":
            L += [kat(d), "rw [Gen1cX4.lum_off]", "apply store_step _ _ _ _ _ o4 _ _ (by ecancel) (by exact ho4)",
                  "intro m3 H3", "simp only [Width.bytes, Width.bits] at H3",
                  "rw [show Int.toBytes 4 (BitVec.truncate 32 (4 : BitVec 64)).toInt = [4, 0, 0, 0] by decide] at H3", "kunfold"]
        elif t == "mov 0x8(%rax),%r8":
            L += [kat(d), "apply load_step_at _ _ (rax.toBitVec + 8) _ _ (Int.toBytes 8 (BitVec.ofNat 64 n).toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)", "kunfold"]
        elif op == "jg" and mode == "fast":
            L += [kat(d), "split", "case isTrue h =>", "  exfalso; rw [jg16_false _ _ (by simp; omega)] at h; simp at h", "simp only [Effects.All]"]
        elif op == "jg":
            tgt = lab_index[a]
            L += [kat(d), "split", "case isFalse h =>",
                  "  exfalso; rw [Gen1cX4.jg16_true _ _ (by simp; omega) (by simp; omega)] at h; simp at h",
                  "simp only [Effects.All]", f"klabel hk hf {code} {tgt}"]
            d = tgt; continue
        elif mode == "toobig" and re.fullmatch(r"mov ssz\.\w+(\+8)?\(%rip\),%r(di|si)", t):
            e = "e1" if "+8" in t else "e0"
            L += [kat(d), f"apply load_step _ _ _ _ (Int.toBytes 8 {e}.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)", "kunfold"]
        elif mode == "toobig" and t in ("xor %ebx,%ebx",):
            L += [kat(d), "intro _"]
        elif mode == "toobig" and t == "mov %rbx,%rcx":
            L.append(kat(d))
        elif mode == "toobig" and op == "pop":
            L += [kat(d), f"rw [ar_m{F + 8}]",
                  "apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)", "kunfold"]
        elif mode == "toobig" and op == "retq":
            L += [kat(d), "rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]",
                  "apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)",
                  "kunfold", "apply Eventually.done", "simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]",
                  "refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, ?_, trivial, ?_⟩", "all_goals first", "  | rfl",
                  "  | (simp [Fk.ofInt_ofBytes_toBytes64]; done)", "  | (apply UInt64.toBitVec_inj.mp; simp; done)",
                  "  | exact sep_true (P := Eq (pre.At rbx.toBitVec) ⋆ R) (by ecancel)"]
            return L
        elif re.fullmatch(r"mov %r(8|9),0x[0-9a-f]+\(%rsp\)", t) and d < M.H:
            off = int(t.split(",")[1].split("(")[0], 16)
            nm, hn_, i = names[M.spills[off]]
            L += [kat(d), f"apply store_step_at _ _ ({M.rel(off)}) _ _ _ {nm} _ _ (ar_s{off} _) (by ecancel) (by exact {hn_})",
                  f"intro m{i} H{i}", f"simp only [Width.bytes, Width.bits] at H{i}", "kunfold"]
        elif t == "mov (%rax),%r9":
            L += [kat(d), "apply load_step _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)", "kunfold"]
        elif t in ("xor %eax,%eax", "xor %edi,%edi", "xor %esi,%esi"):
            L += [kat(d), "intro _"]
        elif op == "jmp" and lab_index[a] == M.H:
            L += [kat(d), f"klabel hk hf {code} {M.H}",
                  "refine eventually_trans _ _ _ _ (mloop k hk hf bs d n hn hbs hd rbx.toBitVec p rcx.toNat rdi.toNat hcap hcap63 _ _ _ n 0 _",
                  "  (by omega) (by simp) rfl (by show (rcx.toBitVec + 4).toNat = rcx.toNat + 4; simp [BitVec.toNat_add]; omega)",
                  "  (by simp) (by show (BitVec.ofNat 64 n).toNat = n; simp; omega) rfl rfl rfl",
                  "  (by simp only [Nat.mul_zero, List.take_zero, List.nil_append, List.drop_zero]; ecancel)) ?_",
                  "rintro ⟨e3, pc3⟩ ⟨hpc3, hrbx3, hrdx3, hrdi3, hrsp3, hrbp3, Hm3⟩",
                  "dsimp only at hpc3 hrbx3 hrdx3 hrdi3 hrsp3 hrbp3 Hm3", "subst hpc3",
                  "obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,",
                  "  zmms3, flags3, mem3⟩ := e3",
                  "simp only at hrbx3 hrdx3 hrdi3 hrsp3 hrbp3 Hm3", "subst hrsp3 hrbp3", kat(M.X)]
            d = M.X + 1; continue
        elif op == "pop" and d > M.X:
            L += [kat(d), f"rw [ar_m{F + 8}]",
                  "apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)", "kunfold"]
        elif op == "retq" and d > M.X:
            L += [kat(d), "rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]",
                  "apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)",
                  "kunfold", "apply Eventually.done", "simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]",
                  "refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, ?_, trivial, ?_⟩",
                  "· exact UInt64.toBitVec_inj.mp hrbx3", "· simpa using hrdx3",
                  "· exact UInt64.toNat_inj.mp (by simpa using hrdi3)",
                  "· apply UInt64.toBitVec_inj.mp; simp", "· apply UInt64.toBitVec_inj.mp; simp", "· apply UInt64.toBitVec_inj.mp; simp",
                  "· exact sep_true (by ecancel)"]
            return L
        else:
            raise SystemExit(f"marshal: directive {d} `{t}`: no tactic template")
        d += 1



# ---------------------------------------------------------------- ListU64 composition (decode then encode)
# Pattern of Fk/Compose.lean (lu_unmarshal_then_marshal) over the generated accept and marshal.

def lu_compose_stmt(cu, cm, A, M):
    F = A.frame
    r = lambda off: A.rel(off)
    inv = {v: k for k, v in M.spills.items()}
    mr = lambda off: M.rel(off).replace("rsp.toBitVec", "s.regs.rsp.toBitVec")
    return f"""def compose_stmt [Host] : Prop :=
  ∀ (kd : Nat) (hkd : {cu}.IsInfixAt Host.prog kd)
    (hfd : LabelsFresh {cu} kd)
    (km : Nat) (hkm : {cm}.IsInfixAt Host.prog km) (hfm : LabelsFresh {cm} km)
    (bs : List UInt8) (n : Nat) (hbs : bs.length = 8 * n) (hn : n ≤ 16)
    (s : MachineData) (ra ra2 guard : UInt64)
    (fp s28 s30 s38 s90 s98 rslot cP cL cC l1 l2 pre o4 d : List UInt8)
    (hfp : fp.length = 8) (h28 : s28.length = 8) (h30 : s30.length = 8) (h38 : s38.length = 8)
    (h90 : s90.length = 8) (h98 : s98.length = 8) (hrs : rslot.length = 8)
    (hcP : cP.length = 8) (hcL : cL.length = 8) (hcC : cC.length = 8)
    (hl1 : l1.length = 8) (hl2 : l2.length = 8) (ho4 : o4.length = 4) (hd : d.length = 8 * n)
    (dptr dlen cap : UInt64) (hpre : pre.length = dlen.toNat)
    (hcap2 : dlen.toNat + 4 + 8 * n ≤ cap.toNat) (hcap2' : cap.toNat < 2 ^ 63)
    (R0 : DataMem → Prop) (S : Nat) (scratch spm : List UInt8) (hsc : scratch.length = S) (hspm : spm.length = 24)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (spm.At (s.regs.rsp.toBitVec - {F + 8}))
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s28.At ({r(0x28)}))
      ⋆ Eq (s30.At ({r(0x30)})) ⋆ Eq (s38.At ({r(0x38)}))
      ⋆ Eq (s90.At ({r(F + 16)})) ⋆ Eq (s98.At ({r(F + 24)}))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - {F + 16})) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - {F + 16} - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq ([4, 0, 0, 0].At s.regs.rbx.toBitVec)
      ⋆ (Eq (bs.At (s.regs.rbx.toBitVec + 4))
        ⋆ Eq (cP.At s.regs.rax.toBitVec) ⋆ Eq (cL.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 16))
        ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
        ⋆ (Eq (l1.At ({mr(inv["r8"])})) ⋆ Eq (l2.At ({mr(inv["r9"])}))
          ⋆ Eq (pre.At dptr.toBitVec) ⋆ Eq (o4.At (dptr.toBitVec + dlen.toBitVec))
          ⋆ Eq (d.At (dptr.toBitVec + BitVec.ofNat 64 (dlen.toNat + 4))) ⋆ R0)))
    (hguard : guard.toNat < s.regs.rsp.toNat - 8) (hsp : 8 ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rcx.toNat = 4 + 8 * n) (hcap : s.regs.rcx.toNat ≤ s.regs.rdi.toNat)
    (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hav : 8 * n ≤ avail)
    (hms : MakesliceC Heap (label "type__" + {A.ty}).toBitVec 8 S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧
        ∀ (m2 : DataMem) (zm : RegZmms) (fl : StatusFlags),
          (∀ F : DataMem → Prop, (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec) ⋆ F) st.data.dmem →
            (Eq ((Int.toBytes 8 ra2.toBitVec.toInt).At s.regs.rsp.toBitVec) ⋆ F) m2) →
          Eventually (step1 Host.exe)
            (fun st' => st'.pc = Int64.ofBitVec ra2.toBitVec ∧ st'.data.regs.rax = dptr
              ∧ st'.data.regs.rbx.toNat = dlen.toNat + 4 + 8 * n ∧
              (Eq (pre.At dptr.toBitVec) ⋆ Eq ([4, 0, 0, 0].At (dptr.toBitVec + dlen.toBitVec))
                ⋆ Eq (bs.At (dptr.toBitVec + BitVec.ofNat 64 (dlen.toNat + 4))) ⋆ fun _ => True) st'.data.dmem)
            ⟨⟨{{ st.data.regs with rax := s.regs.rax, rbx := dptr, rcx := dlen, rdi := cap, rsp := s.regs.rsp }},
              zm, fl, m2⟩, Host.addrOf km⟩)
      ⟨s, Host.addrOf kd⟩
"""


LU_COMPOSE_PROOF = """intro kd hkd hfd km hkm hfm bs n hbs hn s ra ra2 guard fp s28 s30 s38 s90 s98 rslot cP cL cC l1 l2 pre o4 d hfp h28 h30 h38 h90 h98 hrs hcP hcL hcC hl1 hl2 ho4 hd dptr dlen cap hpre hcap2 hcap2' R0 S scratch spm hsc hspm Heap avail h_mem hguard hsp hlen hcap hcap63 hav hms
refine eventually_trans _ _ _ _ (accept kd hkd hfd bs n hbs hn s ra guard fp s28 s30 s38 s90 s98 rslot
  cP cL cC hfp h28 h30 h38 h90 h98 hrs hcP hcL hcC _ S scratch spm hsc hspm Heap avail h_mem hguard hsp hlen
  hcap hcap63 hav hms) ?_
rintro ⟨d', pc⟩ ⟨hpc, hrax, -, -, hr14, p, fp', s28', s30', s38', s90', s98', rs', sc', spm', hfp', h28', h30',
  h38', h90', h98', hrs', hsc', hspm', hm⟩
refine Eventually.done _ ⟨hpc, hrax, fun m2 zm fl hupd => ?_⟩
have hm2 := hupd _ (by ecancel)
refine eventually_trans _ _ _ _ (marshal km hkm hfm bs pre o4 d n hn hbs hd ho4 p _ ra2 guard
  (by dsimp only; exact hpre) fp' s98' l1 l2 hfp' h98' hl1 hl2 _
  (by dsimp only; rw [hr14]; ecancel)
  (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; exact hcap2')) ?_
intro st' hh
obtain ⟨e1, e2, e3, -, -, -, -, -, hm'⟩ := hh
dsimp only at e2 e3 hm'
exact Eventually.done _ ⟨e1, e2, e3, sep_true (by ecancel)⟩""".split("\n")


# ---------------------------------------------------------------- ListC: size (outer loop over item pointers)

class LcSizeShape:
    """SizeSSZ of a list of single-list containers (`size := 4; for o := range Items { size += 4 + o.SizeSSZ() }`,
    the element's SizeSSZ inlined). Every offset, stride and constant is read from the directive list and
    checked against the Desc (offset 4 + inner fixed part + w·len) and the Go layout. The statement uses
    Gen1cX4.lcAcc (8 + 8·l per item), so only inner width 8 and inner fixed part 4 are accepted."""

    def __init__(self, D, desc, layout_t):
        f = desc["fields"][0]
        el = desc["ssz"]["fields"][0]["elem"]
        assert el["k"] == "container" and len(el["fields"]) == 1, el
        inner = el["fields"][0]
        assert inner["k"] == "list" and inner["elem"]["k"] == "uint", inner
        self.w, self.ifixed = inner["elem"]["w"], 4
        lf = layout_t["fields"][0]
        assert lf["kind"] == "slice" and lf["esz"] == 8 and "elem" in lf, lf     # slice of item pointers
        ilay = LAYOUT["types"][lf["elem"]]["fields"][0]
        assert ilay["kind"] == "slice" and ilay["esz"] == self.w, ilay
        self.goff, self.igoff = lf["offset"], ilay["offset"]
        if (self.w, self.ifixed) != (8, 4):
            raise ValueError(f"lcAcc is 8 + 8·l per item; inner width {self.w}, inner fixed part {self.ifixed}")
        m = lambda off, r: f"{hex(off)}(%{r})" if off else f"(%{r})"
        txt = [x[2] for x in D]
        hb = [i for i, (_, k, x) in enumerate(D) if k == "label" and i > 0]
        assert len(hb) == 2, hb
        self.body, self.head = hb
        want = {1: f"mov {m(self.goff, 'rax')},%rcx", 2: f"mov {m(self.goff + 8, 'rax')},%rdx", 3: "xor %eax,%eax",
                4: "mov $0x4,%ebx", 5: f"jmp {txt[self.head]}",
                self.body + 1: "mov (%rcx,%rax,8),%rsi", self.body + 2: f"mov {m(self.igoff + 8, 'rsi')},%rsi",
                self.body + 3: f"lea (%rbx,%rsi,{self.w}),%rbx", self.body + 4: f"lea {hex(4 + self.ifixed)}(%rbx),%rbx",
                self.body + 5: "inc %rax",
                self.head + 1: "cmp %rdx,%rax", self.head + 2: f"jl {txt[self.body]}", self.head + 3: "mov %rbx,%rax",
                self.head + 4: "retq"}
        assert self.body == 6 and self.head == self.body + 6 and len(D) == self.head + 5, (self.body, self.head, len(D))
        for i, x in want.items():
            assert txt[i] == x, (i, txt[i], x)


def lc_size_stmt(code, S):
    item = f"(Eq ((Int.toBytes 8 (ps[i]'(by omega)).toInt).At (q + BitVec.ofNat 64 (8 * i)))\n        ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 ls[i]).toInt).At (ps[i]'(by omega) + {S.igoff + 8})) ⋆ fun _ => True)"
    return f"""def size_stmt [Host] : Prop :=
  ∀ (k : Nat) (hk : {code}.IsInfixAt Host.prog k)
    (hf : LabelsFresh {code} k) (q : BitVec 64) (ps : List (BitVec 64)) (ls : List Nat)
    (hlen : ps.length = ls.length) (hn : ls.length < 2 ^ 62) (hsum : lcAcc ls ls.length < 2 ^ 63)
    (s : MachineData) (ra : UInt64) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq ((Int.toBytes 8 q.toInt).At {plus("s.regs.rax.toBitVec", S.goff)})
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 ls.length).toInt).At (s.regs.rax.toBitVec + {S.goff + 8})) ⋆ R)
    (hall : ∀ i (hi : i < ls.length), {item} s.dmem),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax.toNat = lcAcc ls ls.length
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf k⟩
"""


def lc_size_lemmas(code, S):
    """size_iter (one item, from the loop head back to it) and size_loop (induction over the remaining items);
    directive numbers from the shape, tactic text of Fk/LcSize.lean `lcs_iter`/`lcs_loop`."""
    h, b = S.head, S.body
    ld = lambda v: [f"apply load_step _ _ _ _ (Int.toBytes 8 {v}) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)",
                    "simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]", "kunfold"]
    it = ["obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s",
          "simp only at h_mem hrax hrbx hrcx hrdx ⊢", "subst hrcx",
          "have := rax.toNat_lt_size; have := rbx.toNat_lt_size; have := rdx.toNat_lt_size",
          "simp only [UInt64.size] at *",
          f"kat hk {code} {h}", f"kat hk {code} {h + 1}", f"kat hk {code} {h + 2}",
          "rw [jl_val _ _ (by simp; omega) (by simp; omega)]",
          "simp only [show decide (rax.toBitVec.toNat < rdx.toBitVec.toNat) = true by simp; omega, ↓reduceIte, Effects.All]",
          f"klabel hk hf {code} {b}", f"kat hk {code} {b}", f"kat hk {code} {b + 1}",
          "rw [show rcx.toBitVec + rax.toBitVec * 8#64 = rcx.toBitVec + BitVec.ofNat 64 (8 * i) by",
          "  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_mul]; omega]",
          *ld("p.toInt"), f"kat hk {code} {b + 2}", *ld("(BitVec.ofNat 64 l).toInt"),
          f"kat hk {code} {b + 3}", f"kat hk {code} {b + 4}", f"kat hk {code} {b + 5}",
          "apply Eventually.done", "refine ⟨rfl, ?_, ?_, rfl, hrdx, rfl, rfl⟩",
          "· show (rax.toBitVec + 1).toNat = i + 1; simp [BitVec.toNat_add]; omega",
          f"· show (rbx.toBitVec + BitVec.ofNat 64 l * 8#64 + {4 + S.ifixed}).toNat = _",
          "  simp [BitVec.toNat_add, BitVec.toNat_mul]; omega"]
    iter_stmt = f"""theorem size_iter [Host] (k : Nat) (hk : {code}.IsInfixAt Host.prog k)
    (hf : LabelsFresh {code} k)
    (q p : BitVec 64) (n i acc l : Nat) (hi : i < n) (hn : n < 2 ^ 62) (hl : 8 + 8 * l + acc < 2 ^ 63)
    (s : MachineData) (R : DataMem → Prop)
    (hrax : s.regs.rax.toNat = i) (hrbx : s.regs.rbx.toNat = acc) (hrcx : s.regs.rcx.toBitVec = q)
    (hrdx : s.regs.rdx.toNat = n)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 p.toInt).At (q + BitVec.ofNat 64 (8 * i)))
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 l).toInt).At (p + {S.igoff + 8})) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + {h}) ∧ st.data.regs.rax.toNat = i + 1
        ∧ st.data.regs.rbx.toNat = acc + 8 + 8 * l ∧ st.data.regs.rcx.toBitVec = q
        ∧ st.data.regs.rdx.toNat = n ∧ st.data.regs.rsp = s.regs.rsp ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf (k + {h})⟩ := by"""
    item = f"(Eq ((Int.toBytes 8 (ps[i]'(by omega)).toInt).At (q + BitVec.ofNat 64 (8 * i)))\n        ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 ls[i]).toInt).At (ps[i]'(by omega) + {S.igoff + 8})) ⋆ fun _ => True)"
    loop_stmt = f"""theorem size_loop [Host] (k : Nat) (hk : {code}.IsInfixAt Host.prog k)
    (hf : LabelsFresh {code} k) (q : BitVec 64) (ps : List (BitVec 64)) (ls : List Nat)
    (hlen : ps.length = ls.length) (hn : ls.length < 2 ^ 62) (hsum : lcAcc ls ls.length < 2 ^ 63)
    (ra : UInt64) (R : DataMem → Prop) :
    ∀ (j : Nat) (s : MachineData), j ≤ ls.length → s.regs.rax.toNat = ls.length - j →
      s.regs.rbx.toNat = lcAcc ls (ls.length - j) → s.regs.rcx.toBitVec = q → s.regs.rdx.toNat = ls.length →
      (∀ i (hi : i < ls.length), {item} s.dmem) →
      (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec) ⋆ R) s.dmem →
      Eventually (step1 Host.exe)
        (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax.toNat = lcAcc ls ls.length
          ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.dmem = s.dmem)
        ⟨s, Host.addrOf (k + {h})⟩ := by"""
    lp = ["intro j", "induction j with", "| zero =>",
          "  intro s _ hrax hrbx hrcx hrdx _ hret",
          "  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s",
          "  simp only at hrax hrbx hrcx hrdx hret ⊢",
          "  have := rax.toNat_lt_size; have := rdx.toNat_lt_size; simp only [UInt64.size] at *",
          f"  kat hk {code} {h}", f"  kat hk {code} {h + 1}", f"  kat hk {code} {h + 2}",
          "  rw [jl_val _ _ (by simp; omega) (by simp; omega)]",
          "  simp only [show decide (rax.toBitVec.toNat < rdx.toBitVec.toNat) = false by simp; omega, Bool.false_eq_true,",
          "    ↓reduceIte, Effects.All]",
          f"  kat hk {code} {h + 3}", f"  kat hk {code} {h + 4}",
          "  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)",
          "  kunfold", "  apply Eventually.done", "  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]",
          "  refine ⟨trivial, ?_, ?_, ?_⟩", "  · simpa using hrbx", "  · apply UInt64.toBitVec_inj.mp; simp",
          "  · first | trivial | rfl",
          "| succ j ih =>",
          "  intro s hj hrax hrbx hrcx hrdx hall hret",
          "  have hi : ls.length - (j + 1) < ls.length := by omega",
          "  have hacc := lcAcc_succ ls (ls.length - (j + 1)) hi",
          "  have hle := lcAcc_le ls (ls.length - (j + 1) + 1)",
          "  refine eventually_trans _ _ _ _ (size_iter k hk hf q (ps[ls.length - (j + 1)]'(by omega)) ls.length",
          "    (ls.length - (j + 1)) (lcAcc ls (ls.length - (j + 1))) ls[ls.length - (j + 1)] hi hn (by omega) s",
          "    (fun _ => True) hrax hrbx hrcx hrdx (hall _ hi)) ?_",
          "  rintro ⟨d, pc⟩ ⟨hpc, hrax', hrbx', hrcx', hrdx', hrsp', hmem'⟩",
          "  dsimp only at hpc hrax' hrbx' hrcx' hrdx' hrsp' hmem'",
          "  subst hpc",
          "  have := ih d (by omega) (by rw [hrax']; omega) (by rw [hrbx', ← hacc]; congr 1; omega) hrcx' hrdx'",
          "    (by rw [hmem']; exact hall) (by rw [hmem', hrsp']; exact hret)",
          "  simpa [hrsp', hmem'] using this"]
    return ["set_option maxHeartbeats 4000000 in", "set_option maxRecDepth 20000 in", iter_stmt, *["  " + x for x in it], "",
            loop_stmt, *["  " + x for x in lp], ""]


def lc_size_proof(code, S):
    h = S.head
    ld = lambda v: [f"apply load_step _ _ _ _ (Int.toBytes 8 {v}) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)",
                    "simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]", "kunfold"]
    return ["intro k hk hf q ps ls hlen hn hsum s ra R h_mem hall",
            "obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s",
            "simp only at h_mem hall ⊢",
            f"kat hk {code} 0", f"kat hk {code} 1", *ld("q.toInt"), f"kat hk {code} 2", *ld("(BitVec.ofNat 64 ls.length).toInt"),
            f"kat hk {code} 3", "intro _", f"kat hk {code} 4", f"kat hk {code} 5", f"klabel hk hf {code} {h}",
            "refine eventually_trans _ _ _ _ (size_loop k hk hf q ps ls hlen hn hsum ra (fun _ => True) ls.length _",
            "  (Nat.le_refl _) (by simp) (by simp [lcAcc]; rfl)",
            "  rfl (by show (BitVec.ofNat 64 ls.length).toNat = _; simp; omega) hall (sep_true (by ecancel))) ?_",
            "rintro st ⟨h1, h2, h3, h4⟩", "apply Eventually.done", "exact ⟨h1, h2, h3, h4⟩"]


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
    LIST_OBL = ("size", "accept", "marshal", "marshal_reject", "compose", "reject_short", "reject_offset", "reject_misaligned", "reject_toobig")
    only = [x for x in a.only.split(",") if x in LIST_OBL] if a.only != ap_default() else list(LIST_OBL)
    if L.esz is None:   # list of containers (ListC): size (outer loop) and the templates that do not touch elements
        LC_OBL = ("size", "reject_short", "reject_offset")
        bad = [x for x in only if x not in LC_OBL]
        if a.only != ap_default() and bad:
            raise SystemExit(f"x4gen: refused {key[0]}.{t}: no template for {bad} on a list of containers")
        only = [x for x in only if x in LC_OBL]
    code = {m: f"{t}{m}" for m in ("SizeSSZ", "UnmarshalSSZ", "MarshalSSZTo")}
    head = ["import Fk.Step", "import Fk.Bytes", "import Fk.Labels", "import Fk.Flags", "import Gen1cX4.Support"]
    if any(x in only for x in ("reject_misaligned", "reject_toobig", "accept", "marshal", "marshal_reject")) \
            or (L.esz is None and "size" in only):
        head += ["import Fk.Contracts", "import Fk.Frame", "import Fk.Block"]
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
    if "size" in only and L.esz is None:
        try:
            SS = LcSizeShape(Dsz, desc, LAYOUT["types"][t])
        except (KeyError, AssertionError, IndexError, StopIteration, ValueError, TypeError) as e:
            raise SystemExit(f"x4gen: refused {key[0]}.{t}: list-of-containers size template does not fit "
                             f"({type(e).__name__}: {e})")
        body += ["-- outer item loop of SizeSSZ (generated from its directives)", *lc_size_lemmas(code["SizeSSZ"], SS),
                 lc_size_stmt(code["SizeSSZ"], SS), "theorem size [Host] : size_stmt := by",
                 *["  " + x for x in lc_size_proof(code["SizeSSZ"], SS)], ""]
    elif "size" in only:
        body += [lu_size_stmt(code["SizeSSZ"], L), "theorem size [Host] : size_stmt := by",
                 *["  " + x for x in lu_size_proof(Dsz, L, code["SizeSSZ"])], ""]
    if "accept" in only:
        if (L.esz, L.limit) != (8, 16):
            raise SystemExit(f"x4gen: refused {key[0]}.{t}: the accept/loop template is for 8-byte elements and limit 16")
        try:
            LS, AS = LoopShape(Dun), AcceptShape(Dun, L)
        except (KeyError, AssertionError, IndexError, StopIteration, ValueError, TypeError) as e:
            raise SystemExit(f"x4gen: refused {key[0]}.{t}: accept/loop template does not fit the code ({type(e).__name__}: {e})")
        body += ["-- element loop of the decoder (generated from its directives)", *lu_loop_lemmas(Dun, code["UnmarshalSSZ"], LS),
                 lu_accept_stmt(code["UnmarshalSSZ"], AS), "set_option maxHeartbeats 8000000 in", "set_option maxRecDepth 100000 in",
                 "theorem accept [Host] : accept_stmt := by", *["  " + x for x in lu_accept_proof(Dun, code["UnmarshalSSZ"], AS, LS)], ""]
    if "marshal" in only:
        if (L.esz, L.limit) != (8, 16):
            raise SystemExit(f"x4gen: refused {key[0]}.{t}: the marshal/loop template is for 8-byte elements and limit 16")
        Dma = directives(os.path.join(NORM, f"target.{t}.MarshalSSZTo.S"))
        try:
            MS = MarshalShape(Dma)
        except (KeyError, AssertionError, IndexError, StopIteration, ValueError, TypeError) as e:
            raise SystemExit(f"x4gen: refused {key[0]}.{t}: marshal/loop template does not fit the code ({type(e).__name__}: {e})")
        body += ["-- element loop of the encoder and the frame arithmetic (generated)", *lu_mloop_lemmas(Dma, code["MarshalSSZTo"], MS)]
        body += [f"theorem {n} {v}" for n, v in sorted(lu_marshal_lemmas(MS).items())] + [""]
        body += [lu_marshal_stmt(code["MarshalSSZTo"], MS), "set_option maxHeartbeats 8000000 in", "set_option maxRecDepth 100000 in",
                 "theorem marshal [Host] : marshal_stmt := by", *["  " + x for x in lu_marshal_proof(Dma, code["MarshalSSZTo"], MS)], ""]
    if "marshal_reject" in only:
        Dma = directives(os.path.join(NORM, f"target.{t}.MarshalSSZTo.S"))
        try:
            MS2, err = MarshalShape(Dma), lu_marshal_err(Dma)
        except (KeyError, AssertionError, IndexError, StopIteration, ValueError, TypeError) as e:
            raise SystemExit(f"x4gen: refused {key[0]}.{t}: marshal reject template does not fit the code ({type(e).__name__}: {e})")
        if "marshal" not in only:
            body += [f"theorem {n} {v}" for n, v in sorted(lu_marshal_lemmas(MS2).items())] + [""]
        body += [lu_marshal_reject_stmt(code["MarshalSSZTo"], MS2, err), "set_option maxHeartbeats 8000000 in", "set_option maxRecDepth 100000 in",
                 "theorem marshal_reject [Host] : marshal_reject_stmt := by",
                 *["  " + x for x in lu_marshal_proof(Dma, code["MarshalSSZTo"], MS2, "toobig")], ""]
    if "compose" in only:
        if not ("accept" in only and "marshal" in only):
            raise SystemExit("x4gen: compose uses the generated accept and marshal (add both to --only)")
        body += [lu_compose_stmt(code["UnmarshalSSZ"], code["MarshalSSZTo"], AS, MS), "set_option maxHeartbeats 16000000 in",
                 "set_option maxRecDepth 100000 in", "theorem compose [Host] : compose_stmt := by", *["  " + x for x in LU_COMPOSE_PROOF], ""]
    try:
        G = guard_size(Dun)
        subf = next((int(t.split()[1].split(",")[0][1:], 16) for _, k, t in Dun if k == "instr" and re.fullmatch(r"sub \$0x[0-9a-f]+,%rsp", t)), None)
    except (AssertionError, IndexError, ValueError) as e:
        raise SystemExit(f"x4gen: refused {key[0]}.{t}: prologue does not fit the reject template ({type(e).__name__}: {e})")
    if subf is not None and any(f"reject_{m}" in only for m in ("short", "offset")):
        body += ["-- prologue/epilogue arithmetic of the decoder's frame (generated with its guard distance and frame size)",
                 f"theorem ar_neg{G} (x : BitVec 64) (h : {G} ≤ x.toNat) : (x + -{G}).toNat = x.toNat - {G} := by",
                 "  rw [← BitVec.sub_eq_add_neg, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simpa using h)]; rfl",
                 f"theorem ar_s{subf + 24} (x : BitVec 64) : x - 8#64 - {subf} + {subf + 24} = x + 16 := by bv_omega",
                 f"theorem ar_m{subf + 8} (x : BitVec 64) : {subf} + (x - 8#64 - {subf}) = x - 8 := by bv_omega", ""]
    for mode in ("short", "offset"):
        if f"reject_{mode}" in only:
            body += [lu_rej_stmt(f"reject_{mode}", code["UnmarshalSSZ"], lu_err(Dun, mode), mode, G),
                     "set_option maxHeartbeats 4000000 in", "set_option maxRecDepth 100000 in",
                     f"theorem reject_{mode} [Host] : reject_{mode}_stmt := by",
                     *["  " + x for x in lu_rej_proof(Dun, code["UnmarshalSSZ"], mode, G)], ""]
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
