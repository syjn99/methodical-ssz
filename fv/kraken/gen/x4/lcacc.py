"""ListC accept proofs (X4): the decoder's outer item loop and the two accept paths, from UnmarshalSSZ.S.

Pattern of Fk/LcLoop.lean (lcl_iter, lcl_exit, lcl_loop), Fk/LcAccept.lean (lc_accept_main) and
Fk/LcAcceptEmpty.lean (lc_accept_empty_main). What the code decides here:
- the label positions (item loop head and exit, the n = 1 / last-item branch, the join after the
  offset checks, the loop body, the common return block, the accept and empty-list branches);
- the call sites (makeslice, newobject, the element decoder) and the two type words;
- per directive along each path: which conditional jumps are taken (a jump to an error block, i.e. a
  block that calls fmt.errorf/panicBounds or loads an ssz.Err* global, is not taken; a jump whose
  fall-through goes to an error block is taken; `je`/`jne` after the write-barrier test follow
  writeBarrier = 0; the loop head's `jae` and the last-item `je` are case splits), the frame slot of
  every spill/reload (address rewrite and the value it holds, tracked by a small register/slot table),
  and the directive numbers.
Fixed hand text (lcacc_tpl.py and the blocks below): statements, call/contract blocks, branch-closing
and finishing blocks. The frame layout is not generated: lcacc refuses code whose frame size, guard
distance or spill-slot set differs from the one the statements assume.
"""
import re

import lcacc_tpl as T

FRAME, GUARD = 0xd8, 0x60
SLOTS = {0xe8, 0x30, 0x50, 0x60, 0x38, 0x100, 0x48, 0x40, 0x28, 0x58}   # spill slots of the loop and the accept path
ERR = re.compile(r"callq (fmt\.errorf|runtime\.panicBounds)|ssz\.Err")


class LcAccShape:
    """Labels, call sites and type words of the ListC accept paths (refuses another frame layout)."""
    def __init__(self, D, inner):
        self.D = D
        self.txt = txt = [x[2] for x in D]
        self.lab = lab = {t: d for d, k, t in D if k == "label"}
        F = next(int(t.split()[1].split(",")[0][1:], 16) for t in txt if re.fullmatch(r"sub \$0x[0-9a-f]+,%rsp", t))
        if F != FRAME:
            raise ValueError(f"frame {hex(F)}: the statements assume {hex(FRAME)}")
        self.F, self.C, self.X = F, F + 16, F + 8
        used = {int(m[1], 16) for t in txt for m in [re.search(r"(0x[0-9a-f]+)\(%rsp\)", t)]
                if m and not t.startswith(("lea", "movups", "movq"))}
        used -= {0x8, 0x10, 0x18, 0x20, 0xf0}       # morestack spills and the receiver-pointer slot of the prologue
        used -= {0x68, 0x70, 0x78, 0x80, 0x88, 0x90, 0x98, 0xa0, 0xa8, 0xb0, 0xb8, 0xc0, 0xc8, 0xd0}  # fmt.errorf argument arrays
        if used != SLOTS:
            raise ValueError(f"spill slots {sorted(map(hex, used))}: the statements assume {sorted(map(hex, SLOTS))}")
        jae = next(d for d in range(len(txt)) if txt[d].startswith("jae ") and txt[d - 1] == "cmp %rbx,%rcx")
        self.acc0 = lab[txt[jae].split()[1]]
        self.ms = next(d for d in range(self.acc0, len(txt)) if txt[d] == "callq runtime.makeslice")
        self.msty = int(next(m[1] for t in txt[self.acc0:self.ms] for m in [re.fullmatch(r"lea type__\+(\d+)\(%rip\),%rax", t)] if m))
        j = next(d for d in range(self.ms, len(txt)) if txt[d].startswith("jmpq "))
        self.head = lab[txt[j].split()[1]]
        assert txt[self.head + 1] == "cmp %rdx,%rax" and txt[self.head + 2].startswith("jae "), txt[self.head:self.head + 3]
        self.exit = lab[txt[self.head + 2].split()[1]]
        self.no = next(d for d in range(self.head, len(txt)) if txt[d] == "callq runtime.newobject")
        self.noty = int(re.fullmatch(r"lea type__\+(\d+)\(%rip\),%rax", txt[self.no - 2])[1])
        self.lu = next(d for d in range(self.head, len(txt)) if txt[d].startswith("callq "+ "target."))
        if txt[self.lu] != f"callq target.{inner}.UnmarshalSSZ":
            raise ValueError(f"element decoder call `{txt[self.lu]}`, Desc/layout element {inner}")
        assert txt[self.exit + 3].startswith("jmpq "), txt[self.exit:self.exit + 4]
        self.ret = lab[txt[self.exit + 3].split()[1]]
        assert txt[self.ret + 1:self.ret + 5] == ["mov %rcx,%rbx", f"add ${hex(F)},%rsp", "pop %rbp", "retq"]
        self.code = None

    def is_err(self, d, seen=None):
        """Every path from directive d reaches an error marker (fmt.errorf, panicBounds, ssz.Err*) before a
        retq; both successors of a conditional jump are followed; a revisited directive is neutral."""
        seen = set() if seen is None else seen
        while True:
            if d in seen:
                return True
            seen.add(d)
            t = self.txt[d]
            if ERR.search(t):
                return True
            if t == "retq":
                return False
            if t.startswith("jmp"):
                d = self.lab[t.split()[1]]; continue
            if t.startswith("j"):
                return self.is_err(self.lab[t.split()[1]], seen) and self.is_err(d + 1, seen)
            d += 1


def lemmas(S):
    C, X = S.C, S.X
    u = "simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega"
    return {"lcl_ret": f"(x : BitVec 64) : x - 8#64 - {S.F} - 8#64 = x - {C} := by bv_omega",
            "lcl_g": f"(x o : BitVec 64) : ({{ toBitVec := x - {C} }} + 8 : UInt64).toBitVec + o = x - {X} + o := by\n  {u}",
            "lcl_blk": f"(x : BitVec 64) (S : Nat) : x - {C} - BitVec.ofNat 64 (144 + S) = x - {C} - 144 - BitVec.ofNat 64 S := by\n"
                       "  rw [show BitVec.ofNat 64 (144 + S) = 144 + BitVec.ofNat 64 S by\n"
                       "    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]]\n  bv_omega",
            "lcl_call": f"(x : BitVec 64) : ({{ toBitVec := x - {C} }} + 8 : UInt64).toBitVec - 8#64 = x - {C} := by\n  {u}"}


def sub(s, S):
    for k, v in (("@CODE@", S.code), ("@HEAD@", S.head), ("@EXIT@", S.exit), ("@NOTY@", S.noty),
                 ("@MSTY@", S.msty), ("@MSCALL@", S.ms)):
        s = s.replace(k, str(v))
    return s


def body(s, S):
    """Template proof lines (2-space indented in the hand file) without the indentation."""
    return [x[2:] if x.startswith("  ") else x for x in sub(s, S).split("\n")]


LD = ["simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]", "kunfold"]
SPLIT_T = ["split", "case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h", "simp only [Effects.All]"]
SPLIT_F = ["split", "case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h", "simp only [Effects.All]"]
WB = ["apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)",
      "simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]", "kunfold"]


class Walk:
    """Frame slots (address relative to the entry rsp `base`) and register values along one path."""
    def __init__(self, S, base, slots, regs, ph, m="m", H="H"):
        self.S, self.base, self.slots, self.regs, self.ph, self.m, self.H, self.n = S, base, slots, regs, ph, m, H, 0
        self.shl, self.zx, self.cmp = set(), set(), None

    def adr(self, o):
        d = self.S.X - o
        return f"{self.base} - {d}" if d > 0 else f"{self.base} + {-d}", d

    def rw(self, o):
        a, _ = self.adr(o)
        X, b = self.S.X, self.base
        return {"entry": f"rw [show {b} - 8#64 - {self.S.F} + {o} = {a} by bv_omega]",
                "pre": f"rw [show rsp.toBitVec + {o} = {a} by rw [hrsp]; bv_omega]",
                "call": f"rw [lcl_g, show {b} - {X} + {o} = {a} by bv_omega]",
                "post": f"rw [show {b} - {X} + {o} = {a} by bv_omega]"}[self.ph]

    def load(self, o, r):
        _, d = self.adr(o)
        v = self.slots[d]
        self.regs[r] = v
        self.shl.discard(r)
        return [self.rw(o), f"apply load_step _ _ _ _ (Int.toBytes 8 {v}.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)", *LD]

    def store(self, o, r):
        _, d = self.adr(o)
        old = self.slots[d]
        raw = isinstance(old, tuple)
        self.slots[d] = self.regs.get(r, f"?{r}")
        self.n += 1
        oc, ol = (old[0], old[1]) if raw else (f"(Int.toBytes 8 {old}.toInt)", "Int.toBytes_length 8 _")
        H = self.H
        return [self.rw(o), f"apply store_step _ _ _ _ _ {oc} _ _ (by ecancel) (by exact {ol})",
                f"intro {self.m}{self.n} {H}{self.n}", f"simp only [Width.bytes, Width.bits] at {H}{self.n}", "kunfold"]


def kat(S, d):
    return f"kat hk {S.code} {d}"


def klabel(S, d):
    return f"klabel hk hf {S.code} {d}"


MEMOP = re.compile(r"^(?P<op>mov)\s+(?:(?P<src>0x[0-9a-f]+)\(%rsp\),%(?P<dst>\w+)|%(?P<r>\w+),(?P<o>0x[0-9a-f]+)\(%rsp\))$")


def frame_op(W, t):
    m = MEMOP.match(t)
    if not m:
        return None
    if m["src"]:
        return W.load(int(m["src"], 16), m["dst"])
    return W.store(int(m["o"], 16), m["r"])


# ---------------------------------------------------------------- the item loop (lcl_iter)

def iter_walk(S, W, d, L, last):
    """Walk from directive d to the loop head; `last` = the n = i + 1 branch (T substituted by e)."""
    txt, lab = S.txt, S.lab
    while True:
        t = txt[d]
        if S.D[d][1] == "label":
            if d == S.head:
                return iter_finish(S, W, L)
            L.append(kat(S, d)); d += 1; continue
        op = t.split()[0]
        a = t[len(op):].strip()
        jt = lab.get(a)
        L.append(kat(S, d))
        fo = frame_op(W, t)
        if fo is not None:
            if last:
                fo = [x.replace("(BitVec.ofNat 64 T)", "(BitVec.ofNat 64 e)") for x in fo]
                W.regs = {r: v.replace("(BitVec.ofNat 64 T)", "(BitVec.ofNat 64 e)") for r, v in W.regs.items()}
            L += fo
        elif op == "callq" and d == S.no:
            raise AssertionError("newobject is before the branch")
        elif op == "lea" and re.fullmatch(r"0x1\(%(\w+)\),%(\w+)", a):
            mm = re.fullmatch(r"0x1\(%(\w+)\),%(\w+)", a)
            W.regs[mm[2]] = f"({W.regs[mm[1]]} + 1)"
        elif op == "mov" and re.fullmatch(r"%(\w+),%(\w+)", a):
            mm = re.fullmatch(r"%(\w+),%(\w+)", a)
            if mm[1] in W.regs:
                W.regs[mm[2]] = W.regs[mm[1]]
            (W.shl.add if mm[1] in W.shl else W.shl.discard)(mm[2])
        elif op == "shl":
            r = a.split("%")[1]
            L.append(f"kshl64 {int(a.split(',')[0][1:], 16)}"); W.shl.add(r)
        elif op == "sar":
            L.append(f"kshl64 {int(a.split(',')[0][1:], 16)}")
        elif op == "and" or (op == "test" and a == "%rax,%rax"):
            L.append("intro _")
        elif op == "cmp":
            W.cmp = re.findall(r"%(\w+)", a)
        elif op == "mov" and a == "0x4(%rdx,%rcx,4),%esi":
            b, i = W.regs["rdx"], W.regs["rcx"]
            L += [f"rw [tl_split3 {b} tl (4 * (i + 1)) 4 (by omega) (by omega)] at Hm1",
                  f"rw [show {b} + {i} * 4#64 + 4 = {b} + BitVec.ofNat 64 (4 * (i + 1)) by",
                  "  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_mul]; omega]",
                  "apply load_step _ _ _ _ ((tl.drop (4 * (i + 1))).take 4) _ _ (by ecancel) (by simp; omega)",
                  "rw [hnext (by omega), ofBytes_uintBytes4 e (by omega)]",
                  f"rw [← tl_split3 {b} tl (4 * (i + 1)) 4 (by omega) (by omega)] at Hm1", "kunfold"]
            W.regs["rsi"] = "(BitVec.ofNat 64 e)"; W.zx.add("rsi"); W.shl.discard("rsi")
        elif op == "je" and W.cmp == ["rdx", "rbx"]:
            L += [f"have hi1 : {W.regs['rdx']}.toNat = i + 1 := by simp [BitVec.toNat_add]; omega", "by_cases hl : i + 1 = n"]
            import copy
            W2 = copy.deepcopy(W)
            A = ["have heq := hlast hl", "subst heq", "split", "case isFalse h =>",
                 "  exfalso; simp [CondCode.interp, StatusFlags.from_result] at h",
                 "  apply h; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub, BitVec.toNat_add]; omega",
                 "simp only [Effects.All]", klabel(S, jt)]
            W.slots = {k: v.replace("(BitVec.ofNat 64 T)", "(BitVec.ofNat 64 e)") if isinstance(v, str) else v for k, v in W.slots.items()}
            iter_walk(S, W, jt, A, True)
            B = ["split", "case isTrue h =>", "  exfalso; simp [CondCode.interp, StatusFlags.from_result] at h",
                 "  apply hl; have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega", "simp only [Effects.All]"]
            iter_walk(S, W2, d + 1, B, False)
            L += ["· " + A[0], *["  " + x for x in A[1:]], "· " + B[0], *["  " + x for x in B[1:]]]
            return L
        elif op in ("ja", "jb", "jae", "jne", "je") and S.is_err(jt):
            if op == "jne":
                L += SPLIT_T
            else:
                lem = {"ja": "ja_false", "jb": "jb_false", "jae": "jnc_false"}[op]
                if any(r in W.shl for r in W.cmp or []):
                    L += [f"rw [{lem} _ _ _ _ (by", "  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_add]; omega)]"]
                else:
                    L.append(f"rw [{lem} _ _ _ _ (by simp; omega)]")
                L.append("simp only [Bool.false_eq_true, ↓reduceIte, Effects.All]")
        elif op == "jne" and txt[d - 1].startswith("cmpl $0x0,runtime.writeBarrier"):
            L += SPLIT_T
        elif op == "jae" and S.is_err(lab[txt[d + 1].split()[1]]):
            if any(r in W.zx for r in W.cmp):
                L.append("rw [zx_o e (by omega)]")
            L += ["split", "case isFalse h =>",
                  "  exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega",
                  "simp only [Effects.All]", klabel(S, jt)]
            d = jt; continue
        elif op in ("jmpq", "jmp"):
            L.append(klabel(S, jt)); d = jt; continue
        elif op == "cmpl" and a == "$0x0,runtime.writeBarrier(%rip)":
            L += WB
        elif op == "mov" and a == "0x8(%rcx),%rdx":
            L += [f"apply load_step_at _ _ ({W.regs['rcx']} + 8) _ _ (Int.toBytes 8 (BitVec.ofNat 64 n).toInt) _ _ (by bv_omega) (by ecancel) (by exact Int.toBytes_length 8 _)", *LD]
        elif op == "mov" and a == "(%rcx),%rdx":
            L += ["apply load_step _ _ _ _ (Int.toBytes 8 A.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)", *LD]
        elif op == "callq" and d == S.lu:
            L += iter_lucall(S, W, d); W.ph = "post"
        elif op == "mov" and a == "%r8,(%rdx,%rsi,8)":
            W.n += 1
            n = W.n
            L += ["have hrep : List.replicate (8 * (n - i)) (0 : UInt8) = List.replicate 8 0 ++ List.replicate (8 * (n - (i + 1))) 0 := by",
                  "  rw [List.replicate_append_replicate, show 8 + 8 * (n - (i + 1)) = 8 * (n - i) by omega]",
                  "rw [hrep, at_app ptrs _ (b := A + BitVec.ofNat 64 (8 * i)) (by rw [hptrs]) (by simp [hptrs]; omega),",
                  "  at_app (List.replicate 8 0) _ (b := A + BitVec.ofNat 64 (8 * i) + 8) (by simp) (by simp; omega)] at Hm2",
                  f"rw [show A + {W.regs['rsi']} * 8#64 = A + BitVec.ofNat 64 (8 * i) by",
                  "  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_mul]; omega]",
                  "apply store_step _ _ _ _ _ (List.replicate 8 0) _ _ (by ecancel) (by simp)",
                  f"intro m{n} H{n}", f"simp only [Width.bytes, Width.bits] at H{n}", "kunfold"]
        elif op in ("nop", "lea", "mov", "neg", "sub", "test") and not op.startswith("j"):
            if op == "mov" and re.fullmatch(r"0x[0-9a-f]+\(%rcx\),%\w+|%\w+,\(%\w+\)", a):
                raise SystemExit(f"ListC loop directive {d} `{t}`: no tactic template")
        else:
            raise SystemExit(f"ListC loop directive {d} `{t}`: no tactic template")
        if op == "mov" and a == "0xe8(%rsp),%rcx":
            W.regs["rcx"] = "recv"
        if op == "mov" and a == "0x40(%rsp),%rsi":
            W.regs["rsi"] = "rax.toBitVec"
        d += 1


def iter_newobject(S, W, d):
    C, X, F, n = S.C, S.X, S.F, W.n + 1
    W.n = n
    W.slots[C] = f"(Host.addrOf (k + {d} + 1)).toBitVec"
    W.slots[X] = ("sn1", "hsn1")
    W.regs["rax"] = "rax1.toBitVec"
    return [f"apply store_step_at _ _ (x - {C}) _ _ _ rslot _ _ (by rw [hrsp, lcl_ret]) (by ecancel) (by exact hrs)",
            f"intro m{n} H{n}", f"simp only [Width.bytes, Width.bits] at H{n}", "kunfold",
            f"rw [show rsp.toBitVec - 8#64 = x - {C} by rw [hrsp, lcl_ret]] at *",
            f"have hspA : x - {C} + 8 = x - {X} := by bv_omega",
            f"refine eventually_trans _ _ _ _ (hno _ (Host.addrOf (k + {d} + 1)) avail blk sp1 _ rfl (by omega) hblk hsp1",
            "  (by dsimp only; rw [lcl_blk, hspA]; ecancel)) ?_",
            "rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hr141, -, stk1, sn1, hstk1, hsn1, Hm1⟩",
            "dsimp only at hpc1 hrsp1 hr141 Hm1", "subst hpc1",
            "obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩,",
            "  zmms1, flags1, mem1⟩ := d1", "simp only at hrsp1 hr141 Hm1", "subst hrsp1 hr141",
            "rw [lcl_blk, luObj_sep, hspA] at Hm1"]


def iter_lucall(S, W, d):
    C, X, n = S.C, S.X, W.n + 1
    W.n = n
    sp2 = S.C - 16
    ra = W.slots[C]
    W.slots[C] = f"(Host.addrOf (k + {d} + 1)).toBitVec"
    return ["have hrcx' : rcx.toBitVec = BitVec.ofNat 64 s := by apply BitVec.eq_of_toNat_eq; simp; omega",
            "have hy : (BitVec.ofNat 64 cap0 - rcx.toBitVec + -4).toNat = cap0 - s - 4 := by",
            "  rw [hrcx']; exact lcl_y cap0 s (by omega) hcap63",
            "rw [lc_mask _ _ (by rw [hy]; omega) (by rw [hy]; omega)]",
            "rw [show rcx.toBitVec + base * 1#64 = base + BitVec.ofNat 64 s by rw [hrcx', BitVec.mul_one, BitVec.add_comm]]",
            f"apply store_step_at _ _ (x - {C}) _ _ _ (Int.toBytes 8 {ra}.toInt) _ _",
            "  (lcl_call _) (by ecancel) (by exact Int.toBytes_length 8 _)",
            f"intro m{n} H{n}", f"simp only [Width.bytes, Width.bits] at H{n}", "kunfold", "rw [lcl_call] at *",
            "rw [tl_split3 base tl s (4 + 8 * g.l.length) (by omega) (by omega), hpart,",
            "  at_app [4, 0, 0, 0] (u64Bytes g.l).toList (b := base + BitVec.ofNat 64 s + 4) (by rfl)",
            f"  (by have : g.l.length ≤ 16 := hg; simp [u64Bytes_size]; omega)] at H{n}",
            f"have hx{C} : (x - {C}).toNat = x.toNat - {C} := by",
            "  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp",
            f"refine eventually_trans _ _ _ _ (hlu _ (Host.addrOf (k + {d} + 1)) g stk1 sn1 sp2",
            "  (List.replicate 8 0) (List.replicate 8 0) (List.replicate 8 0) guard (avail - 24) _ hg hstk1 hsn1 hsp2",
            "  (by simp) (by simp) (by simp)",
            "  (by show (BitVec.ofNat 64 e - rcx.toBitVec).toNat = _; rw [hrcx']; simp [BitVec.toNat_sub]; omega)",
            "  (by show (BitVec.ofNat 64 e - rcx.toBitVec).toNat ≤ (BitVec.ofNat 64 cap0 - rcx.toBitVec + -4).toNat",
            "      rw [hy, hrcx']; simp [BitVec.toNat_sub]; omega)",
            "  (by show (BitVec.ofNat 64 cap0 - rcx.toBitVec + -4).toNat < 2 ^ 63; rw [hy]; omega)",
            f"  (by show guard.toNat < (x - {C}).toNat - 8; rw [hx{C}]; omega)",
            f"  (by show 8 ≤ (x - {C}).toNat; rw [hx{C}]; omega) (by omega)",
            f"  (by dsimp only; rw [show x - {C} + 8 = x - {X} by bv_omega, show x - {C} + 16 = x - {sp2} by bv_omega]; ecancel)) ?_",
            "rintro ⟨d2, pc2⟩ ⟨hpc2, hrax2, hrbx2, hrsp2, hr142, q, stk2, sp1', sp2', hstk2, hsp1', hsp2', Hm2⟩",
            "dsimp only at hpc2 hrax2 hrbx2 hrsp2 hr142 Hm2", "subst hpc2",
            "obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,",
            "  zmms2, flags2, mem2⟩ := d2", "simp only at hrax2 hrbx2 hrsp2 hr142 Hm2", "subst hrax2 hrbx2 hrsp2 hr142",
            f"rw [show x - {C} + 8 = x - {X} by bv_omega, show x - {C} + 16 = x - {sp2} by bv_omega] at Hm2",
            f"have hrsp2 : ({{ toBitVec := x - {C} }} + 8 : UInt64) = {{ toBitVec := x - {X} }} := by",
            "  apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega",
            "simp only [hrsp2]"]


def iter_finish(S, W, L):
    """Back at the loop head: the post-state of lcl_iter (hand text; slot values from the walk)."""
    sl = W.slots
    v = lambda d: f"Int.toBytes 8 {sl[d]}.toInt"
    ra, s136, s152, s184 = v(S.C), v(136), v(152), v(184)
    s160 = v(160)
    H = f"H{W.n}"
    L += ["apply Eventually.done",
          f"refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl, {sl[136]}, q, stk2, {ra},",
          f"  sp1', sp2', {s136}, {s152},",
          f"  {s160}, hstk2, Int.toBytes_length 8 _, hsp1', hsp2', Int.toBytes_length 8 _,",
          "  Int.toBytes_length 8 _, Int.toBytes_length 8 _, ?_⟩",
          "· exact hi1", "· show (BitVec.ofNat 64 n).toNat = n; simp; omega",
          "· show (BitVec.ofNat 64 e).toNat = e; simp; omega", "· rfl", "· rfl",
          "· apply UInt64.toBitVec_inj.mp; simp only [hrsp]; bv_omega", "· dsimp only",
          "  rw [tl_split3 base tl s (4 + 8 * g.l.length) (by omega) (by omega), hpart,",
          "    at_app [4, 0, 0, 0] (u64Bytes g.l).toList (b := base + BitVec.ofNat 64 s + 4) (by rfl)",
          "      (by have : g.l.length ≤ 16 := hg; simp [u64Bytes_size]; omega),",
          "    List.append_assoc, at_app ptrs _ (b := A + BitVec.ofNat 64 (8 * i)) (by rw [hptrs])",
          "      (by simp [hptrs, Int.toBytes_length]; omega),",
          f"    at_app ({s136}) _ (b := A + BitVec.ofNat 64 (8 * i) + 8) (by simp [Int.toBytes_length])",
          "      (by simp [Int.toBytes_length]; omega)]",
          f"  simp only [Std.ExtHashMap.sep_assoc] at {H} ⊢", "  ecancel"]
    assert sl[184] == "(BitVec.ofNat 64 e)", sl[184]
    return L


def iter_proof(S):
    h = S.head
    W = Walk(S, "x", {-8: "recv", -32: "(BitVec.ofNat 64 cap0)", 128: "base", 136: ("s136", "h136"),
                      144: "(BitVec.ofNat 64 (cap0 - 4))", 152: ("s152", "h152"), 160: ("s160", "h160"),
                      168: "(BitVec.ofNat 64 n)", 176: "(BitVec.ofNat 64 T)", 184: ("s184", "h184")},
             {"rax": "rax.toBitVec", "rcx": "rcx.toBitVec", "rdx": "rdx.toBitVec"}, "pre")
    L = ["obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s0",
         "simp only at h_mem hrax hrdx hrcx hrsp ⊢",
         "have := rax.toNat_lt_size; have := rdx.toNat_lt_size; have := rcx.toNat_lt_size; have := x.isLt",
         "simp only [UInt64.size] at *", kat(S, h), kat(S, h + 1), kat(S, h + 2),
         "split", "case isTrue h =>", "  exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega",
         "simp only [Effects.All]"]
    d = h + 3
    while d != S.no:
        L.append(kat(S, d))
        fo = frame_op(W, S.txt[d])
        if fo is None and S.txt[d].split()[0] not in ("lea", "nop"):
            raise SystemExit(f"ListC loop directive {d} `{S.txt[d]}` before newobject: no tactic template")
        L += fo or []
        d += 1
    L += [kat(S, d), *iter_newobject(S, W, d)]
    W.ph = "call"
    return iter_walk(S, W, d + 1, L, False)


def exit_proof(S):
    return ["obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s0",
            "dsimp only at hrr", "subst hrr", kat(S, S.head), kat(S, S.head + 1), kat(S, S.head + 2),
            "split", "case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h",
            "simp only [Effects.All]", klabel(S, S.exit), "exact Eventually.done _ (hP _)"]


def loop_block(S):
    """lcl_iter, lcl_exit, lcl_loop (Lean text, theorem level)."""
    st = sub(T.ITER_STMT, S)
    ex = sub(T.EXIT_STMT, S)
    return ["set_option maxHeartbeats 16000000 in", "set_option maxRecDepth 200000 in", st, *["  " + x for x in iter_proof(S)], "",
            "set_option maxHeartbeats 4000000 in", "set_option maxRecDepth 200000 in", ex, *["  " + x for x in exit_proof(S)], "",
            "set_option maxHeartbeats 16000000 in", "set_option maxRecDepth 200000 in", sub(T.LOOP, S), ""]


# ---------------------------------------------------------------- the two accept paths

def ret_tail(S, d, ph, L):
    """From a jump into the common return block: label, mov, add, pop, retq."""
    L += [klabel(S, d), kat(S, d), kat(S, d + 1), kat(S, d + 2), kat(S, d + 3)]
    if ph == "post":
        L += [f"rw [show ({S.F} : BitVec 64) + ({{ toBitVec := rsp.toBitVec - {S.C} }} + 8 : UInt64).toBitVec = rsp.toBitVec - 8 by",
              "  simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega]"]
    else:
        L.append(f"rw [ar_m{S.F + 8}]")
    L += ["apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)", "kunfold",
          kat(S, d + 4), "rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]",
          "apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)", "kunfold"]
    return L


def recv_store(off, name, how="by bv_omega"):
    a = "rax.toBitVec" if off == 0 else f"(rax.toBitVec + {off})"
    return f"apply store_step_at _ _ {a} _ _ _ {name} _ _ ({how}) (by ecancel) (by exact h{name})"


def accept_walk(S, L, d):
    """From the accept branch (container offset and first offset checked) to the end of the function."""
    txt, lab = S.txt, S.lab
    W = Walk(S, "rsp.toBitVec", {-8: ("s8", "h8"), -32: ("s32", "h32")}, {"rax": "rax.toBitVec",
             "rbx": "(BitVec.ofNat 64 (4 * gs.length))", "rdx": "(BitVec.ofNat 64 gs.length)"}, "entry", "n", "N")
    for o in (128, 136, 144, 152, 160, 168, 176, 184):
        W.slots[o] = (f"l{o}", f"hl{o}")
    recv = {8: "cL", 16: "cC", 0: "cP"}
    while True:
        t = txt[d]
        if S.D[d][1] == "label":
            L.append(kat(S, d)); d += 1; continue
        op = t.split()[0]
        a = t[len(op):].strip()
        jt = lab.get(a)
        L.append(kat(S, d))
        fo = frame_op(W, t)
        if fo is not None:
            L += fo
        elif op == "callq" and d == S.ms:
            L += body(T.ACC_MS, S); W.ph = "call"; W.n = 8
        elif op == "mov" and re.fullmatch(r"%rdx,0x(8|10)\(%rsi\)|%rax,\(%rsi\)", a):
            off = 0 if a.endswith("(%rsi)") and "0x" not in a else int(a.split(",")[1].split("(")[0], 16)
            assert W.regs.get("rsi") == "rax.toBitVec", W.regs
            W.n += 1
            L += [recv_store(off, recv[off]), f"intro n{W.n} N{W.n}", f"simp only [Width.bytes, Width.bits] at N{W.n}", "kunfold"]
        elif op == "cmpl" and a == "$0x0,runtime.writeBarrier(%rip)":
            L += WB
        elif op == "je" and txt[d - 1].startswith("cmpl $0x0,runtime.writeBarrier"):
            L += SPLIT_F + [klabel(S, jt)]; d = jt; continue
        elif op == "xor":
            L.append("intro _")
        elif op == "jmpq" and jt == S.head:
            L += [klabel(S, jt), *body(T.ACC_LOOP, S)]
            d = S.exit; L.append(kat(S, d)); d += 1
            continue
        elif op == "jmpq" and jt == S.ret:
            ret_tail(S, jt, "post", L)
            return L + body(T.ACC_FIN, S)
        elif op in ("lea", "mov", "nop"):
            pass
        else:
            raise SystemExit(f"ListC accept directive {d} `{t}`: no tactic template")
        d += 1


def empty_walk(S, L, d):
    """From the `len(buf) - 4 <= 3` branch with len(buf) = 4: the empty list."""
    txt, lab = S.txt, S.lab
    while True:
        t = txt[d]
        if S.D[d][1] == "label":
            L.append(kat(S, d)); d += 1; continue
        op = t.split()[0]
        a = t[len(op):].strip()
        jt = lab.get(a)
        L.append(kat(S, d))
        if op == "jne" and txt[d - 1] == "add $-0x4,%r10":
            L += ["split", "case isTrue h =>", "  exfalso; simp [CondCode.interp, StatusFlags.from_result] at h",
                  "  apply h; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega", "simp only [Effects.All]"]
        elif op == "movups" and a == "%xmm15,0x8(%rax)":
            L += ["simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]", "kunfold",
                  "apply store_avx_step _ _ _ _ cLC _ _ (by ecancel) (by exact hcLC) (by decide)", "intro m3 H3", "kunfold",
                  "rw [hx15, show Int.toBytes AvxWidth.W128.bytes (0 : BitVec 128).toInt = List.replicate 16 0 by decide] at H3"]
        elif op == "cmpl" and a == "$0x0,runtime.writeBarrier(%rip)":
            L += WB
        elif op == "je" and txt[d - 1].startswith("cmpl $0x0,runtime.writeBarrier"):
            L += SPLIT_F + [klabel(S, jt)]; d = jt; continue
        elif op == "mov" and a == "%rcx,(%rax)" and txt[d - 1] == "lea runtime.zerobase(%rip),%rcx":
            L += ["apply store_step_at _ _ rax.toBitVec _ _ _ cP _ _ (by kaddr) (by ecancel) (by exact hcP)",
                  "intro m4 H4", "simp only [Width.bytes, Width.bits] at H4", "kunfold"]
        elif op == "xor":
            L.append("intro _")
        elif op == "jmp" and jt == S.ret:
            ret_tail(S, jt, "pre", L)
            return L + body(T.EMP_FIN, S)
        elif op in ("add", "lea"):
            pass
        else:
            raise SystemExit(f"ListC empty-accept directive {d} `{t}`: no tactic template")
        d += 1


EMPTY_INTRO = "intro k hk hf s ra guard fp slot cP cLC hfp hsl hcP hcLC R h_mem hguard hsp hlen hcap hcap63 hx15"
ACCEPT_INTRO = ("intro k hk hf tl T gs hgs hT hn1 hn hT32 hend hfirst hparts hnexts s ra guard fp slot s8 s32 l128 l136 l144 "
                "l152 l160 l168 l176 l184 l208 l216 l224 rslot blk cP cL cC hfp hsl h8 h32 hl128 hl136 hl144 hl152 hl160 "
                "hl168 hl176 hl184 hl208 hl216 hl224 hrs hcP hcL hcC S hS hblk R Heap avail hav h_mem hguard hsp hlen hcap "
                "hcap63 hms hno hlu")
