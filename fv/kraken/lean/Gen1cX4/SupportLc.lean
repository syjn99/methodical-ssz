import Gen1cX4.Support
import Fk.FunSpecs
import Fk.LuErr

/-! ListC accept support for the proofs that fv/kraken/gen/x4 generates. Written by hand, not generated.
The statement definitions `lcObjs`, `ptrBytes`, `lcStart`, `lcStk` have the same text as in Fk/LcLoop.lean
(so the generated statements compare equal by definitional unfolding); the lemmas are copies of
Fk/LcLoop.lean, Fk/LcAccept.lean (`lca_m4`), Fk/LcMarshal.lean (`sep_mono_right'`), Fk/LcOrder.lean (`jb_true`), Fk/LcItems.lean (the contract statement `LuURejShortC`, with an explicit `[Host]` binder where the hand file has `variable [Host]`) and Fk/NeAccept.lean
(`luObj_sep`) with the same statements, proved here again so the generated module does not import those
hand proof modules. Kept apart from Support.lean so that only the ListC module depends on Fk.LuErr. -/

namespace Gen1cX4
open Fk Fk.Code Fv1 EthLib.Serialization.Ssz

theorem ja_false (a b : BitVec 64) (af of' : Bool) (h : a.toNat ≤ b.toNat) :
    CondCode.a.interp (StatusFlags.from_result (a - b)
      { cf := BitVec.unsigned (a - b) != a.unsigned - b.unsigned, af := af, of := of' }) = false := by
  by_cases he : a = b
  · subst he; simp [CondCode.interp, StatusFlags.from_result]
  · have hlt : a.toNat < b.toNat := by
      have : a.toNat ≠ b.toNat := fun e => he (BitVec.eq_of_toNat_eq e)
      omega
    have hb := b.isLt
    have hs : (a - b).toNat = 2 ^ 64 - b.toNat + a.toNat := by rw [BitVec.toNat_sub]; omega
    simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, hs]
    simp; omega
theorem jb_false (a b : BitVec 64) (af of' : Bool) (h : b.toNat ≤ a.toNat) :
    CondCode.c.interp (StatusFlags.from_result (a - b)
      { cf := BitVec.unsigned (a - b) != a.unsigned - b.unsigned, af := af, of := of' }) = false := by
  have hs : (a - b).toNat = a.toNat - b.toNat := BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
  simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, hs]
  simp; omega

theorem ofBytes_uintBytes4 (e : Nat) (h : e < 2 ^ 32) : Int.ofBytes (uintBytes 4 e).toList = e := by
  have := ofBytes_readUint (uintBytes 4 e) 4 0 (by simp [Fv.uintBytes_size])
  rw [List.drop_zero, List.take_of_length_le (by simp [Fv.uintBytes_size])] at this
  rw [this, readUint_uintBytes 4 e (by simpa using h)]

theorem lc_mask (v y : BitVec 64) (h : 0 < y.toNat) (h2 : y.toNat < 2 ^ 63) :
    v &&& BitVec.sshiftRight (-y) 63 = v := by
  have hm : (-y).msb = true := by
    rw [BitVec.msb_eq_decide, BitVec.toNat_neg]; simp; omega
  have hs : BitVec.sshiftRight (-y) 63 = BitVec.allOnes 64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sshiftRight, ite_cond_eq_true _ _ (by simpa using hm)]
    rw [BitVec.msb_eq_decide] at hm; simp at hm
    simp [Nat.shiftRight_eq_div_pow]; omega
  rw [hs, BitVec.and_allOnes]

theorem lcl_y (c s : Nat) (h1 : s + 4 ≤ c) (h2 : c < 2 ^ 63) :
    (BitVec.ofNat 64 c - BitVec.ofNat 64 s + -4).toNat = c - s - 4 := by
  rw [← BitVec.sub_eq_add_neg]
  have h3 : BitVec.ofNat 64 c - BitVec.ofNat 64 s = BitVec.ofNat 64 (c - s) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega
  rw [h3, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]
  simp; omega

theorem jnc_false (a b : BitVec 64) (af of' : Bool) (h : a.toNat < b.toNat) :
    CondCode.nc.interp (StatusFlags.from_result (a - b)
      { cf := BitVec.unsigned (a - b) != a.unsigned - b.unsigned, af := af, of := of' }) = false := by
  have hs : (a - b).toNat = 2 ^ 64 - b.toNat + a.toNat := by
    rw [BitVec.toNat_sub]; have := b.isLt; omega
  simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, hs]
  simp; omega

/-- The tail chunk split around `[o, o + w)`. -/
theorem tl_split3 (a : BitVec 64) (tl : List UInt8) (o w : Nat) (h : o + w ≤ tl.length) (hl : tl.length < 2 ^ 64) :
    Eq (tl.At a) = Eq ((tl.take o).At a) ⋆ Eq (((tl.drop o).take w).At (a + BitVec.ofNat 64 o))
      ⋆ Eq ((tl.drop (o + w)).At (a + BitVec.ofNat 64 o + BitVec.ofNat 64 w)) := by
  have e1 : tl = tl.take o ++ ((tl.drop o).take w ++ tl.drop (o + w)) := by
    rw [← List.drop_drop, List.take_append_drop, List.take_append_drop]
  conv => lhs; rw [e1]
  rw [Mem.At_append_sep _ _ _ (by simp; omega), Mem.At_append_sep _ _ _ (by simp; omega)]
  simp only [List.length_take, List.length_drop, Std.ExtHashMap.sep_assoc]
  rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]

theorem lca_m4 (y : BitVec 64) (h : 4 ≤ y.toNat) : y + -4 = BitVec.ofNat 64 (y.toNat - 4) := by
  rw [← BitVec.sub_eq_add_neg]; apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simpa using h)]; simp; omega
theorem lca_m4' (y : BitVec 64) (h : 4 ≤ y.toNat) : -4 + y = BitVec.ofNat 64 (y.toNat - 4) := by
  rw [BitVec.add_comm]; exact lca_m4 y h

theorem sep_mono_right' {P Q Q' : DataMem → Prop} {m : DataMem} (hQ : ∀ m, Q m → Q' m)
    (h : (P ⋆ Q) m) : (P ⋆ Q') m := by
  obtain ⟨a, b, hu, hi, hp, hq⟩ := h
  exact ⟨a, b, hu, hi, hp, hQ b hq⟩

/-- A zeroed ListU64 object (24 bytes) as three 8-byte words. -/
theorem luObj_sep (p : BitVec 64) :
    Eq ((List.replicate 24 (0 : UInt8)).At p) = Eq ((List.replicate 8 0).At p) ⋆ Eq ((List.replicate 8 0).At (p + 8))
      ⋆ Eq ((List.replicate 8 0).At (p + 16)) := by
  rw [show List.replicate 24 (0 : UInt8) = List.replicate 8 0 ++ (List.replicate 8 0 ++ List.replicate 8 0) by rfl]
  rw [at_app _ _ (b := p + 8) (by simp) (by simp), at_app _ _ (b := p + 16) (by simp; bv_omega) (by simp)]
  simp only [Std.ExtHashMap.sep_assoc]

/-- The objects decoded so far, newest first: (p, q, g) is a ListU64 object at
p with header (q, len, len) and the elements at q. -/
def lcObjs : List (BitVec 64 × BitVec 64 × ListU64) → DataMem → Prop
  | [] => Std.ExtHashMap.emp
  | (p, q, g) :: rest => Eq ((Int.toBytes 8 q.toInt).At p) ⋆ Eq ((Int.toBytes 8 (g.l.length : Int)).At (p + 8))
      ⋆ Eq ((Int.toBytes 8 (g.l.length : Int)).At (p + 16)) ⋆ Eq ((u64Bytes g.l).toList.At q) ⋆ lcObjs rest

/-- The items array: one 8-byte pointer per element. -/
def ptrBytes (ps : List (BitVec 64)) : List UInt8 := ps.flatMap fun p => Int.toBytes 8 p.toInt

theorem ptrBytes_length (ps : List (BitVec 64)) : (ptrBytes ps).length = 8 * ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [ptrBytes, Int.toBytes_length] at ih ⊢; omega

theorem ptrBytes_snoc (ps : List (BitVec 64)) (p : BitVec 64) :
    ptrBytes (ps ++ [p]) = ptrBytes ps ++ Int.toBytes 8 p.toInt := by
  simp [ptrBytes]

/-- Start offset of element i: the offset table (4n), then the encodings before i. -/
def lcStart (gs : List ListU64) (i : Nat) : Nat := 4 * gs.length + ((gs.take i).map fun g => 4 + 8 * g.l.length).sum

theorem lcStart_succ (gs : List ListU64) (i : Nat) (hi : i < gs.length) :
    lcStart gs (i + 1) = lcStart gs i + (4 + 8 * gs[i].l.length) := by
  simp only [lcStart, List.take_add_one, List.map_append, List.sum_append, List.getElem?_eq_getElem hi]
  simp; omega

theorem lcStart_le (gs : List ListU64) (i : Nat) : lcStart gs i ≤ lcStart gs gs.length := by
  simp only [lcStart, List.take_length]
  have : ((gs.take i).map fun g => 4 + 8 * g.l.length).sum ≤ (gs.map fun g => 4 + 8 * g.l.length).sum := by
    conv => rhs; rw [← List.take_append_drop i gs]
    rw [List.map_append, List.sum_append]; omega
  omega

/-- The dead stack of `ListC.UnmarshalSSZ` after its element loop (fix 3 X4,
astra fix 2 required 6): the slots that the loop owns, relative to the entry
rsp `x` (return address at `x`), as bytes of fixed lengths. The values are not
named (the caller does not read them); the region is owned, not `True`. -/
def lcStk (x : BitVec 64) (S : Nat) : DataMem → Prop := fun m =>
  ∃ a8 a32 b128 b136 b144 b152 b160 b168 b176 b184 b216 b224 b232 blk : List UInt8,
    a8.length = 8 ∧ a32.length = 8 ∧ b128.length = 8 ∧ b136.length = 8 ∧ b144.length = 8 ∧ b152.length = 8
    ∧ b160.length = 8 ∧ b168.length = 8 ∧ b176.length = 8 ∧ b184.length = 8 ∧ b216.length = 8
    ∧ b224.length = 8 ∧ b232.length = 8 ∧ blk.length = 144 + S ∧
    (Eq (a8.At (x + 8)) ⋆ Eq (a32.At (x + 32)) ⋆ Eq (b128.At (x - 128)) ⋆ Eq (b136.At (x - 136))
      ⋆ Eq (b144.At (x - 144)) ⋆ Eq (b152.At (x - 152)) ⋆ Eq (b160.At (x - 160)) ⋆ Eq (b168.At (x - 168))
      ⋆ Eq (b176.At (x - 176)) ⋆ Eq (b184.At (x - 184)) ⋆ Eq (b216.At (x - 216)) ⋆ Eq (b224.At (x - 224))
      ⋆ Eq (b232.At (x - 232)) ⋆ Eq (blk.At (x - 232 - 144 - BitVec.ofNat 64 S))) m

theorem lcs_mono {P P' F : DataMem → Prop} {m : DataMem} (hP : ∀ m, P m → P' m)
    (h : (P ⋆ F) m) : (P' ⋆ F) m := by
  obtain ⟨a, b, hu, hi, hp, hr⟩ := h
  exact ⟨a, b, hu, hi, hP a hp, hr⟩

theorem jb_true (a b : BitVec 64) (af of' : Bool) (h : a.toNat < b.toNat) :
    CondCode.c.interp (StatusFlags.from_result (a - b)
      { cf := BitVec.unsigned (a - b) != a.unsigned - b.unsigned, af := af, of := of' }) = true := by
  have hb := b.isLt
  have hs : (a - b).toNat = 2 ^ 64 - b.toNat + a.toNat := by rw [BitVec.toNat_sub]; omega
  simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, hs]
  simp; omega

/-- ListU64.UnmarshalSSZ, short input (`len(buf) < 4`): it returns the two
words of `ssz.ErrSize` (rax, rbx). Frame like `LuUAccC`: a `144 + S`-byte stack
block below the return slot and the spill slot at rsp + 16; the global words,
the guard and `F` are kept. -/
def LuURejShortC [Host] (S : Nat) : Prop :=
  ∀ (st : MachineData) (ret : Int64) (stk sp2 : List UInt8) (guard e0 e1 : UInt64) (F : DataMem → Prop),
    stk.length = 144 + S → sp2.length = 8 → st.regs.rcx.toNat < 4 →
    guard.toNat < st.regs.rsp.toNat - 8 → 8 ≤ st.regs.rsp.toNat →
    (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
      ⋆ Eq (stk.At (st.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S)) ⋆ Eq (sp2.At (st.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (st.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrSize").toBitVec)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ F) st.dmem →
    Eventually (step1 Host.exe)
      (fun st' => st'.pc = ret ∧ st'.data.regs.rax = e0 ∧ st'.data.regs.rbx = e1
        ∧ st'.data.regs.rsp = st.regs.rsp + 8 ∧ st'.data.regs.r14 = st.regs.r14 ∧
        ∃ stk' sp2' : List UInt8, stk'.length = 144 + S ∧ sp2'.length = 8 ∧
        (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
          ⋆ Eq (stk'.At (st.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S)) ⋆ Eq (sp2'.At (st.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (st.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrSize").toBitVec)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ F) st'.data.dmem)
      ⟨st, label "target.ListU64.UnmarshalSSZ"⟩

end Gen1cX4
