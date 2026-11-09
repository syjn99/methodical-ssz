import Fk.LcOrder
import Fk.LuReject

/-!
# ListC.UnmarshalSSZ, element decode error (fix 3 X5, review fix3-r1 M4)

One element whose bytes are too short for a ListU64 (fewer than 4): the
element decoder `ListU64.UnmarshalSSZ` returns `ssz.ErrSize` (an initialized
`*errors.errorString` global) and the ListC decoder wraps it with
`fmt.Errorf("Items: %w", err)` (format `Fk.Data.lcFmtItems`, contract
`FmtErrorfWC`).

`lu_reject_short_frame` is `lu_reject_short_main` with a conclusion that keeps
the callee's stack slots, r14 and the error global (the statement of
`lu_reject_short_main` is unchanged). `LuURejShortC` is the function
specification of that path; `lu_urej_short_holds` derives it from the machine
code.
-/

open Fk Fk.Code Fv1 EthLib.Serialization.Ssz
variable [Host]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `lu_reject_short_main` with the frame kept: the return slot, the saved
rbp slot and the spill slot (new bytes of the same length), the guard, the
two words of `ssz.ErrSize`, r14. -/
theorem lu_reject_short_frame (k : Nat) (hk : ListU64UnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListU64UnmarshalSSZ k)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp slot : List UInt8) (hfp : fp.length = 8) (hsl : slot.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrSize").toBitVec)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat - 8) (hsp : 8 ≤ s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat < 4) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ ∃ fp' slot' : List UInt8, fp'.length = 8 ∧ slot'.length = 8 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq (fp'.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (slot'.At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrSize").toBitVec)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hlen ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; simp only [UInt64.size] at *
  kat hk ListU64UnmarshalSSZ 0
  kat hk ListU64UnmarshalSSZ 1
  kat hk ListU64UnmarshalSSZ 2
  kat hk ListU64UnmarshalSSZ 3
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListU64UnmarshalSSZ 4
  split
  case isTrue h =>
    exfalso
    rw [cmp_be_false _ _ _ _ (by rw [toNat_add_neg8 _ (by simpa using hsp)]; simpa using hguard)] at h
    exact absurd h (by simp)
  simp only [Effects.All]
  kat hk ListU64UnmarshalSSZ 5
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by kaddr) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk ListU64UnmarshalSSZ 6
  kat hk ListU64UnmarshalSSZ 7
  kat hk ListU64UnmarshalSSZ 8
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ slot _ _ (lu_neg8 _) (by ecancel) (by exact hsl)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk ListU64UnmarshalSSZ 9
  kat hk ListU64UnmarshalSSZ 10
  kat hk ListU64UnmarshalSSZ 11
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
  simp only [Effects.All]
  klabel hk hf ListU64UnmarshalSSZ 137
  kat hk ListU64UnmarshalSSZ 137
  kat hk ListU64UnmarshalSSZ 138
  apply load_step _ _ _ _ (Int.toBytes 8 e0.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListU64UnmarshalSSZ 139
  apply load_step _ _ _ _ (Int.toBytes 8 e1.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListU64UnmarshalSSZ 140
  kat hk ListU64UnmarshalSSZ 141
  rw [lu_pop]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListU64UnmarshalSSZ 142
  rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨trivial, ?_, ?_, ?_, ?_, trivial, Int.toBytes 8 rbp.toBitVec.toInt, Int.toBytes 8 rbx.toBitVec.toInt,
    Int.toBytes_length 8 _, Int.toBytes_length 8 _, ?_⟩
  · first | trivial | rfl | (apply UInt64.toBitVec_inj.mp; simp)
  · first | trivial | rfl | (apply UInt64.toBitVec_inj.mp; simp)
  · apply UInt64.toBitVec_inj.mp; simp
  · first | trivial | rfl
  · ecancel

/-- ListU64.UnmarshalSSZ, short input (`len(buf) < 4`): it returns the two
words of `ssz.ErrSize` (rax, rbx). Frame like `LuUAccC`: a `144 + S`-byte stack
block below the return slot and the spill slot at rsp + 16; the global words,
the guard and `F` are kept. -/
def LuURejShortC (S : Nat) : Prop :=
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

theorem luShort_split (stk : List UInt8) (S : Nat) (hS : S < 2 ^ 60) (h : stk.length = 144 + S) (x : BitVec 64) :
    Eq (stk.At (x - 144 - BitVec.ofNat 64 S)) = Eq ((stk.take (136 + S)).At (x - 144 - BitVec.ofNat 64 S))
      ⋆ Eq ((stk.drop (136 + S)).At (x - 8)) := by
  conv => lhs; rw [← List.take_append_drop (136 + S) stk]
  exact at_app _ _ (by
    simp only [List.length_take, h, show min (136 + S) (144 + S) = 136 + S by omega]
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_sub]; omega) (by simp [h]; omega)

set_option maxHeartbeats 8000000 in
/-- The ListU64 machine code satisfies `LuURejShortC` (from `lu_reject_short_frame`). -/
theorem lu_urej_short_holds (k : Nat) (hk : ListU64UnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListU64UnmarshalSSZ k) (S : Nat) (hS : S < 2 ^ 60) : LuURejShortC S := by
  intro st ret stk sp2 guard e0 e1 F hstk hsp2 hlen hguard hsp hm
  rw [label_at hk hf (j := 0) (l := "target.ListU64.UnmarshalSSZ") (by rfl) (by intro i hi; omega)]
  rw [luShort_split stk S hS hstk] at hm
  refine eventually_trans _ _ _ _ (lu_reject_short_frame k hk hf st (UInt64.ofBitVec ret.toBitVec) guard e0 e1
    (stk.drop (136 + S)) sp2 (by simp [hstk]; omega) hsp2
    (Eq ((stk.take (136 + S)).At (st.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S)) ⋆ F) (by ecancel) hguard hsp hlen) ?_
  rintro ⟨d, pc⟩ ⟨hpc, hrax, hrbx, hrsp, -, hr14, fp', sl', hfp', hsl', hmem⟩
  refine Eventually.done _ ⟨hpc, hrax, hrbx, hrsp, hr14, stk.take (136 + S) ++ fp', sl',
    by simp [hstk, hfp']; omega, hsl', ?_⟩
  rw [luShort_split _ S hS (by simp [hstk, hfp']; omega),
    List.take_left' (by simp [hstk]), List.drop_left' (by simp [hstk])]
  ecancel
