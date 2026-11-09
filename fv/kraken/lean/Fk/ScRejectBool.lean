import Fk.ScSpec

/-!
# Scalars.UnmarshalSSZ, bool reject path

If `len(buf) = 16` and the bool byte `e` is above 1, the function writes the
fields A, B, C, D (Go writes them before the bool test) and returns
`ssz.ErrInvalidSerialization` (the two words of the global) to the return
-/

open Fk Fk.Code Fv1 EthLib.Serialization.Ssz
variable [Host]

theorem sc_ofBytes1 (e : UInt8) : BitVec.ofInt 8 (Int.ofBytes [e]) = e.toBitVec := by
  have := e.toNat_lt
  apply BitVec.eq_of_toNat_eq
  simp [Int.ofBytes, BitVec.toNat_ofInt]

set_option maxHeartbeats 2000000 in
theorem sc_reject_bool_main (k : Nat) (hk : ScalarsUnmarshalSSZ.IsInfixAt Host.prog k)
    (s : MachineData) (ra e0 e1 : UInt64) (slot b0 b1 b2 b3 c0 c1 c2 c3 c4 : List UInt8) (e : UInt8)
    (he : 1 < e.toNat)
    (hsl : slot.length = 8) (h0l : b0.length = 1) (h1l : b1.length = 2) (h2l : b2.length = 4)
    (h3l : b3.length = 8)
    (g0 : c0.length = 1) (g1 : c1.length = 2) (g2 : c2.length = 4) (g3 : c3.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (b0.At s.regs.rbx.toBitVec) ⋆ Eq (b1.At (s.regs.rbx.toBitVec + 1))
      ⋆ Eq (b2.At (s.regs.rbx.toBitVec + 3)) ⋆ Eq (b3.At (s.regs.rbx.toBitVec + 7))
      ⋆ Eq ([e].At (s.regs.rbx.toBitVec + 15))
      ⋆ Eq (c0.At s.regs.rax.toBitVec) ⋆ Eq (c1.At (s.regs.rax.toBitVec + 2))
      ⋆ Eq (c2.At (s.regs.rax.toBitVec + 4)) ⋆ Eq (c3.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (c4.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrInvalidSerialization").toBitVec)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrInvalidSerialization" + 8).toBitVec) ⋆ R)
    (hL41f : ∀ i < k, Host.prog[i]? ≠ some (.label "L_target.Scalars.UnmarshalSSZ_41"))
    (hlen : s.regs.rcx = 16) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq (b0.At s.regs.rax.toBitVec) ⋆ Eq (b1.At (s.regs.rax.toBitVec + 2))
          ⋆ Eq (b2.At (s.regs.rax.toBitVec + 4)) ⋆ Eq (b3.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (c4.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (b0.At s.regs.rbx.toBitVec) ⋆ Eq (b1.At (s.regs.rbx.toBitVec + 1))
          ⋆ Eq (b2.At (s.regs.rbx.toBitVec + 3)) ⋆ Eq (b3.At (s.regs.rbx.toBitVec + 7))
          ⋆ Eq ([e].At (s.regs.rbx.toBitVec + 15))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrInvalidSerialization").toBitVec)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrInvalidSerialization" + 8).toBitVec)
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  have hL41 := label_in_fragment hk (j := 25) (by decide) (by decide) hL41f
  have h0 := hk
  simp only [ScalarsUnmarshalSSZ] at h0
  apply estep h0
  simp [Directive.interp]
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hlen ⊢
  subst hlen
  apply estep h0.cons.2
  kunfold
  apply store_step _ _ _ _ _ slot _ _ (by ecancel) (by exact hsl)
  intro m1 H1
  simp only [Effects.All]
  apply estep h0.cons.2.cons.2
  kunfold
  apply estep h0.cons.2.cons.2.cons.2
  kunfold
  split
  · rename_i h; exact absurd h (by decide)
  simp only [Effects.All]
  apply estep (isInfixAt_drop hk 4)
  kunfold
  apply load_step _ _ _ _ b0 _ _ (by ecancel) (by exact h0l)
  kunfold
  apply estep (isInfixAt_drop hk 5)
  kunfold
  apply store_step _ _ _ _ _ c0 _ _ (by ecancel) (by exact g0)
  intro m2 H2
  kunfold
  apply estep (isInfixAt_drop hk 6)
  kunfold
  apply load_step _ _ _ _ b1 _ _ (by ecancel) (by exact h1l)
  kunfold
  apply estep (isInfixAt_drop hk 7)
  kunfold
  apply store_step _ _ _ _ _ c1 _ _ (by ecancel) (by exact g1)
  intro m3 H3
  kunfold
  apply estep (isInfixAt_drop hk 8)
  kunfold
  apply load_step _ _ _ _ b2 _ _ (by ecancel) (by exact h2l)
  kunfold
  apply estep (isInfixAt_drop hk 9)
  kunfold
  apply store_step _ _ _ _ _ c2 _ _ (by ecancel) (by exact g2)
  intro m4 H4
  kunfold
  apply estep (isInfixAt_drop hk 10)
  kunfold
  apply load_step _ _ _ _ b3 _ _ (by ecancel) (by exact h3l)
  kunfold
  apply estep (isInfixAt_drop hk 11)
  kunfold
  apply store_step _ _ _ _ _ c3 _ _ (by ecancel) (by exact g3)
  intro m5 H5
  kunfold
  apply estep (isInfixAt_drop hk 12)
  kunfold
  apply load_step _ _ _ _ [e] _ _ (by ecancel) (by rfl)
  kunfold
  apply estep (isInfixAt_drop hk 13)
  kunfold
  apply estep (isInfixAt_drop hk 14)
  kunfold
  split
  case isFalse h =>
    exfalso; apply h
    have hb : 1 < e.toBitVec.toNat := he
    have hl := e.toNat_lt
    simp only [sc_ofBytes1]
    have hx : BitVec.extractLsb' 0 8 (BitVec.setWidth 64 e.toBitVec) = e.toBitVec := by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]
    simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, hx] at hb ⊢
    refine ⟨by omega, ?_⟩
    intro h0; have := congrArg BitVec.toNat h0; simp at this; omega
  simp only [Effects.All]
  rw [hL41]
  apply estep (isInfixAt_drop hk 25)
  kunfold
  apply estep (isInfixAt_drop hk 26)
  kunfold
  apply load_step _ _ _ _ (Int.toBytes 8 e0.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply estep (isInfixAt_drop hk 27)
  kunfold
  apply load_step _ _ _ _ (Int.toBytes 8 e1.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply estep (isInfixAt_drop hk 28)
  kunfold
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [Width.bytes, zx8, zx16, zx32, toBytes_ofInt_ofBytes 8 1 rfl b0 h0l,
    toBytes_ofInt_ofBytes 16 2 rfl b1 h1l, toBytes_ofInt_ofBytes 32 4 rfl b2 h2l,
    toBytes_ofInt_ofBytes 64 8 rfl b3 h3l] at H5
  refine ⟨?_, ?_, ?_, ?_, rfl, ?_⟩
  · simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]; rfl
  · apply UInt64.toBitVec_inj.mp; simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  · apply UInt64.toBitVec_inj.mp; simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  · apply UInt64.toBitVec_inj.mp; simp
  · dsimp only at H5 ⊢; (try simp only [BitVec.ofNat_eq_ofNat] at H5 ⊢)
    simp only [Std.ExtHashMap.sep_emp, Width.bits, Width.bytes, Int64.toBitVec_add, Int64.toBitVec_ofNat,
      BitVec.ofNat_eq_ofNat] at H5
    ecancel

/-- **The bool reject path returns a non-nil error** (fix 3 X3, astra fix 2
finding 4). `ssz.ErrInvalidSerialization` is set by `errors.New` in the ssz
package's initialization (ssz/error.go:11): its first word, the errorString
itab pointer, is not 0. With that runtime-initialization premise `he0`, the
decoder returns `rax ≠ 0`: an error, not nil. The memory conclusion is the one
of `sc_reject_bool_main`. -/
theorem sc_reject_bool_err (k : Nat) (hk : ScalarsUnmarshalSSZ.IsInfixAt Host.prog k)
    (s : MachineData) (ra e0 e1 : UInt64) (slot b0 b1 b2 b3 c0 c1 c2 c3 c4 : List UInt8) (e : UInt8)
    (he : 1 < e.toNat) (he0 : e0 ≠ 0)
    (hsl : slot.length = 8) (h0l : b0.length = 1) (h1l : b1.length = 2) (h2l : b2.length = 4)
    (h3l : b3.length = 8)
    (g0 : c0.length = 1) (g1 : c1.length = 2) (g2 : c2.length = 4) (g3 : c3.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (b0.At s.regs.rbx.toBitVec) ⋆ Eq (b1.At (s.regs.rbx.toBitVec + 1))
      ⋆ Eq (b2.At (s.regs.rbx.toBitVec + 3)) ⋆ Eq (b3.At (s.regs.rbx.toBitVec + 7))
      ⋆ Eq ([e].At (s.regs.rbx.toBitVec + 15))
      ⋆ Eq (c0.At s.regs.rax.toBitVec) ⋆ Eq (c1.At (s.regs.rax.toBitVec + 2))
      ⋆ Eq (c2.At (s.regs.rax.toBitVec + 4)) ⋆ Eq (c3.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (c4.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrInvalidSerialization").toBitVec)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrInvalidSerialization" + 8).toBitVec) ⋆ R)
    (hL41f : ∀ i < k, Host.prog[i]? ≠ some (.label "L_target.Scalars.UnmarshalSSZ_41"))
    (hlen : s.regs.rcx = 16) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax ≠ 0 ∧ st.data.regs.rax = e0
        ∧ st.data.regs.rbx = e1 ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq (b0.At s.regs.rax.toBitVec) ⋆ Eq (b1.At (s.regs.rax.toBitVec + 2))
          ⋆ Eq (b2.At (s.regs.rax.toBitVec + 4)) ⋆ Eq (b3.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (c4.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (b0.At s.regs.rbx.toBitVec) ⋆ Eq (b1.At (s.regs.rbx.toBitVec + 1))
          ⋆ Eq (b2.At (s.regs.rbx.toBitVec + 3)) ⋆ Eq (b3.At (s.regs.rbx.toBitVec + 7))
          ⋆ Eq ([e].At (s.regs.rbx.toBitVec + 15))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrInvalidSerialization").toBitVec)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrInvalidSerialization" + 8).toBitVec)
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ :=
  eventually_trans _ _ _ _ (sc_reject_bool_main k hk s ra e0 e1 slot b0 b1 b2 b3 c0 c1 c2 c3 c4 e he hsl h0l h1l
      h2l h3l g0 g1 g2 g3 R h_mem hL41f hlen)
    (fun _ h => Eventually.done _ ⟨h.1, h.2.1 ▸ he0, h.2.1, h.2.2⟩)

/-- **EthLib rejects a bool byte above 1.** If the 16th byte of a 16-byte
input is above 1, EthLib's `deserialize scDesc` does not accept it: every
accepted input is `scEncode g`, whose byte 15 is 0 or 1. -/
theorem sc_spec_rejects_bool (b0 b1 b2 b3 : List UInt8) (e : UInt8) (he : 1 < e.toNat)
    (h0l : b0.length = 1) (h1l : b1.length = 2) (h2l : b2.length = 4) (h3l : b3.length = 8) (v : Value) :
    deserialize scDesc (b0 ++ b1 ++ b2 ++ b3 ++ [e]).toArray ≠ .ok v := by
  intro hd
  obtain ⟨g, -, hg⟩ := accepted_is_enc (toV := Scalars.toValue) (enc := scEncode) scDesc_wellFormed
    sc_serialize (fun v h => sc_toValue_surjective v h) hd
  have h15 := congrArg (fun a : Array UInt8 => a.toList[15]?) hg
  simp only [List.toList_toArray] at h15
  rw [List.getElem?_append_right (l₁ := b0 ++ b1 ++ b2 ++ b3) (by simp [h0l, h1l, h2l, h3l])] at h15
  simp only [List.length_append, h0l, h1l, h2l, h3l] at h15
  simp [scEncode, Fv.uintBytes_size, List.getElem?_append_right] at h15
  split at h15 <;> simp_all
