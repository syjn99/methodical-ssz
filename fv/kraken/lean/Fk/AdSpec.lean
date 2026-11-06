import Fk.CpSpec

/-!
# Prysm AttestationData: size, length reject, EthLib acceptance

- `ad_size_main`: SizeSSZ returns 128.
- `ad_reject_size_main`: `len(buf) ≠ 128` → `ssz.ErrSize`.
-/

open Fk Fk.Code Fv1 EthLib.Serialization.Ssz
variable [Host]

theorem ad_size_main (k : Nat) (hk : PrysmAttestationDataSizeSSZ.IsInfixAt Host.prog k) (s : MachineData) (ra : UInt64)
    (R : DataMem → Prop) (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 128 ∧ st.data.regs.rsp = s.regs.rsp + 8
        ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem ⊢
  kat hk PrysmAttestationDataSizeSSZ 0
  kat hk PrysmAttestationDataSizeSSZ 1
  kat hk PrysmAttestationDataSizeSSZ 2
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl | (apply UInt64.toBitVec_inj.mp; simp)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem ad_reject_size_main (k : Nat) (hk : PrysmAttestationDataUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh PrysmAttestationDataUnmarshalSSZ k)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp slot : List UInt8) (hfp : fp.length = 8) (hsl : slot.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrSize").toBitVec)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx ≠ 128) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; simp only [UInt64.size] at *
  kat hk PrysmAttestationDataUnmarshalSSZ 0
  kat hk PrysmAttestationDataUnmarshalSSZ 1
  kat hk PrysmAttestationDataUnmarshalSSZ 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 3
  split
  · rename_i h; exfalso
    simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk PrysmAttestationDataUnmarshalSSZ 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 5
  kat hk PrysmAttestationDataUnmarshalSSZ 6
  kat hk PrysmAttestationDataUnmarshalSSZ 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ slot _ _ (by bv_omega) (by ecancel) (by exact hsl)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 8
  kat hk PrysmAttestationDataUnmarshalSSZ 9
  kat hk PrysmAttestationDataUnmarshalSSZ 10
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    apply hlen; apply UInt64.toBitVec_inj.mp; apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this ⊢; omega
  simp only [Effects.All]
  klabel hk hf PrysmAttestationDataUnmarshalSSZ 168
  kat hk PrysmAttestationDataUnmarshalSSZ 168
  kat hk PrysmAttestationDataUnmarshalSSZ 169
  apply load_step _ _ _ _ (Int.toBytes 8 e0.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 170
  apply load_step _ _ _ _ (Int.toBytes 8 e1.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 171
  kat hk PrysmAttestationDataUnmarshalSSZ 172
  rw [show (40 : BitVec 64) + (rsp.toBitVec - 8#64 - 40) = rsp.toBitVec - 8 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 173
  rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_⟩
  · first | trivial | rfl | (apply UInt64.toBitVec_inj.mp; simp)
  · first | trivial | rfl | (apply UInt64.toBitVec_inj.mp; simp)
  · apply UInt64.toBitVec_inj.mp; simp
  · first | trivial | rfl
  · exact sep_true (by ecancel)


theorem ad_toValue_surjective' (v : Value) (h : Value.fits adDesc v = true) : ∃ g : AttestationDataG, g.toValue = v :=
  ad_toValue_surjective v h

theorem cp_of_bytes (bs : Array UInt8) (o : Nat) (h : o + 40 ≤ bs.size) :
    ∃ c : CheckpointG, cpEncode c = bs.extract o (o + 40) := by
  have r8 := readUint_lt bs o 8
  simp only [Nat.reducePow, Nat.reduceMul] at r8
  refine ⟨⟨UInt64.ofNat (readUint bs o 8), ⟨bs.extract (o + 8) (o + 40), by simp; omega⟩⟩, ?_⟩
  simp only [cpEncode, UInt64.toNat_ofNat_of_lt' r8, uintBytes_readUint_slice bs o 8 (by omega)]
  rw [Array.extract_append_extract, Nat.min_eq_left (by omega), Nat.max_eq_right (by omega)]

/-- EthLib accepts exactly the 128-byte inputs. -/
theorem ad_spec_accepts_iff (bs : Array UInt8) : (∃ v, deserialize adDesc bs = .ok v) ↔ bs.size = 128 := by
  constructor
  · rintro ⟨v, hd⟩
    obtain ⟨g, rfl, rfl⟩ := accepted_is_enc (G := AttestationDataG) (toV := AttestationDataG.toValue)
      (enc := adEncode) adDesc_wellFormed ad_serialize ad_toValue_surjective' hd
    exact ad_encode_size g
  · intro h
    have r0 := readUint_lt bs 0 8; have r1 := readUint_lt bs 8 8
    simp only [Nat.reducePow, Nat.reduceMul] at r0 r1
    obtain ⟨s, hs⟩ := cp_of_bytes bs 48 (by omega)
    obtain ⟨t, ht⟩ := cp_of_bytes bs 88 (by omega)
    let g : AttestationDataG := ⟨UInt64.ofNat (readUint bs 0 8), UInt64.ofNat (readUint bs 8 8),
      ⟨bs.extract 16 48, by simp; omega⟩, s, t⟩
    have e : bs = adEncode g := by
      simp only [g, adEncode, UInt64.toNat_ofNat_of_lt' r0, UInt64.toNat_ofNat_of_lt' r1, hs, ht,
        uintBytes_readUint_slice bs 0 8 (by omega), uintBytes_readUint_slice bs 8 8 (by omega)]
      simp only [Nat.zero_add, Nat.reduceAdd]
      simp (config := {decide := true}) only [Array.extract_append_extract, Nat.min_def, Nat.max_def, ↓reduceIte]
      rw [← h]; simp
    rw [e]
    exact ⟨_, deserialize_enc (G := AttestationDataG) (toV := AttestationDataG.toValue) (enc := adEncode)
      adDesc_wellFormed ad_serialize ad_toValue_fits g⟩

/-- `len(buf) ≠ 128`: EthLib rejects (the machine: `ad_reject_size_main`). -/
theorem ad_reject_size_spec (bs : Array UInt8) (h : bs.size ≠ 128) : ∃ e, deserialize adDesc bs = .error e := by
  cases hd : deserialize adDesc bs with
  | error e => exact ⟨e, rfl⟩
  | ok v => exact absurd ((ad_spec_accepts_iff bs).mp ⟨v, hd⟩) h

open Fv1 EthLib.Serialization.Ssz in
/-- Round trip at the EthLib level. -/
theorem ad_roundtrip (g : AttestationDataG) :
    deserialize adDesc (adEncode g) = .ok g.toValue ∧ ∀ g', g'.toValue = g.toValue → g' = g :=
  ⟨deserialize_enc adDesc_wellFormed ad_serialize ad_toValue_fits g,
   fun g' h => ad_toValue_injective g' g h⟩
