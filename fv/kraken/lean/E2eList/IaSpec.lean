import E2e.Spec
import E2e.SpecEq
import E2eAd.Spec
import Fk.LuErr
import EthLib.Serialization.Proofs.Ssz.Codec.Table
import EthLib.Serialization.Proofs.Ssz.Codec.CanonicalTable
import E2eList.DefsIa

/-!
# Spec bridge for the real Prysm `v1alpha1.IndexedAttestation` (LV T3)

The order of `DdSpec.lean` / `SaSpec.lean` with one variable field. The list part reuses the Go 1.26.3 ListU64 lemmas
(`Fv1.serializeEach_u64`, `Fv1.inl_*`, `Fv1.luElems`, `Fv1.u64Bytes_luElems`, `Fv1.allFit_u64(_inv)`); the data part
reuses `E2e.pad_*` (AttestationData). `iaChecks` are the four checks of the Go decoder in its order.
-/

namespace E2eList
open EthLib.Serialization.Ssz Fv1

theorem prysmIaDesc_wellFormed : prysmIaDesc.wellFormed = .ok () := by rfl

theorem iaOff_toArray : iaOff.toArray = uintBytes 4 228 := by decide

theorem pia_enc_size (g : PIa) : (piaEnc g).size = 228 + 8 * g.idx.length := by
  simp [piaEnc, iaOff, E2e.pad_enc_size, u64Bytes_size]; omega

theorem pia_toValue_fits (g : PIa) : Value.fits prysmIaDesc g.toValue = true := by
  have h1 := E2e.pad_toValue_fits g.data
  have h2 := g.hidx
  simp only [prysmIaDesc, PIa.toValue, Value.fits, Value.fieldsFit] at *
  simp [h1, allFit_u64, h2]

theorem pia_toValue_surjective (v : Value) (h : Value.fits prysmIaDesc v = true) : ∃ g : PIa, g.toValue = v := by
  obtain ⟨vs, rfl, hf⟩ := fits_container h
  have hl := fieldsFit_length hf
  match vs, hl with
  | [v0, v1, v2], _ =>
    simp only [fieldsFit_cons] at hf
    obtain ⟨h0, h1, h2, -⟩ := hf
    obtain ⟨es, rfl, hlen, hall⟩ : ∃ es, v0 = .seq es ∧ es.length ≤ 2048 ∧ Value.allFit (.uint 8) es = true := by
      cases v0 <;> simp [Value.fits] at h0 ⊢; exact h0
    obtain ⟨l, rfl⟩ := allFit_u64_inv es hall
    obtain ⟨d, rfl⟩ := E2e.pad_toValue_surjective v1 h1
    obtain ⟨z, rfl, hz⟩ : ∃ d, v2 = .bytes d ∧ d.size = 96 := by
      cases v2 <;> simp [Value.fits] at h2 ⊢; exact h2
    exact ⟨⟨l, by simpa using hlen, d, ⟨z, hz⟩⟩, rfl⟩

/-- **`serialize g = offset 228 ‖ data ‖ signature ‖ indices`.** -/
theorem pia_serialize (g : PIa) : serialize prysmIaDesc g.toValue = .ok (piaEnc g) := by
  obtain ⟨l, hl, d, ⟨z, hz⟩⟩ := g
  have hd := E2e.pad_serialize d
  have hds := E2e.pad_enc_size d
  have h32 : 228 + 8 * l.length < 2 ^ (8 * bytesPerOffset) := by simp [bytesPerOffset]; omega
  simp only [prysmIaDesc, PIa.toValue, serialize, serializeStruct, serializeFields, serializeSequence,
    List.length_map, hl, decide_true, if_true, serializeEach_u64, Vector.toArray_mk, hz]
  rw [hd]
  simp only [bind, Except.bind, pure, Except.pure, assemble, Desc.isFixed, Desc.fixedSize, Option.isSome_some]
  simp only [inl_headWidth, inl_bodyWidth, inl_headOf, inl_bodiesOf]
  have h4 : ¬ (4294967296 ≤ 228 + 8 * l.length) := by simp [bytesPerOffset] at h32; omega
  have h8 : ¬ (4294967296 ≤ 8 * l.length) := by omega
  have f1 : ((Desc.uint 8).list 2048).isFixed = false := rfl
  have f2 : (Desc.container ["slot", "index", "beacon_block_root", "source", "target"]
      [Desc.uint 8, Desc.uint 8, Desc.byteVector 32, Desc.container ["epoch", "root"] [Desc.uint 8, Desc.byteVector 32],
        Desc.container ["epoch", "root"] [Desc.uint 8, Desc.byteVector 32]]).isFixed = true := rfl
  have f3 : (Desc.byteVector 96).isFixed = true := rfl
  have f4 : E2e.prysmAdDesc.isFixed = true := rfl
  simp (config := {decide := true}) [bodyWidth, headOf, bodiesOf, headWidth, u64Bytes_size, h4, h8, bytesPerOffset,
    piaEnc, hds, hz, iaOff_toArray, Array.append_assoc, f1, f2, f3, f4]

/-- **Spec roundtrip.** -/
theorem pia_roundtrip (g : PIa) : deserialize prysmIaDesc (piaEnc g) = .ok g.toValue :=
  deserialize_enc (G := PIa) (toV := PIa.toValue) (enc := piaEnc) prysmIaDesc_wellFormed pia_serialize
    pia_toValue_fits g

theorem pia_accepted_is_enc {bs : Array UInt8} {v : Value} (h : deserialize prysmIaDesc bs = .ok v) :
    ∃ g : PIa, v = g.toValue ∧ bs = piaEnc g :=
  accepted_is_enc (G := PIa) (toV := PIa.toValue) (enc := piaEnc) prysmIaDesc_wellFormed pia_serialize
    pia_toValue_surjective h

/-- The four checks of the Go decoder, in its order. -/
def iaChecks (bs : Array UInt8) : Prop :=
  228 ≤ bs.size ∧ bs.toList.take 4 = iaOff ∧ (bs.size - 228) % 8 = 0 ∧ (bs.size - 228) / 8 ≤ 2048

theorem piaEnc_checks (g : PIa) : iaChecks (piaEnc g) := by
  have hs := pia_enc_size g
  have hl := g.hidx
  refine ⟨by omega, ?_, by omega, by omega⟩
  simp [piaEnc, iaOff]

theorem ia_checks_enc (bs : Array UInt8) (h : iaChecks bs) : ∃ g : PIa, bs = piaEnc g := by
  obtain ⟨h228, hoff, hmod, hn⟩ := h
  obtain ⟨n, hndef⟩ : ∃ n, n = (bs.size - 228) / 8 := ⟨_, rfl⟩
  have hsz : bs.size = 228 + 8 * n := by omega
  obtain ⟨vd, hvd⟩ := (E2e.pad_spec_accepts_iff (bs.extract 4 132)).mpr (by simp; omega)
  obtain ⟨d, -, hd⟩ := E2e.pad_accepted_is_enc hvd
  refine ⟨⟨luElems bs 228 n, by simp [luElems_length]; omega, d, ⟨bs.extract 132 228, by simp; omega⟩⟩, ?_⟩
  have h4 : bs.extract 0 4 = iaOff.toArray := by
    apply Array.toList_inj.mp
    simp only [Array.toList_extract, List.extract, Nat.sub_zero, List.drop_zero, hoff]
  have e0 : bs.extract 0 4 ++ bs.extract 4 132 = bs.extract 0 132 := extract_join bs (by omega) (by omega)
  have e1 : bs.extract 0 132 ++ bs.extract 132 228 = bs.extract 0 228 := extract_join bs (by omega) (by omega)
  have e2 : bs.extract 0 228 ++ bs.extract 228 (228 + 8 * n) = bs.extract 0 bs.size := by
    rw [extract_join bs (by omega) (by omega), ← hsz]
  simp only [piaEnc, ← h4, ← hd, u64Bytes_luElems bs n 228 (by omega)]
  rw [e0, e1, e2]; simp

/-- **EthLib accepts exactly the inputs that pass the four checks.** -/
theorem pia_spec_accepts_iff (bs : Array UInt8) : (∃ v, deserialize prysmIaDesc bs = .ok v) ↔ iaChecks bs := by
  constructor
  · rintro ⟨v, hd⟩
    obtain ⟨g, rfl, rfl⟩ := pia_accepted_is_enc hd
    exact piaEnc_checks g
  · intro h
    obtain ⟨g, rfl⟩ := ia_checks_enc bs h
    exact ⟨_, pia_roundtrip g⟩

/-- A failing check makes EthLib reject. -/
theorem pia_spec_rejects (bs : Array UInt8) (h : ¬ iaChecks bs) : ∃ e, deserialize prysmIaDesc bs = .error e := by
  cases hd : deserialize prysmIaDesc bs with
  | error e => exact ⟨e, rfl⟩
  | ok v => exact absurd ((pia_spec_accepts_iff bs).mp ⟨v, hd⟩) h

end E2eList
