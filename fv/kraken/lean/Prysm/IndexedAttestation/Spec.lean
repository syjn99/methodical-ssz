import Prysm.Checkpoint.Spec
import Prysm.Checkpoint.SpecEquivalence
import Prysm.AttestationData.Spec
import Codec.ReadUint64List
import EthLib.Serialization.Proofs.Ssz.Codec.Table
import EthLib.Serialization.Proofs.Ssz.Codec.CanonicalTable
import Prysm.IndexedAttestation.SpecDefinitions

/-!
# Spec bridge for the real Prysm `v1alpha1.IndexedAttestation`

The order of `Prysm/Deposit_Data/Spec.lean` / `Prysm/SyncAggregate/Spec.lean` with one variable field. The list part reuses the Go 1.26.3 ListU64 lemmas
(`Spec.serializeEach_u64`, `Spec.inlineParts_*`, `Codec.readUint64List`, `Codec.u64Bytes_readUint64List`, `Spec.allFit_u64(_inv)`); the data part
reuses `Prysm.AttestationData.SszValue.*`. `decodeChecks` are the four checks of the Go decoder in its order.
-/

namespace Prysm.IndexedAttestation
open EthLib.Serialization.Ssz Spec

theorem desc_wellFormed : desc.wellFormed = .ok () := by rfl

theorem offsetBytes_toArray : offsetBytes.toArray = uintBytes 4 228 := by decide

theorem encode_size (g : SszValue) : (SszValue.encode g).size = 228 + 8 * g.idx.length := by
  simp [SszValue.encode, offsetBytes, Prysm.AttestationData.SszValue.encode_size, u64Bytes_size]; omega

theorem toValue_fits (g : SszValue) : Value.fits desc g.toValue = true := by
  have h1 := Prysm.AttestationData.SszValue.toValue_fits g.data
  have h2 := g.hidx
  simp only [desc, SszValue.toValue, Value.fits, Value.fieldsFit] at *
  simp [h1, allFit_u64, h2]

theorem toValue_surjective (v : Value) (h : Value.fits desc v = true) : ∃ g : SszValue, g.toValue = v := by
  obtain ⟨vs, rfl, hf⟩ := fits_container h
  have hl := fieldsFit_length hf
  match vs, hl with
  | [v0, v1, v2], _ =>
    simp only [fieldsFit_cons] at hf
    obtain ⟨h0, h1, h2, -⟩ := hf
    obtain ⟨es, rfl, hlen, hall⟩ : ∃ es, v0 = .seq es ∧ es.length ≤ 2048 ∧ Value.allFit (.uint 8) es = true := by
      cases v0 <;> simp [Value.fits] at h0 ⊢; exact h0
    obtain ⟨l, rfl⟩ := allFit_u64_inv es hall
    obtain ⟨d, rfl⟩ := Prysm.AttestationData.SszValue.toValue_surjective v1 h1
    obtain ⟨z, rfl, hz⟩ : ∃ d, v2 = .bytes d ∧ d.size = 96 := by
      cases v2 <;> simp [Value.fits] at h2 ⊢; exact h2
    exact ⟨⟨l, by simpa using hlen, d, ⟨z, hz⟩⟩, rfl⟩

/-- **`serialize g = offset 228 ‖ data ‖ signature ‖ indices`.** -/
theorem toValue_serialize (g : SszValue) : serialize desc g.toValue = .ok (SszValue.encode g) := by
  obtain ⟨l, hl, d, ⟨z, hz⟩⟩ := g
  have hd := Prysm.AttestationData.SszValue.serialize_eq d
  have hds := Prysm.AttestationData.SszValue.encode_size d
  have h32 : 228 + 8 * l.length < 2 ^ (8 * bytesPerOffset) := by simp [bytesPerOffset]; omega
  simp only [desc, SszValue.toValue, serialize, serializeStruct, serializeFields, serializeSequence,
    List.length_map, hl, decide_true, if_true, serializeEach_u64, Vector.toArray_mk, hz]
  rw [hd]
  simp only [bind, Except.bind, pure, Except.pure, assemble, Desc.isFixed, Desc.fixedSize, Option.isSome_some]
  simp only [inlineParts_headWidth, inlineParts_bodyWidth, inlineParts_headOf, inlineParts_bodiesOf]
  have h4 : ¬ (4294967296 ≤ 228 + 8 * l.length) := by simp [bytesPerOffset] at h32; omega
  have h8 : ¬ (4294967296 ≤ 8 * l.length) := by omega
  have f1 : ((Desc.uint 8).list 2048).isFixed = false := rfl
  have f2 : (Desc.container ["slot", "index", "beacon_block_root", "source", "target"]
      [Desc.uint 8, Desc.uint 8, Desc.byteVector 32, Desc.container ["epoch", "root"] [Desc.uint 8, Desc.byteVector 32],
        Desc.container ["epoch", "root"] [Desc.uint 8, Desc.byteVector 32]]).isFixed = true := rfl
  have f3 : (Desc.byteVector 96).isFixed = true := rfl
  have f4 : Prysm.AttestationData.desc.isFixed = true := rfl
  simp (config := {decide := true}) [bodyWidth, headOf, bodiesOf, headWidth, u64Bytes_size, h4, h8, bytesPerOffset,
    SszValue.encode, hds, hz, offsetBytes_toArray, Array.append_assoc, f1, f2, f3, f4]

/-- **Spec roundtrip.** -/
theorem encode_roundtrip (g : SszValue) : deserialize desc (SszValue.encode g) = .ok g.toValue :=
  deserialize_encoding (G := SszValue) (toV := SszValue.toValue) (enc := SszValue.encode) desc_wellFormed toValue_serialize
    toValue_fits g

theorem accepted_is_encode {bs : Array UInt8} {v : Value} (h : deserialize desc bs = .ok v) :
    ∃ g : SszValue, v = g.toValue ∧ bs = SszValue.encode g :=
  accepted_input_is_encoding (G := SszValue) (toV := SszValue.toValue) (enc := SszValue.encode) desc_wellFormed toValue_serialize
    toValue_surjective h

/-- The four checks of the Go decoder, in its order. -/
def decodeChecks (bs : Array UInt8) : Prop :=
  228 ≤ bs.size ∧ bs.toList.take 4 = offsetBytes ∧ (bs.size - 228) % 8 = 0 ∧ (bs.size - 228) / 8 ≤ 2048

theorem encode_decodeChecks (g : SszValue) : decodeChecks (SszValue.encode g) := by
  have hs := encode_size g
  have hl := g.hidx
  refine ⟨by omega, ?_, by omega, by omega⟩
  simp [SszValue.encode, offsetBytes]

theorem decodeChecks_encode (bs : Array UInt8) (h : decodeChecks bs) : ∃ g : SszValue, bs = SszValue.encode g := by
  obtain ⟨h228, hoff, hmod, hn⟩ := h
  obtain ⟨n, hndef⟩ : ∃ n, n = (bs.size - 228) / 8 := ⟨_, rfl⟩
  have hsz : bs.size = 228 + 8 * n := by omega
  obtain ⟨vd, hvd⟩ := (Prysm.AttestationData.SszValue.spec_accepts_iff (bs.extract 4 132)).mpr (by simp; omega)
  obtain ⟨d, -, hd⟩ := Prysm.AttestationData.SszValue.accepted_is_encoding hvd
  refine ⟨⟨Codec.readUint64List bs 228 n, by simp [Codec.readUint64List_length]; omega, d, ⟨bs.extract 132 228, by simp; omega⟩⟩, ?_⟩
  have h4 : bs.extract 0 4 = offsetBytes.toArray := by
    apply Array.toList_inj.mp
    simp only [Array.toList_extract, List.extract, Nat.sub_zero, List.drop_zero, hoff]
  have e0 : bs.extract 0 4 ++ bs.extract 4 132 = bs.extract 0 132 := extract_join bs (by omega) (by omega)
  have e1 : bs.extract 0 132 ++ bs.extract 132 228 = bs.extract 0 228 := extract_join bs (by omega) (by omega)
  have e2 : bs.extract 0 228 ++ bs.extract 228 (228 + 8 * n) = bs.extract 0 bs.size := by
    rw [extract_join bs (by omega) (by omega), ← hsz]
  simp only [SszValue.encode, ← h4, ← hd, Codec.u64Bytes_readUint64List bs n 228 (by omega)]
  rw [e0, e1, e2]; simp

/-- **EthLib accepts exactly the inputs that pass the four checks.** -/
theorem spec_accepts_iff (bs : Array UInt8) : (∃ v, deserialize desc bs = .ok v) ↔ decodeChecks bs := by
  constructor
  · rintro ⟨v, hd⟩
    obtain ⟨g, rfl, rfl⟩ := accepted_is_encode hd
    exact encode_decodeChecks g
  · intro h
    obtain ⟨g, rfl⟩ := decodeChecks_encode bs h
    exact ⟨_, encode_roundtrip g⟩

/-- A failing check makes EthLib reject. -/
theorem spec_rejects (bs : Array UInt8) (h : ¬ decodeChecks bs) : ∃ e, deserialize desc bs = .error e := by
  cases hd : deserialize desc bs with
  | error e => exact ⟨e, rfl⟩
  | ok v => exact absurd ((spec_accepts_iff bs).mp ⟨v, hd⟩) h

end Prysm.IndexedAttestation
