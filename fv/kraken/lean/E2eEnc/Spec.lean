import E2e.Spec
import EthLib.Serialization.Proofs.Ssz.Codec.Table
import E2eEnc.StmtEnc

/-!
# Spec bridge for the real Prysm `v1alpha1.DataColumnsByRootIdentifier` (ENC)

The order of `E2eList/IaSpec.lean` (`pia_serialize`): the list part reuses the Go 1.26.3 ListU64 lemmas
(`Fv1.serializeEach_u64`, `Fv1.inl_*`, `Fv1.u64Bytes_size`). `pdc_serialize`: EthLib's `serialize` of a `PDc` is
`block_root ‖ offset 36 ‖ columns`. The two reject specs are the EthLib side of the machine rejects RB and RT.
-/

namespace E2eEnc
open EthLib.Serialization.Ssz Fv1

theorem dcOff_toArray : dcOff.toArray = uintBytes 4 36 := by decide

theorem pdc_enc_size (g : PDc) : (pdcEnc g).size = 36 + 8 * g.cols.length := by
  simp [pdcEnc, dcOff, u64Bytes_size]; omega

theorem pdc_enc_toList (g : PDc) :
    (pdcEnc g).toList = g.root.toList ++ dcOff ++ (u64Bytes g.cols).toList := by
  simp [pdcEnc]; rfl

/-- **`serialize g = block_root ‖ offset 36 ‖ columns`.** -/
theorem pdc_serialize (g : PDc) : serialize prysmDcDesc g.toValue = .ok (pdcEnc g) := by
  obtain ⟨⟨z, hz⟩, l, hl⟩ := g
  have h32 : 36 + 8 * l.length < 2 ^ (8 * bytesPerOffset) := by simp [bytesPerOffset]; omega
  simp only [prysmDcDesc, PDc.toValue, dcValue, serialize, serializeStruct, serializeFields, serializeSequence,
    List.length_map, hl, ite_true, serializeEach_u64, Vector.toArray_mk, hz]
  simp only [bind, Except.bind, pure, Except.pure, assemble, Desc.isFixed, Desc.fixedSize, Option.isSome_some]
  simp only [inl_headWidth, inl_bodyWidth, inl_headOf, inl_bodiesOf]
  have h4 : ¬ (4294967296 ≤ 36 + 8 * l.length) := by simp [bytesPerOffset] at h32; omega
  have h8 : ¬ (4294967296 ≤ 8 * l.length) := by omega
  have f1 : ((Desc.uint 8).list 128).isFixed = false := rfl
  have f3 : (Desc.byteVector 32).isFixed = true := rfl
  simp (config := {decide := true}) [bodyWidth, headOf, bodiesOf, headWidth, u64Bytes_size, h4, h8, bytesPerOffset,
    pdcEnc, hz, dcOff_toArray, Array.append_assoc, f1, f3]

theorem dc_e2e_spec_reject_bytes : dc_spec_reject_bytes_stmt := by
  intro r cols hr
  simp only [prysmDcDesc, dcValue, serialize, serializeStruct, serializeFields]
  simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw, hr]

theorem dc_e2e_spec_reject_toobig : dc_spec_reject_toobig_stmt := by
  intro r cols hc
  obtain ⟨z, hz⟩ := r
  have hc' : ¬ cols.length ≤ 128 := by omega
  simp only [prysmDcDesc, dcValue, serialize, serializeStruct, serializeFields, Vector.toArray_mk, hz,
    List.length_map, hc', decide_false]
  simp [bind, Except.bind, pure, Except.pure, bytesPerOffset]

end E2eEnc
