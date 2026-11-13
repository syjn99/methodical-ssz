import Prysm.Checkpoint.Spec
import EthLib.Serialization.Proofs.Ssz.Codec.Table
import Prysm.DataColumnsByRootIdentifier.StatementsEncode

/-!
# Spec bridge for the real Prysm `v1alpha1.DataColumnsByRootIdentifier`

The order of `Prysm/IndexedAttestation/Spec.lean` (`pia_serialize`): the list part reuses the Go 1.26.3 ListU64 lemmas
(`Spec.serializeEach_u64`, `Spec.inl_*`, `Spec.u64Bytes_size`). `toValue_serialize`: EthLib's `serialize` of a `SszValue` is
`block_root ‖ offset 36 ‖ columns`. The two reject specs are the EthLib side of the machine bytes-length reject and too-big reject.
-/

namespace Prysm.DataColumnsByRootIdentifier
open EthLib.Serialization.Ssz Spec

theorem offsetBytes_toArray : offsetBytes.toArray = uintBytes 4 36 := by decide

theorem encode_size (g : SszValue) : (SszValue.encode g).size = 36 + 8 * g.cols.length := by
  simp [SszValue.encode, offsetBytes, u64Bytes_size]; omega

theorem encode_toList (g : SszValue) :
    (SszValue.encode g).toList = g.root.toList ++ offsetBytes ++ (u64Bytes g.cols).toList := by
  simp [SszValue.encode]; rfl

/-- **`serialize g = block_root ‖ offset 36 ‖ columns`.** -/
theorem toValue_serialize (g : SszValue) : serialize desc g.toValue = .ok (SszValue.encode g) := by
  obtain ⟨⟨z, hz⟩, l, hl⟩ := g
  have h32 : 36 + 8 * l.length < 2 ^ (8 * bytesPerOffset) := by simp [bytesPerOffset]; omega
  simp only [desc, SszValue.toValue, receiverValue, serialize, serializeStruct, serializeFields, serializeSequence,
    List.length_map, hl, ite_true, serializeEach_u64, Vector.toArray_mk, hz]
  simp only [bind, Except.bind, pure, Except.pure, assemble, Desc.isFixed, Desc.fixedSize, Option.isSome_some]
  simp only [inlineParts_headWidth, inlineParts_bodyWidth, inlineParts_headOf, inlineParts_bodiesOf]
  have h4 : ¬ (4294967296 ≤ 36 + 8 * l.length) := by simp [bytesPerOffset] at h32; omega
  have h8 : ¬ (4294967296 ≤ 8 * l.length) := by omega
  have f1 : ((Desc.uint 8).list 128).isFixed = false := rfl
  have f3 : (Desc.byteVector 32).isFixed = true := rfl
  simp (config := {decide := true}) [bodyWidth, headOf, bodiesOf, headWidth, u64Bytes_size, h4, h8, bytesPerOffset,
    SszValue.encode, hz, offsetBytes_toArray, Array.append_assoc, f1, f3]

theorem Encode.reject_length_spec : Encode.reject_length_spec_statement := by
  intro r cols hr
  simp only [desc, receiverValue, serialize, serializeStruct, serializeFields]
  simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw, hr]

theorem Encode.reject_too_big_spec : Encode.reject_too_big_spec_statement := by
  intro r cols hc
  obtain ⟨z, hz⟩ := r
  have hc' : ¬ cols.length ≤ 128 := by omega
  simp only [desc, receiverValue, serialize, serializeStruct, serializeFields, Vector.toArray_mk, hz,
    List.length_map, hc', decide_false]
  simp [bind, Except.bind, pure, Except.pure, bytesPerOffset]

end Prysm.DataColumnsByRootIdentifier
