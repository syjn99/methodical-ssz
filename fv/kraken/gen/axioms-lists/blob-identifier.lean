import Prysm.BlobIdentifier.Spec
import Prysm.BlobIdentifier.DecodeSpec
import Prysm.BlobIdentifier.WitnessGeneratedDecodeAccept
import Prysm.BlobIdentifier.WitnessGeneratedDecodeRejectSize
import Prysm.BlobIdentifier.GeneratedDecodeAccept
import Prysm.BlobIdentifier.Code
import Prysm.BlobIdentifier.GeneratedEncodeFastPath
import Prysm.BlobIdentifier.GeneratedEncodeFastPathSpec
import Prysm.BlobIdentifier.WitnessGeneratedEncodeFastPath

/-! Hand list of the `BlobIdentifier` declarations for `gen/checks/axioms_gate.py`.
Each name must be in the declaration dump and use only the standard axioms. -/

#print axioms Prysm.BlobIdentifier.desc_checker
#print axioms Prysm.BlobIdentifier.desc_wellFormed
#print axioms Prysm.BlobIdentifier.desc_fixedSize
#print axioms Prysm.BlobIdentifier.desc_serialize_checker
#print axioms Prysm.BlobIdentifier.SszValue.encode_size
#print axioms Prysm.BlobIdentifier.SszValue.toValue_fits
#print axioms Prysm.BlobIdentifier.SszValue.toValue_injective
#print axioms Prysm.BlobIdentifier.SszValue.toValue_surjective
#print axioms Prysm.BlobIdentifier.SszValue.toValue_surjective'
#print axioms Prysm.BlobIdentifier.SszValue.serialize_eq
#print axioms Prysm.BlobIdentifier.SszValue.roundtrip
#print axioms Prysm.BlobIdentifier.SszValue.accepted_is_encoding
#print axioms Prysm.BlobIdentifier.SszValue.spec_accepts_iff
#print axioms Prysm.BlobIdentifier.SszValue.spec_rejects
#print axioms Prysm.BlobIdentifier.checker_wellFormed
#print axioms Prysm.BlobIdentifier.SszValue.serialize_eq_checker
#print axioms Prysm.BlobIdentifier.SszValue.toValue_fits_checker
#print axioms Prysm.BlobIdentifier.desc_deserialize_checker
#print axioms Prysm.BlobIdentifier.Decode.accept_spec
#print axioms Prysm.BlobIdentifier.Decode.reject_size_spec
#print axioms Prysm.BlobIdentifier.Decode.reject_complete
#print axioms Prysm.BlobIdentifier.Witness.GeneratedDecodeAccept.program_length
#print axioms Prysm.BlobIdentifier.Witness.GeneratedDecodeAccept.host_program_eq
#print axioms Prysm.BlobIdentifier.Witness.GeneratedDecodeAccept.placed_at_9
#print axioms Prysm.BlobIdentifier.Witness.GeneratedDecodeAccept.placed_at_81
#print axioms Prysm.BlobIdentifier.Witness.GeneratedDecodeAccept.placed_at_87
#print axioms Prysm.BlobIdentifier.Witness.GeneratedDecodeAccept.labels_fresh_at_9
#print axioms Prysm.BlobIdentifier.Witness.GeneratedDecodeAccept.labels_fresh_at_87
#print axioms Prysm.BlobIdentifier.Witness.GeneratedDecodeAccept.labels_fresh_at_81
#print axioms Prysm.BlobIdentifier.Witness.GeneratedDecodeAccept.label_bump_pointer
#print axioms Prysm.BlobIdentifier.Witness.GeneratedDecodeAccept.label_write_barrier
#print axioms Prysm.BlobIdentifier.Witness.GeneratedDecodeAccept.lift_heap
#print axioms Prysm.BlobIdentifier.Witness.GeneratedDecodeAccept.runs
#print axioms Prysm.BlobIdentifier.Witness.GeneratedDecodeRejectSize.program_length
#print axioms Prysm.BlobIdentifier.Witness.GeneratedDecodeRejectSize.placed_at_1
#print axioms Prysm.BlobIdentifier.Witness.GeneratedDecodeRejectSize.labels_fresh_at_1
#print axioms Prysm.BlobIdentifier.Witness.GeneratedDecodeRejectSize.label_err_size
#print axioms Prysm.BlobIdentifier.Witness.GeneratedDecodeRejectSize.runs
#print axioms Prysm.BlobIdentifier.Decode.generated_BlockRoot_segment
#print axioms Prysm.BlobIdentifier.Decode.generated_BlockRoot_segment_kind
#print axioms Prysm.BlobIdentifier.Decode.generated_accept
#print axioms Prysm.BlobIdentifier.Decode.generated_accept_kind
#print axioms Prysm.BlobIdentifier.Decode.generated_epilogue
#print axioms Prysm.BlobIdentifier.Decode.generated_epilogue_kind
#print axioms Prysm.BlobIdentifier.Decode.generated_field_1
#print axioms Prysm.BlobIdentifier.Decode.generated_field_1_kind
#print axioms Prysm.BlobIdentifier.Decode.generated_field_2
#print axioms Prysm.BlobIdentifier.Decode.generated_field_2_kind
#print axioms Prysm.BlobIdentifier.Decode.generated_head
#print axioms Prysm.BlobIdentifier.Decode.generated_head_kind
#print axioms Prysm.BlobIdentifier.Decode.generated_reject
#print axioms Prysm.BlobIdentifier.Decode.generated_reject_kind
#print axioms Prysm.BlobIdentifier.Decode.generated_directive_37
#print axioms Prysm.BlobIdentifier.Decode.generated_directive_37_kind
#print axioms Prysm.BlobIdentifier.Decode.generated_directive_38
#print axioms Prysm.BlobIdentifier.Decode.generated_directive_38_kind
#print axioms Prysm.BlobIdentifier.Decode.generated_directive_45
#print axioms Prysm.BlobIdentifier.Decode.generated_directive_45_kind
#print axioms Prysm.BlobIdentifier.Decode.generated_directive_46
#print axioms Prysm.BlobIdentifier.Decode.generated_directive_46_kind
#print axioms Prysm.BlobIdentifier.Decode.generated_directive_47
#print axioms Prysm.BlobIdentifier.Decode.generated_directive_47_kind
#print axioms Prysm.BlobIdentifier.Decode.generated_directive_48
#print axioms Prysm.BlobIdentifier.Decode.generated_directive_48_kind
#print axioms Prysm.BlobIdentifier.Decode.generated_directive_49
#print axioms Prysm.BlobIdentifier.Decode.generated_directive_49_kind
#print axioms Prysm.BlobIdentifier.Code.marshalSSZTo
#print axioms Prysm.BlobIdentifier.Encode.generated_epilogue
#print axioms Prysm.BlobIdentifier.Encode.generated_epilogue_kind
#print axioms Prysm.BlobIdentifier.Encode.generated_field_0
#print axioms Prysm.BlobIdentifier.Encode.generated_field_0_kind
#print axioms Prysm.BlobIdentifier.Encode.generated_field_1
#print axioms Prysm.BlobIdentifier.Encode.generated_field_1_kind
#print axioms Prysm.BlobIdentifier.Encode.generated_fast
#print axioms Prysm.BlobIdentifier.Encode.generated_fast_kind
#print axioms Prysm.BlobIdentifier.Encode.generated_head
#print axioms Prysm.BlobIdentifier.Encode.generated_head_kind
#print axioms Prysm.BlobIdentifier.Encode.generated_layout
#print axioms Prysm.BlobIdentifier.SszValue.encode_toList_generated
#print axioms Prysm.BlobIdentifier.Encode.generated_fast_spec
#print axioms Prysm.BlobIdentifier.Encode.generated_fast_split
#print axioms Prysm.BlobIdentifier.Witness.GeneratedEncodeFastPath.program
#print axioms Prysm.BlobIdentifier.Witness.GeneratedEncodeFastPath.program_length
#print axioms Prysm.BlobIdentifier.Witness.GeneratedEncodeFastPath.runs_empty
#print axioms Prysm.BlobIdentifier.Witness.GeneratedEncodeFastPath.runs_prefix
#print axioms Prysm.BlobIdentifier.Witness.GeneratedEncodeFastPath.block
#print axioms Prysm.BlobIdentifier.Witness.GeneratedEncodeFastPath.initial_state
#print axioms Prysm.BlobIdentifier.Witness.GeneratedEncodeFastPath.labels_fresh_at_0
#print axioms Prysm.BlobIdentifier.Witness.GeneratedEncodeFastPath.labels_fresh_copy_model
#print axioms Prysm.BlobIdentifier.Witness.GeneratedEncodeFastPath.placed_at_0
#print axioms Prysm.BlobIdentifier.Witness.GeneratedEncodeFastPath.placed_copy_model
#print axioms Prysm.BlobIdentifier.Witness.GeneratedEncodeFastPath.host
#print axioms Prysm.BlobIdentifier.Witness.GeneratedEncodeFastPath.mem
#print axioms Prysm.BlobIdentifier.Witness.GeneratedEncodeFastPath.word_bytes
#print axioms Prysm.BlobIdentifier.Witness.GeneratedEncodeFastPath.zeros
