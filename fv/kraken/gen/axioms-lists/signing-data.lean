import Prysm.SigningData.GeneratedDecodeAccept
import Prysm.SigningData.Spec
import Prysm.SigningData.DecodeSpec
import Prysm.SigningData.WitnessGeneratedDecodeAccept
import Prysm.SigningData.WitnessGeneratedDecodeRejectSize
import Prysm.SigningData.Code
import Prysm.SigningData.GeneratedEncodeFastPath
import Prysm.SigningData.GeneratedEncodeFastPathSpec
import Prysm.SigningData.WitnessGeneratedEncodeFastPath

/-! Hand list of the `SigningData` declarations for `gen/checks/axioms_gate.py`.
Each name must be in the declaration dump and use only the standard axioms. -/

#print axioms Prysm.SigningData.Decode.generated_Domain_segment
#print axioms Prysm.SigningData.Decode.generated_Domain_segment_kind
#print axioms Prysm.SigningData.Decode.generated_ObjectRoot_segment
#print axioms Prysm.SigningData.Decode.generated_ObjectRoot_segment_kind
#print axioms Prysm.SigningData.Decode.generated_accept
#print axioms Prysm.SigningData.Decode.generated_accept_kind
#print axioms Prysm.SigningData.Decode.generated_epilogue
#print axioms Prysm.SigningData.Decode.generated_epilogue_kind
#print axioms Prysm.SigningData.Decode.generated_field_1
#print axioms Prysm.SigningData.Decode.generated_field_1_kind
#print axioms Prysm.SigningData.Decode.generated_field_2
#print axioms Prysm.SigningData.Decode.generated_field_2_kind
#print axioms Prysm.SigningData.Decode.generated_head
#print axioms Prysm.SigningData.Decode.generated_head_kind
#print axioms Prysm.SigningData.Decode.generated_reject
#print axioms Prysm.SigningData.Decode.generated_reject_kind
#print axioms Prysm.SigningData.Decode.generated_directive_37
#print axioms Prysm.SigningData.Decode.generated_directive_37_kind
#print axioms Prysm.SigningData.Decode.generated_directive_38
#print axioms Prysm.SigningData.Decode.generated_directive_38_kind
#print axioms Prysm.SigningData.Decode.generated_directive_45
#print axioms Prysm.SigningData.Decode.generated_directive_45_kind
#print axioms Prysm.SigningData.Decode.generated_directive_46
#print axioms Prysm.SigningData.Decode.generated_directive_46_kind
#print axioms Prysm.SigningData.Decode.generated_directive_73
#print axioms Prysm.SigningData.Decode.generated_directive_73_kind
#print axioms Prysm.SigningData.Decode.generated_directive_74
#print axioms Prysm.SigningData.Decode.generated_directive_74_kind
#print axioms Prysm.SigningData.Decode.generated_directive_81
#print axioms Prysm.SigningData.Decode.generated_directive_81_kind
#print axioms Prysm.SigningData.Decode.generated_directive_82
#print axioms Prysm.SigningData.Decode.generated_directive_82_kind
#print axioms Prysm.SigningData.desc_checker
#print axioms Prysm.SigningData.desc_deserialize_checker
#print axioms Prysm.SigningData.desc_fixedSize
#print axioms Prysm.SigningData.desc_serialize_checker
#print axioms Prysm.SigningData.desc_wellFormed
#print axioms Prysm.SigningData.SszValue.accepted_is_encoding
#print axioms Prysm.SigningData.SszValue.encode_size
#print axioms Prysm.SigningData.SszValue.roundtrip
#print axioms Prysm.SigningData.SszValue.serialize_eq
#print axioms Prysm.SigningData.SszValue.serialize_eq_checker
#print axioms Prysm.SigningData.SszValue.spec_accepts_iff
#print axioms Prysm.SigningData.SszValue.spec_rejects
#print axioms Prysm.SigningData.SszValue.toValue_fits
#print axioms Prysm.SigningData.SszValue.toValue_fits_checker
#print axioms Prysm.SigningData.SszValue.toValue_injective
#print axioms Prysm.SigningData.SszValue.toValue_surjective
#print axioms Prysm.SigningData.SszValue.toValue_surjective'
#print axioms Prysm.SigningData.checker_wellFormed
#print axioms Prysm.SigningData.Decode.accept_spec
#print axioms Prysm.SigningData.Decode.reject_complete
#print axioms Prysm.SigningData.Decode.reject_size_spec
#print axioms Prysm.SigningData.Witness.GeneratedDecodeAccept.program_length
#print axioms Prysm.SigningData.Witness.GeneratedDecodeAccept.labels_fresh_at_114
#print axioms Prysm.SigningData.Witness.GeneratedDecodeAccept.labels_fresh_at_120
#print axioms Prysm.SigningData.Witness.GeneratedDecodeAccept.labels_fresh_at_9
#print axioms Prysm.SigningData.Witness.GeneratedDecodeAccept.placed_at_114
#print axioms Prysm.SigningData.Witness.GeneratedDecodeAccept.placed_at_120
#print axioms Prysm.SigningData.Witness.GeneratedDecodeAccept.placed_at_9
#print axioms Prysm.SigningData.Witness.GeneratedDecodeAccept.label_bump_pointer
#print axioms Prysm.SigningData.Witness.GeneratedDecodeAccept.label_write_barrier
#print axioms Prysm.SigningData.Witness.GeneratedDecodeAccept.lift_heap
#print axioms Prysm.SigningData.Witness.GeneratedDecodeAccept.host_program_eq
#print axioms Prysm.SigningData.Witness.GeneratedDecodeAccept.runs
#print axioms Prysm.SigningData.Witness.GeneratedDecodeRejectSize.program_length
#print axioms Prysm.SigningData.Witness.GeneratedDecodeRejectSize.labels_fresh_at_1
#print axioms Prysm.SigningData.Witness.GeneratedDecodeRejectSize.placed_at_1
#print axioms Prysm.SigningData.Witness.GeneratedDecodeRejectSize.label_err_size
#print axioms Prysm.SigningData.Witness.GeneratedDecodeRejectSize.runs
#print axioms Prysm.SigningData.Code.marshalSSZTo
#print axioms Prysm.SigningData.Encode.generated_epilogue
#print axioms Prysm.SigningData.Encode.generated_epilogue_kind
#print axioms Prysm.SigningData.Encode.generated_field_0
#print axioms Prysm.SigningData.Encode.generated_field_0_kind
#print axioms Prysm.SigningData.Encode.generated_field_1
#print axioms Prysm.SigningData.Encode.generated_field_1_kind
#print axioms Prysm.SigningData.Encode.generated_fast
#print axioms Prysm.SigningData.Encode.generated_fast_kind
#print axioms Prysm.SigningData.Encode.generated_head
#print axioms Prysm.SigningData.Encode.generated_head_kind
#print axioms Prysm.SigningData.Encode.generated_layout
#print axioms Prysm.SigningData.SszValue.encode_toList_generated
#print axioms Prysm.SigningData.Encode.generated_fast_spec
#print axioms Prysm.SigningData.Encode.generated_fast_split
#print axioms Prysm.SigningData.Witness.GeneratedEncodeFastPath.program
#print axioms Prysm.SigningData.Witness.GeneratedEncodeFastPath.program_length
#print axioms Prysm.SigningData.Witness.GeneratedEncodeFastPath.block
#print axioms Prysm.SigningData.Witness.GeneratedEncodeFastPath.initial_state
#print axioms Prysm.SigningData.Witness.GeneratedEncodeFastPath.labels_fresh_at_0
#print axioms Prysm.SigningData.Witness.GeneratedEncodeFastPath.labels_fresh_copy_model
#print axioms Prysm.SigningData.Witness.GeneratedEncodeFastPath.placed_at_0
#print axioms Prysm.SigningData.Witness.GeneratedEncodeFastPath.placed_copy_model
#print axioms Prysm.SigningData.Witness.GeneratedEncodeFastPath.host
#print axioms Prysm.SigningData.Witness.GeneratedEncodeFastPath.mem
#print axioms Prysm.SigningData.Witness.GeneratedEncodeFastPath.runs_empty
#print axioms Prysm.SigningData.Witness.GeneratedEncodeFastPath.runs_prefix
#print axioms Prysm.SigningData.Witness.GeneratedEncodeFastPath.word_bytes
#print axioms Prysm.SigningData.Witness.GeneratedEncodeFastPath.zeros
