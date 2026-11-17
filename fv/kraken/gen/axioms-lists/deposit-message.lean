import Prysm.DepositMessage.Spec
import Prysm.DepositMessage.DecodeSpec
import Prysm.DepositMessage.WitnessGeneratedDecodeAccept
import Prysm.DepositMessage.WitnessGeneratedDecodeRejectSize
import Prysm.DepositMessage.GeneratedDecodeAccept
import Prysm.DepositMessage.Code
import Prysm.DepositMessage.GeneratedEncodeFastPath
import Prysm.DepositMessage.GeneratedEncodeFastPathSpec
import Prysm.DepositMessage.WitnessGeneratedEncodeFastPath

/-! Hand list of the `DepositMessage` declarations for `gen/checks/axioms_gate.py`.
Each name must be in the declaration dump and use only the standard axioms. -/

#print axioms Prysm.DepositMessage.desc_wellFormed
#print axioms Prysm.DepositMessage.desc_fixedSize
#print axioms Prysm.DepositMessage.desc_serialize_checker
#print axioms Prysm.DepositMessage.SszValue.encode_size
#print axioms Prysm.DepositMessage.SszValue.toValue_fits
#print axioms Prysm.DepositMessage.SszValue.toValue_injective
#print axioms Prysm.DepositMessage.SszValue.toValue_surjective'
#print axioms Prysm.DepositMessage.SszValue.serialize_eq
#print axioms Prysm.DepositMessage.SszValue.roundtrip
#print axioms Prysm.DepositMessage.SszValue.accepted_is_encoding
#print axioms Prysm.DepositMessage.SszValue.spec_accepts_iff
#print axioms Prysm.DepositMessage.SszValue.spec_rejects
#print axioms Prysm.DepositMessage.checker_wellFormed
#print axioms Prysm.DepositMessage.SszValue.serialize_eq_checker
#print axioms Prysm.DepositMessage.SszValue.toValue_fits_checker
#print axioms Prysm.DepositMessage.desc_deserialize_checker
#print axioms Prysm.DepositMessage.Decode.accept_spec
#print axioms Prysm.DepositMessage.Decode.reject_size_spec
#print axioms Prysm.DepositMessage.Decode.reject_complete
#print axioms Prysm.DepositMessage.Witness.GeneratedDecodeAccept.program_length
#print axioms Prysm.DepositMessage.Witness.GeneratedDecodeAccept.host_program_eq
#print axioms Prysm.DepositMessage.Witness.GeneratedDecodeAccept.placed_at_9
#print axioms Prysm.DepositMessage.Witness.GeneratedDecodeAccept.placed_at_118
#print axioms Prysm.DepositMessage.Witness.GeneratedDecodeAccept.placed_at_124
#print axioms Prysm.DepositMessage.Witness.GeneratedDecodeAccept.labels_fresh_at_9
#print axioms Prysm.DepositMessage.Witness.GeneratedDecodeAccept.labels_fresh_at_124
#print axioms Prysm.DepositMessage.Witness.GeneratedDecodeAccept.labels_fresh_at_118
#print axioms Prysm.DepositMessage.Witness.GeneratedDecodeAccept.label_bump_pointer
#print axioms Prysm.DepositMessage.Witness.GeneratedDecodeAccept.label_write_barrier
#print axioms Prysm.DepositMessage.Witness.GeneratedDecodeAccept.lift_heap
#print axioms Prysm.DepositMessage.Witness.GeneratedDecodeAccept.runs
#print axioms Prysm.DepositMessage.Witness.GeneratedDecodeRejectSize.program_length
#print axioms Prysm.DepositMessage.Witness.GeneratedDecodeRejectSize.placed_at_1
#print axioms Prysm.DepositMessage.Witness.GeneratedDecodeRejectSize.labels_fresh_at_1
#print axioms Prysm.DepositMessage.Witness.GeneratedDecodeRejectSize.label_err_size
#print axioms Prysm.DepositMessage.Witness.GeneratedDecodeRejectSize.runs
#print axioms Prysm.DepositMessage.Decode.generated_PublicKey_segment
#print axioms Prysm.DepositMessage.Decode.generated_PublicKey_segment_kind
#print axioms Prysm.DepositMessage.Decode.generated_WithdrawalCredentials_segment
#print axioms Prysm.DepositMessage.Decode.generated_WithdrawalCredentials_segment_kind
#print axioms Prysm.DepositMessage.Decode.generated_accept
#print axioms Prysm.DepositMessage.Decode.generated_accept_kind
#print axioms Prysm.DepositMessage.Decode.generated_epilogue
#print axioms Prysm.DepositMessage.Decode.generated_epilogue_kind
#print axioms Prysm.DepositMessage.Decode.generated_field_1
#print axioms Prysm.DepositMessage.Decode.generated_field_1_kind
#print axioms Prysm.DepositMessage.Decode.generated_field_2
#print axioms Prysm.DepositMessage.Decode.generated_field_2_kind
#print axioms Prysm.DepositMessage.Decode.generated_field_3
#print axioms Prysm.DepositMessage.Decode.generated_field_3_kind
#print axioms Prysm.DepositMessage.Decode.generated_head
#print axioms Prysm.DepositMessage.Decode.generated_head_kind
#print axioms Prysm.DepositMessage.Decode.generated_reject
#print axioms Prysm.DepositMessage.Decode.generated_reject_kind
#print axioms Prysm.DepositMessage.Decode.generated_directive_37
#print axioms Prysm.DepositMessage.Decode.generated_directive_37_kind
#print axioms Prysm.DepositMessage.Decode.generated_directive_38
#print axioms Prysm.DepositMessage.Decode.generated_directive_38_kind
#print axioms Prysm.DepositMessage.Decode.generated_directive_45
#print axioms Prysm.DepositMessage.Decode.generated_directive_45_kind
#print axioms Prysm.DepositMessage.Decode.generated_directive_46
#print axioms Prysm.DepositMessage.Decode.generated_directive_46_kind
#print axioms Prysm.DepositMessage.Decode.generated_directive_73
#print axioms Prysm.DepositMessage.Decode.generated_directive_73_kind
#print axioms Prysm.DepositMessage.Decode.generated_directive_74
#print axioms Prysm.DepositMessage.Decode.generated_directive_74_kind
#print axioms Prysm.DepositMessage.Decode.generated_directive_81
#print axioms Prysm.DepositMessage.Decode.generated_directive_81_kind
#print axioms Prysm.DepositMessage.Decode.generated_directive_82
#print axioms Prysm.DepositMessage.Decode.generated_directive_82_kind
#print axioms Prysm.DepositMessage.Decode.generated_directive_83
#print axioms Prysm.DepositMessage.Decode.generated_directive_83_kind
#print axioms Prysm.DepositMessage.Decode.generated_directive_84
#print axioms Prysm.DepositMessage.Decode.generated_directive_84_kind
#print axioms Prysm.DepositMessage.Decode.generated_directive_85
#print axioms Prysm.DepositMessage.Decode.generated_directive_85_kind
#print axioms Prysm.DepositMessage.Code.marshalSSZTo
#print axioms Prysm.DepositMessage.Encode.generated_epilogue
#print axioms Prysm.DepositMessage.Encode.generated_epilogue_kind
#print axioms Prysm.DepositMessage.Encode.generated_field_0
#print axioms Prysm.DepositMessage.Encode.generated_field_0_kind
#print axioms Prysm.DepositMessage.Encode.generated_field_1
#print axioms Prysm.DepositMessage.Encode.generated_field_1_kind
#print axioms Prysm.DepositMessage.Encode.generated_field_2
#print axioms Prysm.DepositMessage.Encode.generated_field_2_kind
#print axioms Prysm.DepositMessage.Encode.generated_fast
#print axioms Prysm.DepositMessage.Encode.generated_fast_kind
#print axioms Prysm.DepositMessage.Encode.generated_head
#print axioms Prysm.DepositMessage.Encode.generated_head_kind
#print axioms Prysm.DepositMessage.Encode.generated_layout
#print axioms Prysm.DepositMessage.SszValue.encode_toList_generated
#print axioms Prysm.DepositMessage.Encode.generated_fast_spec
#print axioms Prysm.DepositMessage.Encode.generated_fast_split
#print axioms Prysm.DepositMessage.Witness.GeneratedEncodeFastPath.program
#print axioms Prysm.DepositMessage.Witness.GeneratedEncodeFastPath.program_length
#print axioms Prysm.DepositMessage.Witness.GeneratedEncodeFastPath.block
#print axioms Prysm.DepositMessage.Witness.GeneratedEncodeFastPath.initial_state
#print axioms Prysm.DepositMessage.Witness.GeneratedEncodeFastPath.runs_empty
#print axioms Prysm.DepositMessage.Witness.GeneratedEncodeFastPath.runs_prefix
#print axioms Prysm.DepositMessage.Witness.GeneratedEncodeFastPath.labels_fresh_at_0
#print axioms Prysm.DepositMessage.Witness.GeneratedEncodeFastPath.labels_fresh_copy_model
#print axioms Prysm.DepositMessage.Witness.GeneratedEncodeFastPath.placed_at_0
#print axioms Prysm.DepositMessage.Witness.GeneratedEncodeFastPath.placed_copy_model
#print axioms Prysm.DepositMessage.Witness.GeneratedEncodeFastPath.host
#print axioms Prysm.DepositMessage.Witness.GeneratedEncodeFastPath.mem
#print axioms Prysm.DepositMessage.Witness.GeneratedEncodeFastPath.word_bytes
#print axioms Prysm.DepositMessage.Witness.GeneratedEncodeFastPath.zeros
