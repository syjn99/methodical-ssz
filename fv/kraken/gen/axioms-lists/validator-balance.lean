import Prysm.ValidatorBalance.GeneratedDecodeAccept
import Prysm.ValidatorBalance.Spec
import Prysm.ValidatorBalance.DecodeSpec
import Prysm.ValidatorBalance.WitnessGeneratedDecodeAccept
import Prysm.ValidatorBalance.WitnessGeneratedDecodeRejectSize
import Prysm.ValidatorBalance.Code
import Prysm.ValidatorBalance.GeneratedEncodeFastPath
import Prysm.ValidatorBalance.GeneratedEncodeFastPathSpec
import Prysm.ValidatorBalance.WitnessGeneratedEncodeFastPath

/-! Hand list of the `ValidatorBalance` declarations for `gen/checks/axioms_gate.py`.
Each name must be in the declaration dump and use only the standard axioms. -/

#print axioms Prysm.ValidatorBalance.Decode.generated_Index_call
#print axioms Prysm.ValidatorBalance.Decode.generated_Index_call_kind
#print axioms Prysm.ValidatorBalance.Decode.generated_accept
#print axioms Prysm.ValidatorBalance.Decode.generated_accept_kind
#print axioms Prysm.ValidatorBalance.Decode.generated_epilogue
#print axioms Prysm.ValidatorBalance.Decode.generated_epilogue_kind
#print axioms Prysm.ValidatorBalance.Decode.generated_field_1
#print axioms Prysm.ValidatorBalance.Decode.generated_field_1_kind
#print axioms Prysm.ValidatorBalance.Decode.generated_field_2
#print axioms Prysm.ValidatorBalance.Decode.generated_field_2_kind
#print axioms Prysm.ValidatorBalance.Decode.generated_head
#print axioms Prysm.ValidatorBalance.Decode.generated_head_kind
#print axioms Prysm.ValidatorBalance.Decode.generated_reject
#print axioms Prysm.ValidatorBalance.Decode.generated_reject_kind
#print axioms Prysm.ValidatorBalance.Decode.generated_directive_14
#print axioms Prysm.ValidatorBalance.Decode.generated_directive_14_kind
#print axioms Prysm.ValidatorBalance.Decode.generated_directive_15
#print axioms Prysm.ValidatorBalance.Decode.generated_directive_15_kind
#print axioms Prysm.ValidatorBalance.Decode.generated_directive_48
#print axioms Prysm.ValidatorBalance.Decode.generated_directive_48_kind
#print axioms Prysm.ValidatorBalance.Decode.generated_directive_49
#print axioms Prysm.ValidatorBalance.Decode.generated_directive_49_kind
#print axioms Prysm.ValidatorBalance.Decode.generated_directive_50
#print axioms Prysm.ValidatorBalance.Decode.generated_directive_50_kind
#print axioms Prysm.ValidatorBalance.Decode.generated_directive_51
#print axioms Prysm.ValidatorBalance.Decode.generated_directive_51_kind
#print axioms Prysm.ValidatorBalance.desc_deserialize_checker
#print axioms Prysm.ValidatorBalance.desc_fixedSize
#print axioms Prysm.ValidatorBalance.desc_serialize_checker
#print axioms Prysm.ValidatorBalance.desc_wellFormed
#print axioms Prysm.ValidatorBalance.SszValue.accepted_is_encoding
#print axioms Prysm.ValidatorBalance.SszValue.encode_size
#print axioms Prysm.ValidatorBalance.SszValue.roundtrip
#print axioms Prysm.ValidatorBalance.SszValue.serialize_eq
#print axioms Prysm.ValidatorBalance.SszValue.serialize_eq_checker
#print axioms Prysm.ValidatorBalance.SszValue.spec_accepts_iff
#print axioms Prysm.ValidatorBalance.SszValue.spec_rejects
#print axioms Prysm.ValidatorBalance.SszValue.toValue_fits
#print axioms Prysm.ValidatorBalance.SszValue.toValue_fits_checker
#print axioms Prysm.ValidatorBalance.SszValue.toValue_injective
#print axioms Prysm.ValidatorBalance.SszValue.toValue_surjective'
#print axioms Prysm.ValidatorBalance.checker_wellFormed
#print axioms Prysm.ValidatorBalance.Decode.accept_spec
#print axioms Prysm.ValidatorBalance.Decode.reject_complete
#print axioms Prysm.ValidatorBalance.Decode.reject_size_spec
#print axioms Prysm.ValidatorBalance.Witness.GeneratedDecodeAccept.program_length
#print axioms Prysm.ValidatorBalance.Witness.GeneratedDecodeAccept.labels_fresh_at_1
#print axioms Prysm.ValidatorBalance.Witness.GeneratedDecodeAccept.labels_fresh_at_74
#print axioms Prysm.ValidatorBalance.Witness.GeneratedDecodeAccept.placed_at_1
#print axioms Prysm.ValidatorBalance.Witness.GeneratedDecodeAccept.placed_at_74
#print axioms Prysm.ValidatorBalance.Witness.GeneratedDecodeAccept.host_program_eq
#print axioms Prysm.ValidatorBalance.Witness.GeneratedDecodeAccept.runs
#print axioms Prysm.ValidatorBalance.Witness.GeneratedDecodeRejectSize.program_length
#print axioms Prysm.ValidatorBalance.Witness.GeneratedDecodeRejectSize.labels_fresh_at_1
#print axioms Prysm.ValidatorBalance.Witness.GeneratedDecodeRejectSize.placed_at_1
#print axioms Prysm.ValidatorBalance.Witness.GeneratedDecodeRejectSize.label_err_size
#print axioms Prysm.ValidatorBalance.Witness.GeneratedDecodeRejectSize.runs
#print axioms Prysm.ValidatorBalance.Code.marshalSSZTo
#print axioms Prysm.ValidatorBalance.Encode.generated_epilogue
#print axioms Prysm.ValidatorBalance.Encode.generated_epilogue_kind
#print axioms Prysm.ValidatorBalance.Encode.generated_field_0
#print axioms Prysm.ValidatorBalance.Encode.generated_field_0_kind
#print axioms Prysm.ValidatorBalance.Encode.generated_field_1
#print axioms Prysm.ValidatorBalance.Encode.generated_field_1_kind
#print axioms Prysm.ValidatorBalance.Encode.generated_fast
#print axioms Prysm.ValidatorBalance.Encode.generated_fast_kind
#print axioms Prysm.ValidatorBalance.Encode.generated_head
#print axioms Prysm.ValidatorBalance.Encode.generated_head_kind
#print axioms Prysm.ValidatorBalance.Encode.generated_layout
#print axioms Prysm.ValidatorBalance.SszValue.encode_toList_generated
#print axioms Prysm.ValidatorBalance.Encode.generated_fast_spec
#print axioms Prysm.ValidatorBalance.Encode.generated_fast_split
#print axioms Prysm.ValidatorBalance.Witness.GeneratedEncodeFastPath.program
#print axioms Prysm.ValidatorBalance.Witness.GeneratedEncodeFastPath.program_length
#print axioms Prysm.ValidatorBalance.Witness.GeneratedEncodeFastPath.block
#print axioms Prysm.ValidatorBalance.Witness.GeneratedEncodeFastPath.initial_state
#print axioms Prysm.ValidatorBalance.Witness.GeneratedEncodeFastPath.labels_fresh_at_0
#print axioms Prysm.ValidatorBalance.Witness.GeneratedEncodeFastPath.placed_at_0
#print axioms Prysm.ValidatorBalance.Witness.GeneratedEncodeFastPath.host
#print axioms Prysm.ValidatorBalance.Witness.GeneratedEncodeFastPath.mem
#print axioms Prysm.ValidatorBalance.Witness.GeneratedEncodeFastPath.runs_empty
#print axioms Prysm.ValidatorBalance.Witness.GeneratedEncodeFastPath.runs_prefix
#print axioms Prysm.ValidatorBalance.Witness.GeneratedEncodeFastPath.word_bytes
#print axioms Prysm.ValidatorBalance.Witness.GeneratedEncodeFastPath.zeros
