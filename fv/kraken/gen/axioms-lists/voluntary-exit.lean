import Prysm.VoluntaryExit.GeneratedDecodeAccept
import Prysm.VoluntaryExit.Spec
import Prysm.VoluntaryExit.DecodeSpec
import Prysm.VoluntaryExit.WitnessGeneratedDecodeAccept
import Prysm.VoluntaryExit.WitnessGeneratedDecodeRejectSize
import Prysm.VoluntaryExit.Code
import Prysm.VoluntaryExit.GeneratedEncodeFastPath
import Prysm.VoluntaryExit.GeneratedEncodeFastPathSpec
import Prysm.VoluntaryExit.WitnessGeneratedEncodeFastPath

/-! Hand list of the `VoluntaryExit` declarations for `gen/checks/axioms_gate.py`.
Each name must be in the declaration dump and use only the standard axioms. -/

#print axioms Prysm.VoluntaryExit.Decode.generated_Epoch_call
#print axioms Prysm.VoluntaryExit.Decode.generated_Epoch_call_kind
#print axioms Prysm.VoluntaryExit.Decode.generated_ValidatorIndex_call
#print axioms Prysm.VoluntaryExit.Decode.generated_ValidatorIndex_call_kind
#print axioms Prysm.VoluntaryExit.Decode.generated_accept
#print axioms Prysm.VoluntaryExit.Decode.generated_accept_kind
#print axioms Prysm.VoluntaryExit.Decode.generated_epilogue
#print axioms Prysm.VoluntaryExit.Decode.generated_epilogue_kind
#print axioms Prysm.VoluntaryExit.Decode.generated_field_1
#print axioms Prysm.VoluntaryExit.Decode.generated_field_1_kind
#print axioms Prysm.VoluntaryExit.Decode.generated_field_2
#print axioms Prysm.VoluntaryExit.Decode.generated_field_2_kind
#print axioms Prysm.VoluntaryExit.Decode.generated_head
#print axioms Prysm.VoluntaryExit.Decode.generated_head_kind
#print axioms Prysm.VoluntaryExit.Decode.generated_reject
#print axioms Prysm.VoluntaryExit.Decode.generated_reject_kind
#print axioms Prysm.VoluntaryExit.Decode.generated_directive_15
#print axioms Prysm.VoluntaryExit.Decode.generated_directive_15_kind
#print axioms Prysm.VoluntaryExit.Decode.generated_directive_16
#print axioms Prysm.VoluntaryExit.Decode.generated_directive_16_kind
#print axioms Prysm.VoluntaryExit.Decode.generated_directive_48
#print axioms Prysm.VoluntaryExit.Decode.generated_directive_48_kind
#print axioms Prysm.VoluntaryExit.Decode.generated_directive_49
#print axioms Prysm.VoluntaryExit.Decode.generated_directive_49_kind
#print axioms Prysm.VoluntaryExit.Decode.generated_directive_50
#print axioms Prysm.VoluntaryExit.Decode.generated_directive_50_kind
#print axioms Prysm.VoluntaryExit.Decode.generated_directive_51
#print axioms Prysm.VoluntaryExit.Decode.generated_directive_51_kind
#print axioms Prysm.VoluntaryExit.Decode.generated_directive_52
#print axioms Prysm.VoluntaryExit.Decode.generated_directive_52_kind
#print axioms Prysm.VoluntaryExit.Decode.generated_directive_53
#print axioms Prysm.VoluntaryExit.Decode.generated_directive_53_kind
#print axioms Prysm.VoluntaryExit.Decode.generated_directive_54
#print axioms Prysm.VoluntaryExit.Decode.generated_directive_54_kind
#print axioms Prysm.VoluntaryExit.desc_deserialize_checker
#print axioms Prysm.VoluntaryExit.desc_fixedSize
#print axioms Prysm.VoluntaryExit.desc_serialize_checker
#print axioms Prysm.VoluntaryExit.desc_wellFormed
#print axioms Prysm.VoluntaryExit.SszValue.accepted_is_encoding
#print axioms Prysm.VoluntaryExit.SszValue.encode_size
#print axioms Prysm.VoluntaryExit.SszValue.roundtrip
#print axioms Prysm.VoluntaryExit.SszValue.serialize_eq
#print axioms Prysm.VoluntaryExit.SszValue.serialize_eq_checker
#print axioms Prysm.VoluntaryExit.SszValue.spec_accepts_iff
#print axioms Prysm.VoluntaryExit.SszValue.spec_rejects
#print axioms Prysm.VoluntaryExit.SszValue.toValue_fits
#print axioms Prysm.VoluntaryExit.SszValue.toValue_fits_checker
#print axioms Prysm.VoluntaryExit.SszValue.toValue_injective
#print axioms Prysm.VoluntaryExit.SszValue.toValue_surjective'
#print axioms Prysm.VoluntaryExit.checker_wellFormed
#print axioms Prysm.VoluntaryExit.Decode.accept_spec
#print axioms Prysm.VoluntaryExit.Decode.reject_complete
#print axioms Prysm.VoluntaryExit.Decode.reject_size_spec
#print axioms Prysm.VoluntaryExit.Witness.GeneratedDecodeAccept.program_length
#print axioms Prysm.VoluntaryExit.Witness.GeneratedDecodeAccept.labels_fresh_at_1
#print axioms Prysm.VoluntaryExit.Witness.GeneratedDecodeAccept.labels_fresh_at_108
#print axioms Prysm.VoluntaryExit.Witness.GeneratedDecodeAccept.labels_fresh_at_171
#print axioms Prysm.VoluntaryExit.Witness.GeneratedDecodeAccept.placed_at_1
#print axioms Prysm.VoluntaryExit.Witness.GeneratedDecodeAccept.placed_at_108
#print axioms Prysm.VoluntaryExit.Witness.GeneratedDecodeAccept.placed_at_171
#print axioms Prysm.VoluntaryExit.Witness.GeneratedDecodeAccept.host_program_eq
#print axioms Prysm.VoluntaryExit.Witness.GeneratedDecodeAccept.runs
#print axioms Prysm.VoluntaryExit.Witness.GeneratedDecodeRejectSize.program_length
#print axioms Prysm.VoluntaryExit.Witness.GeneratedDecodeRejectSize.labels_fresh_at_1
#print axioms Prysm.VoluntaryExit.Witness.GeneratedDecodeRejectSize.placed_at_1
#print axioms Prysm.VoluntaryExit.Witness.GeneratedDecodeRejectSize.label_err_size
#print axioms Prysm.VoluntaryExit.Witness.GeneratedDecodeRejectSize.runs
#print axioms Prysm.VoluntaryExit.Code.marshalSSZTo
#print axioms Prysm.VoluntaryExit.Encode.generated_epilogue
#print axioms Prysm.VoluntaryExit.Encode.generated_epilogue_kind
#print axioms Prysm.VoluntaryExit.Encode.generated_field_0
#print axioms Prysm.VoluntaryExit.Encode.generated_field_0_kind
#print axioms Prysm.VoluntaryExit.Encode.generated_field_1
#print axioms Prysm.VoluntaryExit.Encode.generated_field_1_kind
#print axioms Prysm.VoluntaryExit.Encode.generated_fast
#print axioms Prysm.VoluntaryExit.Encode.generated_fast_kind
#print axioms Prysm.VoluntaryExit.Encode.generated_head
#print axioms Prysm.VoluntaryExit.Encode.generated_head_kind
#print axioms Prysm.VoluntaryExit.Encode.generated_layout
#print axioms Prysm.VoluntaryExit.SszValue.encode_toList_generated
#print axioms Prysm.VoluntaryExit.Encode.generated_fast_spec
#print axioms Prysm.VoluntaryExit.Encode.generated_fast_split
#print axioms Prysm.VoluntaryExit.Witness.GeneratedEncodeFastPath.program
#print axioms Prysm.VoluntaryExit.Witness.GeneratedEncodeFastPath.program_length
#print axioms Prysm.VoluntaryExit.Witness.GeneratedEncodeFastPath.block
#print axioms Prysm.VoluntaryExit.Witness.GeneratedEncodeFastPath.initial_state
#print axioms Prysm.VoluntaryExit.Witness.GeneratedEncodeFastPath.labels_fresh_at_0
#print axioms Prysm.VoluntaryExit.Witness.GeneratedEncodeFastPath.placed_at_0
#print axioms Prysm.VoluntaryExit.Witness.GeneratedEncodeFastPath.host
#print axioms Prysm.VoluntaryExit.Witness.GeneratedEncodeFastPath.mem
#print axioms Prysm.VoluntaryExit.Witness.GeneratedEncodeFastPath.runs_empty
#print axioms Prysm.VoluntaryExit.Witness.GeneratedEncodeFastPath.runs_prefix
#print axioms Prysm.VoluntaryExit.Witness.GeneratedEncodeFastPath.word_bytes
#print axioms Prysm.VoluntaryExit.Witness.GeneratedEncodeFastPath.zeros
