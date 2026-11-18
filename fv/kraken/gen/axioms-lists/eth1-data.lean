import Prysm.Eth1Data.Spec
import Prysm.Eth1Data.DecodeSpec
import Prysm.Eth1Data.WitnessGeneratedDecodeAccept
import Prysm.Eth1Data.WitnessGeneratedDecodeRejectSize
import Prysm.Eth1Data.GeneratedDecodeAccept
import Prysm.Eth1Data.GeneratedEncodeFastPath
import Prysm.Eth1Data.EncodeLayout
import Prysm.Eth1Data.GeneratedEncodeFastPathSpec
import Prysm.Eth1Data.WitnessGeneratedEncodeFastPath

/-! Hand list of the `Eth1Data` declarations for `gen/checks/axioms_gate.py`.
Each name must be in the declaration dump and use only the standard axioms. -/

#print axioms Prysm.Eth1Data.desc_serialize_checker
#print axioms Prysm.Eth1Data.desc_deserialize_checker
#print axioms Prysm.Eth1Data.SszValue.roundtrip
#print axioms Prysm.Eth1Data.SszValue.spec_accepts_iff
#print axioms Prysm.Eth1Data.SszValue.spec_rejects
#print axioms Prysm.Eth1Data.Decode.accept_spec
#print axioms Prysm.Eth1Data.Decode.reject_size_spec
#print axioms Prysm.Eth1Data.Decode.reject_complete
#print axioms Prysm.Eth1Data.Witness.GeneratedDecodeAccept.runs
#print axioms Prysm.Eth1Data.Witness.GeneratedDecodeRejectSize.runs
#print axioms Prysm.Eth1Data.Decode.generated_BlockHash_segment
#print axioms Prysm.Eth1Data.Decode.generated_BlockHash_segment_kind
#print axioms Prysm.Eth1Data.Decode.generated_DepositRoot_segment
#print axioms Prysm.Eth1Data.Decode.generated_DepositRoot_segment_kind
#print axioms Prysm.Eth1Data.Decode.generated_accept
#print axioms Prysm.Eth1Data.Decode.generated_accept_kind
#print axioms Prysm.Eth1Data.Decode.generated_epilogue
#print axioms Prysm.Eth1Data.Decode.generated_epilogue_kind
#print axioms Prysm.Eth1Data.Decode.generated_field_1
#print axioms Prysm.Eth1Data.Decode.generated_field_1_kind
#print axioms Prysm.Eth1Data.Decode.generated_field_2
#print axioms Prysm.Eth1Data.Decode.generated_field_2_kind
#print axioms Prysm.Eth1Data.Decode.generated_field_3
#print axioms Prysm.Eth1Data.Decode.generated_field_3_kind
#print axioms Prysm.Eth1Data.Decode.generated_head
#print axioms Prysm.Eth1Data.Decode.generated_head_kind
#print axioms Prysm.Eth1Data.Decode.generated_reject
#print axioms Prysm.Eth1Data.Decode.generated_reject_kind
#print axioms Prysm.Eth1Data.Decode.generated_directive_37
#print axioms Prysm.Eth1Data.Decode.generated_directive_37_kind
#print axioms Prysm.Eth1Data.Decode.generated_directive_38
#print axioms Prysm.Eth1Data.Decode.generated_directive_38_kind
#print axioms Prysm.Eth1Data.Decode.generated_directive_45
#print axioms Prysm.Eth1Data.Decode.generated_directive_45_kind
#print axioms Prysm.Eth1Data.Decode.generated_directive_46
#print axioms Prysm.Eth1Data.Decode.generated_directive_46_kind
#print axioms Prysm.Eth1Data.Decode.generated_directive_47
#print axioms Prysm.Eth1Data.Decode.generated_directive_47_kind
#print axioms Prysm.Eth1Data.Decode.generated_directive_48
#print axioms Prysm.Eth1Data.Decode.generated_directive_48_kind
#print axioms Prysm.Eth1Data.Decode.generated_directive_49
#print axioms Prysm.Eth1Data.Decode.generated_directive_49_kind
#print axioms Prysm.Eth1Data.Decode.generated_directive_75
#print axioms Prysm.Eth1Data.Decode.generated_directive_75_kind
#print axioms Prysm.Eth1Data.Decode.generated_directive_76
#print axioms Prysm.Eth1Data.Decode.generated_directive_76_kind
#print axioms Prysm.Eth1Data.Decode.generated_directive_84
#print axioms Prysm.Eth1Data.Decode.generated_directive_84_kind
#print axioms Prysm.Eth1Data.Decode.generated_directive_85
#print axioms Prysm.Eth1Data.Decode.generated_directive_85_kind
#print axioms Prysm.Eth1Data.Encode.generated_epilogue
#print axioms Prysm.Eth1Data.Encode.generated_epilogue_kind
#print axioms Prysm.Eth1Data.Encode.generated_field_0
#print axioms Prysm.Eth1Data.Encode.generated_field_0_kind
#print axioms Prysm.Eth1Data.Encode.generated_field_1
#print axioms Prysm.Eth1Data.Encode.generated_field_1_kind
#print axioms Prysm.Eth1Data.Encode.generated_field_2
#print axioms Prysm.Eth1Data.Encode.generated_field_2_kind
#print axioms Prysm.Eth1Data.Encode.generated_fast
#print axioms Prysm.Eth1Data.Encode.generated_fast_kind
#print axioms Prysm.Eth1Data.Encode.generated_head
#print axioms Prysm.Eth1Data.Encode.generated_head_kind
#print axioms Prysm.Eth1Data.encodeLayout
#print axioms Prysm.Eth1Data.SszValue.encode_toList_generated
#print axioms Prysm.Eth1Data.Encode.generated_fast_spec
#print axioms Prysm.Eth1Data.Encode.generated_fast_split
#print axioms Prysm.Eth1Data.Witness.GeneratedEncodeFastPath.program
#print axioms Prysm.Eth1Data.Witness.GeneratedEncodeFastPath.program_length
#print axioms Prysm.Eth1Data.Witness.GeneratedEncodeFastPath.block
#print axioms Prysm.Eth1Data.Witness.GeneratedEncodeFastPath.initial_state
#print axioms Prysm.Eth1Data.Witness.GeneratedEncodeFastPath.runs_empty
#print axioms Prysm.Eth1Data.Witness.GeneratedEncodeFastPath.runs_prefix
#print axioms Prysm.Eth1Data.Witness.GeneratedEncodeFastPath.labels_fresh_at_0
#print axioms Prysm.Eth1Data.Witness.GeneratedEncodeFastPath.labels_fresh_copy_model
#print axioms Prysm.Eth1Data.Witness.GeneratedEncodeFastPath.placed_at_0
#print axioms Prysm.Eth1Data.Witness.GeneratedEncodeFastPath.placed_copy_model
#print axioms Prysm.Eth1Data.Witness.GeneratedEncodeFastPath.host
#print axioms Prysm.Eth1Data.Witness.GeneratedEncodeFastPath.mem
#print axioms Prysm.Eth1Data.Witness.GeneratedEncodeFastPath.word_bytes
#print axioms Prysm.Eth1Data.Witness.GeneratedEncodeFastPath.zeros
