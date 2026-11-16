import Prysm.BeaconBlockHeader.DecodeErrorUnreachable
import Prysm.BeaconBlockHeader.WitnessDecodeErrorUnreachable
import Prysm.BeaconBlockHeader.Spec
import Prysm.BeaconBlockHeader.DecodeSpec
import Prysm.BeaconBlockHeader.WitnessGeneratedDecodeAccept
import Prysm.BeaconBlockHeader.WitnessGeneratedDecodeRejectSize
import Prysm.BeaconBlockHeader.EncodeHead
import Prysm.BeaconBlockHeader.EncodeRootFields
import Prysm.BeaconBlockHeader.EncodeRejectLength
import Prysm.BeaconBlockHeader.WitnessEncodeRejectLength
import Prysm.BeaconBlockHeader.GeneratedDecodeAccept
import Prysm.BeaconBlockHeader.GeneratedEncodeFastPath
import Prysm.BeaconBlockHeader.EncodeLayout
import Prysm.BeaconBlockHeader.GeneratedEncodeFastPathSpec
import Prysm.BeaconBlockHeader.WitnessGeneratedEncodeFastPath

/-! Hand list of the `BeaconBlockHeader` declarations for `gen/checks/axioms_gate.py`.
Each name must be in the declaration dump and use only the standard axioms. -/

#print axioms Prysm.BeaconBlockHeader.Decode.slot_err_unreachable
#print axioms Prysm.BeaconBlockHeader.Decode.validator_index_err_unreachable
#print axioms Prysm.BeaconBlockHeader.Witness.DecodeErrorUnreachable.runs
#print axioms Prysm.BeaconBlockHeader.desc_checker
#print axioms Prysm.BeaconBlockHeader.desc_serialize_checker
#print axioms Prysm.BeaconBlockHeader.desc_deserialize_checker
#print axioms Prysm.BeaconBlockHeader.SszValue.roundtrip
#print axioms Prysm.BeaconBlockHeader.SszValue.spec_accepts_iff
#print axioms Prysm.BeaconBlockHeader.SszValue.spec_rejects
#print axioms Prysm.BeaconBlockHeader.Decode.accept_spec
#print axioms Prysm.BeaconBlockHeader.Decode.reject_size_spec
#print axioms Prysm.BeaconBlockHeader.Decode.reject_complete
#print axioms Prysm.BeaconBlockHeader.Witness.GeneratedDecodeAccept.runs
#print axioms Prysm.BeaconBlockHeader.Witness.GeneratedDecodeRejectSize.runs
#print axioms Prysm.BeaconBlockHeader.Encode.encode_slot
#print axioms Prysm.BeaconBlockHeader.Encode.encode_proposer_index
#print axioms Prysm.BeaconBlockHeader.Encode.encode_parent_root
#print axioms Prysm.BeaconBlockHeader.Encode.encode_state_root
#print axioms Prysm.BeaconBlockHeader.Encode.reject_tails_at
#print axioms Prysm.BeaconBlockHeader.Encode.reject_parent_root
#print axioms Prysm.BeaconBlockHeader.Encode.reject_state_root
#print axioms Prysm.BeaconBlockHeader.Encode.reject_body_root
#print axioms Prysm.BeaconBlockHeader.Encode.reject_length_parent_root
#print axioms Prysm.BeaconBlockHeader.Encode.reject_length_state_root
#print axioms Prysm.BeaconBlockHeader.Encode.reject_length_body_root
#print axioms Prysm.BeaconBlockHeader.Witness.EncodeRejectLength.runs_parent_root
#print axioms Prysm.BeaconBlockHeader.Witness.EncodeRejectLength.runs_state_root
#print axioms Prysm.BeaconBlockHeader.Witness.EncodeRejectLength.runs_body_root
#print axioms Prysm.BeaconBlockHeader.Decode.generated_BodyRoot_segment
#print axioms Prysm.BeaconBlockHeader.Decode.generated_BodyRoot_segment_kind
#print axioms Prysm.BeaconBlockHeader.Decode.generated_ParentRoot_segment
#print axioms Prysm.BeaconBlockHeader.Decode.generated_ParentRoot_segment_kind
#print axioms Prysm.BeaconBlockHeader.Decode.generated_ProposerIndex_call
#print axioms Prysm.BeaconBlockHeader.Decode.generated_ProposerIndex_call_kind
#print axioms Prysm.BeaconBlockHeader.Decode.generated_Slot_call
#print axioms Prysm.BeaconBlockHeader.Decode.generated_Slot_call_kind
#print axioms Prysm.BeaconBlockHeader.Decode.generated_StateRoot_segment
#print axioms Prysm.BeaconBlockHeader.Decode.generated_StateRoot_segment_kind
#print axioms Prysm.BeaconBlockHeader.Decode.generated_accept
#print axioms Prysm.BeaconBlockHeader.Decode.generated_accept_kind
#print axioms Prysm.BeaconBlockHeader.Decode.generated_epilogue
#print axioms Prysm.BeaconBlockHeader.Decode.generated_epilogue_kind
#print axioms Prysm.BeaconBlockHeader.Decode.generated_field_1
#print axioms Prysm.BeaconBlockHeader.Decode.generated_field_1_kind
#print axioms Prysm.BeaconBlockHeader.Decode.generated_field_2
#print axioms Prysm.BeaconBlockHeader.Decode.generated_field_2_kind
#print axioms Prysm.BeaconBlockHeader.Decode.generated_field_3
#print axioms Prysm.BeaconBlockHeader.Decode.generated_field_3_kind
#print axioms Prysm.BeaconBlockHeader.Decode.generated_field_4
#print axioms Prysm.BeaconBlockHeader.Decode.generated_field_4_kind
#print axioms Prysm.BeaconBlockHeader.Decode.generated_field_5
#print axioms Prysm.BeaconBlockHeader.Decode.generated_field_5_kind
#print axioms Prysm.BeaconBlockHeader.Decode.generated_head
#print axioms Prysm.BeaconBlockHeader.Decode.generated_head_kind
#print axioms Prysm.BeaconBlockHeader.Decode.generated_reject
#print axioms Prysm.BeaconBlockHeader.Decode.generated_reject_kind
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_113
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_113_kind
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_115
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_115_kind
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_122
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_122_kind
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_123
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_123_kind
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_149
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_149_kind
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_15
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_150
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_150_kind
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_157
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_157_kind
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_158
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_158_kind
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_15_kind
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_16
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_16_kind
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_184
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_184_kind
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_185
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_185_kind
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_193
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_193_kind
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_194
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_194_kind
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_47
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_47_kind
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_48
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_48_kind
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_49
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_49_kind
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_50
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_50_kind
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_51
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_51_kind
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_52
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_52_kind
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_53
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_53_kind
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_86
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_86_kind
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_87
#print axioms Prysm.BeaconBlockHeader.Decode.generated_directive_87_kind
#print axioms Prysm.BeaconBlockHeader.Encode.generated_epilogue
#print axioms Prysm.BeaconBlockHeader.Encode.generated_epilogue_kind
#print axioms Prysm.BeaconBlockHeader.Encode.generated_field_0
#print axioms Prysm.BeaconBlockHeader.Encode.generated_field_0_kind
#print axioms Prysm.BeaconBlockHeader.Encode.generated_field_1
#print axioms Prysm.BeaconBlockHeader.Encode.generated_field_1_kind
#print axioms Prysm.BeaconBlockHeader.Encode.generated_field_2
#print axioms Prysm.BeaconBlockHeader.Encode.generated_field_2_kind
#print axioms Prysm.BeaconBlockHeader.Encode.generated_field_3
#print axioms Prysm.BeaconBlockHeader.Encode.generated_field_3_kind
#print axioms Prysm.BeaconBlockHeader.Encode.generated_field_4
#print axioms Prysm.BeaconBlockHeader.Encode.generated_field_4_kind
#print axioms Prysm.BeaconBlockHeader.Encode.generated_fast
#print axioms Prysm.BeaconBlockHeader.Encode.generated_fast_kind
#print axioms Prysm.BeaconBlockHeader.Encode.generated_head
#print axioms Prysm.BeaconBlockHeader.Encode.generated_head_kind
#print axioms Prysm.BeaconBlockHeader.encodeLayout
#print axioms Prysm.BeaconBlockHeader.SszValue.encode_toList_generated
#print axioms Prysm.BeaconBlockHeader.Encode.generated_fast_spec
#print axioms Prysm.BeaconBlockHeader.Encode.generated_fast_split
#print axioms Prysm.BeaconBlockHeader.Witness.GeneratedEncodeFastPath.program
#print axioms Prysm.BeaconBlockHeader.Witness.GeneratedEncodeFastPath.program_length
#print axioms Prysm.BeaconBlockHeader.Witness.GeneratedEncodeFastPath.runs_empty
#print axioms Prysm.BeaconBlockHeader.Witness.GeneratedEncodeFastPath.runs_prefix
#print axioms Prysm.BeaconBlockHeader.Witness.GeneratedEncodeFastPath.block
#print axioms Prysm.BeaconBlockHeader.Witness.GeneratedEncodeFastPath.initial_state
#print axioms Prysm.BeaconBlockHeader.Witness.GeneratedEncodeFastPath.labels_fresh_at_0
#print axioms Prysm.BeaconBlockHeader.Witness.GeneratedEncodeFastPath.labels_fresh_copy_model
#print axioms Prysm.BeaconBlockHeader.Witness.GeneratedEncodeFastPath.placed_at_0
#print axioms Prysm.BeaconBlockHeader.Witness.GeneratedEncodeFastPath.placed_copy_model
#print axioms Prysm.BeaconBlockHeader.Witness.GeneratedEncodeFastPath.host
#print axioms Prysm.BeaconBlockHeader.Witness.GeneratedEncodeFastPath.mem
#print axioms Prysm.BeaconBlockHeader.Witness.GeneratedEncodeFastPath.word_bytes
#print axioms Prysm.BeaconBlockHeader.Witness.GeneratedEncodeFastPath.zeros
