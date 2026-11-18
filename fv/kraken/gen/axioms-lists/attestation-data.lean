import Prysm.AttestationData.SpecEquivalence
import Prysm.AttestationData.Spec
import Prysm.AttestationData.DecodeAcceptHead
import Prysm.AttestationData.DecodeAcceptBlockRoot
import Prysm.AttestationData.DecodeAcceptSource
import Prysm.AttestationData.DecodeAcceptTarget
import Prysm.AttestationData.DecodeAccept
import Prysm.AttestationData.DecodeRejectSize
import Prysm.AttestationData.DecodeSpec
import Prysm.AttestationData.WitnessBumpAllocator
import Prysm.AttestationData.WitnessDecodeAccept
import Prysm.AttestationData.WitnessDecodeRejectSize
import Prysm.AttestationData.GeneratedDecodeAccept
import Prysm.AttestationData.GeneratedEncodeFastPath
import Prysm.AttestationData.EncodeFastPathStatementTie
import Prysm.AttestationData.GeneratedEncodeFastPathSpec
import Prysm.AttestationData.WitnessGeneratedEncodeFastPath
import Prysm.AttestationData.Size
import Prysm.AttestationData.WitnessSize
import Prysm.AttestationData.EncodeSpec
import Prysm.AttestationData.WitnessEncodeFastPath

/-! Hand list of the `AttestationData` declarations for `gen/checks/axioms_gate.py`.
Each name must be in the declaration dump and use only the standard axioms. -/

#print axioms Prysm.AttestationData.desc_checker
#print axioms Prysm.AttestationData.desc_serialize_checker
#print axioms Prysm.AttestationData.desc_deserialize_checker
#print axioms Prysm.AttestationData.SszValue.serialize_eq
#print axioms Prysm.AttestationData.SszValue.roundtrip
#print axioms Prysm.AttestationData.SszValue.spec_accepts_iff
#print axioms Prysm.AttestationData.SszValue.spec_rejects
#print axioms Prysm.AttestationData.Decode.head
#print axioms Prysm.AttestationData.Decode.block_root
#print axioms Prysm.AttestationData.Decode.source
#print axioms Prysm.AttestationData.Decode.target
#print axioms Prysm.AttestationData.Decode.accept
#print axioms Prysm.AttestationData.Decode.reject_size
#print axioms Prysm.AttestationData.Decode.accept_spec
#print axioms Prysm.AttestationData.Decode.reject_size_spec
#print axioms Prysm.AttestationData.Decode.reject_complete
#print axioms Prysm.AttestationData.bump_newobject72
#print axioms Prysm.AttestationData.Witness.DecodeAccept.runs
#print axioms Prysm.AttestationData.Witness.DecodeRejectSize.runs
#print axioms Prysm.AttestationData.Decode.generated_directive_15
#print axioms Prysm.AttestationData.Decode.generated_directive_15_kind
#print axioms Prysm.AttestationData.Decode.generated_directive_16
#print axioms Prysm.AttestationData.Decode.generated_directive_16_kind
#print axioms Prysm.AttestationData.Decode.generated_Slot_call
#print axioms Prysm.AttestationData.Decode.generated_Slot_call_kind
#print axioms Prysm.AttestationData.Decode.generated_directive_48
#print axioms Prysm.AttestationData.Decode.generated_directive_48_kind
#print axioms Prysm.AttestationData.Decode.generated_directive_49
#print axioms Prysm.AttestationData.Decode.generated_directive_49_kind
#print axioms Prysm.AttestationData.Decode.generated_directive_50
#print axioms Prysm.AttestationData.Decode.generated_directive_50_kind
#print axioms Prysm.AttestationData.Decode.generated_directive_51
#print axioms Prysm.AttestationData.Decode.generated_directive_51_kind
#print axioms Prysm.AttestationData.Decode.generated_directive_52
#print axioms Prysm.AttestationData.Decode.generated_directive_52_kind
#print axioms Prysm.AttestationData.Decode.generated_directive_53
#print axioms Prysm.AttestationData.Decode.generated_directive_53_kind
#print axioms Prysm.AttestationData.Decode.generated_directive_54
#print axioms Prysm.AttestationData.Decode.generated_directive_54_kind
#print axioms Prysm.AttestationData.Decode.generated_CommitteeIndex_call
#print axioms Prysm.AttestationData.Decode.generated_CommitteeIndex_call_kind
#print axioms Prysm.AttestationData.Decode.generated_BeaconBlockRoot_segment
#print axioms Prysm.AttestationData.Decode.generated_BeaconBlockRoot_segment_kind
#print axioms Prysm.AttestationData.Decode.generated_directive_112
#print axioms Prysm.AttestationData.Decode.generated_directive_112_kind
#print axioms Prysm.AttestationData.Decode.generated_directive_113
#print axioms Prysm.AttestationData.Decode.generated_directive_113_kind
#print axioms Prysm.AttestationData.Decode.generated_directive_120
#print axioms Prysm.AttestationData.Decode.generated_directive_120_kind
#print axioms Prysm.AttestationData.Decode.generated_directive_121
#print axioms Prysm.AttestationData.Decode.generated_directive_121_kind
#print axioms Prysm.AttestationData.Decode.generated_Source_nested
#print axioms Prysm.AttestationData.Decode.generated_Source_nested_kind
#print axioms Prysm.AttestationData.Decode.generated_Target_nested
#print axioms Prysm.AttestationData.Decode.generated_Target_nested_kind
#print axioms Prysm.AttestationData.Decode.generated_head
#print axioms Prysm.AttestationData.Decode.generated_head_kind
#print axioms Prysm.AttestationData.Decode.generated_field_1
#print axioms Prysm.AttestationData.Decode.generated_field_1_kind
#print axioms Prysm.AttestationData.Decode.generated_field_2
#print axioms Prysm.AttestationData.Decode.generated_field_2_kind
#print axioms Prysm.AttestationData.Decode.generated_field_3
#print axioms Prysm.AttestationData.Decode.generated_field_3_kind
#print axioms Prysm.AttestationData.Decode.generated_field_4
#print axioms Prysm.AttestationData.Decode.generated_field_4_kind
#print axioms Prysm.AttestationData.Decode.generated_field_5
#print axioms Prysm.AttestationData.Decode.generated_field_5_kind
#print axioms Prysm.AttestationData.Decode.generated_epilogue
#print axioms Prysm.AttestationData.Decode.generated_epilogue_kind
#print axioms Prysm.AttestationData.Decode.generated_accept
#print axioms Prysm.AttestationData.Decode.generated_accept_kind
#print axioms Prysm.AttestationData.Decode.generated_reject
#print axioms Prysm.AttestationData.Decode.generated_reject_kind
#print axioms Prysm.AttestationData.Size.result
#print axioms Prysm.AttestationData.Size.result_spec
#print axioms Prysm.AttestationData.Witness.Size.runs
#print axioms Prysm.AttestationData.Encode.head_slot
#print axioms Prysm.AttestationData.Encode.head_index
#print axioms Prysm.AttestationData.Encode.head_root
#print axioms Prysm.AttestationData.Encode.source_call
#print axioms Prysm.AttestationData.Encode.target_call
#print axioms Prysm.AttestationData.Encode.head
#print axioms Prysm.AttestationData.Encode.calls
#print axioms Prysm.AttestationData.Encode.fast_path
#print axioms Prysm.AttestationData.Encode.fast_path_spec
#print axioms Prysm.AttestationData.Witness.EncodeFastPath.mem_premise
#print axioms Prysm.AttestationData.Witness.EncodeFastPath.runs_empty
#print axioms Prysm.AttestationData.Witness.EncodeFastPath.Prefix.mem_premise
#print axioms Prysm.AttestationData.Witness.EncodeFastPath.runs_prefix
#print axioms Prysm.AttestationData.Encode.generated_epilogue
#print axioms Prysm.AttestationData.Encode.generated_epilogue_kind
#print axioms Prysm.AttestationData.Encode.generated_fast
#print axioms Prysm.AttestationData.Encode.generated_fast_kind
#print axioms Prysm.AttestationData.Encode.generated_field_0
#print axioms Prysm.AttestationData.Encode.generated_field_0_kind
#print axioms Prysm.AttestationData.Encode.generated_field_1
#print axioms Prysm.AttestationData.Encode.generated_field_1_kind
#print axioms Prysm.AttestationData.Encode.generated_field_2
#print axioms Prysm.AttestationData.Encode.generated_field_2_kind
#print axioms Prysm.AttestationData.Encode.generated_field_3
#print axioms Prysm.AttestationData.Encode.generated_field_3_kind
#print axioms Prysm.AttestationData.Encode.generated_field_4
#print axioms Prysm.AttestationData.Encode.generated_field_4_kind
#print axioms Prysm.AttestationData.Encode.generated_head
#print axioms Prysm.AttestationData.Encode.generated_head_kind
#print axioms Prysm.AttestationData.Encode.generated_layout
#print axioms Prysm.AttestationData.Encode.fast_path_statement_tie
#print axioms Prysm.AttestationData.Encode.fast_path_implies_generated_fast
#print axioms Prysm.AttestationData.Encode.generated_fast_spec
#print axioms Prysm.AttestationData.Witness.GeneratedEncodeFastPath.runs_empty
#print axioms Prysm.AttestationData.Witness.GeneratedEncodeFastPath.runs_prefix
