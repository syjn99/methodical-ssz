import Prysm.PowBlock.GeneratedDecodeAccept
import Prysm.PowBlock.Code
import Prysm.PowBlock.GeneratedEncodeFastPath
import Prysm.PowBlock.GeneratedEncodeFastPathSpec
import Prysm.PowBlock.EncodeFastPathStatements
import Prysm.PowBlock.EncodeFastPathStatementTie
import Prysm.PowBlock.WitnessGeneratedEncodeFastPath

/-! Hand list of the `PowBlock` declarations for `gen/checks/axioms_gate.py`.
Each name must be in the declaration dump and use only the standard axioms. -/

#print axioms Prysm.PowBlock.Decode.generated_BlockHash_segment
#print axioms Prysm.PowBlock.Decode.generated_BlockHash_segment_kind
#print axioms Prysm.PowBlock.Decode.generated_ParentHash_segment
#print axioms Prysm.PowBlock.Decode.generated_ParentHash_segment_kind
#print axioms Prysm.PowBlock.Decode.generated_TotalDifficulty_segment
#print axioms Prysm.PowBlock.Decode.generated_TotalDifficulty_segment_kind
#print axioms Prysm.PowBlock.Decode.generated_accept
#print axioms Prysm.PowBlock.Decode.generated_accept_kind
#print axioms Prysm.PowBlock.Decode.generated_epilogue
#print axioms Prysm.PowBlock.Decode.generated_epilogue_kind
#print axioms Prysm.PowBlock.Decode.generated_field_1
#print axioms Prysm.PowBlock.Decode.generated_field_1_kind
#print axioms Prysm.PowBlock.Decode.generated_field_2
#print axioms Prysm.PowBlock.Decode.generated_field_2_kind
#print axioms Prysm.PowBlock.Decode.generated_field_3
#print axioms Prysm.PowBlock.Decode.generated_field_3_kind
#print axioms Prysm.PowBlock.Decode.generated_head
#print axioms Prysm.PowBlock.Decode.generated_head_kind
#print axioms Prysm.PowBlock.Decode.generated_reject
#print axioms Prysm.PowBlock.Decode.generated_reject_kind
#print axioms Prysm.PowBlock.Decode.generated_directive_109
#print axioms Prysm.PowBlock.Decode.generated_directive_109_kind
#print axioms Prysm.PowBlock.Decode.generated_directive_110
#print axioms Prysm.PowBlock.Decode.generated_directive_110_kind
#print axioms Prysm.PowBlock.Decode.generated_directive_117
#print axioms Prysm.PowBlock.Decode.generated_directive_117_kind
#print axioms Prysm.PowBlock.Decode.generated_directive_118
#print axioms Prysm.PowBlock.Decode.generated_directive_118_kind
#print axioms Prysm.PowBlock.Decode.generated_directive_37
#print axioms Prysm.PowBlock.Decode.generated_directive_37_kind
#print axioms Prysm.PowBlock.Decode.generated_directive_38
#print axioms Prysm.PowBlock.Decode.generated_directive_38_kind
#print axioms Prysm.PowBlock.Decode.generated_directive_45
#print axioms Prysm.PowBlock.Decode.generated_directive_45_kind
#print axioms Prysm.PowBlock.Decode.generated_directive_46
#print axioms Prysm.PowBlock.Decode.generated_directive_46_kind
#print axioms Prysm.PowBlock.Decode.generated_directive_73
#print axioms Prysm.PowBlock.Decode.generated_directive_73_kind
#print axioms Prysm.PowBlock.Decode.generated_directive_74
#print axioms Prysm.PowBlock.Decode.generated_directive_74_kind
#print axioms Prysm.PowBlock.Decode.generated_directive_81
#print axioms Prysm.PowBlock.Decode.generated_directive_81_kind
#print axioms Prysm.PowBlock.Decode.generated_directive_82
#print axioms Prysm.PowBlock.Decode.generated_directive_82_kind
#print axioms Prysm.PowBlock.Code.marshalSSZTo
#print axioms Prysm.PowBlock.Encode.generated_epilogue
#print axioms Prysm.PowBlock.Encode.generated_epilogue_kind
#print axioms Prysm.PowBlock.Encode.generated_field_0
#print axioms Prysm.PowBlock.Encode.generated_field_0_kind
#print axioms Prysm.PowBlock.Encode.generated_field_1
#print axioms Prysm.PowBlock.Encode.generated_field_1_kind
#print axioms Prysm.PowBlock.Encode.generated_field_2
#print axioms Prysm.PowBlock.Encode.generated_field_2_kind
#print axioms Prysm.PowBlock.Encode.generated_fast
#print axioms Prysm.PowBlock.Encode.generated_fast_kind
#print axioms Prysm.PowBlock.Encode.generated_head
#print axioms Prysm.PowBlock.Encode.generated_head_kind
#print axioms Prysm.PowBlock.Encode.generated_layout
#print axioms Prysm.PowBlock.SszValue.encode_toList_generated
#print axioms Prysm.PowBlock.Encode.generated_fast_spec
#print axioms Prysm.PowBlock.Encode.generated_fast_split
#print axioms Prysm.PowBlock.Encode.fast_path_statement
#print axioms Prysm.PowBlock.Encode.fast_path_statement_tie
#print axioms Prysm.PowBlock.Witness.GeneratedEncodeFastPath.program
#print axioms Prysm.PowBlock.Witness.GeneratedEncodeFastPath.program_length
#print axioms Prysm.PowBlock.Witness.GeneratedEncodeFastPath.block
#print axioms Prysm.PowBlock.Witness.GeneratedEncodeFastPath.initial_state
#print axioms Prysm.PowBlock.Witness.GeneratedEncodeFastPath.labels_fresh_at_0
#print axioms Prysm.PowBlock.Witness.GeneratedEncodeFastPath.labels_fresh_copy_model
#print axioms Prysm.PowBlock.Witness.GeneratedEncodeFastPath.placed_at_0
#print axioms Prysm.PowBlock.Witness.GeneratedEncodeFastPath.placed_copy_model
#print axioms Prysm.PowBlock.Witness.GeneratedEncodeFastPath.host
#print axioms Prysm.PowBlock.Witness.GeneratedEncodeFastPath.mem
#print axioms Prysm.PowBlock.Witness.GeneratedEncodeFastPath.runs_empty
#print axioms Prysm.PowBlock.Witness.GeneratedEncodeFastPath.runs_prefix
#print axioms Prysm.PowBlock.Witness.GeneratedEncodeFastPath.word_bytes
#print axioms Prysm.PowBlock.Witness.GeneratedEncodeFastPath.zeros
