import Prysm.Deposit_Data.Spec
import Prysm.Deposit_Data.DecodeSpec
import Prysm.Deposit_Data.WitnessGeneratedDecodeAccept
import Prysm.Deposit_Data.WitnessGeneratedDecodeRejectSize
import Prysm.Deposit_Data.GeneratedDecodeAccept
import Prysm.Deposit_Data.Code
import Prysm.Deposit_Data.GeneratedEncodeFastPath
import Prysm.Deposit_Data.GeneratedEncodeFastPathSpec
import Prysm.Deposit_Data.EncodeFastPathStatements
import Prysm.Deposit_Data.EncodeFastPathStatementTie
import Prysm.Deposit_Data.WitnessGeneratedEncodeFastPath

/-! Hand list of the `Deposit_Data` declarations for `gen/checks/axioms_gate.py`.
Each name must be in the declaration dump and use only the standard axioms. -/

#print axioms Prysm.Deposit_Data.desc_checker
#print axioms Prysm.Deposit_Data.desc_wellFormed
#print axioms Prysm.Deposit_Data.desc_fixedSize
#print axioms Prysm.Deposit_Data.desc_serialize_checker
#print axioms Prysm.Deposit_Data.SszValue.encode_size
#print axioms Prysm.Deposit_Data.SszValue.toValue_fits
#print axioms Prysm.Deposit_Data.SszValue.toValue_injective
#print axioms Prysm.Deposit_Data.SszValue.toValue_surjective
#print axioms Prysm.Deposit_Data.SszValue.serialize_eq
#print axioms Prysm.Deposit_Data.SszValue.roundtrip
#print axioms Prysm.Deposit_Data.SszValue.accepted_is_encoding
#print axioms Prysm.Deposit_Data.SszValue.spec_accepts_iff
#print axioms Prysm.Deposit_Data.SszValue.spec_rejects
#print axioms Prysm.Deposit_Data.desc_deserialize_checker
#print axioms Prysm.Deposit_Data.Decode.accept_spec
#print axioms Prysm.Deposit_Data.Decode.reject_size_spec
#print axioms Prysm.Deposit_Data.Decode.reject_complete
#print axioms Prysm.Deposit_Data.Witness.GeneratedDecodeAccept.runs
#print axioms Prysm.Deposit_Data.Witness.GeneratedDecodeRejectSize.runs
#print axioms Prysm.Deposit_Data.Decode.generated_PublicKey_segment
#print axioms Prysm.Deposit_Data.Decode.generated_PublicKey_segment_kind
#print axioms Prysm.Deposit_Data.Decode.generated_Signature_segment
#print axioms Prysm.Deposit_Data.Decode.generated_Signature_segment_kind
#print axioms Prysm.Deposit_Data.Decode.generated_WithdrawalCredentials_segment
#print axioms Prysm.Deposit_Data.Decode.generated_WithdrawalCredentials_segment_kind
#print axioms Prysm.Deposit_Data.Decode.generated_accept
#print axioms Prysm.Deposit_Data.Decode.generated_accept_kind
#print axioms Prysm.Deposit_Data.Decode.generated_epilogue
#print axioms Prysm.Deposit_Data.Decode.generated_epilogue_kind
#print axioms Prysm.Deposit_Data.Decode.generated_field_1
#print axioms Prysm.Deposit_Data.Decode.generated_field_1_kind
#print axioms Prysm.Deposit_Data.Decode.generated_field_2
#print axioms Prysm.Deposit_Data.Decode.generated_field_2_kind
#print axioms Prysm.Deposit_Data.Decode.generated_field_3
#print axioms Prysm.Deposit_Data.Decode.generated_field_3_kind
#print axioms Prysm.Deposit_Data.Decode.generated_field_4
#print axioms Prysm.Deposit_Data.Decode.generated_field_4_kind
#print axioms Prysm.Deposit_Data.Decode.generated_head
#print axioms Prysm.Deposit_Data.Decode.generated_head_kind
#print axioms Prysm.Deposit_Data.Decode.generated_reject
#print axioms Prysm.Deposit_Data.Decode.generated_reject_kind
#print axioms Prysm.Deposit_Data.Decode.generated_directive_111
#print axioms Prysm.Deposit_Data.Decode.generated_directive_111_kind
#print axioms Prysm.Deposit_Data.Decode.generated_directive_112
#print axioms Prysm.Deposit_Data.Decode.generated_directive_112_kind
#print axioms Prysm.Deposit_Data.Decode.generated_directive_119
#print axioms Prysm.Deposit_Data.Decode.generated_directive_119_kind
#print axioms Prysm.Deposit_Data.Decode.generated_directive_120
#print axioms Prysm.Deposit_Data.Decode.generated_directive_120_kind
#print axioms Prysm.Deposit_Data.Decode.generated_directive_37
#print axioms Prysm.Deposit_Data.Decode.generated_directive_37_kind
#print axioms Prysm.Deposit_Data.Decode.generated_directive_38
#print axioms Prysm.Deposit_Data.Decode.generated_directive_38_kind
#print axioms Prysm.Deposit_Data.Decode.generated_directive_45
#print axioms Prysm.Deposit_Data.Decode.generated_directive_45_kind
#print axioms Prysm.Deposit_Data.Decode.generated_directive_46
#print axioms Prysm.Deposit_Data.Decode.generated_directive_46_kind
#print axioms Prysm.Deposit_Data.Decode.generated_directive_73
#print axioms Prysm.Deposit_Data.Decode.generated_directive_73_kind
#print axioms Prysm.Deposit_Data.Decode.generated_directive_74
#print axioms Prysm.Deposit_Data.Decode.generated_directive_74_kind
#print axioms Prysm.Deposit_Data.Decode.generated_directive_81
#print axioms Prysm.Deposit_Data.Decode.generated_directive_81_kind
#print axioms Prysm.Deposit_Data.Decode.generated_directive_82
#print axioms Prysm.Deposit_Data.Decode.generated_directive_82_kind
#print axioms Prysm.Deposit_Data.Decode.generated_directive_83
#print axioms Prysm.Deposit_Data.Decode.generated_directive_83_kind
#print axioms Prysm.Deposit_Data.Decode.generated_directive_84
#print axioms Prysm.Deposit_Data.Decode.generated_directive_84_kind
#print axioms Prysm.Deposit_Data.Decode.generated_directive_85
#print axioms Prysm.Deposit_Data.Decode.generated_directive_85_kind
#print axioms Prysm.Deposit_Data.Code.marshalSSZTo
#print axioms Prysm.Deposit_Data.Encode.generated_epilogue
#print axioms Prysm.Deposit_Data.Encode.generated_epilogue_kind
#print axioms Prysm.Deposit_Data.Encode.generated_field_0
#print axioms Prysm.Deposit_Data.Encode.generated_field_0_kind
#print axioms Prysm.Deposit_Data.Encode.generated_field_1
#print axioms Prysm.Deposit_Data.Encode.generated_field_1_kind
#print axioms Prysm.Deposit_Data.Encode.generated_field_2
#print axioms Prysm.Deposit_Data.Encode.generated_field_2_kind
#print axioms Prysm.Deposit_Data.Encode.generated_field_3
#print axioms Prysm.Deposit_Data.Encode.generated_field_3_kind
#print axioms Prysm.Deposit_Data.Encode.generated_fast
#print axioms Prysm.Deposit_Data.Encode.generated_fast_kind
#print axioms Prysm.Deposit_Data.Encode.generated_head
#print axioms Prysm.Deposit_Data.Encode.generated_head_kind
#print axioms Prysm.Deposit_Data.Encode.generated_layout
#print axioms Prysm.Deposit_Data.SszValue.encode_toList_generated
#print axioms Prysm.Deposit_Data.Encode.generated_fast_spec
#print axioms Prysm.Deposit_Data.Encode.generated_fast_split
#print axioms Prysm.Deposit_Data.Encode.fast_path_statement
#print axioms Prysm.Deposit_Data.Encode.fast_path_statement_tie
#print axioms Prysm.Deposit_Data.Witness.GeneratedEncodeFastPath.program
#print axioms Prysm.Deposit_Data.Witness.GeneratedEncodeFastPath.program_length
#print axioms Prysm.Deposit_Data.Witness.GeneratedEncodeFastPath.block
#print axioms Prysm.Deposit_Data.Witness.GeneratedEncodeFastPath.initial_state
#print axioms Prysm.Deposit_Data.Witness.GeneratedEncodeFastPath.runs_empty
#print axioms Prysm.Deposit_Data.Witness.GeneratedEncodeFastPath.runs_prefix
#print axioms Prysm.Deposit_Data.Witness.GeneratedEncodeFastPath.labels_fresh_at_0
#print axioms Prysm.Deposit_Data.Witness.GeneratedEncodeFastPath.labels_fresh_copy_model
#print axioms Prysm.Deposit_Data.Witness.GeneratedEncodeFastPath.placed_at_0
#print axioms Prysm.Deposit_Data.Witness.GeneratedEncodeFastPath.placed_copy_model
#print axioms Prysm.Deposit_Data.Witness.GeneratedEncodeFastPath.host
#print axioms Prysm.Deposit_Data.Witness.GeneratedEncodeFastPath.mem
#print axioms Prysm.Deposit_Data.Witness.GeneratedEncodeFastPath.word_bytes
#print axioms Prysm.Deposit_Data.Witness.GeneratedEncodeFastPath.zeros
