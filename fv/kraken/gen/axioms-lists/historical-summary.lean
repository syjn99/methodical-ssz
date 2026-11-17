import Prysm.HistoricalSummary.GeneratedDecodeAccept
import Prysm.HistoricalSummary.Spec
import Prysm.HistoricalSummary.DecodeSpec
import Prysm.HistoricalSummary.WitnessGeneratedDecodeAccept
import Prysm.HistoricalSummary.WitnessGeneratedDecodeRejectSize
import Prysm.HistoricalSummary.Code
import Prysm.HistoricalSummary.GeneratedEncodeFastPath
import Prysm.HistoricalSummary.GeneratedEncodeFastPathSpec
import Prysm.HistoricalSummary.WitnessGeneratedEncodeFastPath

/-! Hand list of the `HistoricalSummary` declarations for `gen/checks/axioms_gate.py`.
Each name must be in the declaration dump and use only the standard axioms. -/

#print axioms Prysm.HistoricalSummary.Decode.generated_BlockSummaryRoot_segment
#print axioms Prysm.HistoricalSummary.Decode.generated_BlockSummaryRoot_segment_kind
#print axioms Prysm.HistoricalSummary.Decode.generated_StateSummaryRoot_segment
#print axioms Prysm.HistoricalSummary.Decode.generated_StateSummaryRoot_segment_kind
#print axioms Prysm.HistoricalSummary.Decode.generated_accept
#print axioms Prysm.HistoricalSummary.Decode.generated_accept_kind
#print axioms Prysm.HistoricalSummary.Decode.generated_epilogue
#print axioms Prysm.HistoricalSummary.Decode.generated_epilogue_kind
#print axioms Prysm.HistoricalSummary.Decode.generated_field_1
#print axioms Prysm.HistoricalSummary.Decode.generated_field_1_kind
#print axioms Prysm.HistoricalSummary.Decode.generated_field_2
#print axioms Prysm.HistoricalSummary.Decode.generated_field_2_kind
#print axioms Prysm.HistoricalSummary.Decode.generated_head
#print axioms Prysm.HistoricalSummary.Decode.generated_head_kind
#print axioms Prysm.HistoricalSummary.Decode.generated_reject
#print axioms Prysm.HistoricalSummary.Decode.generated_reject_kind
#print axioms Prysm.HistoricalSummary.Decode.generated_directive_37
#print axioms Prysm.HistoricalSummary.Decode.generated_directive_37_kind
#print axioms Prysm.HistoricalSummary.Decode.generated_directive_38
#print axioms Prysm.HistoricalSummary.Decode.generated_directive_38_kind
#print axioms Prysm.HistoricalSummary.Decode.generated_directive_45
#print axioms Prysm.HistoricalSummary.Decode.generated_directive_45_kind
#print axioms Prysm.HistoricalSummary.Decode.generated_directive_46
#print axioms Prysm.HistoricalSummary.Decode.generated_directive_46_kind
#print axioms Prysm.HistoricalSummary.Decode.generated_directive_72
#print axioms Prysm.HistoricalSummary.Decode.generated_directive_72_kind
#print axioms Prysm.HistoricalSummary.Decode.generated_directive_73
#print axioms Prysm.HistoricalSummary.Decode.generated_directive_73_kind
#print axioms Prysm.HistoricalSummary.Decode.generated_directive_80
#print axioms Prysm.HistoricalSummary.Decode.generated_directive_80_kind
#print axioms Prysm.HistoricalSummary.Decode.generated_directive_81
#print axioms Prysm.HistoricalSummary.Decode.generated_directive_81_kind
#print axioms Prysm.HistoricalSummary.checker_wellFormed
#print axioms Prysm.HistoricalSummary.SszValue.accepted_is_encoding
#print axioms Prysm.HistoricalSummary.SszValue.encode_size
#print axioms Prysm.HistoricalSummary.SszValue.roundtrip
#print axioms Prysm.HistoricalSummary.SszValue.serialize_eq
#print axioms Prysm.HistoricalSummary.SszValue.serialize_eq_checker
#print axioms Prysm.HistoricalSummary.SszValue.spec_accepts_iff
#print axioms Prysm.HistoricalSummary.SszValue.spec_rejects
#print axioms Prysm.HistoricalSummary.SszValue.toValue_fits
#print axioms Prysm.HistoricalSummary.SszValue.toValue_fits_checker
#print axioms Prysm.HistoricalSummary.SszValue.toValue_injective
#print axioms Prysm.HistoricalSummary.SszValue.toValue_surjective
#print axioms Prysm.HistoricalSummary.SszValue.toValue_surjective'
#print axioms Prysm.HistoricalSummary.desc_checker
#print axioms Prysm.HistoricalSummary.desc_deserialize_checker
#print axioms Prysm.HistoricalSummary.desc_fixedSize
#print axioms Prysm.HistoricalSummary.desc_serialize_checker
#print axioms Prysm.HistoricalSummary.desc_wellFormed
#print axioms Prysm.HistoricalSummary.Decode.accept_spec
#print axioms Prysm.HistoricalSummary.Decode.reject_complete
#print axioms Prysm.HistoricalSummary.Decode.reject_size_spec
#print axioms Prysm.HistoricalSummary.Witness.GeneratedDecodeAccept.program_length
#print axioms Prysm.HistoricalSummary.Witness.GeneratedDecodeAccept.labels_fresh_at_113
#print axioms Prysm.HistoricalSummary.Witness.GeneratedDecodeAccept.labels_fresh_at_119
#print axioms Prysm.HistoricalSummary.Witness.GeneratedDecodeAccept.labels_fresh_at_9
#print axioms Prysm.HistoricalSummary.Witness.GeneratedDecodeAccept.placed_at_113
#print axioms Prysm.HistoricalSummary.Witness.GeneratedDecodeAccept.placed_at_119
#print axioms Prysm.HistoricalSummary.Witness.GeneratedDecodeAccept.placed_at_9
#print axioms Prysm.HistoricalSummary.Witness.GeneratedDecodeAccept.runs
#print axioms Prysm.HistoricalSummary.Witness.GeneratedDecodeAccept.label_bump_pointer
#print axioms Prysm.HistoricalSummary.Witness.GeneratedDecodeAccept.label_write_barrier
#print axioms Prysm.HistoricalSummary.Witness.GeneratedDecodeAccept.lift_heap
#print axioms Prysm.HistoricalSummary.Witness.GeneratedDecodeAccept.host_program_eq
#print axioms Prysm.HistoricalSummary.Witness.GeneratedDecodeRejectSize.program_length
#print axioms Prysm.HistoricalSummary.Witness.GeneratedDecodeRejectSize.labels_fresh_at_1
#print axioms Prysm.HistoricalSummary.Witness.GeneratedDecodeRejectSize.placed_at_1
#print axioms Prysm.HistoricalSummary.Witness.GeneratedDecodeRejectSize.runs
#print axioms Prysm.HistoricalSummary.Witness.GeneratedDecodeRejectSize.label_err_size
#print axioms Prysm.HistoricalSummary.Code.marshalSSZTo
#print axioms Prysm.HistoricalSummary.Encode.generated_epilogue
#print axioms Prysm.HistoricalSummary.Encode.generated_epilogue_kind
#print axioms Prysm.HistoricalSummary.Encode.generated_field_0
#print axioms Prysm.HistoricalSummary.Encode.generated_field_0_kind
#print axioms Prysm.HistoricalSummary.Encode.generated_field_1
#print axioms Prysm.HistoricalSummary.Encode.generated_field_1_kind
#print axioms Prysm.HistoricalSummary.Encode.generated_fast
#print axioms Prysm.HistoricalSummary.Encode.generated_fast_kind
#print axioms Prysm.HistoricalSummary.Encode.generated_head
#print axioms Prysm.HistoricalSummary.Encode.generated_head_kind
#print axioms Prysm.HistoricalSummary.Encode.generated_layout
#print axioms Prysm.HistoricalSummary.SszValue.encode_toList_generated
#print axioms Prysm.HistoricalSummary.Encode.generated_fast_spec
#print axioms Prysm.HistoricalSummary.Encode.generated_fast_split
#print axioms Prysm.HistoricalSummary.Witness.GeneratedEncodeFastPath.program
#print axioms Prysm.HistoricalSummary.Witness.GeneratedEncodeFastPath.program_length
#print axioms Prysm.HistoricalSummary.Witness.GeneratedEncodeFastPath.block
#print axioms Prysm.HistoricalSummary.Witness.GeneratedEncodeFastPath.initial_state
#print axioms Prysm.HistoricalSummary.Witness.GeneratedEncodeFastPath.labels_fresh_at_0
#print axioms Prysm.HistoricalSummary.Witness.GeneratedEncodeFastPath.labels_fresh_copy_model
#print axioms Prysm.HistoricalSummary.Witness.GeneratedEncodeFastPath.placed_at_0
#print axioms Prysm.HistoricalSummary.Witness.GeneratedEncodeFastPath.placed_copy_model
#print axioms Prysm.HistoricalSummary.Witness.GeneratedEncodeFastPath.host
#print axioms Prysm.HistoricalSummary.Witness.GeneratedEncodeFastPath.runs_empty
#print axioms Prysm.HistoricalSummary.Witness.GeneratedEncodeFastPath.runs_prefix
#print axioms Prysm.HistoricalSummary.Witness.GeneratedEncodeFastPath.mem
#print axioms Prysm.HistoricalSummary.Witness.GeneratedEncodeFastPath.word_bytes
#print axioms Prysm.HistoricalSummary.Witness.GeneratedEncodeFastPath.zeros
