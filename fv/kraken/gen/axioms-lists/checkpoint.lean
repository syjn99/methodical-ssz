import Prysm.Checkpoint.FunctionSpecsAsNestedField
import Prysm.Checkpoint.WitnessDecodeFunctionSpecAsNestedField
import Prysm.Checkpoint.WitnessEncodeFunctionSpecAsNestedField
import Prysm.Checkpoint.Spec
import Prysm.Checkpoint.DecodeAccept
import Prysm.Checkpoint.WitnessDecodeAccept
import Prysm.Checkpoint.DecodeRejectSize
import Prysm.Checkpoint.WitnessDecodeRejectSize
import Prysm.Checkpoint.DecodeSpec
import Prysm.Checkpoint.EncodeFastPath
import Prysm.Checkpoint.WitnessEncodeFastPath
import Prysm.Checkpoint.DecodeThenEncodeReceiver
import Prysm.Checkpoint.EncodeRejectLength
import Prysm.Checkpoint.WitnessEncodeRejectLength
import Prysm.Checkpoint.EncodeSpec
import Prysm.Checkpoint.WitnessSize
import Prysm.Checkpoint.GoValue
import Prysm.Checkpoint.DecodeThenEncode
import Prysm.Checkpoint.WitnessDecodeThenEncode
import Prysm.Checkpoint.EncodeGrowFirstSite
import Prysm.Checkpoint.WitnessEncodeGrowFirstSite
import Prysm.Checkpoint.SpecEquivalence
import Prysm.Checkpoint.WitnessDecodeAcceptSpec
import Prysm.Checkpoint.WitnessDecodeRejectSizeSpec
import Prysm.Checkpoint.EncodeTail
import Prysm.Checkpoint.EncodeTailGrow
import Prysm.Checkpoint.EncodeHead
import Prysm.Checkpoint.EncodeGrowSecondSite
import Prysm.Checkpoint.EncodeGrowAnySite
import Prysm.Checkpoint.EncodeCover
import Prysm.Checkpoint.WitnessEncodeCover
import Prysm.Checkpoint.WitnessEncodeRejectLengthCover
import Prysm.Checkpoint.EncodeGrowAnySiteThreeCases
import Prysm.Checkpoint.EncodeCoverFramed
import Prysm.Checkpoint.WitnessEncodeCoverFramed
import Prysm.Checkpoint.WitnessEncodeRejectLengthCoverFramed
import Prysm.Checkpoint.GoValueWitness
import Prysm.Checkpoint.DecodeAcceptKindTie
import Prysm.Checkpoint.DecodeRejectSizeKindTie
import Prysm.Checkpoint.GeneratedEncodeFastPath
import Prysm.Checkpoint.EncodeFastPathKindTie
import Prysm.Checkpoint.GeneratedEncodeFastPathSpec
import Prysm.Checkpoint.WitnessGeneratedEncodeFastPath

/-! Hand list of the `Checkpoint` declarations for `gen/checks/axioms_gate.py`.
Each name must be in the declaration dump and use only the standard axioms. -/

#print axioms Prysm.Checkpoint.Decode.accept_function_spec_holds
#print axioms Prysm.Checkpoint.Encode.fast_path_function_spec_holds
#print axioms Prysm.Checkpoint.Witness.DecodeFunctionSpecAsNestedField.runs_function_spec
#print axioms Prysm.Checkpoint.Witness.EncodeFunctionSpecAsNestedField.runs_function_spec
#print axioms Prysm.Checkpoint.desc_checker
#print axioms Prysm.Checkpoint.SszValue.spec_accepts_iff
#print axioms Prysm.Checkpoint.SszValue.serialize_eq
#print axioms Prysm.Checkpoint.SszValue.roundtrip
#print axioms Prysm.Checkpoint.SszValue.spec_rejects
#print axioms Prysm.Checkpoint.Decode.accept_tail
#print axioms Prysm.Checkpoint.Decode.accept
#print axioms Prysm.Checkpoint.Witness.DecodeAccept.runs
#print axioms Prysm.Checkpoint.Decode.reject_size
#print axioms Prysm.Checkpoint.Witness.DecodeRejectSize.runs
#print axioms Prysm.Checkpoint.Decode.epoch_err_unreachable
#print axioms Prysm.Checkpoint.Decode.accept_spec
#print axioms Prysm.Checkpoint.Decode.reject_size_spec
#print axioms Prysm.Checkpoint.Decode.reject_complete
#print axioms Prysm.Checkpoint.Encode.fast_path
#print axioms Prysm.Checkpoint.Witness.EncodeFastPath.runs_empty
#print axioms Prysm.Checkpoint.Witness.EncodeFastPath.runs_prefix
#print axioms Prysm.Checkpoint.DecodeThenEncode.encode_decoded_receiver
#print axioms Prysm.Checkpoint.DecodeThenEncode.round_trip_spec
#print axioms Prysm.Checkpoint.Encode.reject_length
#print axioms Prysm.Checkpoint.Witness.EncodeRejectLength.runs
#print axioms Prysm.Checkpoint.Witness.EncodeRejectLength.NonEmptyPrefix.runs
#print axioms Prysm.Checkpoint.Encode.fast_path_spec
#print axioms Prysm.Checkpoint.Size.result
#print axioms Prysm.Checkpoint.Size.result_spec
#print axioms Prysm.Checkpoint.Witness.Size.runs
#print axioms Prysm.Checkpoint.layout
#print axioms Prysm.Checkpoint.witness_decode_accept_receiver_pre
#print axioms Prysm.Checkpoint.witness_decode_accept_receiver_post
#print axioms Prysm.Checkpoint.after_decode_goValue
#print axioms Prysm.Checkpoint.witness_encode_fast_path_receiver
#print axioms Prysm.Checkpoint.witness_encode_reject_length_receiver
#print axioms Prysm.Checkpoint.goValue_rejects_bad
#print axioms Prysm.Checkpoint.DecodeThenEncode.round_trip
#print axioms Prysm.Checkpoint.Witness.DecodeThenEncode.runs
#print axioms Prysm.Checkpoint.Witness.DecodeThenEncode.receiver_go_value
#print axioms Prysm.Checkpoint.Encode.grow_first_site
#print axioms Prysm.Checkpoint.Witness.EncodeGrowFirstSite.runs
#print axioms Prysm.Checkpoint.Witness.EncodeGrowFirstSite.receiver_go_value
#print axioms Prysm.Checkpoint.desc_serialize_checker
#print axioms Prysm.Checkpoint.desc_deserialize_checker
#print axioms Prysm.Checkpoint.SszValue.toValue_injective
#print axioms Prysm.Checkpoint.Witness.DecodeAccept.runs_spec
#print axioms Prysm.Checkpoint.Witness.DecodeRejectSize.runs_spec
#print axioms Prysm.Checkpoint.Encode.tail_fit
#print axioms Prysm.Checkpoint.Encode.tail_reject
#print axioms Prysm.Checkpoint.Encode.tail_grow
#print axioms Prysm.Checkpoint.Encode.tail_grow_call
#print axioms Prysm.Checkpoint.Encode.head_fit
#print axioms Prysm.Checkpoint.Encode.head_grow
#print axioms Prysm.Checkpoint.Encode.grow_second_site
#print axioms Prysm.Checkpoint.Encode.grow_any_site
#print axioms Prysm.Checkpoint.Encode.reject_length_grow_first_site
#print axioms Prysm.Checkpoint.Encode.cover
#print axioms Prysm.Checkpoint.Encode.reject_length_cover
#print axioms Prysm.Checkpoint.Witness.EncodeCover.runs
#print axioms Prysm.Checkpoint.Witness.EncodeCover.runs_nil
#print axioms Prysm.Checkpoint.Witness.EncodeRejectLengthCover.runs
#print axioms Prysm.Checkpoint.Witness.EncodeRejectLengthCover.runs_nil
#print axioms Prysm.Checkpoint.Encode.grow_any_site_three_cases
#print axioms Prysm.Checkpoint.Encode.cover_framed
#print axioms Prysm.Checkpoint.Encode.reject_length_cover_framed
#print axioms Prysm.Checkpoint.Witness.EncodeCoverFramed.runs
#print axioms Prysm.Checkpoint.Witness.EncodeCoverFramed.runs_nil
#print axioms Prysm.Checkpoint.Witness.EncodeRejectLengthCoverFramed.runs
#print axioms Prysm.Checkpoint.Witness.EncodeRejectLengthCoverFramed.runs_nil
#print axioms Prysm.Checkpoint.witness_encode_cover_receiver
#print axioms Prysm.Checkpoint.witness_encode_reject_length_cover_receiver
#print axioms Prysm.Checkpoint.witness_encode_reject_length_cover_receiver_bad
#print axioms Prysm.Checkpoint.Decode.accept_kind_tie
#print axioms Prysm.Checkpoint.Decode.low_address
#print axioms Prysm.Checkpoint.Decode.reject_size_kind_tie
#print axioms Prysm.Checkpoint.decodeLayout
#print axioms Prysm.Checkpoint.Encode.generated_epilogue
#print axioms Prysm.Checkpoint.Encode.generated_epilogue_kind
#print axioms Prysm.Checkpoint.Encode.generated_field_0
#print axioms Prysm.Checkpoint.Encode.generated_field_0_kind
#print axioms Prysm.Checkpoint.Encode.generated_field_1
#print axioms Prysm.Checkpoint.Encode.generated_field_1_kind
#print axioms Prysm.Checkpoint.Encode.generated_fast
#print axioms Prysm.Checkpoint.Encode.generated_fast_kind
#print axioms Prysm.Checkpoint.Encode.generated_head
#print axioms Prysm.Checkpoint.Encode.generated_head_kind
#print axioms Prysm.Checkpoint.Encode.generated_fast_statement_tie
#print axioms Prysm.Checkpoint.Encode.fast_path_kind_tie
#print axioms Prysm.Checkpoint.encodeLayout
#print axioms Prysm.Checkpoint.SszValue.encode_toList_generated
#print axioms Prysm.Checkpoint.Encode.generated_fast_spec
#print axioms Prysm.Checkpoint.Encode.generated_fast_split
#print axioms Prysm.Checkpoint.Witness.GeneratedEncodeFastPath.program
#print axioms Prysm.Checkpoint.Witness.GeneratedEncodeFastPath.program_length
#print axioms Prysm.Checkpoint.Witness.GeneratedEncodeFastPath.block
#print axioms Prysm.Checkpoint.Witness.GeneratedEncodeFastPath.runs_empty
#print axioms Prysm.Checkpoint.Witness.GeneratedEncodeFastPath.runs_prefix
#print axioms Prysm.Checkpoint.Witness.GeneratedEncodeFastPath.initial_state
#print axioms Prysm.Checkpoint.Witness.GeneratedEncodeFastPath.labels_fresh_at_0
#print axioms Prysm.Checkpoint.Witness.GeneratedEncodeFastPath.labels_fresh_copy_model
#print axioms Prysm.Checkpoint.Witness.GeneratedEncodeFastPath.placed_at_0
#print axioms Prysm.Checkpoint.Witness.GeneratedEncodeFastPath.placed_copy_model
#print axioms Prysm.Checkpoint.Witness.GeneratedEncodeFastPath.host
#print axioms Prysm.Checkpoint.Witness.GeneratedEncodeFastPath.mem
#print axioms Prysm.Checkpoint.Witness.GeneratedEncodeFastPath.word_bytes
#print axioms Prysm.Checkpoint.Witness.GeneratedEncodeFastPath.zeros
