import Prysm.AttestationData.Spec
import Prysm.Slot.DecodeAccept
import Prysm.Slot.WitnessDecodeAccept
import Prysm.CommitteeIndex.WitnessDecodeAccept
import Prysm.Checkpoint.WitnessDecodeFunctionSpecAsNestedField
import Prysm.Checkpoint.WitnessEncodeFunctionSpecAsNestedField
import Prysm.AttestationData.DecodeSpec
import Prysm.AttestationData.WitnessDecodeAccept
import Prysm.AttestationData.WitnessDecodeRejectSize

-- AttestationData set: the AttestationData, Slot and CommitteeIndex theorems and the Checkpoint function specifications.
#print axioms Prysm.AttestationData.desc_checker
#print axioms Prysm.AttestationData.desc_serialize_checker
#print axioms Prysm.AttestationData.desc_deserialize_checker
#print axioms Prysm.AttestationData.SszValue.serialize_eq
#print axioms Prysm.AttestationData.SszValue.roundtrip
#print axioms Prysm.AttestationData.SszValue.spec_accepts_iff
#print axioms Prysm.AttestationData.SszValue.spec_rejects
#print axioms Prysm.Slot.Decode.accept
#print axioms Prysm.Slot.Decode.accept_function_spec_holds
#print axioms Prysm.CommitteeIndex.Decode.accept
#print axioms Prysm.CommitteeIndex.Decode.accept_function_spec_holds
#print axioms Prysm.Slot.Witness.DecodeAccept.runs
#print axioms Prysm.Slot.Witness.DecodeAccept.runs_function_spec
#print axioms Prysm.CommitteeIndex.Witness.DecodeAccept.runs
#print axioms Prysm.CommitteeIndex.Witness.DecodeAccept.runs_function_spec
#print axioms Prysm.Checkpoint.Decode.accept_function_spec_holds
#print axioms Prysm.Checkpoint.Encode.fast_path_function_spec_holds
#print axioms Prysm.Checkpoint.Witness.DecodeFunctionSpecAsNestedField.runs_function_spec
#print axioms Prysm.Checkpoint.Witness.EncodeFunctionSpecAsNestedField.runs_function_spec
#print axioms Prysm.AttestationData.Decode.head
#print axioms Prysm.AttestationData.Decode.block_root
#print axioms Prysm.AttestationData.Decode.source
#print axioms Prysm.AttestationData.Decode.target
#print axioms Prysm.AttestationData.Decode.accept
#print axioms Prysm.AttestationData.Decode.reject_size
#print axioms Prysm.AttestationData.Decode.slot_err_unreachable
#print axioms Prysm.AttestationData.Decode.committee_index_err_unreachable
#print axioms Prysm.AttestationData.Decode.source_err_unreachable
#print axioms Prysm.AttestationData.Decode.target_err_unreachable
#print axioms Prysm.AttestationData.Decode.accept_spec
#print axioms Prysm.AttestationData.Decode.reject_size_spec
#print axioms Prysm.AttestationData.Decode.reject_complete
#print axioms Prysm.AttestationData.bump_newobject72
#print axioms Prysm.AttestationData.Witness.DecodeAccept.runs
#print axioms Prysm.AttestationData.Witness.DecodeRejectSize.runs
