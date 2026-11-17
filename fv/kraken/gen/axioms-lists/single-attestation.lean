import Prysm.SingleAttestation.SpecEquivalence
import Prysm.SingleAttestation.Spec
import Prysm.SingleAttestation.DecodeAcceptHead
import Prysm.SingleAttestation.DecodeAcceptData
import Prysm.SingleAttestation.DecodeAcceptSignature
import Prysm.SingleAttestation.DecodeAccept
import Prysm.SingleAttestation.DecodeRejectSize
import Prysm.SingleAttestation.DecodeSpec
import Prysm.SingleAttestation.DecodeErrorUnreachable
import Prysm.SingleAttestation.WitnessDecodeAccept
import Prysm.SingleAttestation.WitnessDecodeRejectSize
import Prysm.SingleAttestation.WitnessDecodeErrorUnreachable

/-! Hand list of the `SingleAttestation` declarations for `gen/checks/axioms_gate.py`.
Each name must be in the declaration dump and use only the standard axioms. -/

#print axioms Prysm.SingleAttestation.desc_checker
#print axioms Prysm.SingleAttestation.desc_serialize_checker
#print axioms Prysm.SingleAttestation.desc_deserialize_checker
#print axioms Prysm.SingleAttestation.SszValue.serialize_eq
#print axioms Prysm.SingleAttestation.SszValue.roundtrip
#print axioms Prysm.SingleAttestation.SszValue.spec_accepts_iff
#print axioms Prysm.SingleAttestation.SszValue.spec_rejects
#print axioms Prysm.SingleAttestation.Decode.head
#print axioms Prysm.SingleAttestation.Decode.data
#print axioms Prysm.SingleAttestation.Decode.signature
#print axioms Prysm.SingleAttestation.Decode.accept
#print axioms Prysm.SingleAttestation.Decode.reject_size
#print axioms Prysm.SingleAttestation.Decode.accept_spec
#print axioms Prysm.SingleAttestation.Decode.reject_size_spec
#print axioms Prysm.SingleAttestation.Decode.reject_complete
#print axioms Prysm.SingleAttestation.Decode.committee_id_err_unreachable
#print axioms Prysm.SingleAttestation.Decode.attester_index_err_unreachable
#print axioms Prysm.SingleAttestation.Decode.data_err_unreachable
#print axioms Prysm.SingleAttestation.Witness.DecodeAccept.runs
#print axioms Prysm.SingleAttestation.Witness.DecodeRejectSize.runs
#print axioms Prysm.SingleAttestation.Witness.DecodeErrorUnreachable.runs
