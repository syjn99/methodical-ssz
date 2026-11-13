import Codec.Segment.Bytes32VectorSpec
import Codec.Segment.TripleLoopSyncCommittee
import Prysm.Deposit.DecodeSpec
import Prysm.Deposit.SpecEquivalence
import Prysm.Deposit.WitnessDecodeRejectSize
import Prysm.Deposit.WitnessDecodeAccept
import Prysm.HistoricalBatch.WitnessDecodeRejectSize

/-! Hand list for `gen/checks/seg2axioms_gate.py` ("must exist" names; every name gets the axiom check). -/

#print axioms Codec.Segment.bytes32_vector_serialize
#print axioms Codec.Segment.bytes32_vector_of_bytes
#print axioms Codec.Segment.vtri_iter
#print axioms Codec.Segment.vtri_exit
#print axioms Codec.Segment.vtri_loop
#print axioms Codec.Segment.sync_committee_loop
#print axioms Prysm.Deposit.toValue_serialize
#print axioms Prysm.Deposit.spec_accepts_iff
#print axioms Prysm.Deposit.Decode.accept_spec
#print axioms Prysm.Deposit.Decode.reject_size_spec
#print axioms Prysm.Deposit.Decode.reject_complete
#print axioms Prysm.Deposit.desc_deserialize_checker
#print axioms Prysm.Deposit.bump_newobject120
#print axioms Prysm.Deposit.Witness.DecodeRejectSize.runs
#print axioms Prysm.Deposit.Witness.DecodeAccept.runs
#print axioms Prysm.HistoricalBatch.Witness.DecodeRejectSize.runs
