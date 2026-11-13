import Prysm.SyncAggregate.DecodeRejectSize
import Prysm.SyncAggregate.DecodeAccept
import Prysm.SyncAggregate.DecodeSpec
import Prysm.SyncAggregate.SpecEquivalence
import Prysm.SyncAggregate.WitnessDecodeAccept
import Prysm.SyncCommittee.DecodeRejectSize
import Prysm.SyncCommittee.DecodeAccept
import Prysm.SyncCommittee.DecodeSpec
import Prysm.SyncCommittee.SpecEquivalence
import Prysm.RuntimeModel.BumpAllocatorByteSliceDispatch
import Prysm.SyncCommittee.WitnessDecodeAccept

/-! Hand list of the SyncAggregate and SyncCommittee decoder theorems for `gen/checks/axioms_gate.py` ("must exist" names;
every name also gets the axiom check). -/

#print axioms Prysm.SyncAggregate.Decode.reject_size
#print axioms Prysm.SyncAggregate.Decode.accept
#print axioms Prysm.SyncAggregate.Decode.accept_spec
#print axioms Prysm.SyncAggregate.Decode.reject_size_spec
#print axioms Prysm.SyncAggregate.Decode.reject_complete
#print axioms Prysm.SyncAggregate.desc_deserialize_checker
#print axioms Prysm.SyncAggregate.Witness.DecodeAccept.runs
#print axioms Prysm.SyncCommittee.Decode.reject_size
#print axioms Prysm.SyncCommittee.Decode.iter
#print axioms Prysm.SyncCommittee.Decode.loop
#print axioms Prysm.SyncCommittee.Decode.exit
#print axioms Prysm.SyncCommittee.Decode.accept
#print axioms Prysm.SyncCommittee.Decode.accept_spec
#print axioms Prysm.SyncCommittee.Decode.reject_size_spec
#print axioms Prysm.SyncCommittee.Decode.reject_complete
#print axioms Prysm.SyncCommittee.desc_deserialize_checker
#print axioms Prysm.RuntimeModel.bump_makeslice_byte_slice_dispatch_size1
#print axioms Prysm.RuntimeModel.bump_makeslice_byte_slice_dispatch_size24
#print axioms Prysm.SyncCommittee.Witness.DecodeAccept.runs
