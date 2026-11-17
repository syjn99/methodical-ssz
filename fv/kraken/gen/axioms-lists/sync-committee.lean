import Prysm.SyncCommittee.DecodeRejectSize
import Prysm.SyncCommittee.DecodeLoop
import Prysm.SyncCommittee.DecodeAccept
import Prysm.SyncCommittee.DecodeSpec
import Prysm.SyncCommittee.SpecEquivalence
import Prysm.SyncCommittee.WitnessDecodeAccept
import Prysm.SyncCommittee.WitnessDecodeRejectSize

/-! Hand list of the `SyncCommittee` declarations for `gen/checks/axioms_gate.py`.
Each name must be in the declaration dump and use only the standard axioms. -/

#print axioms Prysm.SyncCommittee.Decode.reject_size
#print axioms Prysm.SyncCommittee.Decode.iter
#print axioms Prysm.SyncCommittee.Decode.loop
#print axioms Prysm.SyncCommittee.Decode.exit
#print axioms Prysm.SyncCommittee.Decode.accept
#print axioms Prysm.SyncCommittee.Decode.accept_spec
#print axioms Prysm.SyncCommittee.Decode.reject_size_spec
#print axioms Prysm.SyncCommittee.Decode.reject_complete
#print axioms Prysm.SyncCommittee.desc_deserialize_checker
#print axioms Prysm.SyncCommittee.Witness.DecodeAccept.runs
#print axioms Prysm.SyncCommittee.Witness.DecodeRejectSize.runs
