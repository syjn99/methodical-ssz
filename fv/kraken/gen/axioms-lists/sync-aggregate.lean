import Prysm.SyncAggregate.DecodeRejectSize
import Prysm.SyncAggregate.DecodeAccept
import Prysm.SyncAggregate.DecodeSpec
import Prysm.SyncAggregate.SpecEquivalence
import Prysm.SyncAggregate.WitnessDecodeAccept

/-! Hand list of the `SyncAggregate` declarations for `gen/checks/axioms_gate.py`.
Each name must be in the declaration dump and use only the standard axioms. -/

#print axioms Prysm.SyncAggregate.Decode.reject_size
#print axioms Prysm.SyncAggregate.Decode.accept
#print axioms Prysm.SyncAggregate.Decode.accept_spec
#print axioms Prysm.SyncAggregate.Decode.reject_size_spec
#print axioms Prysm.SyncAggregate.Decode.reject_complete
#print axioms Prysm.SyncAggregate.desc_deserialize_checker
#print axioms Prysm.SyncAggregate.Witness.DecodeAccept.runs
