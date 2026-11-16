import Prysm.Deposit.DecodeRejectSize
import Prysm.Deposit.DecodeAccept
import Prysm.Deposit.Spec
import Prysm.Deposit.DecodeSpec
import Prysm.Deposit.SpecEquivalence
import Prysm.Deposit.WitnessBumpAllocator
import Prysm.Deposit.WitnessDecodeRejectSize
import Prysm.Deposit.WitnessDecodeAccept

/-! Hand list of the `Deposit` declarations for `gen/checks/axioms_gate.py`.
Each name must be in the declaration dump and use only the standard axioms. -/

#print axioms Prysm.Deposit.Decode.reject_size
#print axioms Prysm.Deposit.Decode.accept
#print axioms Prysm.Deposit.toValue_serialize
#print axioms Prysm.Deposit.spec_accepts_iff
#print axioms Prysm.Deposit.Decode.accept_spec
#print axioms Prysm.Deposit.Decode.reject_size_spec
#print axioms Prysm.Deposit.Decode.reject_complete
#print axioms Prysm.Deposit.desc_deserialize_checker
#print axioms Prysm.Deposit.bump_newobject120
#print axioms Prysm.Deposit.Witness.DecodeRejectSize.runs
#print axioms Prysm.Deposit.Witness.DecodeAccept.runs
