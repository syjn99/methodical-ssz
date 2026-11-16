import Prysm.Epoch.DecodeAccept
import Prysm.Epoch.WitnessDecodeAccept
import Prysm.Epoch.DecodeRejectSize
import Prysm.Epoch.WitnessDecodeRejectSize

/-! Hand list of the `Epoch` declarations for `gen/checks/axioms_gate.py`.
Each name must be in the declaration dump and use only the standard axioms. -/

#print axioms Prysm.Epoch.Decode.accept
#print axioms Prysm.Epoch.Decode.accept_function_spec_holds
#print axioms Prysm.Epoch.Witness.DecodeAccept.runs
#print axioms Prysm.Epoch.Witness.DecodeAccept.runs_function_spec
#print axioms Prysm.Epoch.Decode.reject_size
#print axioms Prysm.Epoch.Witness.DecodeRejectSize.runs
#print axioms Prysm.Epoch.Witness.DecodeRejectSize.InputLength9.runs
#print axioms Prysm.Epoch.Witness.DecodeRejectSize.InputLength300.runs
