import Prysm.Epoch.GeneratedDecodeAccept
import Prysm.Epoch.DecodeAcceptFunctionSpec
import Prysm.Epoch.WitnessGeneratedDecodeAccept
import Prysm.Epoch.DecodeRejectSize
import Prysm.Epoch.WitnessDecodeRejectSize
import Prysm.Epoch.Spec
import Prysm.Epoch.DecodeSpec

/-! Hand list of the `Epoch` declarations for `gen/checks/axioms_gate.py`.
Each name must be in the declaration dump and use only the standard axioms. -/

#print axioms Prysm.Epoch.Decode.generated_accept
#print axioms Prysm.Epoch.Decode.generated_accept_kind
#print axioms Prysm.Epoch.Decode.accept_function_spec_holds
#print axioms Prysm.Epoch.Witness.GeneratedDecodeAccept.witness_mem
#print axioms Prysm.Epoch.Witness.GeneratedDecodeAccept.runs
#print axioms Prysm.Epoch.Witness.GeneratedDecodeAccept.runs_function_spec
#print axioms Prysm.Epoch.Decode.reject_size
#print axioms Prysm.Epoch.Witness.DecodeRejectSize.runs
#print axioms Prysm.Epoch.Witness.DecodeRejectSize.InputLength9.runs
#print axioms Prysm.Epoch.Witness.DecodeRejectSize.InputLength300.runs
#print axioms Prysm.Epoch.uint64_deserialize_ok
#print axioms Prysm.Epoch.uint64_spec_accepts_iff
#print axioms Prysm.Epoch.uint64_spec_rejects
#print axioms Prysm.Epoch.uint64_accepted_is_encoding
#print axioms Prysm.Epoch.Decode.accept_spec
#print axioms Prysm.Epoch.Decode.reject_size_spec
#print axioms Prysm.Epoch.Decode.reject_complete
