import Prysm.CommitteeIndex.GeneratedDecodeAccept
import Prysm.CommitteeIndex.DecodeAcceptFunctionSpec
import Prysm.CommitteeIndex.WitnessGeneratedDecodeAccept
import Prysm.CommitteeIndex.DecodeRejectSize
import Prysm.CommitteeIndex.WitnessDecodeRejectSize
import Prysm.CommitteeIndex.DecodeSpec

/-! Hand list of the `CommitteeIndex` declarations for `gen/checks/axioms_gate.py`.
Each name must be in the declaration dump and use only the standard axioms. -/

#print axioms Prysm.CommitteeIndex.Decode.generated_accept
#print axioms Prysm.CommitteeIndex.Decode.generated_accept_kind
#print axioms Prysm.CommitteeIndex.Decode.accept_function_spec_holds
#print axioms Prysm.CommitteeIndex.Witness.GeneratedDecodeAccept.witness_mem
#print axioms Prysm.CommitteeIndex.Witness.GeneratedDecodeAccept.runs
#print axioms Prysm.CommitteeIndex.Witness.GeneratedDecodeAccept.runs_function_spec
#print axioms Prysm.CommitteeIndex.Decode.reject_size
#print axioms Prysm.CommitteeIndex.Witness.DecodeRejectSize.runs
#print axioms Prysm.CommitteeIndex.Witness.DecodeRejectSize.InputLength9.runs
#print axioms Prysm.CommitteeIndex.Witness.DecodeRejectSize.InputLength300.runs
#print axioms Prysm.CommitteeIndex.Decode.accept_spec
#print axioms Prysm.CommitteeIndex.Decode.reject_size_spec
#print axioms Prysm.CommitteeIndex.Decode.reject_complete
#print axioms Prysm.CommitteeIndex.Decode.reject_format_len
