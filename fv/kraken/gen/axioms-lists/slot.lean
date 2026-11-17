import Prysm.Slot.GeneratedDecodeAccept
import Prysm.Slot.DecodeAcceptFunctionSpec
import Prysm.Slot.WitnessGeneratedDecodeAccept
import Prysm.Slot.Size
import Prysm.Slot.WitnessSize
import Prysm.Slot.EncodeSpec
import Prysm.Slot.WitnessEncodeFastPath

/-! Hand list of the `Slot` declarations for `gen/checks/axioms_gate.py`.
Each name must be in the declaration dump and use only the standard axioms. -/

#print axioms Prysm.Slot.Decode.generated_accept
#print axioms Prysm.Slot.Decode.generated_accept_kind
#print axioms Prysm.Slot.Decode.accept_function_spec_holds
#print axioms Prysm.Slot.Witness.GeneratedDecodeAccept.witness_mem
#print axioms Prysm.Slot.Witness.GeneratedDecodeAccept.runs
#print axioms Prysm.Slot.Witness.GeneratedDecodeAccept.runs_function_spec
#print axioms Prysm.Slot.Size.result
#print axioms Prysm.Slot.Size.result_spec
#print axioms Prysm.Slot.Witness.Size.runs
#print axioms Prysm.Slot.Encode.fast_path
#print axioms Prysm.Slot.Encode.fast_path_spec
#print axioms Prysm.Slot.Witness.EncodeFastPath.runs_empty
#print axioms Prysm.Slot.Witness.EncodeFastPath.runs_prefix
