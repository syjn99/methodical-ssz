import Prysm.Slot.GeneratedDecodeAccept
import Prysm.Slot.DecodeAcceptFunctionSpec
import Prysm.Slot.WitnessGeneratedDecodeAccept
import Prysm.Slot.Size
import Prysm.Slot.WitnessSize
import Prysm.Slot.EncodeSpec
import Prysm.Slot.WitnessEncodeFastPath
import Prysm.Slot.EncodeGrowFirstSite
import Prysm.Slot.WitnessEncodeGrowFirstSite
import Prysm.Slot.EncodeCoverFramed
import Prysm.Slot.WitnessEncodeCoverFramed
import Prysm.Slot.Marshal
import Prysm.Slot.WitnessMarshal
import Prysm.Slot.DecodeRejectSize
import Prysm.Slot.WitnessDecodeRejectSize
import Prysm.Slot.DecodeSpec

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
#print axioms Prysm.Slot.Encode.grow_first_site
#print axioms Prysm.Slot.Witness.EncodeGrowFirstSite.runs
#print axioms Prysm.Slot.Witness.EncodeGrowFirstSite.runs_empty
#print axioms Prysm.Slot.Encode.cover_framed
#print axioms Prysm.Slot.Witness.EncodeCoverFramed.runs
#print axioms Prysm.Slot.Marshal.result
#print axioms Prysm.Slot.Marshal.result_spec
#print axioms Prysm.Slot.Witness.Marshal.runs
#print axioms Prysm.Slot.Decode.reject_size
#print axioms Prysm.Slot.Witness.DecodeRejectSize.runs
#print axioms Prysm.Slot.Witness.DecodeRejectSize.InputLength9.runs
#print axioms Prysm.Slot.Witness.DecodeRejectSize.InputLength300.runs
#print axioms Prysm.Slot.Decode.accept_spec
#print axioms Prysm.Slot.Decode.reject_size_spec
#print axioms Prysm.Slot.Decode.reject_complete
