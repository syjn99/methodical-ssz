import Prysm.ValidatorIndex.GeneratedDecodeAccept
import Prysm.ValidatorIndex.DecodeAcceptFunctionSpec
import Prysm.ValidatorIndex.WitnessGeneratedDecodeAccept
import Prysm.ValidatorIndex.DecodeRejectSize
import Prysm.ValidatorIndex.WitnessDecodeRejectSize
import Prysm.ValidatorIndex.EncodeSpec
import Prysm.ValidatorIndex.WitnessEncodeFastPath
import Prysm.ValidatorIndex.EncodeGrowFirstSite
import Prysm.ValidatorIndex.WitnessEncodeGrowFirstSite
import Prysm.ValidatorIndex.EncodeCoverFramed
import Prysm.ValidatorIndex.WitnessEncodeCoverFramed
import Prysm.ValidatorIndex.DecodeSpec

/-! Hand list of the `ValidatorIndex` declarations for `gen/checks/axioms_gate.py`.
Each name must be in the declaration dump and use only the standard axioms. -/

#print axioms Prysm.ValidatorIndex.Decode.generated_accept
#print axioms Prysm.ValidatorIndex.Decode.generated_accept_kind
#print axioms Prysm.ValidatorIndex.Decode.accept_function_spec_holds
#print axioms Prysm.ValidatorIndex.Witness.GeneratedDecodeAccept.witness_mem
#print axioms Prysm.ValidatorIndex.Witness.GeneratedDecodeAccept.runs
#print axioms Prysm.ValidatorIndex.Witness.GeneratedDecodeAccept.runs_function_spec
#print axioms Prysm.ValidatorIndex.Decode.reject_size
#print axioms Prysm.ValidatorIndex.Witness.DecodeRejectSize.runs
#print axioms Prysm.ValidatorIndex.Witness.DecodeRejectSize.InputLength9.runs_length_9
#print axioms Prysm.ValidatorIndex.Witness.DecodeRejectSize.InputLength300.runs_length_300
#print axioms Prysm.ValidatorIndex.Encode.fast_path
#print axioms Prysm.ValidatorIndex.Encode.fast_path_spec
#print axioms Prysm.ValidatorIndex.Witness.EncodeFastPath.runs_empty
#print axioms Prysm.ValidatorIndex.Witness.EncodeFastPath.runs_prefix
#print axioms Prysm.ValidatorIndex.Encode.grow_first_site
#print axioms Prysm.ValidatorIndex.Witness.EncodeGrowFirstSite.runs
#print axioms Prysm.ValidatorIndex.Witness.EncodeGrowFirstSite.runs_empty
#print axioms Prysm.ValidatorIndex.Encode.cover_framed
#print axioms Prysm.ValidatorIndex.Witness.EncodeCoverFramed.runs
#print axioms Prysm.ValidatorIndex.Decode.accept_spec
#print axioms Prysm.ValidatorIndex.Decode.reject_size_spec
#print axioms Prysm.ValidatorIndex.Decode.reject_complete
