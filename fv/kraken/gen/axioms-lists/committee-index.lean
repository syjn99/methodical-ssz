import Prysm.CommitteeIndex.GeneratedDecodeAccept
import Prysm.CommitteeIndex.DecodeAcceptFunctionSpec
import Prysm.CommitteeIndex.WitnessGeneratedDecodeAccept
import Prysm.CommitteeIndex.Size
import Prysm.CommitteeIndex.WitnessSize
import Prysm.CommitteeIndex.EncodeSpec
import Prysm.CommitteeIndex.WitnessEncodeFastPath
import Prysm.CommitteeIndex.EncodeGrowFirstSite
import Prysm.CommitteeIndex.WitnessEncodeGrowFirstSite
import Prysm.CommitteeIndex.EncodeCoverFramed
import Prysm.CommitteeIndex.WitnessEncodeCoverFramed
import Prysm.CommitteeIndex.Marshal
import Prysm.CommitteeIndex.WitnessMarshal
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
#print axioms Prysm.CommitteeIndex.Size.result
#print axioms Prysm.CommitteeIndex.Size.result_spec
#print axioms Prysm.CommitteeIndex.Witness.Size.runs
#print axioms Prysm.CommitteeIndex.Encode.fast_path
#print axioms Prysm.CommitteeIndex.Encode.fast_path_spec
#print axioms Prysm.CommitteeIndex.Witness.EncodeFastPath.runs_empty
#print axioms Prysm.CommitteeIndex.Witness.EncodeFastPath.runs_prefix
#print axioms Prysm.CommitteeIndex.Encode.grow_first_site
#print axioms Prysm.CommitteeIndex.Witness.EncodeGrowFirstSite.runs
#print axioms Prysm.CommitteeIndex.Witness.EncodeGrowFirstSite.runs_empty
#print axioms Prysm.CommitteeIndex.Encode.cover_framed
#print axioms Prysm.CommitteeIndex.Witness.EncodeCoverFramed.runs
#print axioms Prysm.CommitteeIndex.Marshal.result
#print axioms Prysm.CommitteeIndex.Marshal.result_spec
#print axioms Prysm.CommitteeIndex.Witness.Marshal.runs
#print axioms Prysm.CommitteeIndex.Decode.reject_size
#print axioms Prysm.CommitteeIndex.Witness.DecodeRejectSize.runs
#print axioms Prysm.CommitteeIndex.Witness.DecodeRejectSize.InputLength9.runs
#print axioms Prysm.CommitteeIndex.Witness.DecodeRejectSize.InputLength300.runs
#print axioms Prysm.CommitteeIndex.Decode.accept_spec
#print axioms Prysm.CommitteeIndex.Decode.reject_size_spec
#print axioms Prysm.CommitteeIndex.Decode.reject_complete
#print axioms Prysm.CommitteeIndex.Decode.reject_format_len
