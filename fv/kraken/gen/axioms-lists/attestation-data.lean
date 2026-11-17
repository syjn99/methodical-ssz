import Prysm.AttestationData.SpecEquivalence
import Prysm.AttestationData.Spec
import Prysm.AttestationData.DecodeAcceptHead
import Prysm.AttestationData.DecodeAcceptBlockRoot
import Prysm.AttestationData.DecodeAcceptSource
import Prysm.AttestationData.DecodeAcceptTarget
import Prysm.AttestationData.DecodeAccept
import Prysm.AttestationData.DecodeRejectSize
import Prysm.AttestationData.DecodeSpec
import Prysm.AttestationData.WitnessBumpAllocator
import Prysm.AttestationData.WitnessDecodeAccept
import Prysm.AttestationData.WitnessDecodeRejectSize
import Prysm.AttestationData.Size
import Prysm.AttestationData.WitnessSize
import Prysm.AttestationData.EncodeSpec
import Prysm.AttestationData.WitnessEncodeFastPath

/-! Hand list of the `AttestationData` declarations for `gen/checks/axioms_gate.py`.
Each name must be in the declaration dump and use only the standard axioms. -/

#print axioms Prysm.AttestationData.desc_checker
#print axioms Prysm.AttestationData.desc_serialize_checker
#print axioms Prysm.AttestationData.desc_deserialize_checker
#print axioms Prysm.AttestationData.SszValue.serialize_eq
#print axioms Prysm.AttestationData.SszValue.roundtrip
#print axioms Prysm.AttestationData.SszValue.spec_accepts_iff
#print axioms Prysm.AttestationData.SszValue.spec_rejects
#print axioms Prysm.AttestationData.Decode.head
#print axioms Prysm.AttestationData.Decode.block_root
#print axioms Prysm.AttestationData.Decode.source
#print axioms Prysm.AttestationData.Decode.target
#print axioms Prysm.AttestationData.Decode.accept
#print axioms Prysm.AttestationData.Decode.reject_size
#print axioms Prysm.AttestationData.Decode.accept_spec
#print axioms Prysm.AttestationData.Decode.reject_size_spec
#print axioms Prysm.AttestationData.Decode.reject_complete
#print axioms Prysm.AttestationData.bump_newobject72
#print axioms Prysm.AttestationData.Witness.DecodeAccept.runs
#print axioms Prysm.AttestationData.Witness.DecodeRejectSize.runs
#print axioms Prysm.AttestationData.Size.result
#print axioms Prysm.AttestationData.Size.result_spec
#print axioms Prysm.AttestationData.Witness.Size.runs
#print axioms Prysm.AttestationData.Encode.head_slot
#print axioms Prysm.AttestationData.Encode.head_index
#print axioms Prysm.AttestationData.Encode.head_root
#print axioms Prysm.AttestationData.Encode.source_call
#print axioms Prysm.AttestationData.Encode.target_call
#print axioms Prysm.AttestationData.Encode.head
#print axioms Prysm.AttestationData.Encode.calls
#print axioms Prysm.AttestationData.Encode.fast_path
#print axioms Prysm.AttestationData.Encode.fast_path_spec
#print axioms Prysm.AttestationData.Witness.EncodeFastPath.mem_premise
#print axioms Prysm.AttestationData.Witness.EncodeFastPath.runs_empty
#print axioms Prysm.AttestationData.Witness.EncodeFastPath.Prefix.mem_premise
#print axioms Prysm.AttestationData.Witness.EncodeFastPath.runs_prefix
