import Kraken.X64.Parser
import Machine.Include

/-!
# Code of `v1alpha1.AttestationData`

This module holds the program constants `Code.unmarshalSSZ`, `Code.marshalSSZTo` and `Code.sizeSSZ` of `v1alpha1.AttestationData`.
Each program constant includes a `.S` file of the link set `prysm/go1.26.10/link-set/norm`.
The link set comes from the ELF of `prysm/go1.26.10/build-ids.txt`.
This file is written by hand.
-/

namespace Prysm.AttestationData.Code

/-- `(*v1alpha1.AttestationData).UnmarshalSSZ` (protoc type, `phase0.ssz.go:273`). -/
def unmarshalSSZ : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ.S"
/-- `(*v1alpha1.AttestationData).MarshalSSZTo` (`phase0.ssz.go:235`; Slot/CommitteeIndex `MarshalSSZTo` inlined). -/
def marshalSSZTo : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo.S"
/-- `(*v1alpha1.AttestationData).SizeSSZ`. -/
def sizeSSZ : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.SizeSSZ.S"

end Prysm.AttestationData.Code
