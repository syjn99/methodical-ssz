import Kraken.X64.Parser
import Machine.Include
import Prysm.Checkpoint.Code
import Prysm.CommitteeIndex.Code
import Prysm.Slot.Code

/-!
# Code of the `AttestationData` functions (Go 1.26.10 ELF `c6403c02…911e`)

Each constant includes a `.S` file of `fv/kraken/prysm/go1.26.10/link-set/norm`
(`link/conv.py --norm` of the same ELF as `Prysm.Checkpoint.Code`; `link/check.py` (a)–(f) PASS in `prysm/go1.26.10/link-set/RESULT`). The Checkpoint callees are `Prysm.Checkpoint.Code.unmarshalSSZ` and
`Prysm.Checkpoint.Code.marshalSSZTo` (the call targets of these files are their labels).
-/

namespace Prysm.AttestationData.Code

/-- `(*v1alpha1.AttestationData).UnmarshalSSZ` (protoc type, `phase0.ssz.go:273`). -/
def unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ.S"
/-- `(*v1alpha1.AttestationData).MarshalSSZTo` (`phase0.ssz.go:235`; Slot/CommitteeIndex `MarshalSSZTo` inlined). -/
def marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo.S"
/-- `(*v1alpha1.AttestationData).SizeSSZ`. -/
def sizeSSZ : Program := include_x64_rt "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.SizeSSZ.S"
end Prysm.AttestationData.Code
