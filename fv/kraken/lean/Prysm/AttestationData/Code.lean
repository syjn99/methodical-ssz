import Kraken.X64.Parser
import Machine.Include

/-!
# Code of the AttestationData function set (prysm-e2e A1, Go 1.26.10 ELF `c6403c02…911e`)

Each constant includes a `.S` file of `fv/kraken/prysm/go1.26.10/e2e/ad/link/norm`
(`link/conv.py --norm` of the same ELF as `Prysm.Checkpoint.Code`; `link/check.py` (a)–(f) PASS in
`../RESULT`, bundle `192d066f…`). The Checkpoint callees are `Prysm.Checkpoint.Code.unmarshalSSZ` and
`Prysm.Checkpoint.Code.marshalSSZTo` (the call targets of these files are their labels).
-/

namespace Prysm.AttestationData.Code

/-- `(*v1alpha1.AttestationData).UnmarshalSSZ` (protoc type, `phase0.ssz.go:273`). -/
def unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/e2e/ad/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ.S"
/-- `(*v1alpha1.AttestationData).MarshalSSZTo` (`phase0.ssz.go:235`; Slot/CommitteeIndex `MarshalSSZTo` inlined). -/
def marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/ad/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo.S"
/-- `(*v1alpha1.AttestationData).SizeSSZ`. -/
def sizeSSZ : Program := include_x64_rt "../prysm/go1.26.10/e2e/ad/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.SizeSSZ.S"
/-- `(*primitives.Slot).UnmarshalSSZ` (hand-written, `consensus-types/primitives/slot.go:183`). -/
def slotUnmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/e2e/ad/link/norm/github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ.S"
/-- `(*primitives.CommitteeIndex).UnmarshalSSZ` (hand-written, `committee_index.go:28`). -/
def committeeIndexUnmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/e2e/ad/link/norm/github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.UnmarshalSSZ.S"

abbrev slotUnmarshalLabel : String := "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ"
abbrev committeeIndexUnmarshalLabel : String := "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.UnmarshalSSZ"
abbrev checkpointUnmarshalLabel : String := "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ"
abbrev checkpointMarshalLabel : String := "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo"

end Prysm.AttestationData.Code
