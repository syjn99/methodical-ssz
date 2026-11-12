import Kraken.X64.Parser
import Fk.Include

/-!
# Code of the AttestationData function set (prysm-e2e A1, Go 1.26.10 ELF `c6403c02…911e`)

Each constant includes a `.S` file of `fv/kraken/prysm/go1.26.10/e2e/ad/link/norm`
(`link/conv.py --norm` of the same ELF as `E2e.Code`; `link/check.py` (a)–(f) PASS in
`../RESULT`, bundle `192d066f…`). The Checkpoint callees are `E2e.Code.CpUnmarshal` and
`E2e.Code.CpMarshal` (the call targets of these files are their labels).
-/

namespace E2eAd.Code

/-- `(*v1alpha1.AttestationData).UnmarshalSSZ` (protoc type, `phase0.ssz.go:273`). -/
def AdUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/ad/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ.S"
/-- `(*v1alpha1.AttestationData).MarshalSSZTo` (`phase0.ssz.go:235`; Slot/CommitteeIndex `MarshalSSZTo` inlined). -/
def AdMarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/ad/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo.S"
/-- `(*v1alpha1.AttestationData).SizeSSZ`. -/
def AdSize : Program := include_x64_rt "../prysm/go1.26.10/e2e/ad/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.SizeSSZ.S"
/-- `(*primitives.Slot).UnmarshalSSZ` (hand-written, `consensus-types/primitives/slot.go:183`). -/
def SlUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/ad/link/norm/github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ.S"
/-- `(*primitives.CommitteeIndex).UnmarshalSSZ` (hand-written, `committee_index.go:28`). -/
def CiUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/ad/link/norm/github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.UnmarshalSSZ.S"

abbrev slLabel : String := "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ"
abbrev ciLabel : String := "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.UnmarshalSSZ"
abbrev cpULabel : String := "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ"
abbrev cpMLabel : String := "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo"

end E2eAd.Code
