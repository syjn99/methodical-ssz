import Kraken.X64.Parser
import Fk.Include

/-!
# Code of the prysm-e2e function set (Go 1.26.10 ELF `c6403c02…911e`)

Each constant includes a `.S` file of `fv/kraken/prysm/go1.26.10/e2e/link/norm`
(`link/conv.py --norm` of the Go 1.26.10 ELF; `link/check.py` (a)–(e) PASS in
`../RESULT`). The files are Lake inputs of the `E2e` library (`lakefile.toml`).
Nothing of the Go 1.26.3 code (`Fk.Code`) is used.
-/

namespace E2e.Code

/-- `(*v1alpha1.Checkpoint).UnmarshalSSZ` (protoc type, `phase0.ssz.go:1976`). -/
def CpUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ.S"
/-- `(*v1alpha1.Checkpoint).MarshalSSZTo` (`phase0.ssz.go:1959`; `Epoch.MarshalSSZTo` inlined). -/
def CpMarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo.S"
/-- `(*v1alpha1.Checkpoint).SizeSSZ`. -/
def CpSize : Program := include_x64_rt "../prysm/go1.26.10/e2e/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.SizeSSZ.S"
/-- `(*primitives.Epoch).UnmarshalSSZ` (hand-written, `consensus-types/primitives/epoch.go:126`). -/
def EpUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/link/norm/github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ.S"

/-- The label of the Epoch decoder (the call target in `CpUnmarshal`). -/
abbrev epLabel : String := "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ"

end E2e.Code
