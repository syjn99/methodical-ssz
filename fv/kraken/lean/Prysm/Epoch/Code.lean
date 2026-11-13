import Kraken.X64.Parser
import Machine.Include

/-!
# Code of the prysm-e2e function set (Go 1.26.10 ELF `c6403c02…911e`): the `Epoch` part

The declarations of the other types of this group are in `Prysm/Checkpoint/Code.lean`.
-/

namespace Prysm.Epoch

/-- `(*primitives.Epoch).UnmarshalSSZ` (hand-written, `consensus-types/primitives/epoch.go:126`). -/
def Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/e2e/link/norm/github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ.S"

/-- The label of the Epoch decoder (the call target in `unmarshalSSZ`). -/
abbrev Code.unmarshalSSZLabel : String := "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ"

end Prysm.Epoch
