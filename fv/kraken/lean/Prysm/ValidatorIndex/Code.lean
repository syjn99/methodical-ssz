import Kraken.X64.Parser
import Machine.Include

/-!
# Code of the hold-out function set (Go 1.26.10 ELF `c6403c02…911e`): the `ValidatorIndex` part

The declarations of the other types of this group are in `Prysm/BeaconBlockHeader/Code.lean`.
-/

namespace Prysm.ValidatorIndex

/-- `(*primitives.ValidatorIndex).UnmarshalSSZ` (hand-written, `consensus-types/primitives/validator.go`). -/
def Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/e2e/bh/link/norm/github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ.S"

abbrev Code.unmarshalLabel : String := "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ"

end Prysm.ValidatorIndex
