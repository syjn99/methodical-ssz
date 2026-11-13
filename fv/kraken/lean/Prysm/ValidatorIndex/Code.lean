import Kraken.X64.Parser
import Machine.Include

/-!
# Code of the `ValidatorIndex` functions (Go 1.26.10 ELF `c6403c02…911e`)

The declarations of the other types of this group are in `Prysm/BeaconBlockHeader/Code.lean`.
-/

namespace Prysm.ValidatorIndex

/-- `(*primitives.ValidatorIndex).UnmarshalSSZ` (hand-written, `consensus-types/primitives/validator.go`). -/
def Code.unmarshalSSZ : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ.S"

abbrev Code.unmarshalLabel : String := "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ"

end Prysm.ValidatorIndex
