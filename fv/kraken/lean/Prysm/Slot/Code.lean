import Kraken.X64.Parser
import Machine.Include

/-!
# Program constant of the `primitives.Slot` decoder

`unmarshalSSZ` includes the `.S` file of `fv/kraken/prysm/go1.26.10/link-set/norm` (`link/check.py` (a)–(f) PASS in
`prysm/go1.26.10/link-set/RESULT`); `unmarshalSSZLabel` is its label, the call target in the AttestationData decoder.
-/

namespace Prysm.Slot

/-- `(*primitives.Slot).UnmarshalSSZ` (hand-written, `consensus-types/primitives/slot.go:183`). -/
def Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ.S"

abbrev Code.unmarshalSSZLabel : String := "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ"

end Prysm.Slot
