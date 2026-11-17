import Kraken.X64.Parser
import Machine.Include

/-!
# Code of `primitives.Slot`

This module holds the program constant `Code.unmarshalSSZ` of `primitives.Slot`.
It also holds the label abbreviation `Code.unmarshalSSZLabel`.
Each program constant includes a `.S` file of the link set `prysm/go1.26.10/link-set/norm`.
The link set comes from the ELF of `prysm/go1.26.10/build-ids.txt`.
This file is written by hand.
-/

namespace Prysm.Slot

/-- `(*primitives.Slot).UnmarshalSSZ` (hand-written, `consensus-types/primitives/slot.go:183`). -/
def Code.unmarshalSSZ : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ.S"

abbrev Code.unmarshalSSZLabel : String := "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ"

end Prysm.Slot
