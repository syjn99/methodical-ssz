module

public import Kraken.X64.Parser
public import Machine.Include

@[expose] public section

/-!
# Code of `primitives.Slot`

This module holds the program constants `Code.unmarshalSSZ`, `Code.marshalSSZTo`, `Code.marshalSSZ` and `Code.sizeSSZ` of `primitives.Slot`.
It also holds the label abbreviation `Code.unmarshalSSZLabel`.
Each program constant includes a `.S` file of the link set `prysm/go1.26.10/link-set/norm`.
The link set comes from the ELF of `prysm/go1.26.10/build-ids.txt`.
This file is written by hand.
-/

namespace Prysm.Slot

/-- `(*primitives.Slot).UnmarshalSSZ` (hand-written, `consensus-types/primitives/slot.go:183`). -/
def Code.unmarshalSSZ : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ.S"
/-- `(*primitives.Slot).MarshalSSZTo` (hand-written; `append(dst, 8 little-endian bytes of the value)`). -/
def Code.marshalSSZTo : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.MarshalSSZTo.S"
/-- `(*primitives.Slot).MarshalSSZ` (hand-written; `append([]byte{}, 8 little-endian bytes of the value)`). -/
def Code.marshalSSZ : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.MarshalSSZ.S"
/-- `(*primitives.Slot).SizeSSZ` (hand-written; `mov $0x8,%eax`, `retq`). -/
def Code.sizeSSZ : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.SizeSSZ.S"

abbrev Code.unmarshalSSZLabel : String := "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ"

end Prysm.Slot
