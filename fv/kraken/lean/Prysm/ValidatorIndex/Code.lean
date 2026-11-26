module

public import Kraken.X64.Parser
public import Machine.Include

@[expose] public section

/-!
# Code of `primitives.ValidatorIndex`

This module holds the program constants `Code.unmarshalSSZ` and `Code.marshalSSZTo` of `primitives.ValidatorIndex`.
It also holds the label abbreviation `Code.unmarshalSSZLabel`.
Each program constant includes a `.S` file of the link set `prysm/go1.26.10/link-set/norm`.
The link set comes from the ELF of `prysm/go1.26.10/build-ids.txt`.
This file is written by hand.
-/

namespace Prysm.ValidatorIndex

/-- `(*primitives.ValidatorIndex).UnmarshalSSZ` (hand-written, `consensus-types/primitives/validator.go`). -/
def Code.unmarshalSSZ : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ.S"
/-- `(*primitives.ValidatorIndex).MarshalSSZTo` (hand-written; `append(dst, 8 little-endian bytes of the value)`). -/
def Code.marshalSSZTo : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.MarshalSSZTo.S"

abbrev Code.unmarshalSSZLabel : String := "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ"

end Prysm.ValidatorIndex
