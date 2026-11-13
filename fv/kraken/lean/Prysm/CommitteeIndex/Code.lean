import Kraken.X64.Parser
import Machine.Include

/-!
# Program constant of the `primitives.CommitteeIndex` decoder

`unmarshalSSZ` includes the `.S` file of `fv/kraken/prysm/go1.26.10/link-set/norm` (`link/check.py` (a)–(f) PASS in
`prysm/go1.26.10/link-set/RESULT`); `unmarshalSSZLabel` is its label, the call target in the AttestationData decoder.
-/

namespace Prysm.CommitteeIndex

/-- `(*primitives.CommitteeIndex).UnmarshalSSZ` (hand-written, `committee_index.go:28`). -/
def Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.UnmarshalSSZ.S"

abbrev Code.unmarshalSSZLabel : String := "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.UnmarshalSSZ"

end Prysm.CommitteeIndex
