import Kraken.X64.Parser
import Machine.Include

/-!
# Program constant of the `primitives.ValidatorIndex` MarshalSSZTo method

`Code.marshalSSZTo` includes the `.S` file of `fv/kraken/prysm/go1.26.10/link-set/norm` (`link/check.py` (a)–(f) PASS in
`prysm/go1.26.10/link-set/RESULT`).
This module is apart from `Code.lean`, so that the modules that import `Code.lean` do not build again.
-/

namespace Prysm.ValidatorIndex

/-- `(*primitives.ValidatorIndex).MarshalSSZTo` (hand-written; `append(dst, 8 little-endian bytes of the value)`). -/
def Code.marshalSSZTo : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.MarshalSSZTo.S"

end Prysm.ValidatorIndex
