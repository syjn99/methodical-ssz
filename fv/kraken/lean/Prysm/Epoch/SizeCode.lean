import Kraken.X64.Parser
import Machine.Include

/-!
# Program constant of the `primitives.Epoch` SizeSSZ method

`Code.sizeSSZ` includes the `.S` file of `fv/kraken/prysm/go1.26.10/link-set/norm` (`link/check.py` (a)–(f) PASS in
`prysm/go1.26.10/link-set/RESULT`).
This module is apart from `Code.lean`, so that the modules that import `Code.lean` do not build again.
-/

namespace Prysm.Epoch

/-- `(*primitives.Epoch).SizeSSZ` (hand-written; `mov $0x8,%eax`, `retq`). -/
def Code.sizeSSZ : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.SizeSSZ.S"

end Prysm.Epoch
