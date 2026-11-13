import Kraken.X64.Parser
import Machine.Include

/-!
# Code of the encoder of `v1alpha1.PendingPartialWithdrawal` (Go 1.26.10 ELF `c6403c02…911e`)

The constant includes a `.S` file of `fv/kraken/prysm/go1.26.10/link-set/norm`.
`link/check.py` (a)–(f) PASS in `prysm/go1.26.10/link-set/RESULT`. `Prysm/BlobIdentifier/EncoderCode.lean` imports this module.
-/

namespace Prysm.PendingPartialWithdrawal

/-- `(*v1alpha1.PendingPartialWithdrawal).MarshalSSZTo`. -/
def Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.MarshalSSZTo.S"

end Prysm.PendingPartialWithdrawal
