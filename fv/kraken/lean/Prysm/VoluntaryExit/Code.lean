import Kraken.X64.Parser
import Machine.Include

/-!
# Code of the `VoluntaryExit` functions (Go 1.26.10 ELF `c6403c02…911e`)

The declarations of the other types of this group are in `Prysm/PendingDeposit/Code.lean`.
-/

namespace Prysm.VoluntaryExit

/-- `(*v1alpha1.VoluntaryExit).UnmarshalSSZ`. -/
def Code.unmarshalSSZ : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.VoluntaryExit.UnmarshalSSZ.S"

end Prysm.VoluntaryExit
