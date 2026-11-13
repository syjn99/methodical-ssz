import Kraken.X64.Parser
import Machine.Include

/-!
# Code of the hold-out function set (Go 1.26.10 ELF `c6403c02…911e`): the `PendingPartialWithdrawal` part

The declarations of the other types of this group are in `Prysm/Deposit_Data/Code.lean`.
-/

namespace Prysm.PendingPartialWithdrawal

/-- `(*v1alpha1.PendingPartialWithdrawal).UnmarshalSSZ`. -/
def Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/e2e/h4/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ.S"

end Prysm.PendingPartialWithdrawal
