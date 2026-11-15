import Kraken.X64.Parser
import Machine.Include

/-!
# Code of the `PowBlock` functions (Go 1.26.10 ELF `9a37219e…10e9`)

The declarations of the other types of this group are in `Prysm/PendingDeposit/Code.lean`.
-/

namespace Prysm.PowBlock

/-- `(*v1alpha1.PowBlock).UnmarshalSSZ`. -/
def Code.unmarshalSSZ : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.UnmarshalSSZ.S"

end Prysm.PowBlock
