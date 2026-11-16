import Kraken.X64.Parser
import Machine.Include

/-!
# Code of the `DepositMessage` functions (the Go 1.26.10 ELF of `prysm/go1.26.10/build-ids.txt`)

The declarations of the other types of this group are in `Prysm/BlobIdentifier/Code.lean`.
-/

namespace Prysm.DepositMessage

/-- `(*v1alpha1.DepositMessage).UnmarshalSSZ`. -/
def Code.unmarshalSSZ : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ.S"

end Prysm.DepositMessage
