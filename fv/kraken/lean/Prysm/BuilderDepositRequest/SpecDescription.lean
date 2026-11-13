import Prysm.Checkpoint.Spec

/-!
# Independent hand `Desc` of the eight types with a generated theorem: the `BuilderDepositRequest` part

The declarations of the other types of this group are in `Prysm/DepositRequest/SpecDescription.lean`.
-/

namespace Prysm.BuilderDepositRequest
open EthLib.Serialization.Ssz

/-- Prysm `engine/v1.BuilderDepositRequest` (Gloas). -/
def desc : Desc := .container ["pubkey", "withdrawal_credentials", "amount", "signature"]
  [.byteVector 48, .byteVector 32, .uint 8, .byteVector 96]

end Prysm.BuilderDepositRequest
