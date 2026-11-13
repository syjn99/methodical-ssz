import Prysm.Checkpoint.Spec

/-!
# Independent hand `Desc` of the eight types with a generated theorem: the `ValidatorIdentity` part

The declarations of the other types of this group are in `Prysm/DepositRequest/SpecDescription.lean`.
-/

namespace Prysm.ValidatorIdentity
open EthLib.Serialization.Ssz

/-- Prysm `v1alpha1.ValidatorIdentity`. -/
def desc : Desc := .container ["index", "pubkey", "activation_epoch"]
  [.uint 8, .byteVector 48, .uint 8]

end Prysm.ValidatorIdentity
