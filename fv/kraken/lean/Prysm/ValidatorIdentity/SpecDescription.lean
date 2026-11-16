import Prysm.Checkpoint.Spec

/-!
# Independent hand `Desc` of `ValidatorIdentity`

This description is written by hand from the Prysm proto definitions in the Prysm source tree that the Go differential uses.
It does not use the checker descriptions `Prysm/<Type>/SpecChecker.lean`.
It is not independent of the source of the Desc producer (as `Prysm/ValidatorBalance/SpecDescription.lean`).
Where the proto cites a spec definition, the comment is quoted.
Overlay types (`cast_type` Slot, Epoch, ValidatorIndex, Gwei) are `uint64` in SSZ.
The proto file is `proto/prysm/v1alpha1/validator.proto`.

    message ValidatorIdentity { uint64 index [ValidatorIndex]; bytes pubkey [48]; uint64 activation_epoch [Epoch]; }
-/

namespace Prysm.ValidatorIdentity
open EthLib.Serialization.Ssz

/-- Prysm `v1alpha1.ValidatorIdentity`. -/
def desc : Desc := .container ["index", "pubkey", "activation_epoch"]
  [.uint 8, .byteVector 48, .uint 8]

end Prysm.ValidatorIdentity
