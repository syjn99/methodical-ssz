import Prysm.Checkpoint.Spec

/-!
# Independent hand `Desc` of the eight types with a generated theorem: the `PartialDataColumnGroupID` part

The declarations of the other types of this group are in `Prysm/DepositRequest/SpecDescription.lean`.
-/

namespace Prysm.PartialDataColumnGroupID
open EthLib.Serialization.Ssz

/-- Prysm `v1alpha1.PartialDataColumnGroupID`. -/
def desc : Desc := .container ["beacon_block_root", "slot"]
  [.byteVector 32, .uint 8]

end Prysm.PartialDataColumnGroupID
