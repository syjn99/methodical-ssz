import Codec.Kind.DecodeAcceptComposition
import Prysm.BlobIdentifier.GeneratedDecodeAcceptComposition
import Prysm.DepositMessage.GeneratedDecodeAcceptComposition
import Prysm.Eth1Data.GeneratedDecodeAcceptComposition

/-!
# The three generated composed accept theorems have the kind `decAcceptKind`: the `Eth1Data` part

The declarations of the other types of this group are in `Prysm/BlobIdentifier/GeneratedDecodeAcceptCompositionKind.lean`.
-/

open Machine Runtime

open Codec
namespace Prysm.Eth1Data

theorem Decode.accept_generated_composition_is_kind : ∀ (h : Host), type_of% (@Prysm.Eth1Data.Decode.accept_generated_composition h)
    = @decAcceptKind h Prysm.Eth1Data.Code.unmarshalSSZ true [.bytes 32, .u64, .bytes 32] 70 := by
  intro h; rfl

end Prysm.Eth1Data
