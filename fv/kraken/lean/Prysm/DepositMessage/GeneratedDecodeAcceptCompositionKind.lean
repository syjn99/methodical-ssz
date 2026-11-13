import Codec.Kind.DecodeAcceptComposition
import Prysm.BlobIdentifier.GeneratedDecodeAcceptComposition
import Prysm.DepositMessage.GeneratedDecodeAcceptComposition
import Prysm.Eth1Data.GeneratedDecodeAcceptComposition

/-!
# The three generated composed accept theorems have the kind `decodeAcceptKind`: the `DepositMessage` part

The declarations of the other types of this group are in `Prysm/BlobIdentifier/GeneratedDecodeAcceptCompositionKind.lean`.
-/

open Machine Runtime

open Codec
namespace Prysm.DepositMessage

theorem Decode.accept_generated_composition_is_kind : ∀ (h : Host), type_of% (@Prysm.DepositMessage.Decode.accept_generated_composition h)
    = @decodeAcceptKind h Prysm.DepositMessage.Code.unmarshalSSZ false [.bytes 48, .bytes 32, .uint64] 68 := by
  intro h; rfl

end Prysm.DepositMessage
