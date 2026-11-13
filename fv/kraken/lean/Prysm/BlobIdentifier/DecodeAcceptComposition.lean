import Prysm.BlobIdentifier.DecodeAccept
import Prysm.DepositMessage.DecodeAccept
import Prysm.Eth1Data.DecodeAccept
import Prysm.Deposit_Data.Statements
import Codec.Kind.DecodeAcceptComposition

/-!
# A statement kind for composed decoder accept theorems (byte-vector / inline-uint64 shapes): the `BlobIdentifier` part

The declarations of the other types of this group are in `Codec/Kind/DecodeAcceptComposition.lean`.
-/

open Machine Runtime

open Codec
namespace Prysm.BlobIdentifier

variable [Host]

/-- BlobIdentifier: the hand accept theorem has the kind `[bytes 32, u64]`. -/
theorem Decode.accept_is_kind : ∀ (h : Host), type_of% (@Prysm.BlobIdentifier.Decode.accept h)
    = @decodeAcceptKind h Prysm.BlobIdentifier.Code.unmarshalSSZ true [.bytes 32, .uint64] 32 := by
  intro h; rfl

end Prysm.BlobIdentifier
