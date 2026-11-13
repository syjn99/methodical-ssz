import Prysm.BlobIdentifier.DecodeAccept
import Prysm.DepositMessage.DecodeAccept
import Prysm.Eth1Data.DecodeAccept
import Prysm.Deposit_Data.Statements
import Codec.Kind.DecodeAcceptComposition

/-!
# A statement kind for composed decoder accept theorems (byte-vector / inline-uint64 shapes): the `DepositMessage` part

The declarations of the other types of this group are in `Codec/Kind/DecodeAcceptComposition.lean`.
-/

open Machine Runtime

open Codec
namespace Prysm.DepositMessage

variable [Host]

/-- DepositMessage: the hand accept theorem has the kind `[bytes 48, bytes 32, u64]` (no `state` word). -/
theorem Decode.accept_is_kind : ∀ (h : Host), type_of% (@Prysm.DepositMessage.Decode.accept h)
    = @decodeAcceptKind h Prysm.DepositMessage.Code.unmarshalSSZ false [.bytes 48, .bytes 32, .uint64] 68 := by
  intro h; rfl

end Prysm.DepositMessage
