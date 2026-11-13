import Prysm.BlobIdentifier.DecodeAccept
import Prysm.DepositMessage.DecodeAccept
import Prysm.Eth1Data.DecodeAccept
import Prysm.Deposit_Data.Statements
import Codec.Kind.DecodeAcceptComposition

/-!
# A statement kind for composed decoder accept theorems (byte-vector / inline-uint64 shapes): the `Eth1Data` part

The declarations of the other types of this group are in `Codec/Kind/DecodeAcceptComposition.lean`.
-/

open Machine Runtime

open Codec
namespace Prysm.Eth1Data

variable [Host]

/-- Eth1Data: the hand accept theorem has the kind `[bytes 32, u64, bytes 32]`. -/
theorem Decode.accept_is_kind : ∀ (h : Host), type_of% (@Prysm.Eth1Data.Decode.accept h)
    = @decodeAcceptKind h Prysm.Eth1Data.Code.unmarshalSSZ true [.bytes 32, .uint64, .bytes 32] 70 := by
  intro h; rfl

end Prysm.Eth1Data
