import Prysm.BlobIdentifier.DecodeAccept
import Prysm.DepositMessage.DecodeAccept
import Prysm.Eth1Data.DecodeAccept
import Prysm.Deposit_Data.Statements
import Codec.Kind.DecodeAcceptComposition

/-!
# A statement kind for composed decoder accept theorems (byte-vector / inline-uint64 shapes): the `Deposit_Data` part

The declarations of the other types of this group are in `Codec/Kind/DecodeAcceptComposition.lean`.
-/

open Machine Runtime

open Codec
namespace Prysm.Deposit_Data

variable [Host]

/-- Deposit_Data: the hand statement is the kind `[bytes 48, bytes 32, u64, bytes 96]`. -/
theorem Decode.accept_is_kind : ∀ (h : Host), @Prysm.Deposit_Data.Decode.accept_statement h
    = @decodeAcceptKind h Prysm.Deposit_Data.Code.unmarshalSSZ true [.bytes 48, .bytes 32, .uint64, .bytes 96] 106 := by
  intro h; rfl

end Prysm.Deposit_Data
