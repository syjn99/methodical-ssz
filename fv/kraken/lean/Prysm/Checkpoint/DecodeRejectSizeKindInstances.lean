import Prysm.Checkpoint.DecodeRejectSize
import Codec.DecodeRejectSizeAnyFrame
import Prysm.Checkpoint.Code

/-!
# Tie of `decodeRejectKindAnyFrame` to the size-reject theorem of `Checkpoint`

This theorem shows that the kind `Codec.decodeRejectKindAnyFrame` (size 40) is the statement of the hand theorem `Prysm.Checkpoint.Decode.reject_size`.
-/

open Machine Runtime

open Codec
namespace Prysm.Checkpoint

theorem Decode.reject_size_is_kind_any_frame : ∀ (h : Host), type_of% (@Prysm.Checkpoint.Decode.reject_size h)
    = @decodeRejectKindAnyFrame h Prysm.Checkpoint.Code.unmarshalSSZ 40 := by
  intro h; with_reducible rfl

end Prysm.Checkpoint
