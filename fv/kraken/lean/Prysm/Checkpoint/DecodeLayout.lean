import Codec.Kind.DecodeAcceptAnyFrame
import Prysm.Checkpoint.DecodeAccept
import Prysm.Epoch.Code

/-!
# Frame layout of the Checkpoint decoder for the accept kind

`decodeLayout` is the frame layout that `Codec.decodeAcceptKindAnyFrame` reads in the tie `Decode.accept_kind_tie`
(`Prysm/Checkpoint/DecodeAcceptKindTie.lean`).
`Decode.low_address` restates the address of the low stack of the hand statement in the form of the kind.
The tie uses it.
-/

open Machine Runtime

open Codec
namespace Prysm.Checkpoint

variable [Host]

/-- Checkpoint layout for the kind (frame `0x50`; callee `Epoch`, one byte field). -/
def decodeLayout : DecoderFrameLayout where
  callees := [Prysm.Epoch.Code.unmarshalSSZ]
  stackChunkCount := 11
  stackChunkLengths := [(0, 8), (1, 8), (2, 8), (3, 8), (4, 8), (5, 8), (6, 8), (7, 8), (8, 8), (9, 8)]
  pre := [.at (.below 8) (.original 0), .at (.above 8) (.original 1), .at (.above 16) (.original 2), .at (.below 32) (.original 3),
    .at (.below 40) (.original 4), .at (.below 48) (.original 5), .at (.below 88) (.original 6), .at (.below 80) (.original 7),
    .at (.below 72) (.original 8), .at (.below 96) (.original 9), .low (.original 10)]
  runtime := some ⟨true, 8, 10, 104⟩
  guardAddend := 96
  stateWord := true
  existentials := [.fixed 24, .low]
  post := [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 32) (.ptr 0),
    .at (.below 40) .zero, .at (.below 48) .zero, .at (.below 88) (.existential 0), .at (.below 96) (.ret 70), .low (.existential 1)]
  frame := 88

theorem Decode.low_address (x : BitVec 64) (S : Nat) (h8 : 8 ≤ S) (hS : S < 2 ^ 60) :
    x - 96 - BitVec.ofNat 64 S = x - 104 - BitVec.ofNat 64 (S - 8) := by
  rw [Prysm.Checkpoint.Decode.accept_ofNat S h8 hS]; bv_omega

end Prysm.Checkpoint
