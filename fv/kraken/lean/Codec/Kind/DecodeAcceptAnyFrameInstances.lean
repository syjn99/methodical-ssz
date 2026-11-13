import Codec.Kind.DecodeAcceptAnyFrame
import Prysm.BeaconBlockHeader.DecodeAccept
import Prysm.PendingPartialWithdrawal.DecodeAccept
import Prysm.SyncCommitteeMessage.Statements
import Prysm.PendingDeposit.Statements
import Prysm.Checkpoint.DecodeAccept

/-!
# Ties of `decAcceptKindAnyFrame` to the hand accept statements

For every flat development type with a hand-written accept statement, the kind instance is that statement.
`rfl` at default transparency (the recursive definitions of the kind unfold on the literal layout and field
list), as the ties of the composed accept kind `decAcceptKind`. The hand statements and theorems are used as committed.

Layouts: three frame classes.
- `layoutRuntimeCalls st jret nb` (frame `0x20`, `makeslice` / `memmove` only): BlobIdentifier, DepositMessage, Eth1Data,
  Deposit_Data, PowBlock.
- `layoutCalleeCalls callees jret` (frame `0x48`, callee decoders only): PendingPartialWithdrawal, PendingConsolidation.
- `layoutMixedFrame40`, `layoutMixedFrame60` (frames `0x40`, `0x60`, both): PendingDeposit; SyncCommitteeMessage,
  BeaconBlockHeader.

Checkpoint (`Prysm.Checkpoint.Decode.accept`) is not `rfl`: see `Prysm.Checkpoint.Decode.accept_of_kind` (the kind instance implies the
hand statement; the converse does not hold).
After the split of this module, the declarations of single types are in `Prysm/BeaconBlockHeader/DecodeAcceptAnyFrameInstances.lean`, `Prysm/BlobIdentifier/DecodeAcceptAnyFrameInstances.lean`, `Prysm/Checkpoint/DecodeAcceptAnyFrameInstances.lean`, `Prysm/DepositMessage/DecodeAcceptAnyFrameInstances.lean`, `Prysm/Deposit_Data/DecodeAcceptAnyFrameInstances.lean`, `Prysm/Eth1Data/DecodeAcceptAnyFrameInstances.lean`, `Prysm/PendingConsolidation/DecodeAcceptAnyFrameInstances.lean`, `Prysm/PendingDeposit/DecodeAcceptAnyFrameInstances.lean`, `Prysm/PendingPartialWithdrawal/DecodeAcceptAnyFrameInstances.lean`, `Prysm/PowBlock/DecodeAcceptAnyFrameInstances.lean`, `Prysm/SyncCommitteeMessage/DecodeAcceptAnyFrameInstances.lean`.
-/

open Machine Runtime

open Codec
namespace Codec

/-- Frame `0x20`, runtime calls only. `nb` = number of byte fields (the pointer save slot holds the last
pointer), `jret` = the directive after the last `callq runtime.memmove`. -/
def layoutRuntimeCalls (st : Bool) (jret nb : Nat) : DecoderFrameLayout where
  callees := []
  stackChunkCount := 7
  stackChunkLengths := [(0, 8), (1, 8), (2, 8), (3, 24), (4, 8), (5, 8)]
  pre := [.at (.below 8) (.original 0), .at (.above 8) (.original 1), .at (.above 16) (.original 2), .at (.below 40) (.original 3),
    .at (.below 16) (.original 4), .at (.below 48) (.original 5), .low (.original 6)]
  runtime := some ⟨false, 0, 6, 48⟩
  guardAddend := 0
  stateWord := st
  existentials := [.fixed 24, .low]
  post := [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 40) (.existential 0),
    .at (.below 16) (.ptr (nb - 1)), .at (.below 48) (.ret jret), .low (.existential 1)]
  frame := 40

/-- Frame `0x48`, callee decoders only. `jret` = the directive after the last callee `callq`. -/
def layoutCalleeCalls (callees : List Program) (jret : Nat) : DecoderFrameLayout where
  callees := callees
  stackChunkCount := 7
  stackChunkLengths := [(0, 8), (1, 8), (2, 8), (3, 8), (4, 8), (5, 8), (6, 8)]
  pre := [.at (.below 8) (.original 0), .at (.above 8) (.original 1), .at (.above 16) (.original 2), .at (.above 32) (.original 3),
    .at (.below 72) (.original 4), .at (.below 88) (.original 5), .at (.below 96) (.original 6)]
  runtime := none
  guardAddend := 88
  stateWord := true
  existentials := [.fixed 8, .fixed 8]
  post := [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.above 32) (.reg .rdi),
    .at (.below 72) (.existential 0), .at (.below 88) (.ret jret), .at (.below 96) (.existential 1)]
  frame := 80

/-- Frame `0x40`, callee decoders and runtime calls (PendingDeposit). `ip` = index of the byte field whose
pointer is in the save slot at the end. -/
def layoutMixedFrame40 (callees : List Program) (jret ip : Nat) : DecoderFrameLayout where
  callees := callees
  stackChunkCount := 10
  stackChunkLengths := [(0, 8), (1, 8), (2, 8), (3, 8), (4, 8), (5, 8), (6, 8), (7, 8), (8, 8)]
  pre := [.at (.below 8) (.original 0), .at (.above 8) (.original 1), .at (.above 16) (.original 2), .at (.above 32) (.original 3),
    .at (.below 72) (.original 4), .at (.below 64) (.original 5), .at (.below 56) (.original 6), .at (.below 32) (.original 7),
    .at (.below 80) (.original 8), .low (.original 9)]
  runtime := some ⟨true, 8, 9, 88⟩
  guardAddend := 80
  stateWord := true
  existentials := [.fixed 24, .low]
  post := [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.above 32) (.reg .rdi),
    .at (.below 72) (.existential 0), .at (.below 32) (.ptr ip), .at (.below 80) (.ret jret), .low (.existential 1)]
  frame := 72

/-- Frame `0x60`, callee decoders and runtime calls (SyncCommitteeMessage, BeaconBlockHeader). -/
def layoutMixedFrame60 (callees : List Program) (jret ip : Nat) : DecoderFrameLayout where
  callees := callees
  stackChunkCount := 12
  stackChunkLengths := [(0, 8), (1, 8), (2, 8), (3, 8), (4, 8), (5, 8), (6, 8), (7, 8), (8, 8), (9, 8), (10, 8)]
  pre := [.at (.below 8) (.original 0), .at (.above 8) (.original 1), .at (.above 16) (.original 2), .at (.above 32) (.original 3),
    .at (.below 104) (.original 4), .at (.below 96) (.original 5), .at (.below 88) (.original 6), .at (.below 64) (.original 7),
    .at (.below 56) (.original 8), .at (.below 48) (.original 9), .at (.below 112) (.original 10), .low (.original 11)]
  runtime := some ⟨true, 8, 11, 120⟩
  guardAddend := 112
  stateWord := true
  existentials := [.fixed 24, .low]
  post := [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.above 32) (.reg .rdi),
    .at (.below 104) (.existential 0), .at (.below 64) .zero, .at (.below 56) .zero, .at (.below 48) (.ptr ip),
    .at (.below 112) (.ret jret), .low (.existential 1)]
  frame := 104

/-! ## Checkpoint: implication, not `rfl` -/

variable [Host]

end Codec
