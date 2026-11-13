import Codec.Kind.DecodeAcceptAnyFrame
import Prysm.BeaconBlockHeader.DecodeAccept
import Prysm.PendingPartialWithdrawal.DecodeAccept
import Prysm.SyncCommitteeMessage.Statements
import Prysm.PendingDeposit.Statements
import Prysm.Checkpoint.DecodeAccept

/-!
# GEN5 L1: ties of `decAcceptKindN` to the hand accept statements

For every flat development type with a hand-written accept statement, the kind instance is that statement.
`rfl` at default transparency (the recursive definitions of the kind unfold on the literal layout and field
list), as the GEN3 ties of `decAcceptKind`. The hand statements and theorems are used as committed.

Layouts: three frame classes.
- `layRt st jret nb` (frame `0x20`, `makeslice` / `memmove` only): BlobIdentifier, DepositMessage, Eth1Data,
  Deposit_Data, PowBlock.
- `layCal callees jret` (frame `0x48`, callee decoders only): PendingPartialWithdrawal, PendingConsolidation.
- `layMix40`, `layMix60` (frames `0x40`, `0x60`, both): PendingDeposit; SyncCommitteeMessage,
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
def layRt (st : Bool) (jret nb : Nat) : DecLayout where
  callees := []
  nstk := 7
  lens := [(0, 8), (1, 8), (2, 8), (3, 24), (4, 8), (5, 8)]
  pre := [.at (.dn 8) (.orig 0), .at (.up 8) (.orig 1), .at (.up 16) (.orig 2), .at (.dn 40) (.orig 3),
    .at (.dn 16) (.orig 4), .at (.dn 48) (.orig 5), .lo (.orig 6)]
  rt := some ⟨false, 0, 6, 48⟩
  gd := 0
  st := st
  exs := [.n 24, .lo]
  post := [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 40) (.ex 0),
    .at (.dn 16) (.ptr (nb - 1)), .at (.dn 48) (.ret jret), .lo (.ex 1)]
  frame := 40

/-- Frame `0x48`, callee decoders only. `jret` = the directive after the last callee `callq`. -/
def layCal (callees : List Program) (jret : Nat) : DecLayout where
  callees := callees
  nstk := 7
  lens := [(0, 8), (1, 8), (2, 8), (3, 8), (4, 8), (5, 8), (6, 8)]
  pre := [.at (.dn 8) (.orig 0), .at (.up 8) (.orig 1), .at (.up 16) (.orig 2), .at (.up 32) (.orig 3),
    .at (.dn 72) (.orig 4), .at (.dn 88) (.orig 5), .at (.dn 96) (.orig 6)]
  rt := none
  gd := 88
  st := true
  exs := [.n 8, .n 8]
  post := [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.up 32) (.reg .rdi),
    .at (.dn 72) (.ex 0), .at (.dn 88) (.ret jret), .at (.dn 96) (.ex 1)]
  frame := 80

/-- Frame `0x40`, callee decoders and runtime calls (PendingDeposit). `ip` = index of the byte field whose
pointer is in the save slot at the end. -/
def layMix40 (callees : List Program) (jret ip : Nat) : DecLayout where
  callees := callees
  nstk := 10
  lens := [(0, 8), (1, 8), (2, 8), (3, 8), (4, 8), (5, 8), (6, 8), (7, 8), (8, 8)]
  pre := [.at (.dn 8) (.orig 0), .at (.up 8) (.orig 1), .at (.up 16) (.orig 2), .at (.up 32) (.orig 3),
    .at (.dn 72) (.orig 4), .at (.dn 64) (.orig 5), .at (.dn 56) (.orig 6), .at (.dn 32) (.orig 7),
    .at (.dn 80) (.orig 8), .lo (.orig 9)]
  rt := some ⟨true, 8, 9, 88⟩
  gd := 80
  st := true
  exs := [.n 24, .lo]
  post := [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.up 32) (.reg .rdi),
    .at (.dn 72) (.ex 0), .at (.dn 32) (.ptr ip), .at (.dn 80) (.ret jret), .lo (.ex 1)]
  frame := 72

/-- Frame `0x60`, callee decoders and runtime calls (SyncCommitteeMessage, BeaconBlockHeader). -/
def layMix60 (callees : List Program) (jret ip : Nat) : DecLayout where
  callees := callees
  nstk := 12
  lens := [(0, 8), (1, 8), (2, 8), (3, 8), (4, 8), (5, 8), (6, 8), (7, 8), (8, 8), (9, 8), (10, 8)]
  pre := [.at (.dn 8) (.orig 0), .at (.up 8) (.orig 1), .at (.up 16) (.orig 2), .at (.up 32) (.orig 3),
    .at (.dn 104) (.orig 4), .at (.dn 96) (.orig 5), .at (.dn 88) (.orig 6), .at (.dn 64) (.orig 7),
    .at (.dn 56) (.orig 8), .at (.dn 48) (.orig 9), .at (.dn 112) (.orig 10), .lo (.orig 11)]
  rt := some ⟨true, 8, 11, 120⟩
  gd := 112
  st := true
  exs := [.n 24, .lo]
  post := [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.up 32) (.reg .rdi),
    .at (.dn 104) (.ex 0), .at (.dn 64) .zero, .at (.dn 56) .zero, .at (.dn 48) (.ptr ip),
    .at (.dn 112) (.ret jret), .lo (.ex 1)]
  frame := 104

/-! ## Checkpoint: implication, not `rfl` -/

variable [Host]

end Codec
