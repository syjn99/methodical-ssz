import Codec.Kind.EncodeFastPathAnyFrame
import Prysm.BeaconBlockHeader.EncodeFastPath
import Prysm.Eth1Data.EncodeFastPath
import Prysm.Checkpoint.EncodeFastPath
import Prysm.Checkpoint.EncodeFastPathKindInstances
import Prysm.Eth1Data.EncodeFastPathKindInstances

/-!
# Ties of `encFastKindN` to the three hand-written encoder fast-path statements

- BeaconBlockHeader (`Encode.fast_path`) and Eth1Data (`Prysm.Eth1Data.Encode.fast_path`): the declared type of
  the committed theorem is the kind instance, `rfl` at default transparency (the recursive definitions of
  the kind unfold on the literal layout and field list).
- Checkpoint (`Prysm.Checkpoint.Encode.fast_path`): not `rfl`. The hand statement names a 32-byte chunk `ctl` at
  `rax + 40` (after the capacity word of `Root`; not part of the Go layout of the receiver). In the kind that
  memory is part of `R`. `Prysm.Checkpoint.Encode.fast_path_of_kind`: the kind instance implies the hand statement. The converse
  does not hold as stated (`R` need not contain such a chunk). No other difference: with the binder `ctl`,
  its length hypothesis and its chunk removed, the two statements have the same text.

The hand statements and theorems are used as committed.
After the split of this module, the Checkpoint declarations are in `Prysm/Checkpoint/EncodeFastPathKindInstances.lean`.
The Eth1Data layout is in `Prysm/Eth1Data/EncodeFastPathKindInstances.lean`.
The Eth1Data tie theorem stays here: its negative case puts the BeaconBlockHeader layout into its statement.
-/

open Machine Runtime

open Codec
namespace Prysm.BeaconBlockHeader

/-- BeaconBlockHeader `MarshalSSZTo`: frame `0x98`, large-frame guard (`lea -0x20(%rsp),%r12`). Stack chunks
`fp s1 s2 l16 l96 l104 t1a t1b t2a t2b rslot`. -/
def encodeLayout : EncLayout where
  st := true
  frame := 152
  gd := 32
  rt := true
  nstk := 11
  lens := [(0, 8), (1, 8), (2, 8), (3, 8), (4, 8), (5, 8), (6, 16), (7, 16), (8, 16), (9, 16), (10, 8)]
  pre := [.at (.dn 8) (.orig 0), .at (.up 8) (.orig 1), .at (.up 16) (.orig 2), .at (.dn 16) (.orig 3),
    .at (.dn 96) (.orig 4), .at (.dn 104) (.orig 5), .at (.dn 56) (.orig 6), .at (.dn 40) (.orig 7),
    .at (.dn 88) (.orig 8), .at (.dn 72) (.orig 9), .at (.dn 168) (.orig 10), .lo .scr]
  exs := [.n 8, .n 16, .n 8, .n 16, .lo]
  post := [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 16) (.reg .rbx),
    .at (.dn 96) (.reg .rdi), .at (.dn 104) (.len 112), .at (.dn 56) (.fld 0), .at (.dn 48) (.ex 0),
    .at (.dn 40) (.ex 1), .at (.dn 88) (.fld 1), .at (.dn 80) (.ex 2), .at (.dn 72) (.ex 3),
    .at (.dn 168) (.ret 148), .lo (.ex 4)]

variable [Host]

/-- BeaconBlockHeader: the declared type of the hand theorem is the kind instance. -/
theorem Encode.fast_path_is_kind_any_frame : ∀ (h : Host), type_of% (@Prysm.BeaconBlockHeader.Encode.fast_path h)
    = @encFastKindN h Prysm.BeaconBlockHeader.Code.marshalSSZTo encodeLayout [.u64, .u64, .bytes 32, .bytes 32, .bytes 32] := by
  intro h; rfl

/-- Eth1Data: the declared type of the hand theorem is the kind instance. -/
theorem _root_.Prysm.Eth1Data.Encode.fast_path_is_kind_any_frame : ∀ (h : Host), type_of% (@Prysm.Eth1Data.Encode.fast_path h)
    = @encFastKindN h Prysm.Eth1Data.Code.marshalSSZTo Prysm.Eth1Data.encodeLayout [.bytes 32, .u64, .bytes 32] := by
  intro h; rfl

end Prysm.BeaconBlockHeader
