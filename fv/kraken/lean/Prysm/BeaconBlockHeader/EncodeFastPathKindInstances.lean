import Codec.Kind.EncodeFastPathAnyFrame
import Prysm.BeaconBlockHeader.EncodeFastPath
import Prysm.Eth1Data.EncodeFastPath
import Prysm.Checkpoint.EncodeFastPath
import Prysm.Checkpoint.EncodeFastPathKindInstances
import Prysm.Eth1Data.EncodeFastPathKindInstances

/-!
# Ties of `encodeFastPathKindAnyFrame` to the three hand-written encoder fast-path statements

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
def encodeLayout : EncoderFrameLayout where
  stateWord := true
  frame := 152
  guardAddend := 32
  callsMemmove := true
  stackChunkCount := 11
  stackChunkLengths := [(0, 8), (1, 8), (2, 8), (3, 8), (4, 8), (5, 8), (6, 16), (7, 16), (8, 16), (9, 16), (10, 8)]
  pre := [.at (.below 8) (.original 0), .at (.above 8) (.original 1), .at (.above 16) (.original 2), .at (.below 16) (.original 3),
    .at (.below 96) (.original 4), .at (.below 104) (.original 5), .at (.below 56) (.original 6), .at (.below 40) (.original 7),
    .at (.below 88) (.original 8), .at (.below 72) (.original 9), .at (.below 168) (.original 10), .low .scratch]
  existentials := [.fixed 8, .fixed 16, .fixed 8, .fixed 16, .low]
  post := [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 16) (.reg .rbx),
    .at (.below 96) (.reg .rdi), .at (.below 104) (.len 112), .at (.below 56) (.field 0), .at (.below 48) (.existential 0),
    .at (.below 40) (.existential 1), .at (.below 88) (.field 1), .at (.below 80) (.existential 2), .at (.below 72) (.existential 3),
    .at (.below 168) (.ret 148), .low (.existential 4)]

variable [Host]

/-- BeaconBlockHeader: the declared type of the hand theorem is the kind instance. -/
theorem Encode.fast_path_is_kind_any_frame : ∀ (h : Host), type_of% (@Prysm.BeaconBlockHeader.Encode.fast_path h)
    = @encodeFastPathKindAnyFrame h Prysm.BeaconBlockHeader.Code.marshalSSZTo encodeLayout [.uint64, .uint64, .bytes 32, .bytes 32, .bytes 32] := by
  intro h; rfl

/-- Eth1Data: the declared type of the hand theorem is the kind instance. -/
theorem _root_.Prysm.Eth1Data.Encode.fast_path_is_kind_any_frame : ∀ (h : Host), type_of% (@Prysm.Eth1Data.Encode.fast_path h)
    = @encodeFastPathKindAnyFrame h Prysm.Eth1Data.Code.marshalSSZTo Prysm.Eth1Data.encodeLayout [.bytes 32, .uint64, .bytes 32] := by
  intro h; rfl

end Prysm.BeaconBlockHeader
