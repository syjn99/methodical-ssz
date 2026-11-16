import Codec.Kind.EncodeFastPathAnyFrame
import Prysm.Eth1Data.EncodeFastPath
import Prysm.Eth1Data.Code

/-!
# Hand layout of the Eth1Data encoder fast-path statement, and its tie to `encodeFastPathKindAnyFrame`

`encodeLayout` is the layout of the hand statement `Encode.fast_path`, as `encodeFastPathKindAnyFrame` reads it.
`Encode.fast_path_is_kind_any_frame`: the declared type of the committed theorem is the kind instance, `rfl` at
default transparency. Its negative case puts the BeaconBlockHeader layout into the statement; the mutated copy
imports `Prysm.BeaconBlockHeader.EncodeFastPathKindInstances` (case key `mutant_imports` of `gen/checks/negative.py`).
-/

open Machine Runtime

open Codec
namespace Prysm.Eth1Data

/-- Eth1Data `MarshalSSZTo`: frame `0x80` (`add $-0x80,%rsp`), large-frame guard (`lea -0x8(%rsp),%r12`).
Stack chunks `fp s1 s2 l16 l24 l32 l40 l48 l56 rslot`. -/
def encodeLayout : EncoderFrameLayout where
  stateWord := true
  frame := 128
  guardAddend := 8
  callsMemmove := true
  stackChunkCount := 10
  stackChunkLengths := [(0, 8), (1, 8), (2, 8), (3, 8), (4, 8), (5, 8), (6, 8), (7, 8), (8, 8), (9, 8)]
  pre := [.at (.below 8) (.original 0), .at (.above 8) (.original 1), .at (.above 16) (.original 2), .at (.below 16) (.original 3),
    .at (.below 24) (.original 4), .at (.below 32) (.original 5), .at (.below 40) (.original 6), .at (.below 48) (.original 7),
    .at (.below 56) (.original 8), .at (.below 144) (.original 9), .low .scratch]
  existentials := [.low]
  post := [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 16) (.reg .rbx),
    .at (.below 24) (.reg .rbx), .at (.below 32) (.len 72), .at (.below 40) (.reg .rdi), .at (.below 48) (.reg .rdi),
    .at (.below 56) (.len 32), .at (.below 144) (.ret 81), .low (.existential 0)]

variable [Host]

/-- Eth1Data: the declared type of the hand theorem is the kind instance. -/
theorem Encode.fast_path_is_kind_any_frame : ∀ (h : Host), type_of% (@Prysm.Eth1Data.Encode.fast_path h)
    = @encodeFastPathKindAnyFrame h Prysm.Eth1Data.Code.marshalSSZTo Prysm.Eth1Data.encodeLayout [.bytes 32, .uint64, .bytes 32] := by
  intro h; rfl

end Prysm.Eth1Data
