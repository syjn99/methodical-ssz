import Codec.Kind.EncodeFastPathAnyFrame

/-!
# Hand layout of the Eth1Data encoder fast-path statement

`encodeLayout` is the layout of the hand statement `Encode.fast_path`, as `encodeFastPathKindAnyFrame` reads it.
The tie theorem of Eth1Data stays in `Prysm/BeaconBlockHeader/EncodeFastPathKindInstances.lean`, because its negative case compares the two layouts.
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

end Prysm.Eth1Data
