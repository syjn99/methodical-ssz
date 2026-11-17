import Codec.Kind.EncodeFastPathAnyFrame

/-!
# Frame layout of the Checkpoint encoder fast-path statement

`encodeLayout` is the frame layout that `encodeFastPathKindAnyFrame` reads for `Encode.generated_fast`
(`Prysm/Checkpoint/GeneratedEncodeFastPath.lean`) and for the tie `Encode.fast_path_kind_tie` (`Prysm/Checkpoint/EncodeFastPathKindTie.lean`).
The generator reads this definition through its options `--hand-layout` and `--hand-layout-src` (`gen/generator/gen.sh`).
-/

open Codec
namespace Prysm.Checkpoint

/-- Checkpoint `MarshalSSZTo`: frame `0x68`, small guard. Stack chunks `fp s2 l16 l24 l32 t40 t30 rslot` (the
order of the hand statement). -/
def encodeLayout : EncoderFrameLayout where
  stateWord := true
  frame := 104
  guardAddend := 0
  callsMemmove := true
  stackChunkCount := 8
  stackChunkLengths := [(0, 8), (1, 8), (2, 8), (3, 8), (4, 8), (5, 16), (6, 16), (7, 8)]
  pre := [.at (.below 8) (.original 0), .at (.above 16) (.original 1), .at (.below 16) (.original 2), .at (.below 24) (.original 3),
    .at (.below 32) (.original 4), .at (.below 48) (.original 6), .at (.below 64) (.original 5), .at (.below 120) (.original 7), .low .scratch]
  existentials := [.fixed 8, .fixed 16, .low]
  post := [.at (.below 8) (.reg .rbp), .at (.above 16) (.reg .rbx), .at (.below 16) (.reg .rbx), .at (.below 24) (.reg .rdi),
    .at (.below 32) (.len 40), .at (.below 48) (.existential 1), .at (.below 64) (.field 0), .at (.below 56) (.existential 0),
    .at (.below 120) (.ret 63), .low (.existential 2)]

end Prysm.Checkpoint
