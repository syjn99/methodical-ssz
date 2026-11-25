module

public import Codec.Kind.EncodeFastPathAnyFrame

@[expose] public section

/-!
# Frame layout of the BeaconBlockHeader encoder fast-path statement

`encodeLayout` is the frame layout that `encodeFastPathKindAnyFrame` reads for `Encode.generated_fast`
(`Prysm/BeaconBlockHeader/GeneratedEncodeFastPath.lean`).
The `encoder --fast-path` row of the type in `gen/generator/types.tsv` gives this definition to the generator.
The row names it with the options `--hand-layout` and `--hand-layout-src`, and `gen/generator/gen.sh` runs the row.
-/

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

end Prysm.BeaconBlockHeader
