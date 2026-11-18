import Codec.Kind.EncodeFastPathAnyFrame

/-!
# Frame layout of the Eth1Data encoder fast-path statement

`encodeLayout` is the frame layout that `encodeFastPathKindAnyFrame` reads for `Encode.generated_fast`
(`Prysm/Eth1Data/GeneratedEncodeFastPath.lean`).
The `encoder --fast-path` row of the type in `gen/generator/types.tsv` gives this definition to the generator.
The row names it with the options `--hand-layout` and `--hand-layout-src`, and `gen/generator/gen.sh` runs the row.
-/

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
