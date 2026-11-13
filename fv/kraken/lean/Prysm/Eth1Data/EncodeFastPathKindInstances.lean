import Codec.Kind.EncodeFastPathAnyFrame

/-!
# Hand layout of the Eth1Data encoder fast-path statement

`encodeLayout` is the layout of the hand statement `Encode.fast_path`, as `encFastKindN` reads it.
The tie theorem of Eth1Data stays in `Prysm/BeaconBlockHeader/EncodeFastPathKindInstances.lean`, because its negative case compares the two layouts.
-/

open Machine Runtime

open Codec
namespace Prysm.Eth1Data

/-- Eth1Data `MarshalSSZTo`: frame `0x80` (`add $-0x80,%rsp`), large-frame guard (`lea -0x8(%rsp),%r12`).
Stack chunks `fp s1 s2 l16 l24 l32 l40 l48 l56 rslot`. -/
def encodeLayout : EncLayout where
  st := true
  frame := 128
  gd := 8
  rt := true
  nstk := 10
  lens := [(0, 8), (1, 8), (2, 8), (3, 8), (4, 8), (5, 8), (6, 8), (7, 8), (8, 8), (9, 8)]
  pre := [.at (.dn 8) (.orig 0), .at (.up 8) (.orig 1), .at (.up 16) (.orig 2), .at (.dn 16) (.orig 3),
    .at (.dn 24) (.orig 4), .at (.dn 32) (.orig 5), .at (.dn 40) (.orig 6), .at (.dn 48) (.orig 7),
    .at (.dn 56) (.orig 8), .at (.dn 144) (.orig 9), .lo .scr]
  exs := [.lo]
  post := [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 16) (.reg .rbx),
    .at (.dn 24) (.reg .rbx), .at (.dn 32) (.len 72), .at (.dn 40) (.reg .rdi), .at (.dn 48) (.reg .rdi),
    .at (.dn 56) (.len 32), .at (.dn 144) (.ret 81), .lo (.ex 0)]

end Prysm.Eth1Data
