import Prysm.Checkpoint.Spec
import Prysm.Checkpoint.SpecEquivalence
import Prysm.AttestationData.SpecChecker
import Prysm.AttestationData.Spec

/-!
# Field lists with the same encoders

`SameEncode fs gs`: the fields of the two lists encode every value the same way. `serializeFields_congr`:
`serializeFields` of such lists agree. EthLib's `serialize` reads only the encoders of the fields, so two
`Desc`s that differ only in their names serialize alike.
-/

namespace Codec
open EthLib.Serialization.Ssz
open Spec hiding readUint_lt

/-- Two field lists whose fields encode every value the same way. -/
inductive SameEncode : List Desc → List Desc → Prop
  | nil : Codec.SameEncode [] []
  | cons {a b : Desc} {as bs : List Desc} : (∀ v, serialize a v = serialize b v) → Codec.SameEncode as bs →
      Codec.SameEncode (a :: as) (b :: bs)

/-- `serializeFields` only reads `serialize` of each field: field lists with the same encoders agree. -/
theorem serializeFields_congr : ∀ (fs gs : List Desc) (vs : List Value),
    Codec.SameEncode fs gs → serializeFields fs vs = serializeFields gs vs
  | [], [], [], _ => rfl
  | [], [], _ :: _, _ => by simp [serializeFields]
  | _ :: _, _ :: _, [], _ => by simp [serializeFields]
  | f :: fs, g :: gs, v :: vs, .cons h hs => by
    simp only [serializeFields, h v, Codec.serializeFields_congr fs gs vs hs]

end Codec
