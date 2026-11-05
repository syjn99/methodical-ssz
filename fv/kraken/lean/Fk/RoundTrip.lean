import Fk.FvSpec
import Fk.LuSpec
import Fk.ScSpec

/-!
# Go-level round trips (B2.4): Scalars, ListU64, FixedVec

For each type, with `enc` the Go encoder's output as a function of the Go value:
1. the marshal fast path writes `enc g` at `dst[len:]` and leaves `dst[:len]`
   (`sc_marshal_spec_k`, `lu_marshal_main` + `luEncode_toList`,
   `fv_marshal_main` + `fv_marshal_spec_k`);
2. EthLib decodes `enc g` to `g.toValue` (below, `deserialize_enc`);
3. the unmarshal accept theorem on input `enc g` gives a receiver holding the
   Go layout of some `g'` with `g'.toValue = g.toValue` (`*_unmarshal_accept_spec_k`),
   and the abstraction is injective, so `g' = g` (below).
So unmarshalling what marshal wrote restores the same Go value. The two
machine runs are separate theorems (two calls); this file states the link.
-/

open Fv1 EthLib.Serialization.Ssz

theorem sc_roundtrip (g : Scalars) :
    deserialize scDesc (scEncode g) = .ok g.toValue ∧ ∀ g', g'.toValue = g.toValue → g' = g :=
  ⟨deserialize_enc scDesc_wellFormed sc_serialize sc_toValue_fits g,
   fun g' h => sc_toValue_injective g' g h⟩

theorem lu_roundtrip (g : ListU64) (hg : g.ok) :
    deserialize luDesc (luEncode g) = .ok g.toValue ∧ ∀ g', g'.toValue = g.toValue → g' = g :=
  ⟨deserialize_enc (G := LuG) (toV := fun g => g.1.toValue) (enc := fun g => luEncode g.1)
     luDesc_wellFormed (fun g => lu_serialize g.1 g.2) (fun g => lu_toValue_fits g.1 g.2) ⟨g, hg⟩,
   fun g' h => lu_toValue_injective g' g h⟩

theorem fv_roundtrip (g : FixedVecG) :
    deserialize fvDesc (fvEncode g) = .ok g.toValue ∧ ∀ g', g'.toValue = g.toValue → g' = g :=
  ⟨deserialize_enc fvDesc_wellFormed fv_serialize fv_toValue_fits g,
   fun g' h => fv_toValue_injective g' g h⟩
