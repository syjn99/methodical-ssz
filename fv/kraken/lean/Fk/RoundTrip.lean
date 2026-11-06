import Fk.FvSpec
import Fk.LuSpec
import Fk.ScSpec

/-!
# Go-level round trips: Scalars, ListU64, FixedVec

For each type, with `enc` the Go encoder's output as a function of the Go value:
1.
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
