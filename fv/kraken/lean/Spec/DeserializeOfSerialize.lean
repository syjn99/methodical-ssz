import EthLib.Serialization.Proofs.Ssz.Codec.Canonicality
import EthLib.Serialization.Proofs.Ssz.Codec.DecodeFits
import EthLib.Serialization.Proofs.Ssz.Codec.RoundTrip
import EthLib.Serialization.Proofs.Ssz.Type.FitsLaws

/-!
# From a `serialize` characterization to `deserialize` (EthLib theorems)

For a well-formed `Desc` and an abstraction `toV : G → Value` onto the
fitting values with `serialize d (toV g) = .ok (enc g)`:
* `deserialize d (enc g) = .ok (toV g)` (EthLib `roundTrip_of_wellFormed`);
* every accepted input is `enc g` of exactly that value
  (`serialize_of_deserialize`, `fits_of_deserialize`).
So a machine proof only has to say what the code does on `enc g`, and that
it refuses every input that is not of that form.
-/

namespace Spec
open EthLib.Serialization.Ssz

variable {G : Type} {d : Desc} (hw : d.wellFormed = .ok ()) {toV : G → Value} {enc : G → Bytes}
  (hser : ∀ g, serialize d (toV g) = .ok (enc g))
  (hfit : ∀ g, Value.fits d (toV g) = true)
  (hsurj : ∀ v, Value.fits d v = true → ∃ g, toV g = v)

include hw hser hfit in
theorem deserialize_enc (g : G) : deserialize d (enc g) = .ok (toV g) :=
  roundTrip_of_wellFormed hw ((Value.fits_eq_true hw).mp (hfit g)) (hser g)

include hw hser hsurj in
theorem accepted_is_enc {bs : Bytes} {v : Value} (h : deserialize d bs = .ok v) :
    ∃ g, v = toV g ∧ bs = enc g := by
  have hf := (Value.fits_eq_true hw).mpr (fits_of_deserialize d bs v h)
  obtain ⟨g, rfl⟩ := hsurj v hf
  have := serialize_of_deserialize d hw bs (toV g) h
  rw [hser] at this
  exact ⟨g, rfl, (Except.ok.inj this).symm⟩

include hw hser hfit in
theorem rejected_not_enc {bs : Bytes} {e : Err} (h : deserialize d bs = .error e) (g : G) : bs ≠ enc g := by
  rintro rfl; rw [deserialize_enc hw hser hfit] at h; cases h

end Spec
