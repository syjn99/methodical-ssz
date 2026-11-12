import E2eEnc.SpecD

/-!
# Spec-level round trip (the shape of `Prysm.Checkpoint.DecodeThenEncode.round_trip_spec`)

Every input that EthLib accepts against `prysmDcDesc` serializes back to itself, and every `PDc` value
deserializes back to itself.
-/

namespace E2eEnc
open EthLib.Serialization.Ssz

theorem dc_e2e_spec_roundtrip (bs : Array UInt8) (v : Value) (hd : deserialize prysmDcDesc bs = .ok v) :
    serialize prysmDcDesc v = .ok bs := by
  obtain ⟨g, rfl, rfl⟩ := pdc_accepted_is_enc hd
  exact pdc_serialize g

theorem dc_e2e_spec_roundtrip' (g : PDc) :
    ∃ bs, serialize prysmDcDesc g.toValue = .ok bs ∧ deserialize prysmDcDesc bs = .ok g.toValue :=
  ⟨pdcEnc g, pdc_serialize g, pdc_roundtrip g⟩

end E2eEnc
