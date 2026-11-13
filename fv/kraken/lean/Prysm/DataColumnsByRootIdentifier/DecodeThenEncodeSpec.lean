import Prysm.DataColumnsByRootIdentifier.SpecDecodeBridge

/-!
# Spec-level round trip (the shape of `Prysm.Checkpoint.DecodeThenEncode.round_trip_spec`)

Every input that EthLib accepts against `desc` serializes back to itself, and every `SszValue` value
deserializes back to itself.
-/

namespace Prysm.DataColumnsByRootIdentifier
open EthLib.Serialization.Ssz

theorem DecodeThenEncode.round_trip_spec (bs : Array UInt8) (v : Value) (hd : deserialize desc bs = .ok v) :
    serialize desc v = .ok bs := by
  obtain ⟨g, rfl, rfl⟩ := accepted_is_encode hd
  exact toValue_serialize g

theorem DecodeThenEncode.round_trip_spec' (g : SszValue) :
    ∃ bs, serialize desc g.toValue = .ok bs ∧ deserialize desc bs = .ok g.toValue :=
  ⟨SszValue.encode g, toValue_serialize g, encode_roundtrip g⟩

end Prysm.DataColumnsByRootIdentifier
