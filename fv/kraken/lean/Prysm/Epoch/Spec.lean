import EthLib.Serialization.Ssz
import EthLib.Serialization.Proofs.Ssz.Codec.DecodeFits
import EthLib.Serialization.Proofs.Ssz.Codec.CanonicalTable

/-!
# Spec of the hand-written Prysm `primitives.Epoch`

Independent hand `Desc`, written from consensus-specs phase0 (`specs/phase0/beacon-chain.md`, "Custom types"):
`Epoch = uint64`.
EthLib `Desc.uint` takes a byte width, so the type is `.uint 8`.
No Desc checker record exists for the type, so this module has no `checkerDesc`.
The lemmas below about `.uint 8` read EthLib only; the specifications of `Slot` and `ValidatorIndex` use them too.
`deserialize (.uint 8) bs` accepts exactly the inputs of 8 bytes, and its value is the little-endian number of the 8 bytes.
-/

namespace Prysm.Epoch
open EthLib.Serialization.Ssz

/-- consensus-specs phase0 `Epoch`. -/
def desc : Desc := .uint 8

/-- An input of 8 bytes: EthLib returns the little-endian number of the 8 bytes. -/
theorem uint64_deserialize_ok (bs : Array UInt8) (h : bs.size = 8) :
    deserialize (.uint 8) bs = .ok (.uint (readUint bs 0 8)) := by
  simp [deserialize, h, pure, Except.pure]

/-- **EthLib accepts exactly the 8-byte inputs.** -/
theorem uint64_spec_accepts_iff (bs : Array UInt8) : (∃ v, deserialize (.uint 8) bs = .ok v) ↔ bs.size = 8 := by
  constructor
  · rintro ⟨v, hd⟩
    by_cases h : bs.size = 8
    · exact h
    · simp [deserialize, h, throw, throwThe, MonadExceptOf.throw, Functor.map, Except.map] at hd
  · intro h
    exact ⟨_, uint64_deserialize_ok bs h⟩

/-- `len(buf) ≠ 8`: EthLib rejects. -/
theorem uint64_spec_rejects (bs : Array UInt8) (h : bs.size ≠ 8) : ∃ e, deserialize (.uint 8) bs = .error e := by
  cases hd : deserialize (.uint 8) bs with
  | error e => exact ⟨e, rfl⟩
  | ok v => exact absurd ((uint64_spec_accepts_iff bs).mp ⟨v, hd⟩) h

/-- Every input that EthLib accepts is `uintBytes 8 x` of the value `x` that it returns. -/
theorem uint64_accepted_is_encoding {bs : Array UInt8} {v : Value} (h : deserialize (.uint 8) bs = .ok v) :
    ∃ x : UInt64, v = .uint x.toNat ∧ bs = uintBytes 8 x.toNat := by
  have h8 : bs.size = 8 := (uint64_spec_accepts_iff bs).mp ⟨v, h⟩
  rw [uint64_deserialize_ok bs h8] at h
  cases h
  have hlt : readUint bs 0 8 < 2 ^ 64 := readUint_lt bs 0 8
  refine ⟨UInt64.ofNat (readUint bs 0 8), ?_, ?_⟩
  · rw [UInt64.toNat_ofNat_of_lt' hlt]
  · rw [UInt64.toNat_ofNat_of_lt' hlt, uintBytes_readUint_slice bs 0 8 (by omega), Nat.zero_add, ← h8,
      Array.extract_size]

end Prysm.Epoch
