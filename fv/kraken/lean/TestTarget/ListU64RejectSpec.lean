import Spec.TestListU64
import Spec.DeserializeOfSerialize
import EthLib.Serialization.Proofs.Ssz.Codec.CanonicalTable
import EthLib.Serialization.Proofs.Ssz.Codec.Table
import TestTarget.ListU64AcceptSpec

/-!
# ListU64: reject correspondence with EthLib

The Go decoder checks four things, in this order (`types.ssz.go`):
1. `len(buf) ≥ 4`, else `ssz.ErrSize`;
2.
-/

open Spec hiding readUint_lt
namespace TestTarget
open EthLib.Serialization.Ssz

/-- The elements read back: `m` little-endian words from `start`. -/
def luElems (bs : Array UInt8) (start : Nat) : Nat → List UInt64
  | 0 => []
  | m + 1 => UInt64.ofNat (readUint bs start 8) :: luElems bs (start + 8) m

theorem luElems_length (bs : Array UInt8) (start m : Nat) : (luElems bs start m).length = m := by
  induction m generalizing start <;> simp [luElems, *]

theorem u64Bytes_luElems (bs : Array UInt8) : ∀ m start, start + 8 * m ≤ bs.size →
    u64Bytes (luElems bs start m) = bs.extract start (start + 8 * m)
  | 0, start, _ => by simp [luElems, u64Bytes]; omega
  | m + 1, start, h => by
    simp only [luElems, u64Bytes]
    have hlt := readUint_lt bs start 8
    rw [UInt64.toNat_ofNat_of_lt' (by simpa using hlt), uintBytes_readUint_slice bs start 8 (by omega),
      u64Bytes_luElems bs m (start + 8) (by omega), Array.extract_append_extract]
    congr 1 <;> omega

theorem lu_checks_enc (bs : Array UInt8) (n : Nat) (hsz : bs.size = 4 + 8 * n) (hn : n ≤ 16)
    (hoff : readUint bs 0 4 = 4) : ∃ g : ListU64, g.ok ∧ bs = luEncode g := by
  refine ⟨⟨luElems bs 4 n⟩, by simp [ListU64.ok, luElems_length]; omega, ?_⟩
  have h1 := uintBytes_readUint_slice bs 0 4 (by omega)
  rw [hoff] at h1
  simp only [luEncode, h1, u64Bytes_luElems bs n 4 (by omega), Array.extract_append_extract]
  rw [show min 0 4 = 0 by rfl, show max (0 + 4) (4 + 8 * n) = bs.size by omega]; simp

/-- Kraken's `Int.ofBytes` (the machine load) and EthLib's `readUint` read the same number. -/
theorem ofBytes_readUint (bs : Array UInt8) : ∀ w s, s + w ≤ bs.size →
    Int.ofBytes ((bs.toList.drop s).take w) = (readUint bs s w : Int)
  | 0, s, _ => by simp [readUint, Int.ofBytes]
  | w + 1, s, h => by
    rw [List.drop_eq_getElem_cons (by simp; omega), List.take_succ_cons, Int.ofBytes_cons,
      ofBytes_readUint bs w (s + 1) (by omega)]
    simp only [readUint, Array.getElem_toList]
    rw [Array.getElem?_eq_getElem (by omega)]; simp; omega

/-- The four checks, as the Go code makes them (EthLib's `readUint` for the offset). -/
def luChecks (bs : Array UInt8) : Prop :=
  4 ≤ bs.size ∧ readUint bs 0 4 = 4 ∧ (bs.size - 4) % 8 = 0 ∧ (bs.size - 4) / 8 ≤ 16

theorem luEncode_checks (g : ListU64) (hg : g.ok) : luChecks (luEncode g) := by
  have hs := lu_encode_size g
  have hr : readUint (luEncode g) 0 4 = 4 := by
    simp only [luEncode]; exact readUint_uintBytes_prefix _ 4 4 (by decide)
  simp only [ListU64.ok] at hg
  refine ⟨by omega, hr, by omega, by omega⟩

/-- **EthLib accepts exactly the inputs that pass the four checks.** -/
theorem lu_spec_accepts_iff (bs : Array UInt8) :
    (∃ v, deserialize luDesc bs = .ok v) ↔ luChecks bs := by
  constructor
  · rintro ⟨v, hd⟩
    obtain ⟨⟨g, hg⟩, rfl, rfl⟩ := accepted_is_enc (G := LuG) (toV := fun g => g.1.toValue)
      (enc := fun g => luEncode g.1) luDesc_wellFormed (fun g => lu_serialize g.1 g.2)
      lu_toValue_surjective' hd
    exact luEncode_checks g hg
  · rintro ⟨h4, hoff, hmod, hn⟩
    obtain ⟨g, hg, rfl⟩ := lu_checks_enc bs ((bs.size - 4) / 8) (by omega) hn hoff
    exact ⟨_, deserialize_enc (G := LuG) (toV := fun g => g.1.toValue) (enc := fun g => luEncode g.1)
      luDesc_wellFormed (fun g => lu_serialize g.1 g.2) (fun g => lu_toValue_fits g.1 g.2) ⟨g, hg⟩⟩

/-- Each failing check makes EthLib reject (the order of the Go checks). -/
theorem lu_spec_rejects (bs : Array UInt8)
    (h : bs.size < 4 ∨ readUint bs 0 4 ≠ 4 ∨ (bs.size - 4) % 8 ≠ 0 ∨ 16 < (bs.size - 4) / 8) :
    ∃ e, deserialize luDesc bs = .error e := by
  cases hd : deserialize luDesc bs with
  | error e => exact ⟨e, rfl⟩
  | ok v =>
    obtain ⟨h4, hoff, hmod, hn⟩ := (lu_spec_accepts_iff bs).mp ⟨v, hd⟩
    rcases h with h | h | h | h <;> first | omega | exact absurd hoff h

end TestTarget
