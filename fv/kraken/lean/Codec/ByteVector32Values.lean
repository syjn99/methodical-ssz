import Prysm.SyncCommittee.Spec
import Prysm.HistoricalBatch.SpecDefinitions

/-!
# Values of `byteVector 32`

`toByteVector32` reads a 32-byte vector from a value; `allFit_byteVector32` and `allFit_map_byteVector32` relate
a list of fitting values and a list of 32-byte vectors.
-/

namespace Codec
open EthLib.Serialization.Ssz Spec

/-- A total reading of a value as 32 bytes (the zero vector if it is not 32 bytes). -/
def toByteVector32 : Value → Vector UInt8 32
  | .bytes d => if h : d.size = 32 then ⟨d, h⟩ else ⟨Array.replicate 32 0, by simp⟩
  | _ => ⟨Array.replicate 32 0, by simp⟩

theorem allFit_byteVector32 : ∀ (vs : List Value), Value.allFit (.byteVector 32) vs = true →
    (vs.map Codec.toByteVector32).map (fun p => Value.bytes p.toArray) = vs
  | [], _ => rfl
  | v :: vs, h => by
    simp only [Value.allFit, Bool.and_eq_true] at h
    obtain ⟨h0, h1⟩ := h
    simp only [List.map_cons, Codec.allFit_byteVector32 vs h1, List.cons.injEq, and_true]
    cases v <;> simp [Value.fits] at h0
    simp [Codec.toByteVector32, h0]

theorem allFit_map_byteVector32 : ∀ (l : List (Vector UInt8 32)),
    Value.allFit (.byteVector 32) (l.map fun p => Value.bytes p.toArray) = true
  | [] => by simp [Value.allFit]
  | p :: l => by simp [Value.allFit, Value.fits, Codec.allFit_map_byteVector32 l]

end Codec
