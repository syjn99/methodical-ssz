import Spec.TestListU64
import Spec.DeserializeOfSerialize
import EthLib.Serialization.Proofs.Ssz.Codec.CanonicalTable
import EthLib.Serialization.Proofs.Ssz.Codec.Table

/-!
# A list of uint64 values read back from bytes

`Codec.readUint64List bs start m` reads `m` little-endian 8-byte words from `start` (EthLib `readUint`).
`Codec.uint64Bytes_readUint64List`: their encoding (`Spec.uint64Bytes`) is the slice of `bs`.
The namespace is `Codec`, not `Spec`:
in `Spec`, the name `readUint_lt` of the proof would resolve to `Spec.readUint_lt`.
-/

open Spec hiding readUint_lt
open EthLib.Serialization.Ssz

/-- The elements read back: `m` little-endian words from `start`. -/
def _root_.Codec.readUint64List (bs : Array UInt8) (start : Nat) : Nat → List UInt64
  | 0 => []
  | m + 1 => UInt64.ofNat (readUint bs start 8) :: Codec.readUint64List bs (start + 8) m

theorem _root_.Codec.readUint64List_length (bs : Array UInt8) (start m : Nat) : (Codec.readUint64List bs start m).length = m := by
  induction m generalizing start <;> simp [Codec.readUint64List, *]

theorem _root_.Codec.uint64Bytes_readUint64List (bs : Array UInt8) : ∀ m start, start + 8 * m ≤ bs.size →
    uint64Bytes (Codec.readUint64List bs start m) = bs.extract start (start + 8 * m)
  | 0, start, _ => by simp [Codec.readUint64List, uint64Bytes]; omega
  | m + 1, start, h => by
    simp only [Codec.readUint64List, uint64Bytes]
    have hlt := readUint_lt bs start 8
    rw [UInt64.toNat_ofNat_of_lt' (by simpa using hlt), uintBytes_readUint_slice bs start 8 (by omega),
      Codec.uint64Bytes_readUint64List bs m (start + 8) (by omega), Array.extract_append_extract]
    congr 1 <;> omega
