import Runtime.Contracts
import Prysm.AttestationData.Spec
import Spec.TestListU64

/-!
# Definitions that the IndexedAttestation statements use (IndexedAttestation)

These definitions are part of the frozen IndexedAttestation statements (`Prysm/IndexedAttestation/Statements.lean`). A later change needs a new name and a reason.

- `desc`: hand `Desc` from consensus-specs phase0 (no local copy of the spec text):

      class IndexedAttestation(Container):
          attesting_indices: List[ValidatorIndex, MAX_VALIDATORS_PER_COMMITTEE]   # uint64, 2048
          data: AttestationData
          signature: BLSSignature                                                # Bytes96

  `data` reuses the existing hand `Prysm.AttestationData.desc`.
- `SszValue`: the SSZ content of a Go `v1alpha1.IndexedAttestation` whose Signature has 96 bytes and whose AttestingIndices
  has at most 2048 elements (the field `hidx` keeps the length condition explicit).
- `SszValue.encode`: offset 228 (4 bytes) ‖ data (128) ‖ signature (96) ‖ the indices as 8-byte little-endian words.
- `offsetBytes`: the 4 bytes of the offset 228.
The element backing array of `[]uint64` is one contiguous block equal to the input bytes `buf[228:]`; the statements
state it as one byte list of length `8 · n` with `n ≤ 2048`, so no per-element predicate (and not `Prysm.SyncCommittee.elementBlocks`) is used.
-/

open Machine Runtime EthLib.Serialization.Ssz

namespace Prysm.IndexedAttestation

/-- consensus-specs phase0 `IndexedAttestation` (mainnet). -/
def desc : Desc := .container ["attesting_indices", "data", "signature"]
  [.list (.uint 8) 2048, Prysm.AttestationData.desc, .byteVector 96]

/-- SSZ content of a Go `v1alpha1.IndexedAttestation` (at most 2048 indices, Data, 96-byte Signature). -/
structure SszValue where
  idx : List UInt64
  hidx : idx.length ≤ 2048
  data : Prysm.AttestationData.SszValue
  signature : Vector UInt8 96

def SszValue.toValue (g : SszValue) : Value :=
  .seq [.seq (g.idx.map fun x => .uint x.toNat), g.data.toValue, .bytes g.signature.toArray]

/-- The 4-byte little-endian offset 228. -/
def offsetBytes : List UInt8 := [0xe4, 0, 0, 0]

/-- `offset 228 ‖ data ‖ signature ‖ indices`. -/
def SszValue.encode (g : SszValue) : Array UInt8 :=
  offsetBytes.toArray ++ Prysm.AttestationData.SszValue.encode g.data ++ g.signature.toArray ++ Spec.u64Bytes g.idx

end Prysm.IndexedAttestation
