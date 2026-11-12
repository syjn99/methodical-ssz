import Runtime.Contracts
import E2eAd.Spec
import Spec.TestListU64

/-!
# Definitions that the IndexedAttestation statements use (IndexedAttestation)

These definitions are part of the frozen IndexedAttestation statements (`StmtIa.lean`). A later change needs a new name and a reason.

- `prysmIaDesc`: hand `Desc` from consensus-specs phase0 (no local copy of the spec text):

      class IndexedAttestation(Container):
          attesting_indices: List[ValidatorIndex, MAX_VALIDATORS_PER_COMMITTEE]   # uint64, 2048
          data: AttestationData
          signature: BLSSignature                                                # Bytes96

  `data` reuses the existing hand `E2e.prysmAdDesc`.
- `PIa`: the SSZ content of a Go `v1alpha1.IndexedAttestation` whose Signature has 96 bytes and whose AttestingIndices
  has at most 2048 elements (the field `hidx` keeps the length condition explicit).
- `piaEnc`: offset 228 (4 bytes) ‖ data (128) ‖ signature (96) ‖ the indices as 8-byte little-endian words.
- `iaOff`: the 4 bytes of the offset 228.
The element backing array of `[]uint64` is one contiguous block equal to the input bytes `buf[228:]`; the statements
state it as one byte list of length `8 · n` with `n ≤ 2048`, so no per-element predicate (and not `lvElems`) is used.
-/

open Machine Runtime TestTarget EthLib.Serialization.Ssz

namespace E2eList

/-- consensus-specs phase0 `IndexedAttestation` (mainnet). -/
def prysmIaDesc : Desc := .container ["attesting_indices", "data", "signature"]
  [.list (.uint 8) 2048, E2e.prysmAdDesc, .byteVector 96]

/-- SSZ content of a Go `v1alpha1.IndexedAttestation` (at most 2048 indices, Data, 96-byte Signature). -/
structure PIa where
  idx : List UInt64
  hidx : idx.length ≤ 2048
  data : E2e.PAd
  signature : Vector UInt8 96

def PIa.toValue (g : PIa) : Value :=
  .seq [.seq (g.idx.map fun x => .uint x.toNat), g.data.toValue, .bytes g.signature.toArray]

/-- The 4-byte little-endian offset 228. -/
def iaOff : List UInt8 := [0xe4, 0, 0, 0]

/-- `offset 228 ‖ data ‖ signature ‖ indices`. -/
def piaEnc (g : PIa) : Array UInt8 :=
  iaOff.toArray ++ E2e.padEnc g.data ++ g.signature.toArray ++ Spec.u64Bytes g.idx

end E2eList
