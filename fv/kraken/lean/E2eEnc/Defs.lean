import Spec.TestListU64

/-!
# Definitions that the encoder statements use (DataColumnsByRootIdentifier)

These definitions are part of the frozen encoder statements (`StmtEnc.lean`). A later change needs a new name and a reason.

- `prysmDcDesc`: hand `Desc` from consensus-specs fulu (p2p-interface; no local copy of the spec text):

      class DataColumnsByRootIdentifier(Container):
          block_root: Root                                    # Bytes32
          columns: List[ColumnIndex, NUMBER_OF_COLUMNS]       # uint64, 128

- `PDc`: the SSZ content of a Go `v1alpha1.DataColumnsByRootIdentifier` whose BlockRoot has 32 bytes and whose
  Columns has at most 128 elements (the field `hcols` keeps the length condition explicit).
- `dcValue`: the `Value` of a Go receiver with any BlockRoot bytes and any Columns (for the reject specs).
- `dcOff`: the 4 bytes of the offset 36.
- `pdcEnc`: block_root (32) ‖ offset 36 (4) ‖ the columns as 8-byte little-endian words.
The backing array of `[]uint64` is one contiguous block; its bytes are `Spec.u64Bytes cols`.
-/

open EthLib.Serialization.Ssz

namespace E2eEnc

/-- consensus-specs fulu `DataColumnsByRootIdentifier` (mainnet, NUMBER_OF_COLUMNS = 128). -/
def prysmDcDesc : Desc := .container ["block_root", "columns"] [.byteVector 32, .list (.uint 8) 128]

/-- SSZ content of a Go `v1alpha1.DataColumnsByRootIdentifier` (32-byte BlockRoot, at most 128 Columns). -/
structure PDc where
  root : Vector UInt8 32
  cols : List UInt64
  hcols : cols.length ≤ 128

/-- The `Value` of a Go receiver with BlockRoot bytes `r` and Columns `cols` (any lengths; used by the reject specs). -/
def dcValue (r : Array UInt8) (cols : List UInt64) : Value :=
  .seq [.bytes r, .seq (cols.map fun x => .uint x.toNat)]

def PDc.toValue (g : PDc) : Value := dcValue g.root.toArray g.cols

/-- The 4-byte little-endian offset 36. -/
def dcOff : List UInt8 := [0x24, 0, 0, 0]

/-- `block_root ‖ offset 36 ‖ columns`. -/
def pdcEnc (g : PDc) : Array UInt8 := g.root.toArray ++ dcOff.toArray ++ Spec.u64Bytes g.cols

end E2eEnc
