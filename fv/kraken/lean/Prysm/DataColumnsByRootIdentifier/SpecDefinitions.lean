import Spec.TestListU64

/-!
# Definitions that the encoder statements use (DataColumnsByRootIdentifier)

These definitions are part of the frozen encoder statements (`Prysm/DataColumnsByRootIdentifier/StatementsEncode.lean`). A later change needs a new name and a reason.

- `desc`: hand `Desc` from consensus-specs fulu (p2p-interface; no local copy of the spec text):

      class DataColumnsByRootIdentifier(Container):
          block_root: Root                                    # Bytes32
          columns: List[ColumnIndex, NUMBER_OF_COLUMNS]       # uint64, 128

- `SszValue`: the SSZ content of a Go `v1alpha1.DataColumnsByRootIdentifier` whose BlockRoot has 32 bytes and whose
  Columns has at most 128 elements (the field `hcols` keeps the length condition explicit).
- `receiverValue`: the `Value` of a Go receiver with any BlockRoot bytes and any Columns (for the reject specs).
- `offsetBytes`: the 4 bytes of the offset 36.
- `SszValue.encode`: block_root (32) ‖ offset 36 (4) ‖ the columns as 8-byte little-endian words.
The backing array of `[]uint64` is one contiguous block; its bytes are `Spec.uint64Bytes cols`.
-/

open EthLib.Serialization.Ssz

namespace Prysm.DataColumnsByRootIdentifier

/-- consensus-specs fulu `DataColumnsByRootIdentifier` (mainnet, NUMBER_OF_COLUMNS = 128). -/
def desc : Desc := .container ["block_root", "columns"] [.byteVector 32, .list (.uint 8) 128]

/-- SSZ content of a Go `v1alpha1.DataColumnsByRootIdentifier` (32-byte BlockRoot, at most 128 Columns). -/
structure SszValue where
  root : Vector UInt8 32
  cols : List UInt64
  hcols : cols.length ≤ 128

/-- The `Value` of a Go receiver with BlockRoot bytes `r` and Columns `cols` (any lengths; used by the reject specs). -/
def receiverValue (r : Array UInt8) (cols : List UInt64) : Value :=
  .seq [.bytes r, .seq (cols.map fun x => .uint x.toNat)]

def SszValue.toValue (g : SszValue) : Value := receiverValue g.root.toArray g.cols

/-- The 4-byte little-endian offset 36. -/
def offsetBytes : List UInt8 := [0x24, 0, 0, 0]

/-- `block_root ‖ offset 36 ‖ columns`. -/
def SszValue.encode (g : SszValue) : Array UInt8 := g.root.toArray ++ offsetBytes.toArray ++ Spec.uint64Bytes g.cols

end Prysm.DataColumnsByRootIdentifier
