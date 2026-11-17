import EthLib.Serialization.Ssz

/-!
# Independent hand `Desc` of `v1alpha1.DataColumnsByRootIdentifier`

This description is written by hand from consensus-specs fulu (`ethereum/consensus-specs` release `v1.7.0-beta.4`, `specs/fulu/p2p-interface.md`).
It does not use the checker description `Prysm/DataColumnsByRootIdentifier/SpecChecker.lean`.

    class DataColumnsByRootIdentifier(Container):
        block_root: Root                                    # Bytes32
        columns: List[ColumnIndex, NUMBER_OF_COLUMNS]       # uint64, 128
-/

open EthLib.Serialization.Ssz

namespace Prysm.DataColumnsByRootIdentifier

/-- consensus-specs fulu `DataColumnsByRootIdentifier` (mainnet, NUMBER_OF_COLUMNS = 128). -/
def desc : Desc := .container ["block_root", "columns"] [.byteVector 32, .list (.uint 8) 128]

end Prysm.DataColumnsByRootIdentifier
