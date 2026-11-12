import Kraken.X64.WP
import Prysm.ElfData.SyncAggregateAndSyncCommitteeReader

/-!
# ELF data of the SyncAggregate and SyncCommittee set that their statements read

Every definition is elaborated from a file of `fv/kraken/prysm/go1.26.10/e2e/lv/link/data/` by
`lv_data_include`; the files are written by `gen/e2e/lvlink.py data` (with `link/data.py`'s code)
from the operands of the converted code, and `link/check.py` (f) compares them with the ELF.
No byte and no offset below is written by hand.

Operands that equal an item of the Checkpoint / Epoch set are not repeated here (`lvlink.py` asserts
the equality): the statements use `ElfData.CheckpointAndEpoch.e2eU8Type_addr` (uint8 element type word) and
`ElfData.CheckpointAndEpoch.e2eErrSize_addr` (`ssz.ErrSize`).
-/

namespace ElfData.SyncAggregateAndSyncCommittee

-- the element type word of the SyncCommittee `[][]byte` backing array (`make([][]byte, 512)`,
-- makeslice esz 24): abi.Type of `[]uint8`
lv_data_include lvSliceType

end ElfData.SyncAggregateAndSyncCommittee
