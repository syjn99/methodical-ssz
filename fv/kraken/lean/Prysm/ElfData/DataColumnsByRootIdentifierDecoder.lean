import Kraken.X64.WP
import Prysm.ElfData.DataColumnsByRootIdentifierDecoderReader

/-!
# ELF data of the `DataColumnsByRootIdentifier` decoder set that the decoder statements read

Elaborated from `fv/kraken/prysm/go1.26.10/e2e/lv/link-dec/data/` by `dcd_data_include`; the files are written by
`gen/e2e/encdeclink.py data` (with `link/data.py`'s code) from the operands of the converted code, and
`link/check.py` (f) compares them with the ELF. Operands equal to an item of the Checkpoint or IndexedAttestation set are asserted
equal by `encdeclink.py` and the statements use the existing names: `ElfData.CheckpointAndEpoch.e2eU8Type_addr`,
`ElfData.IndexedAttestation.lvU64Type_addr`, `ElfData.CheckpointAndEpoch.e2eIntType_addr`, `ElfData.CheckpointAndEpoch.e2eErrSize_addr`,
`ElfData.IndexedAttestation.lvErrInvalidVariableOffset_addr`, `ElfData.IndexedAttestation.lvErrIncorrectListSize_addr`,
`ElfData.IndexedAttestation.lvErrListTooBig_addr`. New here: the two `fmt.Errorf` formats of the list rejects.
-/

namespace ElfData.DataColumnsByRootIdentifierDecoder
-- "ssz-max exceeded: c.Columns has %d elements, ssz-max is 128: %w" (63 bytes)
dcd_data_include dcdFmtTooBig
-- "misaligned bytes: c.Columns length is %d, which is not a multiple of 8: %w" (74 bytes)
dcd_data_include dcdFmtMis
end ElfData.DataColumnsByRootIdentifierDecoder
