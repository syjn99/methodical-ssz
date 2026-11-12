import Kraken.X64.WP
import E2eDec.Include

/-!
# ELF data of the ENC decoder set that the decoder statements read

Elaborated from `fv/kraken/prysm/go1.26.10/e2e/lv/link-dec/data/` by `dcd_data_include`; the files are written by
`gen/e2e/encdeclink.py data` (with `link/data.py`'s code) from the operands of the converted code, and
`link/check.py` (f) compares them with the ELF. Operands equal to an item of the Checkpoint or LV T3 set are asserted
equal by `encdeclink.py` and the statements use the existing names: `E2e.Data.e2eU8Type_addr`,
`E2eList.Data.lvU64Type_addr`, `E2e.Data.e2eIntType_addr`, `E2e.Data.e2eErrSize_addr`,
`E2eList.Data.lvErrInvalidVariableOffset_addr`, `E2eList.Data.lvErrIncorrectListSize_addr`,
`E2eList.Data.lvErrListTooBig_addr`. New here: the two `fmt.Errorf` formats of the list rejects.
-/

namespace E2eDec.Data
-- "ssz-max exceeded: c.Columns has %d elements, ssz-max is 128: %w" (63 bytes)
dcd_data_include dcdFmtTooBig
-- "misaligned bytes: c.Columns length is %d, which is not a multiple of 8: %w" (74 bytes)
dcd_data_include dcdFmtMis
end E2eDec.Data
