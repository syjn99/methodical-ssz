import Kraken.X64.WP
import E2eList.IncludeIa

/-!
# ELF data of the IndexedAttestation set that its statements read

Every definition is elaborated from a file of `fv/kraken/prysm/go1.26.10/e2e/lv/link-t3/data/` by
`lvt3_data_include`; the files are written by `gen/e2e/lvlink.py data --t3` (with `link/data.py`'s code)
from the operands of the converted code, and `link/check.py` (f) compares them with the ELF.
No byte and no offset below is written by hand.

Operands that equal an item of the Checkpoint / Epoch set are not repeated here (`lvlink.py` asserts the
equality): the statements use `E2e.Data.e2eU8Type_addr` (uint8), `E2e.Data.e2eErrSize_addr` (`ssz.ErrSize`),
`E2e.Data.e2eIntType_addr` (`type:int`) and the label `go_itab._errors.errorString_error`.
-/

namespace E2eList.Data

-- element type word of `make([]uint64, numElem)` (makeslice esz 8): abi.Type of uint64 (Size_ 8, Kind 11)
lvt3_data_include lvU64Type
-- type word of `new(AttestationData)` (newobject sz 96): abi.Type of the struct (Size_ 96, Kind 25)
lvt3_data_include lvAdType
-- the two `fmt.Errorf` formats of the list rejects ("%d … %w")
lvt3_data_include lvFmtTooBig
lvt3_data_include lvFmtMis
-- error globals: addresses only (values are set by the runtime's package init)
lvt3_data_include lvErrListTooBig
lvt3_data_include lvErrIncorrectListSize
lvt3_data_include lvErrInvalidVariableOffset

end E2eList.Data
