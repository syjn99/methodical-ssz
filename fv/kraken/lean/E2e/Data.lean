import Kraken.X64.WP
import E2e.Include

/-!
# ELF data of the Go 1.26.10 namespace that the prysm-e2e theorems read

Every definition is elaborated from a file of
`fv/kraken/prysm/go1.26.10/e2e/link/data/` by `e2e_data_include`; the files are
written by `gen/e2e/e2elink.py data` (with `link/data.py`'s code) from the
operands of the converted code, and `link/check.py` (f) compares them with the
ELF. No byte and no offset below is written by hand.
-/

namespace E2e.Data

-- the uint8 element type word (makeslice in the decoder, growslice in the encoder)
e2e_data_include e2eU8Type
-- "Epoch: %w" (Checkpoint decoder, error path) and its errors.errorString type
e2e_data_include e2eCpFmtW
e2e_data_include e2eErrStrType
e2e_data_include e2eErrorStringItab
-- error globals: addresses only (values are set by the runtime's package init)
e2e_data_include e2eErrSize
e2e_data_include e2eErrBytesLength
-- Epoch decoder reject: format, type:int, the static box of the constant 8, staticuint64s
e2e_data_include e2eEpFmt
e2e_data_include e2eIntType
e2e_data_include e2eEight
e2e_data_include e2eStaticuint64s

end E2e.Data
