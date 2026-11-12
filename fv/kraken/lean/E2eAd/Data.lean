import Kraken.X64.WP
import E2eAd.Include

/-!
# ELF data of the AttestationData set (Go 1.26.10)

Elaborated from `fv/kraken/prysm/go1.26.10/e2e/ad/link/data/` by `ad_data_include`; written by
`gen/e2e/adlink.py data` from the operands of the converted code; `link/check.py` (f) compares
them with the ELF. The uint8 type word, `ssz.ErrSize`, `ssz.ErrBytesLength` and the errorString
type are the Checkpoint set's items (`Prysm.ElfData.CheckpointAndEpoch`): `adlink.py` asserts that the AttestationData
code uses the same operands.
-/

namespace E2eAd.Data

-- the Checkpoint abi.Type word passed to runtime.newobject (decoder Source/Target, encoder nil fields)
ad_data_include adCpType
-- the four field wraps "Slot: %w", "CommitteeIndex: %w", "Source: %w", "Target: %w"
ad_data_include adFmtSlot
ad_data_include adFmtCi
ad_data_include adFmtSource
ad_data_include adFmtTarget

end E2eAd.Data
