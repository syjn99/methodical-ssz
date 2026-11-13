import Kraken.X64.Parser
import Machine.Include
import Kraken.X64.WP
import Machine.Labels

/-!
# Code and data of the Deposit decoder (Go 1.26.10 ELF `c6403c02…911e`)

`unmarshalSSZ` includes the `.S` file of `fv/kraken/prysm/go1.26.10/e2e/lv/link-dep/norm` (`gen/e2e/deplink.py`,
`link/conv.py --norm`, `link/check.py` (a)–(f) PASS in `lv/link-dep/RESULT`). `depDataType_addr` is the address of
the data item `lv/link-dep/data/depDataType.data` (checked against the ELF by `check.py` (f)).
-/

namespace Prysm.Deposit.Code

/-- `(*v1alpha1.Deposit).UnmarshalSSZ` (protoc type, `phase0.ssz.go:2059`). -/
def unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/e2e/lv/link-dep/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ.S"

/-- The abi.Type of `v1alpha1.Deposit_Data` (Size_ 0x78 = 120): the `new(Deposit_Data)` type word.
The value is the `at type__ 1421952` line of `lv/link-dep/data/depDataType.data` in the form of the data reader of `Prysm/ElfData/SyncAggregateAndSyncCommitteeReader.lean`
(`lvLabelTerm`). It is written here because the reader's helpers are private to `Prysm/ElfData/SyncAggregateAndSyncCommitteeReader.lean`; the operand
is also the `.S` operand of directive 85 (`link/check.py` (b)), which the accept proof steps through. -/
def depDataType_addr [Host] : BitVec 64 := (label "type__" + 1421952).toBitVec

end Prysm.Deposit.Code
