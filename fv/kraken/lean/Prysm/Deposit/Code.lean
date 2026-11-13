import Kraken.X64.Parser
import Machine.Include
import Kraken.X64.WP
import Machine.Labels

/-!
# Code and data of the Deposit decoder (Go 1.26.10 ELF `c6403c02…911e`)

`unmarshalSSZ` includes the `.S` file of `fv/kraken/prysm/go1.26.10/link-set/norm` (`gen/checks/deposit_link.py`,
`link/conv.py --norm`, `link/check.py` (a)–(f) PASS in `prysm/go1.26.10/link-set/RESULT`). `ElfData.PrysmTarget.typeDeposit_Data_addr` is the address of
the data item `prysm/go1.26.10/link-set/data/typeDeposit_Data.data` (checked against the ELF by `check.py` (f)).
-/

namespace Prysm.Deposit.Code

/-- `(*v1alpha1.Deposit).UnmarshalSSZ` (protoc type, `phase0.ssz.go:2059`). -/
def unmarshalSSZ : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ.S"


end Prysm.Deposit.Code
