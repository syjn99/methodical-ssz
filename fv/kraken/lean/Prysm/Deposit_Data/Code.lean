import Kraken.X64.Parser
import Machine.Include

/-!
# Code of the hold-out function set (Go 1.26.10 ELF `c6403c02…911e`)

Each constant includes a `.S` file of `fv/kraken/prysm/go1.26.10/e2e/h4/link/norm`
(`link/conv.py --norm` of the same ELF as `Prysm.Checkpoint.Code`, `Prysm.AttestationData.Code`, `Prysm.BeaconBlockHeader.Code`, `Prysm.Eth1Data.Code` and
`Prysm.BlobIdentifier.Code`; `link/check.py` (a)–(f) PASS in `../RESULT`, bundle `e1d4d2e3…`).
Hand-written include file (not generator output; the text of `H3Code.lean`).
Limit: the directory `h4/link/norm` is not a Lake `input_dir` of the `E2eScal` library (a lakefile change
needs approval), so Lake does not rebuild these modules when a `.S` file changes. The `.S` files are
bound by the link bundle hash; a cold build is the check after any change.
-/

namespace Prysm.Deposit_Data

/-- `(*v1alpha1.Deposit_Data).UnmarshalSSZ`. -/
def Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/e2e/h4/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ.S"
/-- `(*v1alpha1.PendingPartialWithdrawal).UnmarshalSSZ`. -/
def _root_.Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/e2e/h4/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ.S"

end Prysm.Deposit_Data
