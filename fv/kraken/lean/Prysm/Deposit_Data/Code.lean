import Kraken.X64.Parser
import Machine.Include
import Prysm.PendingPartialWithdrawal.Code

/-!
# Code of the `Deposit_Data` functions (Go 1.26.10 ELF `c6403c02…911e`)

Each constant includes a `.S` file of `fv/kraken/prysm/go1.26.10/link-set/norm`
(`link/conv.py --norm` of the same ELF as `Prysm.Checkpoint.Code`, `Prysm.AttestationData.Code`, `Prysm.BeaconBlockHeader.Code`, `Prysm.Eth1Data.Code` and
`Prysm.BlobIdentifier.Code`; `link/check.py` (a)–(f) PASS in `prysm/go1.26.10/link-set/RESULT`).
Hand-written include file (not generator output; the text of `Prysm/BlobIdentifier/Code.lean`).
The directory `prysm/go1.26.10/link-set/norm` is a Lake `input_dir` of the `Prysm` library,
so Lake rebuilds these modules when a `.S` file changes.
After the split of this module, the declarations of the other types are in `Prysm/PendingPartialWithdrawal/Code.lean`.
-/

namespace Prysm.Deposit_Data

/-- `(*v1alpha1.Deposit_Data).UnmarshalSSZ`. -/
def Code.unmarshalSSZ : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ.S"
end Prysm.Deposit_Data
