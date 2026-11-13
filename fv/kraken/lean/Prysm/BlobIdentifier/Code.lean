import Kraken.X64.Parser
import Machine.Include
import Prysm.DepositMessage.Code

/-!
# Code of the hold-out function set (Go 1.26.10 ELF `c6403c02…911e`)

Each constant includes a `.S` file of `fv/kraken/prysm/go1.26.10/e2e/h3/link/norm`
(`link/conv.py --norm` of the same ELF as `Prysm.Checkpoint.Code`, `Prysm.AttestationData.Code`, `Prysm.BeaconBlockHeader.Code` and `Prysm.Eth1Data.Code`;
`link/check.py` (a)–(f) PASS in `../RESULT`, bundle `320a9df6…`).
Hand-written include file (not generator output; the text of `Prysm/Eth1Data/Code.lean`).
Limit: the directory `h3/link/norm` is not a Lake `input_dir` of the `Prysm` library (a lakefile change
needs approval), so Lake does not rebuild these modules when a `.S` file changes. The `.S` files are
bound by the link bundle hash; a cold build is the check after any change.
After the split of this module, the declarations of the other types are in `Prysm/DepositMessage/Code.lean`.
-/

namespace Prysm.BlobIdentifier

/-- `(*v1alpha1.BlobIdentifier).UnmarshalSSZ`. -/
def Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/e2e/h3/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.UnmarshalSSZ.S"
end Prysm.BlobIdentifier
