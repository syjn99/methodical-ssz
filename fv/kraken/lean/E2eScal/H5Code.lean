import Kraken.X64.Parser
import Machine.Include

/-!
# Code of the hold-out function set (Go 1.26.10 ELF `c6403c02…911e`)

Each constant includes a `.S` file of `fv/kraken/prysm/go1.26.10/e2e/h5/link/norm`
(`link/conv.py --norm` of the same ELF as `Prysm.Checkpoint.Code`, `Prysm.AttestationData.Code`, `E2eScal.BhCode`, `E2eScal.E1Code`,
`E2eScal.H3Code` and `E2eScal.H4Code`; `link/check.py` (a)–(f) PASS in `../RESULT`, bundle `d532fc57…`).
Hand-written include file (not generator output; the text of `H4Code.lean`).
Limit: the directory `h5/link/norm` is not a Lake `input_dir` of the `E2eScal` library (a lakefile change
needs approval), so Lake does not rebuild these modules when a `.S` file changes. The `.S` files are
bound by the link bundle hash; a cold build is the check after any change.
-/

namespace E2eScal.H5Code

/-- `(*v1alpha1.SyncCommitteeMessage).UnmarshalSSZ`. -/
def SmUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/h5/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ.S"
/-- `(*v1alpha1.PendingConsolidation).UnmarshalSSZ`. -/
def PcUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/h5/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.UnmarshalSSZ.S"

end E2eScal.H5Code
