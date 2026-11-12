import Kraken.X64.Parser
import Machine.Include

/-!
# Code of the hold-out function set (Go 1.26.10 ELF `c6403c02…911e`)

Each constant includes a `.S` file of `fv/kraken/prysm/go1.26.10/e2e/e1/link/norm`
(`link/conv.py --norm` of the same ELF as `Prysm.Checkpoint.Code`, `E2eAd.Code` and `E2eScal.BhCode`; `link/check.py`
(a)–(f) PASS in `../RESULT`, bundle `d5cc804d…`).
Hand-written include file (not generator output).
Limit: the directory `e1/link/norm` is not a Lake `input_dir` of the `E2eScal` library (a lakefile change
needs approval), so Lake does not rebuild these modules when a `.S` file changes. The `.S` files are
bound by the link bundle hash; a cold build is the check after any change.
-/

namespace E2eScal.E1Code

/-- `(*v1alpha1.Eth1Data).UnmarshalSSZ` (protoc type, `phase0.ssz.go`). -/
def E1Unmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/e1/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ.S"
/-- `(*v1alpha1.Eth1Data).MarshalSSZTo` (`phase0.ssz.go`). -/
def E1Marshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/e1/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.MarshalSSZTo.S"

end E2eScal.E1Code
