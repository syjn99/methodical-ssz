import Kraken.X64.Parser
import Machine.Include

/-!
# Code of the `Eth1Data` functions (Go 1.26.10 ELF `c6403c02…911e`)

Each constant includes a `.S` file of `fv/kraken/prysm/go1.26.10/link-set/norm`
(`link/convert_objdump.py --norm` of the same ELF as `Prysm.Checkpoint.Code`, `Prysm.AttestationData.Code` and `Prysm.BeaconBlockHeader.Code`; `link/check.py` (a)–(f) PASS in `prysm/go1.26.10/link-set/RESULT`).
Hand-written include file (not generator output).
The directory `prysm/go1.26.10/link-set/norm` is a Lake `input_dir` of the `Prysm` library,
so Lake rebuilds these modules when a `.S` file changes.
-/

namespace Prysm.Eth1Data

/-- `(*v1alpha1.Eth1Data).UnmarshalSSZ` (protoc type, `phase0.ssz.go`). -/
def Code.unmarshalSSZ : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ.S"
/-- `(*v1alpha1.Eth1Data).MarshalSSZTo` (`phase0.ssz.go`). -/
def Code.marshalSSZTo : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.MarshalSSZTo.S"

end Prysm.Eth1Data
