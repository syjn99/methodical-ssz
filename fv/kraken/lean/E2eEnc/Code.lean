import Kraken.X64.Parser
import Fk.Include

/-!
# Code of the `DataColumnsByRootIdentifier` encoder (Go 1.26.10 ELF `c6403c02…911e`)

`DcMarshal` includes the `.S` file of `fv/kraken/prysm/go1.26.10/e2e/lv/link-enc/norm`
(`link/conv.py --norm`; `gen/e2e/enclink.py filter/data`;
`link/check.py` (a)–(f) PASS in `prysm/go1.26.10/e2e/lv/link-enc/RESULT`, bundle `f7cdf5e5…`).
The directory is a Lake `input_dir` of the `E2eEnc` library (`lakefile.toml`).
-/

namespace E2eEnc.Code

/-- `(*v1alpha1.DataColumnsByRootIdentifier).MarshalSSZTo` (protoc type, `fulu.ssz.go:1754`). -/
def DcMarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/lv/link-enc/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.MarshalSSZTo.S"

end E2eEnc.Code
