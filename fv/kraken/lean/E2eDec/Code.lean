import Kraken.X64.Parser
import Fk.Include

/-!
# Code of the ENC decoder (Go 1.26.10 ELF `c6403c02…911e`)

`DcUnmarshal` includes the `.S` file of `fv/kraken/prysm/go1.26.10/e2e/lv/link-dec/norm`
(`link/conv.py --norm`; `gen/e2e/encdeclink.py filter/data`;
`link/check.py` (a)–(f) PASS in `prysm/go1.26.10/e2e/lv/link-dec/RESULT`, bundle `7b8d6500…`).
The directory is a Lake `input_dir` of the `E2eDec` library (`lakefile.toml`).
-/

namespace E2eDec.Code

/-- `(*v1alpha1.DataColumnsByRootIdentifier).UnmarshalSSZ` (protoc type, `fulu.ssz.go:1778`). -/
def DcUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/lv/link-dec/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ.S"

end E2eDec.Code
