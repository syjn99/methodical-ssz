import Kraken.X64.Parser
import Machine.Include

/-!
# Code of the `DataColumnsByRootIdentifier` decoder (Go 1.26.10 ELF `c6403c02…911e`)

`unmarshalSSZ` includes the `.S` file of `fv/kraken/prysm/go1.26.10/link-set/norm`
(`link/conv.py --norm`; `gen/e2e/encdeclink.py filter/data`;
`link/check.py` (a)–(f) PASS in `prysm/go1.26.10/link-set/RESULT`).
The directory is a Lake `input_dir` of the `Prysm` library (`lakefile.toml`).
-/

namespace Prysm.DataColumnsByRootIdentifier.Code

/-- `(*v1alpha1.DataColumnsByRootIdentifier).UnmarshalSSZ` (protoc type, `fulu.ssz.go:1778`). -/
def unmarshalSSZ : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ.S"

end Prysm.DataColumnsByRootIdentifier.Code
