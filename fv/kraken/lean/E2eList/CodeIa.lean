import Kraken.X64.Parser
import Fk.Include

/-!
# Code of the LV T3 function (Go 1.26.10 ELF `c6403c02…911e`)

`IaUnmarshal` includes the `.S` file of `fv/kraken/prysm/go1.26.10/e2e/lv/link-t3/norm`
(`link/conv.py --norm` after the LV-1 fix `93b3f2a`; `gen/e2e/lvlink.py filter/data --t3`;
`link/check.py` (a)–(f) PASS in `prysm/go1.26.10/e2e/lv/link-t3/RESULT`, bundle `393eade6…`).
The directory is a Lake `input_dir` of the `E2eList` library (`lakefile.toml`).
-/

namespace E2eList.Code

/-- `(*v1alpha1.IndexedAttestation).UnmarshalSSZ` (protoc type, `phase0.ssz.go:2819`). -/
def IaUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/lv/link-t3/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ.S"

end E2eList.Code
