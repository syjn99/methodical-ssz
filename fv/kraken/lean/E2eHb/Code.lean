import Kraken.X64.Parser
import Fk.Include

/-!
# Code of the HB function (Go 1.26.10 ELF `c6403c02…911e`)

`HbUnmarshal` includes the `.S` file of `fv/kraken/prysm/go1.26.10/e2e/lv/link-hb/norm`
(`gen/e2e/hblink.py filter`, `link/conv.py --norm`, `hblink.py data`; `link/check.py` (a)–(f) PASS in
`prysm/go1.26.10/e2e/lv/link-hb/RESULT`). The directory is a Lake `input_dir` of the `E2eHb` library.
-/

namespace E2eHb.Code

/-- `(*v1alpha1.HistoricalBatch).UnmarshalSSZ` (native struct, `phase0.ssz.go:2693`). -/
def HbUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/lv/link-hb/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ.S"

end E2eHb.Code
