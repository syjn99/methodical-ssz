import Kraken.X64.Parser
import Machine.Include

/-!
# Code of the HistoricalBatch decoder (Go 1.26.10 ELF `c6403c02…911e`)

`unmarshalSSZ` includes the `.S` file of `fv/kraken/prysm/go1.26.10/link-set/norm`
(`gen/checks/historical_batch_link.py filter`, `link/conv.py --norm`, `historical_batch_link.py data`; `link/check.py` (a)–(f) PASS in
`prysm/go1.26.10/link-set/RESULT`). The directory is a Lake `input_dir` of the `Prysm` library.
-/

namespace Prysm.HistoricalBatch.Code

/-- `(*v1alpha1.HistoricalBatch).UnmarshalSSZ` (native struct, `phase0.ssz.go:2693`). -/
def unmarshalSSZ : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ.S"

end Prysm.HistoricalBatch.Code
