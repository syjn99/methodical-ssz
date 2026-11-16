import Kraken.X64.Parser
import Machine.Include

/-!
# Code of the `HistoricalSummary` functions (the Go 1.26.10 ELF of `prysm/go1.26.10/build-ids.txt`)

The declarations of the other types of this group are in `Prysm/PendingDeposit/Code.lean`.
-/

namespace Prysm.HistoricalSummary

/-- `(*v1alpha1.HistoricalSummary).UnmarshalSSZ`. -/
def Code.unmarshalSSZ : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.UnmarshalSSZ.S"

end Prysm.HistoricalSummary
