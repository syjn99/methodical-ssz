import Kraken.X64.Parser
import Fk.Include

/-!
# Code of the hold-out function set (Go 1.26.10 ELF `c6403c02…911e`)

Each constant includes a `.S` file of `fv/kraken/prysm/go1.26.10/e2e/bh/link/norm`
(`link/conv.py --norm` of the same ELF as `E2e.Code` and `E2eAd.Code`; `link/check.py` (a)–(f) PASS in
`../RESULT`, bundle `140eb7bd…`). The Slot callee is `E2eAd.Code.SlUnmarshal`.
Hand-written include file (not generator output).
Limit: the directory `bh/link/norm` is not a Lake `input_dir` of the `E2eScal` library (a lakefile change
needs approval), so Lake does not rebuild these modules when a `.S` file changes. The `.S` files are
bound by the link bundle hash; a cold build is the check after any change.
-/

namespace E2eScal.BhCode

/-- `(*primitives.ValidatorIndex).UnmarshalSSZ` (hand-written, `consensus-types/primitives/validator.go`). -/
def ViUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/bh/link/norm/github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ.S"
/-- `(*v1alpha1.BeaconBlockHeader).UnmarshalSSZ` (protoc type, `phase0.ssz.go`). -/
def BhUnmarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/bh/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ.S"
/-- `(*v1alpha1.BeaconBlockHeader).MarshalSSZTo` (`phase0.ssz.go`; Slot/ValidatorIndex `MarshalSSZTo` inlined). -/
def BhMarshal : Program := include_x64_rt "../prysm/go1.26.10/e2e/bh/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo.S"

abbrev viLabel : String := "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ"

end E2eScal.BhCode
