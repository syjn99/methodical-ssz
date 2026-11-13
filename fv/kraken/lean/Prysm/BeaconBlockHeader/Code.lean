import Kraken.X64.Parser
import Machine.Include

/-!
# Code of the hold-out function set (Go 1.26.10 ELF `c6403c02…911e`)

Each constant includes a `.S` file of `fv/kraken/prysm/go1.26.10/e2e/bh/link/norm`
(`link/conv.py --norm` of the same ELF as `Prysm.Checkpoint.Code` and `Prysm.AttestationData.Code`; `link/check.py` (a)–(f) PASS in
`../RESULT`, bundle `140eb7bd…`). The Slot callee is `Prysm.AttestationData.Code.slotUnmarshalSSZ`.
Hand-written include file (not generator output).
Limit: the directory `bh/link/norm` is not a Lake `input_dir` of the `E2eScal` library (a lakefile change
needs approval), so Lake does not rebuild these modules when a `.S` file changes. The `.S` files are
bound by the link bundle hash; a cold build is the check after any change.
-/

namespace Prysm.BeaconBlockHeader

/-- `(*primitives.ValidatorIndex).UnmarshalSSZ` (hand-written, `consensus-types/primitives/validator.go`). -/
def _root_.Prysm.ValidatorIndex.Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/e2e/bh/link/norm/github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ.S"
/-- `(*v1alpha1.BeaconBlockHeader).UnmarshalSSZ` (protoc type, `phase0.ssz.go`). -/
def Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/e2e/bh/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ.S"
/-- `(*v1alpha1.BeaconBlockHeader).MarshalSSZTo` (`phase0.ssz.go`; Slot/ValidatorIndex `MarshalSSZTo` inlined). -/
def Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/bh/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo.S"

abbrev _root_.Prysm.ValidatorIndex.Code.unmarshalLabel : String := "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ"

end Prysm.BeaconBlockHeader
