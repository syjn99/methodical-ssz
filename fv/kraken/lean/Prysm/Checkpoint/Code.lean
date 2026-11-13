import Kraken.X64.Parser
import Machine.Include
import Prysm.Epoch.Code

/-!
# Code of the `Checkpoint` functions (Go 1.26.10 ELF `c6403c02…911e`)

Each constant includes a `.S` file of `fv/kraken/prysm/go1.26.10/link-set/norm`
(`link/conv.py --norm` of the Go 1.26.10 ELF; `link/check.py` (a)–(f) PASS in `prysm/go1.26.10/link-set/RESULT`). The files are Lake inputs of the `Prysm` library (`lakefile.toml`).
Nothing of the code of the Go 1.26.3 test target is used.
After the split of this module, the declarations of the other types are in `Prysm/Epoch/Code.lean`.
-/

namespace Prysm.Checkpoint.Code

/-- `(*v1alpha1.Checkpoint).UnmarshalSSZ` (protoc type, `phase0.ssz.go:1976`). -/
def unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ.S"
/-- `(*v1alpha1.Checkpoint).MarshalSSZTo` (`phase0.ssz.go:1959`; `Epoch.MarshalSSZTo` inlined). -/
def marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo.S"
/-- `(*v1alpha1.Checkpoint).SizeSSZ`. -/
def sizeSSZ : Program := include_x64_rt "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.SizeSSZ.S"

abbrev unmarshalSSZLabel : String := "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ"
abbrev marshalSSZToLabel : String := "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo"

end Prysm.Checkpoint.Code
