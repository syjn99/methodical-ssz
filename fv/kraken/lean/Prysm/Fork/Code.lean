import Kraken.X64.Parser
import Machine.Include

/-!
# Code of the decoder and the encoder of `v1alpha1.Fork` (the Go 1.26.10 ELF of `prysm/go1.26.10/build-ids.txt`)

The constants include `.S` files of `fv/kraken/prysm/go1.26.10/link-set/norm`.
`link/check.py` (a)–(f) PASS in `prysm/go1.26.10/link-set/RESULT`. `Prysm/BuilderDepositRequest/Code.lean` imports this module.
-/

namespace Prysm.Fork

/-- `(*v1alpha1.Fork).UnmarshalSSZ`. -/
def Code.unmarshalSSZ : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ.S"
/-- `(*v1alpha1.Fork).MarshalSSZTo`. -/
def Code.marshalSSZTo : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.MarshalSSZTo.S"

end Prysm.Fork
