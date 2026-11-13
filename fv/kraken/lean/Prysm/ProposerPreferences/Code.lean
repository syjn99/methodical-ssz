import Kraken.X64.Parser
import Machine.Include

/-!
# Code of the decoder and the encoder of `v1alpha1.ProposerPreferences` (Go 1.26.10 ELF `c6403c02…911e`)

The constants include `.S` files of `fv/kraken/prysm/go1.26.10/link-set/norm`.
`link/check.py` (a)–(f) PASS in `prysm/go1.26.10/link-set/RESULT`. `Prysm/BuilderDepositRequest/Code.lean` imports this module.
-/

namespace Prysm.ProposerPreferences

/-- `(*v1alpha1.ProposerPreferences).UnmarshalSSZ`. -/
def Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ.S"
/-- `(*v1alpha1.ProposerPreferences).MarshalSSZTo`. -/
def Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo.S"

end Prysm.ProposerPreferences
