import Kraken.X64.Parser
import Machine.Include

/-!
# Code of the decoder and the encoder of `v1alpha1.Builder` (Go 1.26.10 ELF `c6403c02…911e`)

The constants include `.S` files of `fv/kraken/prysm/go1.26.10/link-set/norm`.
The link check, the bundle hash and the rebuild limit are in `Prysm/BuilderDepositRequest/Code.lean`, which imports this module.
-/

namespace Prysm.Builder

/-- `(*v1alpha1.Builder).UnmarshalSSZ`. -/
def Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ.S"
/-- `(*v1alpha1.Builder).MarshalSSZTo`. -/
def Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo.S"

end Prysm.Builder
