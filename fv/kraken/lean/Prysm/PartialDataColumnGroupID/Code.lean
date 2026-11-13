import Kraken.X64.Parser
import Machine.Include

/-!
# Code of the decoder and the encoder of `v1alpha1.PartialDataColumnGroupID` (Go 1.26.10 ELF `c6403c02…911e`)

The constants include `.S` files of `fv/kraken/prysm/go1.26.10/link-set/norm`.
The link check, the bundle hash and the rebuild limit are in `Prysm/BuilderDepositRequest/Code.lean`, which imports this module.
-/

namespace Prysm.PartialDataColumnGroupID

/-- `(*v1alpha1.PartialDataColumnGroupID).UnmarshalSSZ`. -/
def Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnGroupID.UnmarshalSSZ.S"
/-- `(*v1alpha1.PartialDataColumnGroupID).MarshalSSZTo`. -/
def Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnGroupID.MarshalSSZTo.S"

end Prysm.PartialDataColumnGroupID
