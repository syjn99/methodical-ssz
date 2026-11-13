import Kraken.X64.Parser
import Machine.Include

/-!
# Code of the decoder and the encoder of `v1.DepositRequest` (Go 1.26.10 ELF `c6403c02…911e`)

The constants include `.S` files of `fv/kraken/prysm/go1.26.10/link-set/norm`.
The link check, the bundle hash and the rebuild limit are in `Prysm/BuilderDepositRequest/Code.lean`, which imports this module.
-/

namespace Prysm.DepositRequest

/-- `(*v1.DepositRequest).UnmarshalSSZ`. -/
def Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.UnmarshalSSZ.S"
/-- `(*v1.DepositRequest).MarshalSSZTo`. -/
def Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo.S"

end Prysm.DepositRequest
