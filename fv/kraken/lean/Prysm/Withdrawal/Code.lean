import Kraken.X64.Parser
import Machine.Include

/-!
# Code of the decoder and the encoder of `v1.Withdrawal` (Go 1.26.10 ELF `c6403c02…911e`)

The constants include `.S` files of `fv/kraken/prysm/go1.26.10/e2e/f24/link/norm`.
The link check, the bundle hash and the rebuild limit are in `Prysm/BuilderDepositRequest/Code.lean`, which imports this module.
-/

namespace Prysm.Withdrawal

/-- `(*v1.Withdrawal).UnmarshalSSZ`. -/
def Code.unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ.S"
/-- `(*v1.Withdrawal).MarshalSSZTo`. -/
def Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.MarshalSSZTo.S"

end Prysm.Withdrawal
