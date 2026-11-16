import Kraken.X64.Parser
import Machine.Include

/-!
# Code of the decoder and the encoder of `v1.WithdrawalRequest` (the Go 1.26.10 ELF of `prysm/go1.26.10/build-ids.txt`)

The constants include `.S` files of `fv/kraken/prysm/go1.26.10/link-set/norm`.
`link/check.py` (a)–(f) PASS in `prysm/go1.26.10/link-set/RESULT`. `Prysm/BuilderDepositRequest/Code.lean` imports this module.
-/

namespace Prysm.WithdrawalRequest

/-- `(*v1.WithdrawalRequest).UnmarshalSSZ`. -/
def Code.unmarshalSSZ : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.UnmarshalSSZ.S"
/-- `(*v1.WithdrawalRequest).MarshalSSZTo`. -/
def Code.marshalSSZTo : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.MarshalSSZTo.S"

end Prysm.WithdrawalRequest
