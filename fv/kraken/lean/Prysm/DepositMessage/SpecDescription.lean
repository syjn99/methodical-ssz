import Prysm.Checkpoint.Spec

/-!
# Independent hand `Desc` of `v1alpha1.DepositMessage`

This description is written by hand from consensus-specs phase0 (`specs/phase0/beacon-chain.md`).
It does not use the checker description `Prysm/DepositMessage/SpecChecker.lean`.

    class DepositMessage(Container):
        pubkey: BLSPubkey                   # Bytes48
        withdrawal_credentials: Bytes32
        amount: Gwei                        # uint64
-/

namespace Prysm.DepositMessage
open EthLib.Serialization.Ssz

/-- consensus-specs phase0 `DepositMessage`. -/
def desc : Desc := .container ["pubkey", "withdrawal_credentials", "amount"]
  [.byteVector 48, .byteVector 32, .uint 8]

end Prysm.DepositMessage
