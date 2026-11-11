import E2e.Spec

/-!
# Independent hand `Desc` of `v1alpha1.DepositMessage` (H3 hold-out)

Hand-written by the H3 evaluation session from consensus-specs phase0 (`specs/phase0/beacon-chain.md`),
BEFORE the Desc checker's Desc of `(v1alpha1, DepositMessage)` was generated or printed (FINDINGS NF-10).
This file is committed before `DmSpecChecker.lean` exists.

    class DepositMessage(Container):
        pubkey: BLSPubkey                   # Bytes48
        withdrawal_credentials: Bytes32
        amount: Gwei                        # uint64
-/

namespace E2e
open EthLib.Serialization.Ssz

/-- consensus-specs phase0 `DepositMessage`. -/
def prysmDmDesc : Desc := .container ["pubkey", "withdrawal_credentials", "amount"]
  [.byteVector 48, .byteVector 32, .uint 8]

end E2e
