import E2e.Spec

/-!
# Independent hand `Desc` of `v1alpha1.PendingDeposit` (H6 hold-out, full-proof type)

Hand-written by the H6 evaluation session from consensus-specs electra (`specs/electra/beacon-chain.md`),
BEFORE the Desc checker's Desc of `(v1alpha1, PendingDeposit)` was generated or printed (FINDINGS NF-10).
This file is committed before `PdSpecChecker.lean` exists.

    class PendingDeposit(Container):
        pubkey: BLSPubkey                   # Bytes48
        withdrawal_credentials: Bytes32
        amount: Gwei                        # uint64
        signature: BLSSignature             # Bytes96
        slot: Slot                          # uint64
-/

namespace E2e
open EthLib.Serialization.Ssz

/-- consensus-specs electra `PendingDeposit`. -/
def prysmPdDesc : Desc := .container ["pubkey", "withdrawal_credentials", "amount", "signature", "slot"]
  [.byteVector 48, .byteVector 32, .uint 8, .byteVector 96, .uint 8]

end E2e
