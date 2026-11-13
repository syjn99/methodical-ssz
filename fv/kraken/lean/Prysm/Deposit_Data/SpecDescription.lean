import Prysm.Checkpoint.Spec

/-!
# Independent hand `Desc` of `v1alpha1.Deposit_Data` (hold-out, class A)

Hand-written from consensus-specs phase0 (`specs/phase0/beacon-chain.md`),
BEFORE the Desc checker's Desc of `(v1alpha1, Deposit_Data)` was generated or printed (so that the hand Desc is independent of the checker output in time, not only in content).
This file is committed before `DdSpecChecker.lean` exists.

    class DepositData(Container):
        pubkey: BLSPubkey                   # Bytes48
        withdrawal_credentials: Bytes32
        amount: Gwei                        # uint64
        signature: BLSSignature             # Bytes96
-/

namespace Prysm.Deposit_Data
open EthLib.Serialization.Ssz

/-- consensus-specs phase0 `DepositData`. -/
def desc : Desc := .container ["pubkey", "withdrawal_credentials", "amount", "signature"]
  [.byteVector 48, .byteVector 32, .uint 8, .byteVector 96]

end Prysm.Deposit_Data
