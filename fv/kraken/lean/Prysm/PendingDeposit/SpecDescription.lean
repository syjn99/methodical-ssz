module

public import EthLib.Serialization.Ssz

@[expose] public section

/-!
# Independent hand `Desc` of `v1alpha1.PendingDeposit`

This description is written by hand from consensus-specs electra (`specs/electra/beacon-chain.md`).
It does not use the checker description `Prysm/PendingDeposit/SpecChecker.lean`.

    class PendingDeposit(Container):
        pubkey: BLSPubkey                   # Bytes48
        withdrawal_credentials: Bytes32
        amount: Gwei                        # uint64
        signature: BLSSignature             # Bytes96
        slot: Slot                          # uint64
-/

namespace Prysm.PendingDeposit
open EthLib.Serialization.Ssz

/-- consensus-specs electra `PendingDeposit`. -/
def desc : Desc := .container ["pubkey", "withdrawal_credentials", "amount", "signature", "slot"]
  [.byteVector 48, .byteVector 32, .uint 8, .byteVector 96, .uint 8]

end Prysm.PendingDeposit
