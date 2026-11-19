module

public import EthLib.Serialization.Ssz

@[expose] public section

/-!
# Independent hand `Desc` of `v1alpha1.Deposit_Data`

This description is written by hand from consensus-specs phase0 (`specs/phase0/beacon-chain.md`).
It does not use the checker description `Prysm/Deposit_Data/SpecChecker.lean`.

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
