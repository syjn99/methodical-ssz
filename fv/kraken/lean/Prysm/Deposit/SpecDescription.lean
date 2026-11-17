import Prysm.Deposit_Data.SpecDescription

/-!
# Independent hand `Desc` of `v1alpha1.Deposit`

This description is written by hand from consensus-specs phase0 (`specs/phase0/beacon-chain.md`).
It does not use the Desc of `(v1alpha1, Deposit)` that the producer writes.

    DEPOSIT_CONTRACT_TREE_DEPTH = 32
    class Deposit(Container):
        proof: Vector[Bytes32, DEPOSIT_CONTRACT_TREE_DEPTH + 1]   # 33
        data: DepositData

`DepositData` is the hand `Desc` `Prysm.Deposit_Data.desc`.
-/

open EthLib.Serialization.Ssz

namespace Prysm.Deposit

/-- consensus-specs phase0 `Deposit`. -/
def desc : Desc := .container ["proof", "data"] [.vector (.byteVector 32) 33, Prysm.Deposit_Data.desc]

end Prysm.Deposit
