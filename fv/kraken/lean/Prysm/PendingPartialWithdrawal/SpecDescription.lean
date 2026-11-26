module

public import EthLib.Serialization.Ssz

@[expose] public section

/-!
# Independent hand `Desc` of `v1alpha1.PendingPartialWithdrawal`

This description is written by hand from consensus-specs electra (`specs/electra/beacon-chain.md`).
It does not use the checker description `Prysm/PendingPartialWithdrawal/SpecChecker.lean`.

    class PendingPartialWithdrawal(Container):
        validator_index: ValidatorIndex     # uint64
        amount: Gwei                        # uint64
        withdrawable_epoch: Epoch           # uint64
-/

namespace Prysm.PendingPartialWithdrawal
open EthLib.Serialization.Ssz

/-- consensus-specs electra `PendingPartialWithdrawal`. -/
def desc : Desc := .container ["validator_index", "amount", "withdrawable_epoch"]
  [.uint 8, .uint 8, .uint 8]

end Prysm.PendingPartialWithdrawal
