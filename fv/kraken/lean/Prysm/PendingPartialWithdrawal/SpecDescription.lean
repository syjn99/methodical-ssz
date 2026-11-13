import Prysm.Checkpoint.Spec

/-!
# Independent hand `Desc` of `v1alpha1.PendingPartialWithdrawal` (hold-out, class B)

Hand-written from consensus-specs electra (`specs/electra/beacon-chain.md`),
BEFORE the Desc checker's Desc of `(v1alpha1, PendingPartialWithdrawal)` was generated or printed (so that the hand Desc is independent of the checker output in time, not only in content).
This file is committed before `Prysm/PendingPartialWithdrawal/SpecChecker.lean` exists.

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
