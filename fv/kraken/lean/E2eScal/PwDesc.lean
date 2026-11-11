import E2e.Spec

/-!
# Independent hand `Desc` of `v1alpha1.PendingPartialWithdrawal` (H4 hold-out, class B)

Hand-written by the H4 evaluation session from consensus-specs electra (`specs/electra/beacon-chain.md`),
BEFORE the Desc checker's Desc of `(v1alpha1, PendingPartialWithdrawal)` was generated or printed (FINDINGS NF-10).
This file is committed before `PwSpecChecker.lean` exists.

    class PendingPartialWithdrawal(Container):
        validator_index: ValidatorIndex     # uint64
        amount: Gwei                        # uint64
        withdrawable_epoch: Epoch           # uint64
-/

namespace E2e
open EthLib.Serialization.Ssz

/-- consensus-specs electra `PendingPartialWithdrawal`. -/
def prysmPwDesc : Desc := .container ["validator_index", "amount", "withdrawable_epoch"]
  [.uint 8, .uint 8, .uint 8]

end E2e
