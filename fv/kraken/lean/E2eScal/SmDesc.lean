import E2e.Spec

/-!
# Independent hand `Desc` of `v1alpha1.SyncCommitteeMessage` (H5 hold-out, class C)

Hand-written by the H5 evaluation session from consensus-specs altair (`specs/altair/validator.md`),
BEFORE the Desc checker's Desc of `(v1alpha1, SyncCommitteeMessage)` was generated or printed (FINDINGS NF-10).
This file is committed before `SmSpecChecker.lean` exists.

    class SyncCommitteeMessage(Container):
        slot: Slot                          # uint64
        beacon_block_root: Root             # Bytes32
        validator_index: ValidatorIndex     # uint64
        signature: BLSSignature             # Bytes96
-/

namespace E2e
open EthLib.Serialization.Ssz

/-- consensus-specs altair `SyncCommitteeMessage`. -/
def prysmSmDesc : Desc := .container ["slot", "beacon_block_root", "validator_index", "signature"]
  [.uint 8, .byteVector 32, .uint 8, .byteVector 96]

end E2e
