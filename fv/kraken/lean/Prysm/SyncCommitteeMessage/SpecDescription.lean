import EthLib.Serialization.Ssz

/-!
# Independent hand `Desc` of `v1alpha1.SyncCommitteeMessage`

This description is written by hand from consensus-specs altair (`specs/altair/validator.md`).
It does not use the checker description `Prysm/SyncCommitteeMessage/SpecChecker.lean`.

    class SyncCommitteeMessage(Container):
        slot: Slot                          # uint64
        beacon_block_root: Root             # Bytes32
        validator_index: ValidatorIndex     # uint64
        signature: BLSSignature             # Bytes96
-/

namespace Prysm.SyncCommitteeMessage
open EthLib.Serialization.Ssz

/-- consensus-specs altair `SyncCommitteeMessage`. -/
def desc : Desc := .container ["slot", "beacon_block_root", "validator_index", "signature"]
  [.uint 8, .byteVector 32, .uint 8, .byteVector 96]

end Prysm.SyncCommitteeMessage
