import Prysm.Checkpoint.Spec
import Prysm.SyncCommittee.SpecDescription

/-!
# Independent hand `Desc` of `v1alpha1.SyncAggregate` and `v1alpha1.SyncCommittee`

This description is written by hand from the consensus-specs altair container definitions (`specs/altair/beacon-chain.md`).
It does not use the Desc files of the producer.
These files are `prysm/go1.26.10/evidence/prysm_v1alpha1.SyncAggregate.desc.json` and `prysm/go1.26.10/evidence/prysm_v1alpha1.SyncCommittee.desc.json`.

    SYNC_COMMITTEE_SIZE = 512                       # mainnet preset
    class SyncAggregate(Container):
        sync_committee_bits: Bitvector[SYNC_COMMITTEE_SIZE]
        sync_committee_signature: BLSSignature      # Bytes96
    class SyncCommittee(Container):
        pubkeys: Vector[BLSPubkey, SYNC_COMMITTEE_SIZE]   # BLSPubkey = Bytes48
        aggregate_pubkey: BLSPubkey
-/

namespace Prysm.SyncAggregate
open EthLib.Serialization.Ssz

/-- consensus-specs altair `SyncAggregate` (mainnet). -/
def desc : Desc := .container ["sync_committee_bits", "sync_committee_signature"]
  [.bitVector 512, .byteVector 96]

end Prysm.SyncAggregate
