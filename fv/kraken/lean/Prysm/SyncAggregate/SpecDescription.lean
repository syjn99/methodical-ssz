import Prysm.Checkpoint.Spec

/-!
# Independent hand `Desc` of `v1alpha1.SyncAggregate` and `v1alpha1.SyncCommittee`

Hand-written from the consensus-specs altair container definitions
(`specs/altair/beacon-chain.md`; the repository has no local copy of that file), BEFORE the Desc producer's
output for these two types was printed. The producer's Desc files (`e2e/lv/desc/*.desc.json`, sha256 equal to
the checker records in `gen/desc/results/main.result.json`) are compared with these terms in a later unit.

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

/-- consensus-specs altair `SyncCommittee` (mainnet). -/
def _root_.Prysm.SyncCommittee.desc : Desc := .container ["pubkeys", "aggregate_pubkey"]
  [.vector (.byteVector 48) 512, .byteVector 48]

end Prysm.SyncAggregate
