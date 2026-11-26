module

public import EthLib.Serialization.Ssz

@[expose] public section

/-!
# Independent hand `Desc` of `v1alpha1.SyncCommittee`

This description is written by hand from the consensus-specs altair container definitions (`specs/altair/beacon-chain.md`).
It does not use the Desc file of the producer, `prysm/go1.26.10/evidence/prysm_v1alpha1.SyncCommittee.desc.json`.

    SYNC_COMMITTEE_SIZE = 512                       # mainnet preset
    class SyncCommittee(Container):
        pubkeys: Vector[BLSPubkey, SYNC_COMMITTEE_SIZE]   # BLSPubkey = Bytes48
        aggregate_pubkey: BLSPubkey
-/

namespace Prysm.SyncCommittee
open EthLib.Serialization.Ssz

/-- consensus-specs altair `SyncCommittee` (mainnet). -/
def desc : Desc := .container ["pubkeys", "aggregate_pubkey"]
  [.vector (.byteVector 48) 512, .byteVector 48]

end Prysm.SyncCommittee
