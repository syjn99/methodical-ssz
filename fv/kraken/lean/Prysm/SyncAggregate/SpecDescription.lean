module

public import EthLib.Serialization.Ssz

@[expose] public section

/-!
# Independent hand `Desc` of `v1alpha1.SyncAggregate`

This description is written by hand from the consensus-specs altair container definitions (`specs/altair/beacon-chain.md`).
It does not use the Desc file of the producer, `prysm/go1.26.10/evidence/prysm_v1alpha1.SyncAggregate.desc.json`.

    SYNC_COMMITTEE_SIZE = 512                       # mainnet preset
    class SyncAggregate(Container):
        sync_committee_bits: Bitvector[SYNC_COMMITTEE_SIZE]
        sync_committee_signature: BLSSignature      # Bytes96
-/

namespace Prysm.SyncAggregate
open EthLib.Serialization.Ssz

/-- consensus-specs altair `SyncAggregate` (mainnet). -/
def desc : Desc := .container ["sync_committee_bits", "sync_committee_signature"]
  [.bitVector 512, .byteVector 96]

end Prysm.SyncAggregate
