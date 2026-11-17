import Prysm.AttestationData.SpecDescription

/-!
# Independent hand `Desc` of `v1alpha1.IndexedAttestation`

This description is written by hand from consensus-specs phase0 (`ethereum/consensus-specs` release `v1.7.0-beta.4`, `specs/phase0/beacon-chain.md`).
It does not use the checker description `Prysm/IndexedAttestation/SpecChecker.lean`.

    class IndexedAttestation(Container):
        attesting_indices: List[ValidatorIndex, MAX_VALIDATORS_PER_COMMITTEE]   # uint64, 2048
        data: AttestationData
        signature: BLSSignature                                                # Bytes96

`data` uses the hand `Desc` `Prysm.AttestationData.desc`.
-/

namespace Prysm.IndexedAttestation
open EthLib.Serialization.Ssz

/-- consensus-specs phase0 `IndexedAttestation` (mainnet). -/
def desc : Desc := .container ["attesting_indices", "data", "signature"]
  [.list (.uint 8) 2048, Prysm.AttestationData.desc, .byteVector 96]

end Prysm.IndexedAttestation
