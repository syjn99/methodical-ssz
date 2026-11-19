module

public import Prysm.AttestationData.SpecDescription

@[expose] public section

/-!
# Independent hand `Desc` of `v1alpha1.SingleAttestation`

This description is written by hand from consensus-specs electra (`ethereum/consensus-specs` release `v1.7.0-beta.4`, `specs/electra/beacon-chain.md`).
It does not use the checker description `Prysm/SingleAttestation/SpecChecker.lean`.

    class SingleAttestation(Container):
        committee_index: CommitteeIndex   # uint64
        attester_index: ValidatorIndex    # uint64
        data: AttestationData
        signature: BLSSignature           # Bytes96

`data` uses the hand `Desc` `Prysm.AttestationData.desc`.
-/

namespace Prysm.SingleAttestation
open EthLib.Serialization.Ssz

/-- consensus-specs electra `SingleAttestation`. -/
def desc : Desc := .container ["committee_index", "attester_index", "data", "signature"]
  [.uint 8, .uint 8, Prysm.AttestationData.desc, .byteVector 96]

end Prysm.SingleAttestation
