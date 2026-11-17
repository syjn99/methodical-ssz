import EthLib.Serialization.Ssz

/-!
# Independent hand `Desc` of `v1alpha1.StatusV2`

This description is written by hand from consensus-specs Fulu (`ethereum/consensus-specs` release `v1.7.0-beta.4`, `specs/fulu/p2p-interface.md`).
It does not use the checker description `Prysm/StatusV2/SpecChecker.lean`.
The request and response content of the Req/Resp message `Status` v2 is this container:

    (
      fork_digest: ForkDigest
      finalized_root: Root
      finalized_epoch: Epoch
      head_root: Root
      head_slot: Slot
      earliest_available_slot: Slot
    )

The phase0 custom type `ForkDigest` is `Bytes4`, `Root` is `Bytes32`, and `Epoch` and `Slot` are `uint64`.
-/

namespace Prysm.StatusV2
open EthLib.Serialization.Ssz

/-- consensus-specs Fulu Req/Resp `Status` v2. -/
def desc : Desc := .container ["fork_digest", "finalized_root", "finalized_epoch", "head_root", "head_slot",
    "earliest_available_slot"]
  [.byteVector 4, .byteVector 32, .uint 8, .byteVector 32, .uint 8, .uint 8]

end Prysm.StatusV2
