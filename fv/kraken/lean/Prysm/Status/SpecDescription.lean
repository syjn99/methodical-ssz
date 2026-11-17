import EthLib.Serialization.Ssz

/-!
# Independent hand `Desc` of `v1alpha1.Status`

This description is written by hand from consensus-specs phase0 (`ethereum/consensus-specs` release `v1.7.0-beta.4`, `specs/phase0/p2p-interface.md`).
It does not use the checker description `Prysm/Status/SpecChecker.lean`.
The request and response content of the Req/Resp message `Status` is this container:

    (
      fork_digest: ForkDigest             # Bytes4
      finalized_root: Root                # Bytes32
      finalized_epoch: Epoch              # uint64
      head_root: Root                     # Bytes32
      head_slot: Slot                     # uint64
    )

The phase0 custom type `ForkDigest` is `Bytes4`, `Root` is `Bytes32`, and `Epoch` and `Slot` are `uint64`.
-/

namespace Prysm.Status
open EthLib.Serialization.Ssz

/-- consensus-specs phase0 Req/Resp `Status`. -/
def desc : Desc := .container ["fork_digest", "finalized_root", "finalized_epoch", "head_root", "head_slot"]
  [.byteVector 4, .byteVector 32, .uint 8, .byteVector 32, .uint 8]

end Prysm.Status
