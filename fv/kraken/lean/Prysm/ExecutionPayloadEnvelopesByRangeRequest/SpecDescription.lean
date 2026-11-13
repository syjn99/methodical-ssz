import Prysm.Checkpoint.Spec

/-!
# Independent hand `Desc` of the eight types with a generated theorem: the `ExecutionPayloadEnvelopesByRangeRequest` part

The declarations of the other types of this group are in `Prysm/DepositRequest/SpecDescription.lean`.
-/

namespace Prysm.ExecutionPayloadEnvelopesByRangeRequest
open EthLib.Serialization.Ssz

/-- Prysm `v1alpha1.ExecutionPayloadEnvelopesByRangeRequest`. -/
def desc : Desc := .container ["start_slot", "count"]
  [.uint 8, .uint 8]

end Prysm.ExecutionPayloadEnvelopesByRangeRequest
