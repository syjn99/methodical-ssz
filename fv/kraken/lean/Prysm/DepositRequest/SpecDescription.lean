import Prysm.Checkpoint.Spec
import Prysm.BeaconBlocksByRangeRequest.SpecDescription
import Prysm.BlobSidecarsByRangeRequest.SpecDescription
import Prysm.BuilderDepositRequest.SpecDescription
import Prysm.BuilderPreferences.SpecDescription
import Prysm.ExecutionPayloadEnvelopesByRangeRequest.SpecDescription
import Prysm.PartialDataColumnGroupID.SpecDescription
import Prysm.ValidatorIdentity.SpecDescription

/-!
# Independent hand `Desc` of the eight types with a generated theorem

These descriptions are written by hand from the Prysm proto definitions in the Prysm source tree that the Go differential uses.
The files are `proto/engine/v1/electra.proto`, `proto/engine/v1/gloas.proto` and `proto/prysm/v1alpha1/p2p_messages.proto`.
The other files are `p2p_messages_gloas.proto`, `partial_data_columns.proto`, `validator.proto` and `gloas_builder_api.proto`.
They do not use the checker descriptions `Prysm/<Type>/SpecChecker.lean`.
They are not independent of the source of the Desc producer (as `Prysm/ValidatorBalance/SpecDescription.lean`).
Where the proto cites a spec definition, the comment is quoted.
Overlay types (`cast_type` Slot, Epoch, ValidatorIndex, Gwei) are `uint64` in SSZ.

    message DepositRequest { bytes pubkey [48]; bytes withdrawal_credentials [32]; uint64 amount;
                             bytes signature [96]; uint64 index; }                       // engine/v1, Electra
    message BuilderDepositRequest { bytes pubkey [48]; bytes withdrawal_credentials [32]; uint64 amount;
                                    bytes signature [96]; }                              // engine/v1, Gloas
    message BeaconBlocksByRangeRequest { uint64 start_slot [Slot]; uint64 count; uint64 step; }
    message BlobSidecarsByRangeRequest { uint64 start_slot [Slot]; uint64 count; }      // "Spec Definition: (start_slot: Slot, count: uint64)"
    message ExecutionPayloadEnvelopesByRangeRequest { uint64 start_slot [Slot]; uint64 count; }  // "Spec Definition"
    message PartialDataColumnGroupID { bytes beacon_block_root [32]; uint64 slot [Slot]; }  // "Field order follows the spec"
    message ValidatorIdentity { uint64 index [ValidatorIndex]; bytes pubkey [48]; uint64 activation_epoch [Epoch]; }
    message BuilderPreferences { uint64 max_execution_payment [Gwei]; }
-/

namespace Prysm.DepositRequest
open EthLib.Serialization.Ssz

/-- Prysm `engine/v1.DepositRequest` (Electra deposit request). -/
def desc : Desc := .container ["pubkey", "withdrawal_credentials", "amount", "signature", "index"]
  [.byteVector 48, .byteVector 32, .uint 8, .byteVector 96, .uint 8]

end Prysm.DepositRequest
