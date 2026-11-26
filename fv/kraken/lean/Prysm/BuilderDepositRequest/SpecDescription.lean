module

public import EthLib.Serialization.Ssz

@[expose] public section

/-!
# Independent hand `Desc` of `BuilderDepositRequest`

This description is written by hand from the Prysm proto definitions in the Prysm source tree that the Go differential uses.
It does not use the checker descriptions `Prysm/<Type>/SpecChecker.lean`.
It is not independent of the source of the Desc producer (as `Prysm/ValidatorBalance/SpecDescription.lean`).
Where the proto cites a spec definition, the comment is quoted.
Overlay types (`cast_type` Slot, Epoch, ValidatorIndex, Gwei) are `uint64` in SSZ.
The proto file is `proto/engine/v1/gloas.proto`.

    message BuilderDepositRequest { bytes pubkey [48]; bytes withdrawal_credentials [32]; uint64 amount;
                                    bytes signature [96]; }                              // engine/v1, Gloas
-/

namespace Prysm.BuilderDepositRequest
open EthLib.Serialization.Ssz

/-- Prysm `engine/v1.BuilderDepositRequest` (Gloas). -/
def desc : Desc := .container ["pubkey", "withdrawal_credentials", "amount", "signature"]
  [.byteVector 48, .byteVector 32, .uint 8, .byteVector 96]

end Prysm.BuilderDepositRequest
