import Prysm.DepositRequest.Statements
import Prysm.DepositRequest.GeneratedDecodeAccept
import Prysm.BeaconBlocksByRangeRequest.GeneratedDecodeAccept
import Prysm.PartialDataColumnGroupID.GeneratedDecodeAccept
import Prysm.ValidatorIdentity.GeneratedDecodeAccept
import Prysm.BuilderPreferences.GeneratedEncodeFastPath
import Prysm.BeaconBlocksByRangeRequest.GeneratedEncodeFastPath
import Prysm.PartialDataColumnGroupID.GeneratedEncodeFastPath
import Prysm.ValidatorIdentity.GeneratedEncodeFastPath

/-!
# Identity of four generated decoder accept theorems and four generated encoder fast-path theorems
with the independent hand statements of `F24Stmt.lean`

`F24Stmt.lean` was committed before this session opened the generated modules imported here. Each line type-checks
only if the type of the generated theorem (`p2dec --gen5` / `p2enc --gen6`, raw output of the one-shot runs on the 24 flat types) is
definitionally the hand statement. Neither side is edited for this check. `maxHeartbeats 4000000` = the value of the
model identity files (`E2cSame.lean`).
-/

open Machine Runtime TestTarget
variable [Host]

open Codec
namespace Prysm.DepositRequest

set_option maxHeartbeats 4000000 in
theorem Decode.generated_accept_same_as_statement : ∀ (h : Host), type_of% (@Prysm.DepositRequest.Decode.generated_accept h) = @Decode.accept_statement h := by
  intro h; rfl

/-- The generated accept theorem proves the independent hand statement. -/
theorem Decode.generated_accept_satisfies_statement : Decode.accept_statement := Prysm.DepositRequest.Decode.generated_accept

set_option maxHeartbeats 4000000 in
theorem _root_.Prysm.BeaconBlocksByRangeRequest.Decode.generated_accept_same_as_statement : ∀ (h : Host), type_of% (@Prysm.BeaconBlocksByRangeRequest.Decode.generated_accept h) = @Prysm.BeaconBlocksByRangeRequest.Decode.accept_statement h := by
  intro h; rfl

/-- The generated accept theorem proves the independent hand statement. -/
theorem _root_.Prysm.BeaconBlocksByRangeRequest.Decode.generated_accept_satisfies_statement : Prysm.BeaconBlocksByRangeRequest.Decode.accept_statement := Prysm.BeaconBlocksByRangeRequest.Decode.generated_accept

set_option maxHeartbeats 4000000 in
theorem _root_.Prysm.PartialDataColumnGroupID.Decode.generated_accept_same_as_statement : ∀ (h : Host), type_of% (@Prysm.PartialDataColumnGroupID.Decode.generated_accept h) = @Prysm.PartialDataColumnGroupID.Decode.accept_statement h := by
  intro h; rfl

/-- The generated accept theorem proves the independent hand statement. -/
theorem _root_.Prysm.PartialDataColumnGroupID.Decode.generated_accept_satisfies_statement : Prysm.PartialDataColumnGroupID.Decode.accept_statement := Prysm.PartialDataColumnGroupID.Decode.generated_accept

set_option maxHeartbeats 4000000 in
theorem _root_.Prysm.ValidatorIdentity.Decode.generated_accept_same_as_statement : ∀ (h : Host), type_of% (@Prysm.ValidatorIdentity.Decode.generated_accept h) = @Prysm.ValidatorIdentity.Decode.accept_statement h := by
  intro h; rfl

/-- The generated accept theorem proves the independent hand statement. -/
theorem _root_.Prysm.ValidatorIdentity.Decode.generated_accept_satisfies_statement : Prysm.ValidatorIdentity.Decode.accept_statement := Prysm.ValidatorIdentity.Decode.generated_accept

set_option maxHeartbeats 4000000 in
theorem _root_.Prysm.BuilderPreferences.Encode.generated_fast_same_as_statement : ∀ (h : Host), type_of% (@Prysm.BuilderPreferences.Encode.generated_fast h) = @Prysm.BuilderPreferences.Encode.fast_path_statement h := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
theorem _root_.Prysm.BeaconBlocksByRangeRequest.Encode.generated_fast_same_as_statement : ∀ (h : Host), type_of% (@Prysm.BeaconBlocksByRangeRequest.Encode.generated_fast h) = @Prysm.BeaconBlocksByRangeRequest.Encode.fast_path_statement h := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
theorem _root_.Prysm.PartialDataColumnGroupID.Encode.generated_fast_same_as_statement : ∀ (h : Host), type_of% (@Prysm.PartialDataColumnGroupID.Encode.generated_fast h) = @Prysm.PartialDataColumnGroupID.Encode.fast_path_statement h := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
theorem _root_.Prysm.ValidatorIdentity.Encode.generated_fast_same_as_statement : ∀ (h : Host), type_of% (@Prysm.ValidatorIdentity.Encode.generated_fast h) = @Prysm.ValidatorIdentity.Encode.fast_path_statement h := by
  intro h; rfl

end Prysm.DepositRequest
