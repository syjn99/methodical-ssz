import E2eScal.F24Stmt
import E2eScal.Gen5F24DprDec
import E2eScal.Gen5F24BbrDec
import E2eScal.Gen5F24PdcDec
import E2eScal.Gen5F24VidDec
import E2eScal.Gen6F24BpfEnc
import E2eScal.Gen6F24BbrEnc
import E2eScal.Gen6F24PdcEnc
import E2eScal.Gen6F24VidEnc

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
namespace E2eScal.F24

set_option maxHeartbeats 4000000 in
theorem dpr_accept_same : ∀ (h : Host), type_of% (@E2eScal.Gen.dpr_g5dec_accept h) = @dpr_accept_stmt h := by
  intro h; rfl

/-- The generated accept theorem proves the independent hand statement. -/
theorem dpr_accept_hand : dpr_accept_stmt := E2eScal.Gen.dpr_g5dec_accept

set_option maxHeartbeats 4000000 in
theorem bbr_accept_same : ∀ (h : Host), type_of% (@E2eScal.Gen.bbr_g5dec_accept h) = @bbr_accept_stmt h := by
  intro h; rfl

/-- The generated accept theorem proves the independent hand statement. -/
theorem bbr_accept_hand : bbr_accept_stmt := E2eScal.Gen.bbr_g5dec_accept

set_option maxHeartbeats 4000000 in
theorem pdc_accept_same : ∀ (h : Host), type_of% (@E2eScal.Gen.pdc_g5dec_accept h) = @pdc_accept_stmt h := by
  intro h; rfl

/-- The generated accept theorem proves the independent hand statement. -/
theorem pdc_accept_hand : pdc_accept_stmt := E2eScal.Gen.pdc_g5dec_accept

set_option maxHeartbeats 4000000 in
theorem vid_accept_same : ∀ (h : Host), type_of% (@E2eScal.Gen.vid_g5dec_accept h) = @vid_accept_stmt h := by
  intro h; rfl

/-- The generated accept theorem proves the independent hand statement. -/
theorem vid_accept_hand : vid_accept_stmt := E2eScal.Gen.vid_g5dec_accept

set_option maxHeartbeats 4000000 in
theorem bpf_fast_same : ∀ (h : Host), type_of% (@E2eScal.Gen6Enc.bpf_g6e_fast h) = @bpf_hand_fast h := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
theorem bbr_fast_same : ∀ (h : Host), type_of% (@E2eScal.Gen6Enc.bbr_g6e_fast h) = @bbr_hand_fast h := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
theorem pdc_fast_same : ∀ (h : Host), type_of% (@E2eScal.Gen6Enc.pdc_g6e_fast h) = @pdc_hand_fast h := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
theorem vid_fast_same : ∀ (h : Host), type_of% (@E2eScal.Gen6Enc.vid_g6e_fast h) = @vid_hand_fast h := by
  intro h; rfl

end E2eScal.F24
