import E2eScal.E2cStmt
import E2eScal.Gen6PbEnc
import E2eScal.Gen6ScEnc
import E2eScal.Gen6PwEnc
import E2eScal.Gen6DdEnc

/-!
# ENC2 unit E2-C: identities of the generated encoder fast-path theorems with the independent hand statements

`E2cStmt.lean` was committed before the generated theorems were read. Each identity is `rfl` at default
transparency; a failed identity is recorded, not forced. Encoder fast path only.
-/

open Fk E2eScal

namespace E2eScal.E2c

set_option maxHeartbeats 4000000 in
theorem pb_same : ∀ (h : Host), type_of% (@E2eScal.Gen6Enc.pb_g6e_fast h) = @pb_hand_fast h := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
theorem sc_same : ∀ (h : Host), type_of% (@E2eScal.Gen6Enc.sc_g6e_fast h) = @sc_hand_fast h := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
theorem pw_same : ∀ (h : Host), type_of% (@E2eScal.Gen6Enc.pw_g6e_fast h) = @pw_hand_fast h := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
theorem dd_same : ∀ (h : Host), type_of% (@E2eScal.Gen6Enc.dd_g6e_fast h) = @dd_hand_fast h := by
  intro h; rfl

end E2eScal.E2c
