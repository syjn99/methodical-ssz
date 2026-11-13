import Runtime.Contracts

/-! # Congruence of the contract form `StaticBox` (text of `TestTarget/ListU64DecodeRejectCall.lean`) -/

open Machine Runtime
variable [Host]

theorem Runtime.staticBox_congr {x y : BitVec 64} (h : x = y) : StaticBox x = StaticBox y := h ▸ rfl
