module

public import Runtime.Contracts

@[expose] public section

/-! # Congruence of the contract form `StaticBox` -/

open Machine Runtime
variable [Host]

theorem Runtime.staticBox_congr {x y : BitVec 64} (h : x = y) : StaticBox x = StaticBox y := h ▸ rfl
