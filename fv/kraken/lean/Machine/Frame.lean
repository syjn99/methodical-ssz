import Machine.Bytes

/-!
# Stack frames as one block (for function specifications)

A caller gives a callee one block of stack bytes below the return slot. The
callee's theorem names its slots.
-/

namespace Machine

/-- scratch (S) · rslot (8) · gap (40) · s28 · s30 · s38 (8 each) · gap (64) · fp (8). -/
def stackFrame144 (scratch rslot g1 s28 s30 s38 g2 fp : List UInt8) : List UInt8 :=
  scratch ++ (rslot ++ (g1 ++ (s28 ++ (s30 ++ (s38 ++ (g2 ++ fp))))))

theorem at_app {a : BitVec 64} {b : BitVec 64} (l1 l2 : List UInt8) (h : b = a + BitVec.ofNat 64 l1.length)
    (hl : l1.length + l2.length ≤ 2 ^ 64) :
    Eq ((l1 ++ l2).At a) = Eq (l1.At a) ⋆ Eq (l2.At b) := by
  rw [Mem.At_append_sep _ _ _ hl, h]

theorem stackFrame144_sep (x : BitVec 64) (S : Nat) (hS : S < 2 ^ 60) (scratch rslot g1 s28 s30 s38 g2 fp : List UInt8)
    (h0 : scratch.length = S) (h1 : rslot.length = 8) (h2 : g1.length = 40) (h3 : s28.length = 8)
    (h4 : s30.length = 8) (h5 : s38.length = 8) (h6 : g2.length = 64) (h7 : fp.length = 8) :
    Eq ((stackFrame144 scratch rslot g1 s28 s30 s38 g2 fp).At (x - 144 - BitVec.ofNat 64 S)) =
      Eq (scratch.At (x - 144 - BitVec.ofNat 64 S)) ⋆ Eq (rslot.At (x - 144)) ⋆ Eq (g1.At (x - 136))
      ⋆ Eq (s28.At (x - 96)) ⋆ Eq (s30.At (x - 88)) ⋆ Eq (s38.At (x - 80)) ⋆ Eq (g2.At (x - 72))
      ⋆ Eq (fp.At (x - 8)) := by
  simp only [stackFrame144]
  rw [at_app _ _ (b := x - 144) (by rw [h0]; bv_omega) (by simp [*]; omega),
    at_app _ _ (b := x - 136) (by rw [h1]; bv_omega) (by simp [*]),
    at_app _ _ (b := x - 96) (by rw [h2]; bv_omega) (by simp [*]),
    at_app _ _ (b := x - 88) (by rw [h3]; bv_omega) (by simp [*]),
    at_app _ _ (b := x - 80) (by rw [h4]; bv_omega) (by simp [*]),
    at_app _ _ (b := x - 72) (by rw [h5]; bv_omega) (by simp [*]),
    at_app _ _ (b := x - 8) (by rw [h6]; bv_omega) (by simp [*])]
  simp only [Std.ExtHashMap.sep_assoc]

/-- Any block of `144 + S` bytes is a frame layout (slices by nested `drop`). -/
theorem stackFrame144_slices (stk : List UInt8) (S : Nat) :
    let t0 := stk.drop S; let t1 := t0.drop 8; let t2 := t1.drop 40; let t3 := t2.drop 8
    let t4 := t3.drop 8; let t5 := t4.drop 8; let t6 := t5.drop 64
    stk = stackFrame144 (stk.take S) (t0.take 8) (t1.take 40) (t2.take 8) (t3.take 8) (t4.take 8) (t5.take 64) t6 := by
  intro t0 t1 t2 t3 t4 t5 t6
  simp only [stackFrame144, t0, t1, t2, t3, t4, t5, t6, List.take_append_drop]

end Machine
