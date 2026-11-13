import Machine.Step
import Machine.Frame

/-!
# Store and address lemmas that the encoder proofs use

- `Machine.store_avx_step`: one 16-byte AVX store into a separated chunk.
- `Machine.at_split16`: a 16-byte chunk is two 8-byte chunks.
- `Machine.add8_neg8`: the address arithmetic `8 + y + x * 1 - 8 = x + y`.

The texts are the texts of `TestTarget/ListU64DecodeRejectCall.lean` and `TestTarget/FixedVecEncode.lean`.
-/

open Machine
variable [Host]

/-- A 16-byte AVX store (`movups`) into a separated chunk. -/
theorem Machine.store_avx_step (s : MachineData) (addr : BitVec 64) {w : AvxWidth} (v : w.type) (ret : MachineData → Effects)
    (bs : List UInt8) (F : DataMem → Prop) (post : MachineState → Prop)
    (H : (Eq (bs.At addr) ⋆ F) s.dmem) (hl : bs.length = w.bytes) (hw : w.bytes ≤ 2 ^ 64)
    (k : ∀ m', (Eq ((Int.toBytes w.bytes v.toInt).At addr) ⋆ F) m' → (ret { s with dmem := m' }).All post) :
    (MachineData.storeAvx s addr v ret).All post := by
  unfold MachineData.storeAvx
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rw [Effects.All_require_write_access]
  rw [Mem.loadInt_sep bs addr _ F s.dmem H hl hw]
  exact k _ (Mem.storeInt_sep addr w.bytes bs F s.dmem ⟨H, hl⟩ v.toInt)

theorem Machine.at_split16 (bs : List UInt8) (h : bs.length = 16) (a : BitVec 64) :
    Eq (bs.At a) = Eq ((bs.take 8).At a) ⋆ Eq ((bs.drop 8).At (a + 8)) := by
  conv => lhs; rw [← List.take_append_drop 8 bs]
  rw [Mem.At_append_sep _ _ _ (by simp; omega)]; simp [h]

theorem Machine.add8_neg8 (x y : BitVec 64) : 8 + y + x * 1#64 + -8 = x + y := by
  rw [BitVec.mul_one, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm 8, BitVec.add_assoc, BitVec.add_assoc]
  rw [show (-8 : BitVec 64) + 8 = 0 by decide, Machine.add_lit_zero, BitVec.add_comm]
