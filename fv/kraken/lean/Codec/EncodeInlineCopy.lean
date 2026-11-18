import Codec.EncodeSteps

/-!
# Step lemmas of the 4-byte inline copy of the encoder fast path

Go 1.26.10 compiles the append of a 4-byte field (`dst = append(dst, f...)`, capacity sufficient) without a
`runtime.memmove` call.
The copy is one 32-bit load from the field pointer and one 32-bit indexed store into the output:
`mov disp(%rB),%eD; mov %eS,disp(%rB,%rI,1)`.

* `step_load_bytes32 rD rB disp`: the 4 bytes `bs` at `base + disp`; `rD` gets them, zero-extended to 64 bits.
* `step_store_indexed32 rS rB rI disp`: the 4 bytes at `base + idx + disp` get the low 32 bits of `rS`.

Both lemmas are in the continuation form of `Codec/WindowSteps.lean`; nops may be anywhere in a window.
-/

open Machine Runtime

namespace Codec

/-- `mov disp(%rB),%eD` (32-bit load; the upper half of `rD` is cleared). -/
def instrLoad32 (rD rB : Reg64) (disp : Int64) : Directive :=
  Kraken.Directive.instr (Instr.regular Width.W64 Width.W32
    (Operation.mov (RegOrMem.reg (Reg.low rD Width.W32))
      (Operand.regOrMem (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg rB)) none (ConstExpr.int64 disp))))))

/-- `mov %eS,disp(%rB,%rI,1)` (32-bit store of the low half of `rS`). -/
def instrStoreIndexed32 (rS rB rI : Reg64) (disp : Int64) : Directive :=
  Kraken.Directive.instr (Instr.regular Width.W64 Width.W32
    (Operation.mov (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg rB)) (some (AddrIndex.mk rI Width.W8))
        (ConstExpr.int64 disp)))
      (Operand.regOrMem (RegOrMem.reg (Reg.low rS Width.W32)))))

variable [Host]

/-- **Step: `mov disp(%rB),%eD`**: the 4 bytes `bs` at `a = base + disp`, `base` = the value of `rB`; `rD` gets them
zero-extended. -/
theorem step_load_bytes32 (rD rB : Reg64) (disp : Int64) (q : Program) (j e : Nat)
    (hq : q.IsInfixAt Host.prog j) (he : eraseNop q = [instrLoad32 rD rB disp]) (hend : j + q.length = e)
    (base a : BitVec 64) (ha : base + disp.toBitVec = a) (bs : List UInt8) (hbs : bs.length = 4)
    (F : DataMem → Prop) (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 rB = base) (hm : (Eq (bs.At a) ⋆ F) s.dmem)
    (hk : Eventually (step1 Host.exe) final
      ⟨setRegister s rD (BitVec.zeroExtend 64 (BitVec.ofInt 32 (Int.ofBytes bs))), Host.addrOf e⟩) :
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf j⟩ := by
  subst ha hb
  window_skip_leading_nops hq
  have hd : [instrLoad32 rD rB disp].IsInfixAt Host.prog (j + nonNopIndex q 0) := window_directive_at hq he 0
  unfold instrLoad32 at hd
  apply Machine.eventually_step_directive hd
  unfold_step_keep_registers
  apply load_step_at _ _ (s.regs.get64 rB + disp.toBitVec) _ _ bs _ _ rfl hm (by exact hbs)
  unfold_step_keep_registers
  window_skip_to_end hq he 0 hend
  exact hk

/-- **Step: `mov %eS,disp(%rB,%rI,1)`**: the 4 bytes `bs` at `a = base + idx + disp` get the low 32 bits of `rS`. -/
theorem step_store_indexed32 (rS rB rI : Reg64) (disp : Int64) (q : Program) (j e : Nat)
    (hq : q.IsInfixAt Host.prog j) (he : eraseNop q = [instrStoreIndexed32 rS rB rI disp]) (hend : j + q.length = e)
    (base idx a : BitVec 64) (ha : base + idx + disp.toBitVec = a) (bs : List UInt8) (hbs : bs.length = 4)
    (F : DataMem → Prop) (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 rB = base) (hi : s.regs.get64 rI = idx) (hm : (Eq (bs.At a) ⋆ F) s.dmem)
    (hk : ∀ m' : DataMem, (Eq ((Int.toBytes 4 (BitVec.extractLsb' 0 32 (s.regs.get64 rS)).toInt).At a) ⋆ F) m' →
      Eventually (step1 Host.exe) final ⟨{ s with dmem := m' }, Host.addrOf e⟩) :
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf j⟩ := by
  subst ha hb hi
  window_skip_leading_nops hq
  have hd : [instrStoreIndexed32 rS rB rI disp].IsInfixAt Host.prog (j + nonNopIndex q 0) := window_directive_at hq he 0
  unfold instrStoreIndexed32 at hd
  apply Machine.eventually_step_directive hd
  unfold_step_keep_registers
  simp only [Machine.ofInt_base_index_scale, BitVec.mul_one]
  apply store_step_at _ _ (s.regs.get64 rB + s.regs.get64 rI + disp.toBitVec) _ _ _ bs _ _ rfl hm (by exact hbs)
  intro m' H
  simp only [Width.bytes, Width.bits] at H
  try unfold_step_keep_registers
  window_skip_to_end hq he 0 hend
  exact hk m' H

end Codec
