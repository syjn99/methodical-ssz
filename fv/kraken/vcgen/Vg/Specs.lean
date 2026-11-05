import Kraken.X64.WP.Spec

/-! B0: instruction specs that vcgen (a4cce2e) lacks for Scalars.UnmarshalSSZ.
Same proof pattern as Kraken's `Program.WP.mov_reg8_mem`. -/

open Std.WP
open Lean.Order

namespace Program.WP
def vgR32 (s : MachineData) (r : Reg64) (v : BitVec 32) : MachineData := { s with regs := s.regs.set (.low r .W32) v }
def vgR64 (s : MachineData) (r : Reg64) (v : BitVec 64) : MachineData := { s with regs := s.regs.set64 r v }
def vgSt (s : MachineData) (a : BitVec 64) (n : Nat) (v : Int) : MachineData := { s with dmem := Mem.storeInt s.dmem a n v }

variable [Host] [FunDecls] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}

@[spec] theorem vg_movzx32_mem8 (r b : Reg64) (d : Int64) :
    ⦃ fun s => (Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 1).isSome = true
        ∧ Q () (vgR32 s r ((BitVec.ofInt 8 (Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 1).get!).zeroExtend 32)) ⦄
      (Directive.instr (.regular .W64 .W32
          (.movzx (w' := .W8) (.reg (.low r .W32)) (.mem ⟨some (.reg b), none, .int64 d⟩))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨i, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load, MachineData.set, MachineData.setReg, vgR32, vgR64, vgSt,
    AddrExpr.zeroExtend_interp_base_disp, Width.bytes, hload, Effects.All, ite_true]
  exact hn _ (by rwa [hload, Option.get!_some] at hpre)

@[spec] theorem vg_movzx32_mem16 (r b : Reg64) (d : Int64) :
    ⦃ fun s => (Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 2).isSome = true
        ∧ Q () (vgR32 s r ((BitVec.ofInt 16 (Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 2).get!).zeroExtend 32)) ⦄
      (Directive.instr (.regular .W64 .W32
          (.movzx (w' := .W16) (.reg (.low r .W32)) (.mem ⟨some (.reg b), none, .int64 d⟩))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨i, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load, MachineData.set, MachineData.setReg, vgR32, vgR64, vgSt,
    AddrExpr.zeroExtend_interp_base_disp, Width.bytes, hload, Effects.All, ite_true]
  exact hn _ (by rwa [hload, Option.get!_some] at hpre)

@[spec] theorem vg_mov_reg64_mem (r b : Reg64) (d : Int64) :
    ⦃ fun s => (Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 8).isSome = true
        ∧ Q () (vgR64 s r (BitVec.ofInt 64 (Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 8).get!)) ⦄
      (Directive.instr (.regular .W64 .W64
          (.mov (.reg (.low r .W64)) (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨i, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load, MachineData.set, MachineData.setReg, vgR32, vgR64, vgSt, Reg64s.set_low_W64,
    AddrExpr.zeroExtend_interp_base_disp, Width.bytes, hload, Effects.All, ite_true]
  exact hn _ (by rwa [hload, Option.get!_some] at hpre)

@[spec] theorem vg_mov_mem8_imm (b : Reg64) (d i : Int64) :
    ⦃ fun s => (Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 1).isSome = true
        ∧ Q () (vgSt s (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 1 (BitVec.toInt (BitVec.setWidth 8 i.toBitVec))) ⦄
      (Directive.instr (.regular .W64 .W8
          (.mov (.mem ⟨some (.reg b), none, .int64 d⟩) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s hpre => ?_
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨i, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.store, vgSt,
    AddrExpr.zeroExtend_interp_base_disp, Width.bytes, hload, Effects.All, ite_true]
  exact hn _ hpre

def vgFl (s : MachineData) (f : StatusFlags) : MachineData := { s with status := f }

@[spec] theorem vg_cmp_reg8_imm (r : Reg64) (i : Int64) :
    ⦃ fun s => Q () (vgFl s (StatusFlags.ofSub (s.regs.get (.low r .W8)) (BitVec.setWidth 8 i.toBitVec))) ⦄
      (Directive.instr (.regular .W64 .W8 (.cmp (.reg (.low r .W8)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄ :=
  Triple.intro fun _ hq => Program.wp_single fun _ _ _ _ hn _ => by
    simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
      MachineData.set, MachineData.setReg, Effects.All]
    exact hn _ hq

end Program.WP
