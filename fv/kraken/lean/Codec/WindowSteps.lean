import Codec.NopWindow

/-!
# GEN4 L2: per-instruction step lemmas (variation class V2: registers and straight-line set-up)

The hold-outs H4 and H5 missed fields whose argument set-up used another register or another order of
`mov` / `lea` / `add` than the GEN3 set-up templates. Here every straight-line directive form of the surveyed
set-ups has ONE lemma, parametric in its registers, over a window (`NopView.lean`: nops allowed anywhere):

    kstep_X params q j e hq he hend … : Eventually final ⟨post s, addrOf e⟩ → Eventually final ⟨s, addrOf j⟩

for every `final` (continuation form). `post s` is an explicit state: `setR s r v` (one register written),
`∀ fl` for the status flags of `add`, `∀ m'` with the separation fact for a store. A set-up of any order and
any registers is a sequence of `apply`; the block lemma that follows is the last step and its entry
conditions are checked by Lean on the computed state. The tactic `kn` normalises that state after a step.
No runtime contract is used. Not here: `test %al,(%rax)` (only in function heads).
-/

open Machine TestTarget

namespace Codec

/-- `mov %rS,%rD`. -/
def iMovRR (rD rS : Reg64) : Directive :=
  Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
    (Operation.mov (RegOrMem.reg (Reg.low rD Width.W64)) (Operand.regOrMem (RegOrMem.reg (Reg.low rS Width.W64)))))
/-- `mov disp(%rB),%rD` (`rB` may be rsp). -/
def iLd (rD rB : Reg64) (disp : Int64) : Directive :=
  Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
    (Operation.mov (RegOrMem.reg (Reg.low rD Width.W64))
      (Operand.regOrMem (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg rB)) none (ConstExpr.int64 disp))))))
/-- `mov %rS,disp(%rB)`. -/
def iSt (rS rB : Reg64) (disp : Int64) : Directive :=
  Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
    (Operation.mov (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg rB)) none (ConstExpr.int64 disp)))
      (Operand.regOrMem (RegOrMem.reg (Reg.low rS Width.W64)))))
/-- `lea disp(%rB),%rD`. -/
def iLea (rD rB : Reg64) (disp : Int64) : Directive :=
  Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
    (Operation.lea (Reg.low rD Width.W64) (AddrExpr.mk (some (RegOrRip.reg rB)) none (ConstExpr.int64 disp))))
/-- `add $imm,%rD`. -/
def iAdd (rD : Reg64) (imm : Int64) : Directive :=
  Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
    (Operation.add (RegOrMem.reg (Reg.low rD Width.W64)) (Operand.imm (ConstExpr.int64 imm))))
/-- `mov $imm,%eD` (32-bit destination; the upper half is cleared). -/
def iMovI (rD : Reg64) (imm : Int64) : Directive :=
  Kraken.Directive.instr (Instr.regular Width.W64 Width.W32
    (Operation.mov (RegOrMem.reg (Reg.low rD Width.W32)) (Operand.imm (ConstExpr.int64 imm))))
/-- `jmp l`. -/
def iJmp (l : String) : Directive :=
  Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
    (Operation.jmp (RelRegOrMem.rel ((ConstExpr.label l).sub ConstExpr.after_current_instruction))))


/-- A label directive. -/
def iLabel (l : String) : Directive := Kraken.Directive.label l

/-- The state after a write of `v` to the 64-bit register `r`. -/
def setR (s : MachineData) (r : Reg64) (v : BitVec 64) : MachineData := { s with regs := s.regs.set64 r v }

end Codec

/-- `kunfold` without the unfolding of `Reg64s.get64` / `Reg64s.set64` (the registers are parameters). -/
macro "kunf" : tactic => `(tactic| simp only [Directive.interp, Instr.interp, Operation.interp,
  Operand.interp, RegOrMem.interp, RelRegOrMem.interp, Machine.jmp_rel, AddrExpr.interp, ConstExpr.interp, MachineData.set,
  MachineData.setReg, Effects.All, Width.bits, Width.bytes, Width.bytesv, Int.add_zero, BitVec.setWidth_eq,
  Reg64s.get, Reg64s.set, Reg.base, Reg.offset, BitVec.toAddressSize,
  BitVec.take, BitVec.drop, BitVec.signed, Machine.ofInt_toInt_add, Machine.ofInt_int64, Machine.extractLsb'_full,
  Nat.sub_zero, BitVec.add_zero, Machine.add_ofNat_zero, Machine.add_lit_zero, Machine.add_ofInt_zero, Machine.add_int64_zero, Machine.rip_addr, Machine.rip_addr'])

/-- Normalise the state after a step on a state with literal registers (`setR`, register reads and writes,
immediate literals). Does nothing if the state is already normal. -/
macro "kn" : tactic => `(tactic| try simp only [Codec.setR, Reg64s.set64, Reg64s.get64, Int64.toBitVec_ofNat])

namespace Codec
variable [Host]

/-- **Step: a run of `nop` directives** (window with no other directive). -/
theorem kstep_nops (q : Program) (j e : Nat) (hq : q.IsInfixAt Host.prog j) (he : eraseNop q = [])
    (hend : j + q.length = e) (final : MachineState → Prop) (s : MachineData)
    (hk : Eventually (step1 Host.exe) final ⟨s, Host.addrOf e⟩) :
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf j⟩ := wnops hq he hend hk

/-- **Step: a label** (inert). -/
theorem kstep_label (l : String) (q : Program) (j e : Nat) (hq : q.IsInfixAt Host.prog j)
    (he : eraseNop q = [iLabel l]) (hend : j + q.length = e) (final : MachineState → Prop) (s : MachineData)
    (hk : Eventually (step1 Host.exe) final ⟨s, Host.addrOf e⟩) :
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf j⟩ := by
  kwin hq
  have hd : [iLabel l].IsInfixAt Host.prog (j + nopPos q 0) := wat hq he 0
  unfold iLabel at hd
  apply Machine.estep hd
  kunf
  kwend hq he 0 hend
  exact hk

/-- **Step: `jmp l`**; `jl` is the index of the label `l` (`hl`, from `Machine.label_at'`). Nops after the `jmp` are not executed. -/
theorem kstep_jmp (l : String) (q : Program) (j jl : Nat) (hq : q.IsInfixAt Host.prog j)
    (he : eraseNop q = [iJmp l]) (hl : label l = Host.addrOf jl) (final : MachineState → Prop) (s : MachineData)
    (hk : Eventually (step1 Host.exe) final ⟨s, Host.addrOf jl⟩) :
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf j⟩ := by
  kwin hq
  have hd : [iJmp l].IsInfixAt Host.prog (j + nopPos q 0) := wat hq he 0
  unfold iJmp at hd
  apply Machine.estep hd
  kunf
  rw [hl]
  exact hk

/-- **Step: `mov %rS,%rD`**. -/
theorem kstep_mov_rr (rD rS : Reg64) (q : Program) (j e : Nat) (hq : q.IsInfixAt Host.prog j)
    (he : eraseNop q = [iMovRR rD rS]) (hend : j + q.length = e) (final : MachineState → Prop) (s : MachineData)
    (hk : Eventually (step1 Host.exe) final ⟨setR s rD (s.regs.get64 rS), Host.addrOf e⟩) :
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf j⟩ := by
  kwin hq
  have hd : [iMovRR rD rS].IsInfixAt Host.prog (j + nopPos q 0) := wat hq he 0
  unfold iMovRR at hd
  apply Machine.estep hd
  kunf
  kwend hq he 0 hend
  exact hk

/-- **Step: `mov disp(%rB),%rD`**, bytes form: the 8 bytes `bs` at `a = base + disp`, `base` = the value of `rB`. -/
theorem kstep_ldb (rD rB : Reg64) (disp : Int64) (q : Program) (j e : Nat)
    (hq : q.IsInfixAt Host.prog j) (he : eraseNop q = [iLd rD rB disp]) (hend : j + q.length = e)
    (base a : BitVec 64) (ha : base + disp.toBitVec = a) (bs : List UInt8) (hbs : bs.length = 8)
    (F : DataMem → Prop) (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 rB = base) (hm : (Eq (bs.At a) ⋆ F) s.dmem)
    (hk : Eventually (step1 Host.exe) final ⟨setR s rD (BitVec.ofInt 64 (Int.ofBytes bs)), Host.addrOf e⟩) :
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf j⟩ := by
  subst ha hb
  kwin hq
  have hd : [iLd rD rB disp].IsInfixAt Host.prog (j + nopPos q 0) := wat hq he 0
  unfold iLd at hd
  apply Machine.estep hd
  kunf
  apply load_step_at _ _ (s.regs.get64 rB + disp.toBitVec) _ _ bs _ _ rfl hm (by exact hbs)
  kunf
  kwend hq he 0 hend
  exact hk

/-- **Step: `mov disp(%rB),%rD`**, value form: the slot holds the 8 bytes of `v`; `rD` gets `v`. -/
theorem kstep_ldv (rD rB : Reg64) (disp : Int64) (q : Program) (j e : Nat)
    (hq : q.IsInfixAt Host.prog j) (he : eraseNop q = [iLd rD rB disp]) (hend : j + q.length = e)
    (base a v : BitVec 64) (ha : base + disp.toBitVec = a)
    (F : DataMem → Prop) (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 rB = base) (hm : (Eq ((Int.toBytes 8 v.toInt).At a) ⋆ F) s.dmem)
    (hk : Eventually (step1 Host.exe) final ⟨setR s rD v, Host.addrOf e⟩) :
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf j⟩ :=
  kstep_ldb rD rB disp q j e hq he hend base a ha _ (Int.toBytes_length 8 _) F final s hb hm
    (by rw [Machine.ofInt_ofBytes_toBytes64]; exact hk)

/-- **Step: `mov %rS,disp(%rB)`**: the slot `a = base + disp` (8 bytes `bs`) gets the value of `rS`. The width of
`toInt` is written `64` (not `Width.W64.bits`) so that the new memory fact is in the form `ecancel` matches. -/
theorem kstep_st (rS rB : Reg64) (disp : Int64) (q : Program) (j e : Nat)
    (hq : q.IsInfixAt Host.prog j) (he : eraseNop q = [iSt rS rB disp]) (hend : j + q.length = e)
    (base a : BitVec 64) (ha : base + disp.toBitVec = a) (bs : List UInt8) (hbs : bs.length = 8)
    (F : DataMem → Prop) (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 rB = base) (hm : (Eq (bs.At a) ⋆ F) s.dmem)
    (hk : ∀ m' : DataMem, (Eq ((Int.toBytes 8 (@BitVec.toInt 64 (s.regs.get64 rS))).At a) ⋆ F) m' →
      Eventually (step1 Host.exe) final ⟨{ s with dmem := m' }, Host.addrOf e⟩) :
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf j⟩ := by
  subst ha hb
  kwin hq
  have hd : [iSt rS rB disp].IsInfixAt Host.prog (j + nopPos q 0) := wat hq he 0
  unfold iSt at hd
  apply Machine.estep hd
  kunf
  apply store_step_at _ _ (s.regs.get64 rB + disp.toBitVec) _ _ _ bs _ _ rfl hm (by exact hbs)
  intro m' H
  simp only [Width.bytes, Width.bits] at H
  try kunf
  kwend hq he 0 hend
  exact hk m' H

/-- **Step: `lea disp(%rB),%rD`**. -/
theorem kstep_lea (rD rB : Reg64) (disp : Int64) (q : Program) (j e : Nat) (hq : q.IsInfixAt Host.prog j)
    (he : eraseNop q = [iLea rD rB disp]) (hend : j + q.length = e) (final : MachineState → Prop) (s : MachineData)
    (hk : Eventually (step1 Host.exe) final ⟨setR s rD (s.regs.get64 rB + disp.toBitVec), Host.addrOf e⟩) :
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf j⟩ := by
  kwin hq
  have hd : [iLea rD rB disp].IsInfixAt Host.prog (j + nopPos q 0) := wat hq he 0
  unfold iLea at hd
  apply Machine.estep hd
  kunf
  kwend hq he 0 hend
  exact hk

/-- **Step: `add $imm,%rD`**; the status flags after it are not stated (`∀ fl`). -/
theorem kstep_add (rD : Reg64) (imm : Int64) (q : Program) (j e : Nat) (hq : q.IsInfixAt Host.prog j)
    (he : eraseNop q = [iAdd rD imm]) (hend : j + q.length = e) (final : MachineState → Prop) (s : MachineData)
    (hk : ∀ fl : StatusFlags, Eventually (step1 Host.exe) final
      ⟨{ regs := s.regs.set64 rD (s.regs.get64 rD + imm.toBitVec), zmms := s.zmms, status := fl, dmem := s.dmem },
        Host.addrOf e⟩) :
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf j⟩ := by
  kwin hq
  have hd : [iAdd rD imm].IsInfixAt Host.prog (j + nopPos q 0) := wat hq he 0
  unfold iAdd at hd
  apply Machine.estep hd
  kunf
  simp only [BitVec.add_comm imm.toBitVec (s.regs.get64 rD)]
  kwend hq he 0 hend
  exact hk _

/-- **Step: `mov $imm,%eD`**. -/
theorem kstep_movi (rD : Reg64) (imm : Int64) (q : Program) (j e : Nat) (hq : q.IsInfixAt Host.prog j)
    (he : eraseNop q = [iMovI rD imm]) (hend : j + q.length = e) (final : MachineState → Prop) (s : MachineData)
    (hk : Eventually (step1 Host.exe) final ⟨setR s rD (BitVec.zeroExtend 64 (BitVec.truncate 32 imm.toBitVec)), Host.addrOf e⟩) :
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf j⟩ := by
  kwin hq
  have hd : [iMovI rD imm].IsInfixAt Host.prog (j + nopPos q 0) := wat hq he 0
  unfold iMovI at hd
  apply Machine.estep hd
  kunf
  kwend hq he 0 hend
  exact hk

end Codec
