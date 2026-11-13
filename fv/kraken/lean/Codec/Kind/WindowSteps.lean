import Codec.WindowSteps
import Machine.Labels

/-!
# Statement kinds of the per-instruction step lemmas

Each kind is the statement of its lemma (`Codec/WindowSteps.lean`) for a window of the decoder `C` that starts at `k + j`
and ends at `k + e`, after the binders `k hk hf` (the idiom of `Codec/Kind/FieldPatterns.lean` / `Codec/Kind/CalleeDecode.lean`). The registers,
the displacement and the immediate are kind parameters, because they are in the statement. A generated step
theorem is tied to its kind by `with_reducible rfl`; the `_of` theorems prove each kind from its lemma and
the window facts, so the kind bodies are kernel-checked against the lemma conclusions.
-/

open Machine

namespace Codec

variable [Host]

set_option linter.unusedVariables false in
/-- Kind of `kstep_nops`: a run of nops from `k + j` to `k + e`. -/
abbrev stepNopsKind (C : Program) (j e : Nat) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k)
    (final : MachineState → Prop) (s : MachineData)
    (hk' : Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + e)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + j)⟩

theorem stepNopsKind_of (C : Program) (j e : Nat) (q : Program)
    (hq : ∀ k, C.IsInfixAt Host.prog k → q.IsInfixAt Host.prog (k + j)) (he : eraseNop q = [])
    (hend : j + q.length = e) : stepNopsKind C j e :=
  fun k hk _ final s h => kstep_nops q (k + j) (k + e) (hq k hk) he (by omega) final s h

set_option linter.unusedVariables false in
/-- Kind of `kstep_label`: the label `l`. -/
abbrev stepLabelKind (C : Program) (l : String) (j e : Nat) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k)
    (final : MachineState → Prop) (s : MachineData)
    (hk' : Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + e)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + j)⟩

theorem stepLabelKind_of (C : Program) (l : String) (j e : Nat) (q : Program)
    (hq : ∀ k, C.IsInfixAt Host.prog k → q.IsInfixAt Host.prog (k + j)) (he : eraseNop q = [iLabel l])
    (hend : j + q.length = e) : stepLabelKind C l j e :=
  fun k hk _ final s h => kstep_label l q (k + j) (k + e) (hq k hk) he (by omega) final s h

set_option linter.unusedVariables false in
/-- Kind of `kstep_jmp`: `jmp l` at `k + j`, the label `l` at `k + jl`. -/
abbrev stepJmpKind (C : Program) (l : String) (j jl : Nat) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k)
    (final : MachineState → Prop) (s : MachineData)
    (hk' : Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + jl)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + j)⟩

theorem stepJmpKind_of (C : Program) (l : String) (j jl : Nat) (q : Program)
    (hq : ∀ k, C.IsInfixAt Host.prog k → q.IsInfixAt Host.prog (k + j)) (he : eraseNop q = [iJmp l])
    (hl : ∀ k, C.IsInfixAt Host.prog k → LabelsFresh C k → label l = Host.addrOf (k + jl)) : stepJmpKind C l j jl :=
  fun k hk hf final s h => kstep_jmp l q (k + j) (k + jl) (hq k hk) he (hl k hk hf) final s h

set_option linter.unusedVariables false in
/-- Kind of `kstep_mov_rr`: `mov %rS,%rD`. -/
abbrev stepMovRRKind (C : Program) (rD rS : Reg64) (j e : Nat) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k)
    (final : MachineState → Prop) (s : MachineData)
    (hk' : Eventually (step1 Host.exe) final ⟨setR s rD (s.regs.get64 rS), Host.addrOf (k + e)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + j)⟩

theorem stepMovRRKind_of (C : Program) (rD rS : Reg64) (j e : Nat) (q : Program)
    (hq : ∀ k, C.IsInfixAt Host.prog k → q.IsInfixAt Host.prog (k + j)) (he : eraseNop q = [iMovRR rD rS])
    (hend : j + q.length = e) : stepMovRRKind C rD rS j e :=
  fun k hk _ final s h => kstep_mov_rr rD rS q (k + j) (k + e) (hq k hk) he (by omega) final s h

set_option linter.unusedVariables false in
/-- Kind of `kstep_ldb`: `mov disp(%rB),%rD`, bytes form. -/
abbrev stepLdbKind (C : Program) (rD rB : Reg64) (disp : Int64) (j e : Nat) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k)
    (base a : BitVec 64) (ha : base + disp.toBitVec = a) (bs : List UInt8) (hbs : bs.length = 8)
    (F : DataMem → Prop)
    (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 rB = base) (hm : (Eq (bs.At a) ⋆ F) s.dmem)
    (hk' : Eventually (step1 Host.exe) final ⟨setR s rD (BitVec.ofInt 64 (Int.ofBytes bs)), Host.addrOf (k + e)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + j)⟩

theorem stepLdbKind_of (C : Program) (rD rB : Reg64) (disp : Int64) (j e : Nat) (q : Program)
    (hq : ∀ k, C.IsInfixAt Host.prog k → q.IsInfixAt Host.prog (k + j)) (he : eraseNop q = [iLd rD rB disp])
    (hend : j + q.length = e) : stepLdbKind C rD rB disp j e :=
  fun k hk _ => kstep_ldb rD rB disp q (k + j) (k + e) (hq k hk) he (by omega)

set_option linter.unusedVariables false in
/-- Kind of `kstep_ldv`: `mov disp(%rB),%rD`, value form. -/
abbrev stepLdvKind (C : Program) (rD rB : Reg64) (disp : Int64) (j e : Nat) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k)
    (base a v : BitVec 64) (ha : base + disp.toBitVec = a)
    (F : DataMem → Prop)
    (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 rB = base) (hm : (Eq ((Int.toBytes 8 v.toInt).At a) ⋆ F) s.dmem)
    (hk' : Eventually (step1 Host.exe) final ⟨setR s rD v, Host.addrOf (k + e)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + j)⟩

theorem stepLdvKind_of (C : Program) (rD rB : Reg64) (disp : Int64) (j e : Nat) (q : Program)
    (hq : ∀ k, C.IsInfixAt Host.prog k → q.IsInfixAt Host.prog (k + j)) (he : eraseNop q = [iLd rD rB disp])
    (hend : j + q.length = e) : stepLdvKind C rD rB disp j e :=
  fun k hk _ => kstep_ldv rD rB disp q (k + j) (k + e) (hq k hk) he (by omega)

set_option linter.unusedVariables false in
/-- Kind of `kstep_st`: `mov %rS,disp(%rB)`. -/
abbrev stepStKind (C : Program) (rS rB : Reg64) (disp : Int64) (j e : Nat) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k)
    (base a : BitVec 64) (ha : base + disp.toBitVec = a) (bs : List UInt8) (hbs : bs.length = 8)
    (F : DataMem → Prop)
    (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 rB = base) (hm : (Eq (bs.At a) ⋆ F) s.dmem)
    (hk' : ∀ m' : DataMem, (Eq ((Int.toBytes 8 (@BitVec.toInt 64 (s.regs.get64 rS))).At a) ⋆ F) m' →
      Eventually (step1 Host.exe) final ⟨{ s with dmem := m' }, Host.addrOf (k + e)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + j)⟩

theorem stepStKind_of (C : Program) (rS rB : Reg64) (disp : Int64) (j e : Nat) (q : Program)
    (hq : ∀ k, C.IsInfixAt Host.prog k → q.IsInfixAt Host.prog (k + j)) (he : eraseNop q = [iSt rS rB disp])
    (hend : j + q.length = e) : stepStKind C rS rB disp j e :=
  fun k hk _ => kstep_st rS rB disp q (k + j) (k + e) (hq k hk) he (by omega)

set_option linter.unusedVariables false in
/-- Kind of `kstep_lea`: `lea disp(%rB),%rD`. -/
abbrev stepLeaKind (C : Program) (rD rB : Reg64) (disp : Int64) (j e : Nat) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k)
    (final : MachineState → Prop) (s : MachineData)
    (hk' : Eventually (step1 Host.exe) final ⟨setR s rD (s.regs.get64 rB + disp.toBitVec), Host.addrOf (k + e)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + j)⟩

theorem stepLeaKind_of (C : Program) (rD rB : Reg64) (disp : Int64) (j e : Nat) (q : Program)
    (hq : ∀ k, C.IsInfixAt Host.prog k → q.IsInfixAt Host.prog (k + j)) (he : eraseNop q = [iLea rD rB disp])
    (hend : j + q.length = e) : stepLeaKind C rD rB disp j e :=
  fun k hk _ final s h => kstep_lea rD rB disp q (k + j) (k + e) (hq k hk) he (by omega) final s h

set_option linter.unusedVariables false in
/-- Kind of `kstep_add`: `add $imm,%rD`. -/
abbrev stepAddKind (C : Program) (rD : Reg64) (imm : Int64) (j e : Nat) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k)
    (final : MachineState → Prop) (s : MachineData)
    (hk' : ∀ fl : StatusFlags, Eventually (step1 Host.exe) final
      ⟨{ regs := s.regs.set64 rD (s.regs.get64 rD + imm.toBitVec), zmms := s.zmms, status := fl, dmem := s.dmem },
        Host.addrOf (k + e)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + j)⟩

theorem stepAddKind_of (C : Program) (rD : Reg64) (imm : Int64) (j e : Nat) (q : Program)
    (hq : ∀ k, C.IsInfixAt Host.prog k → q.IsInfixAt Host.prog (k + j)) (he : eraseNop q = [iAdd rD imm])
    (hend : j + q.length = e) : stepAddKind C rD imm j e :=
  fun k hk _ final s h => kstep_add rD imm q (k + j) (k + e) (hq k hk) he (by omega) final s h

set_option linter.unusedVariables false in
/-- Kind of `kstep_movi`: `mov $imm,%eD`. -/
abbrev stepMovIKind (C : Program) (rD : Reg64) (imm : Int64) (j e : Nat) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k)
    (final : MachineState → Prop) (s : MachineData)
    (hk' : Eventually (step1 Host.exe) final ⟨setR s rD (BitVec.zeroExtend 64 (BitVec.truncate 32 imm.toBitVec)), Host.addrOf (k + e)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + j)⟩

theorem stepMovIKind_of (C : Program) (rD : Reg64) (imm : Int64) (j e : Nat) (q : Program)
    (hq : ∀ k, C.IsInfixAt Host.prog k → q.IsInfixAt Host.prog (k + j)) (he : eraseNop q = [iMovI rD imm])
    (hend : j + q.length = e) : stepMovIKind C rD imm j e :=
  fun k hk _ final s h => kstep_movi rD imm q (k + j) (k + e) (hq k hk) he (by omega) final s h

end Codec
