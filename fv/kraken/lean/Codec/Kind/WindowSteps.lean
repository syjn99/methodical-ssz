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
/-- Kind of `step_nops`: a run of nops from `k + j` to `k + e`. -/
abbrev stepNopsKind (C : Program) (j e : Nat) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k)
    (final : MachineState → Prop) (s : MachineData)
    (hk' : Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + e)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + j)⟩

theorem stepNopsKind_of (C : Program) (j e : Nat) (q : Program)
    (hq : ∀ k, C.IsInfixAt Host.prog k → q.IsInfixAt Host.prog (k + j)) (he : eraseNop q = [])
    (hend : j + q.length = e) : stepNopsKind C j e :=
  fun k hk _ final s h => step_nops q (k + j) (k + e) (hq k hk) he (by omega) final s h

set_option linter.unusedVariables false in
/-- Kind of `step_label`: the label `l`. -/
abbrev stepLabelKind (C : Program) (l : String) (j e : Nat) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k)
    (final : MachineState → Prop) (s : MachineData)
    (hk' : Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + e)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + j)⟩

theorem stepLabelKind_of (C : Program) (l : String) (j e : Nat) (q : Program)
    (hq : ∀ k, C.IsInfixAt Host.prog k → q.IsInfixAt Host.prog (k + j)) (he : eraseNop q = [instrLabel l])
    (hend : j + q.length = e) : stepLabelKind C l j e :=
  fun k hk _ final s h => step_label l q (k + j) (k + e) (hq k hk) he (by omega) final s h

set_option linter.unusedVariables false in
/-- Kind of `step_jump`: `jmp l` at `k + j`, the label `l` at `k + jl`. -/
abbrev stepJumpKind (C : Program) (l : String) (j jl : Nat) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k)
    (final : MachineState → Prop) (s : MachineData)
    (hk' : Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + jl)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + j)⟩

theorem stepJumpKind_of (C : Program) (l : String) (j jl : Nat) (q : Program)
    (hq : ∀ k, C.IsInfixAt Host.prog k → q.IsInfixAt Host.prog (k + j)) (he : eraseNop q = [instrJump l])
    (hl : ∀ k, C.IsInfixAt Host.prog k → LabelsFresh C k → label l = Host.addrOf (k + jl)) : stepJumpKind C l j jl :=
  fun k hk hf final s h => step_jump l q (k + j) (k + jl) (hq k hk) he (hl k hk hf) final s h

set_option linter.unusedVariables false in
/-- Kind of `step_move_register`: `mov %rS,%rD`. -/
abbrev stepMoveRegisterKind (C : Program) (rD rS : Reg64) (j e : Nat) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k)
    (final : MachineState → Prop) (s : MachineData)
    (hk' : Eventually (step1 Host.exe) final ⟨setRegister s rD (s.regs.get64 rS), Host.addrOf (k + e)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + j)⟩

theorem stepMoveRegisterKind_of (C : Program) (rD rS : Reg64) (j e : Nat) (q : Program)
    (hq : ∀ k, C.IsInfixAt Host.prog k → q.IsInfixAt Host.prog (k + j)) (he : eraseNop q = [instrMoveRegister rD rS])
    (hend : j + q.length = e) : stepMoveRegisterKind C rD rS j e :=
  fun k hk _ final s h => step_move_register rD rS q (k + j) (k + e) (hq k hk) he (by omega) final s h

set_option linter.unusedVariables false in
/-- Kind of `step_load_bytes`: `mov disp(%rB),%rD`, bytes form. -/
abbrev stepLoadBytesKind (C : Program) (rD rB : Reg64) (disp : Int64) (j e : Nat) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k)
    (base a : BitVec 64) (ha : base + disp.toBitVec = a) (bs : List UInt8) (hbs : bs.length = 8)
    (F : DataMem → Prop)
    (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 rB = base) (hm : (Eq (bs.At a) ⋆ F) s.dmem)
    (hk' : Eventually (step1 Host.exe) final ⟨setRegister s rD (BitVec.ofInt 64 (Int.ofBytes bs)), Host.addrOf (k + e)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + j)⟩

theorem stepLoadBytesKind_of (C : Program) (rD rB : Reg64) (disp : Int64) (j e : Nat) (q : Program)
    (hq : ∀ k, C.IsInfixAt Host.prog k → q.IsInfixAt Host.prog (k + j)) (he : eraseNop q = [instrLoad rD rB disp])
    (hend : j + q.length = e) : stepLoadBytesKind C rD rB disp j e :=
  fun k hk _ => step_load_bytes rD rB disp q (k + j) (k + e) (hq k hk) he (by omega)

set_option linter.unusedVariables false in
/-- Kind of `step_load_value`: `mov disp(%rB),%rD`, value form. -/
abbrev stepLoadValueKind (C : Program) (rD rB : Reg64) (disp : Int64) (j e : Nat) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k)
    (base a v : BitVec 64) (ha : base + disp.toBitVec = a)
    (F : DataMem → Prop)
    (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 rB = base) (hm : (Eq ((Int.toBytes 8 v.toInt).At a) ⋆ F) s.dmem)
    (hk' : Eventually (step1 Host.exe) final ⟨setRegister s rD v, Host.addrOf (k + e)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + j)⟩

theorem stepLoadValueKind_of (C : Program) (rD rB : Reg64) (disp : Int64) (j e : Nat) (q : Program)
    (hq : ∀ k, C.IsInfixAt Host.prog k → q.IsInfixAt Host.prog (k + j)) (he : eraseNop q = [instrLoad rD rB disp])
    (hend : j + q.length = e) : stepLoadValueKind C rD rB disp j e :=
  fun k hk _ => step_load_value rD rB disp q (k + j) (k + e) (hq k hk) he (by omega)

set_option linter.unusedVariables false in
/-- Kind of `step_store`: `mov %rS,disp(%rB)`. -/
abbrev stepStoreKind (C : Program) (rS rB : Reg64) (disp : Int64) (j e : Nat) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k)
    (base a : BitVec 64) (ha : base + disp.toBitVec = a) (bs : List UInt8) (hbs : bs.length = 8)
    (F : DataMem → Prop)
    (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 rB = base) (hm : (Eq (bs.At a) ⋆ F) s.dmem)
    (hk' : ∀ m' : DataMem, (Eq ((Int.toBytes 8 (@BitVec.toInt 64 (s.regs.get64 rS))).At a) ⋆ F) m' →
      Eventually (step1 Host.exe) final ⟨{ s with dmem := m' }, Host.addrOf (k + e)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + j)⟩

theorem stepStoreKind_of (C : Program) (rS rB : Reg64) (disp : Int64) (j e : Nat) (q : Program)
    (hq : ∀ k, C.IsInfixAt Host.prog k → q.IsInfixAt Host.prog (k + j)) (he : eraseNop q = [instrStore rS rB disp])
    (hend : j + q.length = e) : stepStoreKind C rS rB disp j e :=
  fun k hk _ => step_store rS rB disp q (k + j) (k + e) (hq k hk) he (by omega)

set_option linter.unusedVariables false in
/-- Kind of `step_lea`: `lea disp(%rB),%rD`. -/
abbrev stepLeaKind (C : Program) (rD rB : Reg64) (disp : Int64) (j e : Nat) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k)
    (final : MachineState → Prop) (s : MachineData)
    (hk' : Eventually (step1 Host.exe) final ⟨setRegister s rD (s.regs.get64 rB + disp.toBitVec), Host.addrOf (k + e)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + j)⟩

theorem stepLeaKind_of (C : Program) (rD rB : Reg64) (disp : Int64) (j e : Nat) (q : Program)
    (hq : ∀ k, C.IsInfixAt Host.prog k → q.IsInfixAt Host.prog (k + j)) (he : eraseNop q = [instrLea rD rB disp])
    (hend : j + q.length = e) : stepLeaKind C rD rB disp j e :=
  fun k hk _ final s h => step_lea rD rB disp q (k + j) (k + e) (hq k hk) he (by omega) final s h

set_option linter.unusedVariables false in
/-- Kind of `step_add_immediate`: `add $imm,%rD`. -/
abbrev stepAddKind (C : Program) (rD : Reg64) (imm : Int64) (j e : Nat) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k)
    (final : MachineState → Prop) (s : MachineData)
    (hk' : ∀ fl : StatusFlags, Eventually (step1 Host.exe) final
      ⟨{ regs := s.regs.set64 rD (s.regs.get64 rD + imm.toBitVec), zmms := s.zmms, status := fl, dmem := s.dmem },
        Host.addrOf (k + e)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + j)⟩

theorem stepAddKind_of (C : Program) (rD : Reg64) (imm : Int64) (j e : Nat) (q : Program)
    (hq : ∀ k, C.IsInfixAt Host.prog k → q.IsInfixAt Host.prog (k + j)) (he : eraseNop q = [instrAddImmediate rD imm])
    (hend : j + q.length = e) : stepAddKind C rD imm j e :=
  fun k hk _ final s h => step_add_immediate rD imm q (k + j) (k + e) (hq k hk) he (by omega) final s h

set_option linter.unusedVariables false in
/-- Kind of `step_move_immediate`: `mov $imm,%eD`. -/
abbrev stepMoveImmediateKind (C : Program) (rD : Reg64) (imm : Int64) (j e : Nat) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k)
    (final : MachineState → Prop) (s : MachineData)
    (hk' : Eventually (step1 Host.exe) final ⟨setRegister s rD (BitVec.zeroExtend 64 (BitVec.truncate 32 imm.toBitVec)), Host.addrOf (k + e)⟩),
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (k + j)⟩

theorem stepMoveImmediateKind_of (C : Program) (rD : Reg64) (imm : Int64) (j e : Nat) (q : Program)
    (hq : ∀ k, C.IsInfixAt Host.prog k → q.IsInfixAt Host.prog (k + j)) (he : eraseNop q = [instrMoveImmediate32 rD imm])
    (hend : j + q.length = e) : stepMoveImmediateKind C rD imm j e :=
  fun k hk _ final s h => step_move_immediate rD imm q (k + j) (k + e) (hq k hk) he (by omega) final s h

end Codec
