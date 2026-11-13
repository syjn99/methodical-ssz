import Codec.DecoderPrologue
import Codec.StackGuard
import Codec.EncodeMemmove
import Machine.StoreLemmas
import Runtime.StaticBoxLemmas

/-!
# Step lemmas for the encoder fast path (window form, registers as parameters)

The fast path of a flat `MarshalSSZTo` is straight-line code with three kinds of branch. Each has ONE lemma
whose premise is the fact that decides the branch; a `runtime.growslice` directive is never stepped:

* `kstep_cmp_jae_t rC rN l` — `cmp %rN,%rC; jae l` with `N ≤ C` (unsigned): control is at `l` (the capacity
  test passed; the growslice block between the `jae` and `l` is jumped over);
* `kstep_cmp_jb_f rC rN l` — `cmp %rN,%rC; jb l` with `N ≤ C`: control falls through (the growslice block is
  at `l`);
* `kstep_lenchk rB d n l` — `cmpq $n,d(%rB); jne l` when the slot holds `n`: control falls through (the length
  reject is at `l`).

Straight-line forms not in `Codec/WindowSteps.lean`: `kstep_lea_idx` (`lea (%rB,%rI,1),%rD`), `kstep_add_rr`
(`add %rS,%rD`), `kstep_st_idx` (`mov %rS,d(%rB,%rI,1)`), `kstep_movups15` (`movups %xmm15,d(%rB)`),
`kstep_xor32` (`xor %eD,%eD`), `kstep_sub_i` (`sub $i,%rD`).
Frame: `encpro_s` (small stack guard) and `encpro_l` (large-frame guard `lea -N(%rsp),%r12`): labels, guard,
`push %rbp`, `mov %rsp,%rbp`; the frame allocation and the spills are steps. `encn_call`: the
`callq runtime.memmove` block for any length (`enc32_call` is the 32-byte case), contract `MemmoveC` in its
existing form. The return is `decret_seg` (`Codec/DecoderPrologue.lean`).
All lemmas are in the continuation form of `Codec/WindowSteps.lean`; nops may be anywhere in a window.
-/

open Machine Runtime

namespace Codec

/-- `cmp %rN,%rC` (flags of `C − N`). -/
def iCmpRR (rC rN : Reg64) : Directive :=
  Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
    (Operation.cmp (RegOrMem.reg (Reg.low rC Width.W64)) (Operand.regOrMem (RegOrMem.reg (Reg.low rN Width.W64)))))
/-- `jcc l`. -/
def iJcc (cc : CondCode) (l : String) : Directive :=
  Kraken.Directive.instr (Instr.regular Width.W64 Width.W64 (Operation.jcc cc l))
/-- `cmpq $imm,disp(%rB)`. -/
def iCmpMI (rB : Reg64) (disp imm : Int64) : Directive :=
  Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
    (Operation.cmp (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg rB)) none (ConstExpr.int64 disp)))
      (Operand.imm (ConstExpr.int64 imm))))
/-- `lea (%rB,%rI,1),%rD`. -/
def iLeaIdx (rD rB rI : Reg64) : Directive :=
  Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
    (Operation.lea (Reg.low rD Width.W64)
      (AddrExpr.mk (some (RegOrRip.reg rB)) (some (AddrIndex.mk rI Width.W8)) (ConstExpr.int64 0))))
/-- `add %rS,%rD`. -/
def iAddRR (rD rS : Reg64) : Directive :=
  Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
    (Operation.add (RegOrMem.reg (Reg.low rD Width.W64)) (Operand.regOrMem (RegOrMem.reg (Reg.low rS Width.W64)))))
/-- `mov %rS,disp(%rB,%rI,1)`. -/
def iStIdx (rS rB rI : Reg64) (disp : Int64) : Directive :=
  Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
    (Operation.mov (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg rB)) (some (AddrIndex.mk rI Width.W8))
        (ConstExpr.int64 disp)))
      (Operand.regOrMem (RegOrMem.reg (Reg.low rS Width.W64)))))
/-- `movups %xmm15,disp(%rB)`. -/
def iMovups15 (rB : Reg64) (disp : Int64) : Directive :=
  Kraken.Directive.instr (Instr.avx Width.W64 AvxWidth.W128
    (AvxOperation.movups (AvxRegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg rB)) none (ConstExpr.int64 disp)))
      (AvxRegOrMem.avx (AvxReg.xmm RegMm.mm15))))
/-- `xor %eD,%eD`. -/
def iXor32 (rD : Reg64) : Directive :=
  Kraken.Directive.instr (Instr.regular Width.W64 Width.W32
    (Operation.xor (RegOrMem.reg (Reg.low rD Width.W32)) (Operand.regOrMem (RegOrMem.reg (Reg.low rD Width.W32)))))
/-- `sub $imm,%rD`. -/
def iSubI (rD : Reg64) (imm : Int64) : Directive :=
  Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
    (Operation.sub (RegOrMem.reg (Reg.low rD Width.W64)) (Operand.imm (ConstExpr.int64 imm))))

/-- Labels, small stack guard, `push %rbp`, `mov %rsp,%rbp`. -/
def encProS (fn l0 lmore : String) : Program :=
  [Kraken.Directive.label fn,
   Kraken.Directive.label l0,
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.cmp (RegOrMem.reg (Reg.low Reg64.rsp Width.W64))
       (Operand.regOrMem (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.r14)) none (ConstExpr.int64 16)))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64 (Operation.jcc CondCode.be lmore)),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.push (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rbp Width.W64))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.reg (Reg.low Reg64.rbp Width.W64))
       (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rsp Width.W64)))))]

/-- Labels, large-frame stack guard (`lea N(%rsp),%r12`, `N` negative), `push %rbp`, `mov %rsp,%rbp`. -/
def encProL (fn l0 lmore : String) (N : Int64) : Program :=
  [Kraken.Directive.label fn,
   Kraken.Directive.label l0,
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.lea (Reg.low Reg64.r12 Width.W64) (AddrExpr.mk (some (RegOrRip.reg Reg64.rsp)) none (ConstExpr.int64 N)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.cmp (RegOrMem.reg (Reg.low Reg64.r12 Width.W64))
       (Operand.regOrMem (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.r14)) none (ConstExpr.int64 16)))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64 (Operation.jcc CondCode.be lmore)),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.push (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rbp Width.W64))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.reg (Reg.low Reg64.rbp Width.W64))
       (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rsp Width.W64)))))]

/-- `cmp b,a; jb` is not taken when `b ≤ a` (unsigned). -/
theorem cmp_c_false (a b : BitVec 64) (af of' : Bool) (h : b.toNat ≤ a.toNat) :
    CondCode.c.interp (StatusFlags.from_result (a - b)
      { cf := BitVec.unsigned (a - b) != a.unsigned - b.unsigned, af := af, of := of' }) = false := by
  have hle : b ≤ a := by rw [BitVec.le_def]; omega
  have hs : (a - b).toNat = a.toNat - b.toNat := BitVec.toNat_sub_of_le hle
  simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, hs]
  simp; omega

/-- `cmp b,a; jae` is taken when `b ≤ a` (unsigned). -/
theorem cmp_nc_true (a b : BitVec 64) (af of' : Bool) (h : b.toNat ≤ a.toNat) :
    CondCode.nc.interp (StatusFlags.from_result (a - b)
      { cf := BitVec.unsigned (a - b) != a.unsigned - b.unsigned, af := af, of := of' }) = true := by
  have hle : b ≤ a := by rw [BitVec.le_def]; omega
  have hs : (a - b).toNat = a.toNat - b.toNat := BitVec.toNat_sub_of_le hle
  simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, hs]
  simp; omega

/-- `cmp a,a; jne` is not taken. -/
theorem cmp_nz_false (a : BitVec 64) (cf af of' : Bool) :
    CondCode.nz.interp (StatusFlags.from_result (a - a) { cf := cf, af := af, of := of' }) = false := by
  simp [CondCode.interp, StatusFlags.from_result]

variable [Host]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Step: `cmp %rN,%rC; jae l` taken** (`N ≤ C`, unsigned): control is at the label `l` (index `jl`). The
directives between the `jae` and `l` are not executed. -/
theorem kstep_cmp_jae_t (rC rN : Reg64) (l : String) (q : Program) (j jl : Nat) (hq : q.IsInfixAt Host.prog j)
    (he : eraseNop q = [iCmpRR rC rN, iJcc CondCode.nc l]) (hl : label l = Host.addrOf jl)
    (final : MachineState → Prop) (s : MachineData)
    (hle : (s.regs.get64 rN).toNat ≤ (s.regs.get64 rC).toNat)
    (hk : ∀ fl : StatusFlags, Eventually (step1 Host.exe) final
      ⟨{ regs := s.regs, zmms := s.zmms, status := fl, dmem := s.dmem }, Host.addrOf jl⟩) :
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf j⟩ := by
  kwin hq
  have hd : [iCmpRR rC rN].IsInfixAt Host.prog (j + nopPos q 0) := wat hq he 0
  unfold iCmpRR at hd
  apply Machine.estep hd
  kunf
  kwnx hq he 0
  have hd2 : [iJcc CondCode.nc l].IsInfixAt Host.prog (j + nopPos q 1) := wat hq he 1
  unfold iJcc at hd2
  apply Machine.estep hd2
  kunf
  rw [if_pos (cmp_nc_true _ _ _ _ hle)]
  simp only [Effects.All]
  rw [hl]
  exact hk _

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Step: `cmp %rN,%rC; jb l` not taken** (`N ≤ C`, unsigned): control falls through to the window end. -/
theorem kstep_cmp_jb_f (rC rN : Reg64) (l : String) (q : Program) (j e : Nat) (hq : q.IsInfixAt Host.prog j)
    (he : eraseNop q = [iCmpRR rC rN, iJcc CondCode.c l]) (hend : j + q.length = e)
    (final : MachineState → Prop) (s : MachineData)
    (hle : (s.regs.get64 rN).toNat ≤ (s.regs.get64 rC).toNat)
    (hk : ∀ fl : StatusFlags, Eventually (step1 Host.exe) final
      ⟨{ regs := s.regs, zmms := s.zmms, status := fl, dmem := s.dmem }, Host.addrOf e⟩) :
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf j⟩ := by
  kwin hq
  have hd : [iCmpRR rC rN].IsInfixAt Host.prog (j + nopPos q 0) := wat hq he 0
  unfold iCmpRR at hd
  apply Machine.estep hd
  kunf
  kwnx hq he 0
  have hd2 : [iJcc CondCode.c l].IsInfixAt Host.prog (j + nopPos q 1) := wat hq he 1
  unfold iJcc at hd2
  apply Machine.estep hd2
  kunf
  rw [if_neg (by rw [cmp_c_false _ _ _ _ hle]; exact Bool.false_ne_true)]
  simp only [Effects.All]
  kwend hq he 1 hend
  exact hk _

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Step: `cmpq $imm,disp(%rB); jne l` not taken**: the 8 bytes `bs` at `a = base + disp` hold `imm`. -/
theorem kstep_lenchk (rB : Reg64) (disp imm : Int64) (l : String) (q : Program) (j e : Nat)
    (hq : q.IsInfixAt Host.prog j) (he : eraseNop q = [iCmpMI rB disp imm, iJcc CondCode.nz l])
    (hend : j + q.length = e)
    (base a : BitVec 64) (ha : base + disp.toBitVec = a) (bs : List UInt8) (hbs : bs.length = 8)
    (hv : BitVec.ofInt 64 (Int.ofBytes bs) = imm.toBitVec)
    (F : DataMem → Prop) (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 rB = base) (hm : (Eq (bs.At a) ⋆ F) s.dmem)
    (hk : ∀ fl : StatusFlags, Eventually (step1 Host.exe) final
      ⟨{ regs := s.regs, zmms := s.zmms, status := fl, dmem := s.dmem }, Host.addrOf e⟩) :
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf j⟩ := by
  subst ha hb
  kwin hq
  have hd : [iCmpMI rB disp imm].IsInfixAt Host.prog (j + nopPos q 0) := wat hq he 0
  unfold iCmpMI at hd
  apply Machine.estep hd
  kunf
  apply load_step_at _ _ (s.regs.get64 rB + disp.toBitVec) _ _ bs _ _ rfl hm (by exact hbs)
  kunf
  rw [hv]
  kwnx hq he 0
  have hd2 : [iJcc CondCode.nz l].IsInfixAt Host.prog (j + nopPos q 1) := wat hq he 1
  unfold iJcc at hd2
  apply Machine.estep hd2
  kunf
  rw [if_neg (by rw [cmp_nz_false]; exact Bool.false_ne_true)]
  simp only [Effects.All]
  kwend hq he 1 hend
  exact hk _

/-- **Step: `lea (%rB,%rI,1),%rD`**. -/
theorem kstep_lea_idx (rD rB rI : Reg64) (q : Program) (j e : Nat) (hq : q.IsInfixAt Host.prog j)
    (he : eraseNop q = [iLeaIdx rD rB rI]) (hend : j + q.length = e) (final : MachineState → Prop) (s : MachineData)
    (hk : Eventually (step1 Host.exe) final ⟨setR s rD (s.regs.get64 rB + s.regs.get64 rI), Host.addrOf e⟩) :
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf j⟩ := by
  kwin hq
  have hd : [iLeaIdx rD rB rI].IsInfixAt Host.prog (j + nopPos q 0) := wat hq he 0
  unfold iLeaIdx at hd
  apply Machine.estep hd
  kunf
  simp only [Machine.ofInt_sib, BitVec.mul_one, Machine.add_int64_zero]
  kwend hq he 0 hend
  exact hk

/-- **Step: `add %rS,%rD`**; the status flags after it are not stated (`∀ fl`). -/
theorem kstep_add_rr (rD rS : Reg64) (q : Program) (j e : Nat) (hq : q.IsInfixAt Host.prog j)
    (he : eraseNop q = [iAddRR rD rS]) (hend : j + q.length = e) (final : MachineState → Prop) (s : MachineData)
    (hk : ∀ fl : StatusFlags, Eventually (step1 Host.exe) final
      ⟨{ regs := s.regs.set64 rD (s.regs.get64 rD + s.regs.get64 rS), zmms := s.zmms, status := fl, dmem := s.dmem },
        Host.addrOf e⟩) :
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf j⟩ := by
  kwin hq
  have hd : [iAddRR rD rS].IsInfixAt Host.prog (j + nopPos q 0) := wat hq he 0
  unfold iAddRR at hd
  apply Machine.estep hd
  kunf
  simp only [BitVec.add_comm (s.regs.get64 rS) (s.regs.get64 rD)]
  kwend hq he 0 hend
  exact hk _

/-- **Step: `sub $imm,%rD`**; the status flags after it are not stated (`∀ fl`). -/
theorem kstep_sub_i (rD : Reg64) (imm : Int64) (q : Program) (j e : Nat) (hq : q.IsInfixAt Host.prog j)
    (he : eraseNop q = [iSubI rD imm]) (hend : j + q.length = e) (final : MachineState → Prop) (s : MachineData)
    (hk : ∀ fl : StatusFlags, Eventually (step1 Host.exe) final
      ⟨{ regs := s.regs.set64 rD (s.regs.get64 rD - imm.toBitVec), zmms := s.zmms, status := fl, dmem := s.dmem },
        Host.addrOf e⟩) :
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf j⟩ := by
  kwin hq
  have hd : [iSubI rD imm].IsInfixAt Host.prog (j + nopPos q 0) := wat hq he 0
  unfold iSubI at hd
  apply Machine.estep hd
  kunf
  kwend hq he 0 hend
  exact hk _

/-- **Step: `xor %eD,%eD`**: `rD` is 0; the status flags after it are not stated (`∀ fl`). -/
theorem kstep_xor32 (rD : Reg64) (q : Program) (j e : Nat) (hq : q.IsInfixAt Host.prog j)
    (he : eraseNop q = [iXor32 rD]) (hend : j + q.length = e) (final : MachineState → Prop) (s : MachineData)
    (hk : ∀ fl : StatusFlags, Eventually (step1 Host.exe) final
      ⟨{ regs := s.regs.set64 rD 0, zmms := s.zmms, status := fl, dmem := s.dmem }, Host.addrOf e⟩) :
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf j⟩ := by
  kwin hq
  have hd : [iXor32 rD].IsInfixAt Host.prog (j + nopPos q 0) := wat hq he 0
  unfold iXor32 at hd
  apply Machine.estep hd
  kunf
  intro af
  simp only [BitVec.xor_self]
  kwend hq he 0 hend
  exact hk _

/-- **Step: `mov %rS,disp(%rB,%rI,1)`**: the slot `a = base + idx + disp` (8 bytes `bs`) gets the value of `rS`. -/
theorem kstep_st_idx (rS rB rI : Reg64) (disp : Int64) (q : Program) (j e : Nat)
    (hq : q.IsInfixAt Host.prog j) (he : eraseNop q = [iStIdx rS rB rI disp]) (hend : j + q.length = e)
    (base idx a : BitVec 64) (ha : base + idx + disp.toBitVec = a) (bs : List UInt8) (hbs : bs.length = 8)
    (F : DataMem → Prop) (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 rB = base) (hi : s.regs.get64 rI = idx) (hm : (Eq (bs.At a) ⋆ F) s.dmem)
    (hk : ∀ m' : DataMem, (Eq ((Int.toBytes 8 (@BitVec.toInt 64 (s.regs.get64 rS))).At a) ⋆ F) m' →
      Eventually (step1 Host.exe) final ⟨{ s with dmem := m' }, Host.addrOf e⟩) :
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf j⟩ := by
  subst ha hb hi
  kwin hq
  have hd : [iStIdx rS rB rI disp].IsInfixAt Host.prog (j + nopPos q 0) := wat hq he 0
  unfold iStIdx at hd
  apply Machine.estep hd
  kunf
  simp only [Machine.ofInt_sib, BitVec.mul_one]
  apply store_step_at _ _ (s.regs.get64 rB + s.regs.get64 rI + disp.toBitVec) _ _ _ bs _ _ rfl hm (by exact hbs)
  intro m' H
  simp only [Width.bytes, Width.bits] at H
  try kunf
  kwend hq he 0 hend
  exact hk m' H

/-- **Step: `movups %xmm15,disp(%rB)`**: the 16 bytes `bs` at `a = base + disp` get the low 128 bits of X15. -/
theorem kstep_movups15 (rB : Reg64) (disp : Int64) (q : Program) (j e : Nat)
    (hq : q.IsInfixAt Host.prog j) (he : eraseNop q = [iMovups15 rB disp]) (hend : j + q.length = e)
    (base a : BitVec 64) (ha : base + disp.toBitVec = a) (bs : List UInt8) (hbs : bs.length = 16)
    (F : DataMem → Prop) (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 rB = base) (hm : (Eq (bs.At a) ⋆ F) s.dmem)
    (hk : ∀ m' : DataMem, (Eq ((Int.toBytes 16 (s.zmms.get (AvxReg.xmm RegMm.mm15)).toInt).At a) ⋆ F) m' →
      Eventually (step1 Host.exe) final ⟨{ s with dmem := m' }, Host.addrOf e⟩) :
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf j⟩ := by
  subst ha hb
  kwin hq
  have hd : [iMovups15 rB disp].IsInfixAt Host.prog (j + nopPos q 0) := wat hq he 0
  unfold iMovups15 at hd
  apply Machine.estep hd
  kunf
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  kunf
  refine Machine.store_avx_step _ (s.regs.get64 rB + disp.toBitVec) _ _ bs _ _ hm (by exact hbs) (by decide) ?_
  intro m' H
  try kunf
  kwend hq he 0 hend
  exact hk m' H

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Prologue, small stack guard**: the window holds `encProS …` and nops. With the guard below rsp: the
caller's rbp is saved at `rsp − 8`; rsp = rbp = `rsp − 8`; the flags are not stated. -/
theorem encpro_s (fn l0 lmore : String) (q : Program) (j e : Nat)
    (hq : q.IsInfixAt Host.prog j) (he : eraseNop q = encProS fn l0 lmore) (hend : j + q.length = e)
    (guard : UInt64) (fp : List UInt8) (hfp : fp.length = 8)
    (F : DataMem → Prop) (final : MachineState → Prop) (s : MachineData)
    (hm : (Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16)) ⋆ F) s.dmem)
    (hguard : guard.toNat < s.regs.rsp.toNat)
    (hk : ∀ (m' : DataMem), (Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
        ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16)) ⋆ F) m' →
      ∀ fl : StatusFlags, Eventually (step1 Host.exe) final
        ⟨{ regs := (s.regs.set64 Reg64.rsp (s.regs.rsp.toBitVec - 8)).set64 Reg64.rbp (s.regs.rsp.toBitVec - 8),
           zmms := s.zmms, status := fl, dmem := m' }, Host.addrOf e⟩) :
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf j⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only [Reg64s.set64] at hm hguard hk ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; simp only [UInt64.size] at *
  kwin hq
  kwat hq he encProS 0
  kwnx hq he 0
  kwat hq he encProS 1
  kwnx hq he 1
  kwat hq he encProS 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kwnx hq he 2
  kwat hq he encProS 3
  split
  · rename_i h; exfalso
    rw [Machine.cmp_be_false rsp.toBitVec guard.toBitVec _ _ hguard] at h
    exact Bool.noConfusion h
  simp only [Effects.All]
  kwnx hq he 3
  kwat hq he encProS 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1' H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kwnx hq he 4
  kwat hq he encProS 5
  kwend hq he 5 hend
  exact hk m1' (by ecancel) _

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Prologue, large-frame stack guard** (`lea N(%rsp),%r12`, `−N = n`): the window holds `encProL …` and nops.
With `guard + n < rsp`: the caller's rbp is saved at `rsp − 8`; rsp = rbp = `rsp − 8`; r12 = `rsp + N`. -/
theorem encpro_l (fn l0 lmore : String) (N : Int64) (n : Nat) (q : Program) (j e : Nat)
    (hq : q.IsInfixAt Host.prog j) (he : eraseNop q = encProL fn l0 lmore N) (hend : j + q.length = e)
    (hN : (-N.toBitVec).toNat = n)
    (guard : UInt64) (fp : List UInt8) (hfp : fp.length = 8)
    (F : DataMem → Prop) (final : MachineState → Prop) (s : MachineData)
    (hm : (Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16)) ⋆ F) s.dmem)
    (hguard : guard.toNat + n < s.regs.rsp.toNat)
    (hk : ∀ (m' : DataMem), (Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
        ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16)) ⋆ F) m' →
      ∀ fl : StatusFlags, Eventually (step1 Host.exe) final
        ⟨{ regs := ((s.regs.set64 Reg64.r12 (s.regs.rsp.toBitVec + N.toBitVec)).set64 Reg64.rsp
              (s.regs.rsp.toBitVec - 8)).set64 Reg64.rbp (s.regs.rsp.toBitVec - 8),
           zmms := s.zmms, status := fl, dmem := m' }, Host.addrOf e⟩) :
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf j⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only [Reg64s.set64] at hm hguard hk ⊢
  kwin hq
  kwat hq he encProL 0
  kwnx hq he 0
  kwat hq he encProL 1
  kwnx hq he 1
  kwat hq he encProL 2
  kwnx hq he 2
  kwat hq he encProL 3
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kwnx hq he 3
  kwat hq he encProL 4
  split
  · rename_i h; exfalso
    rw [lea_cmp_be_false rsp.toBitVec _ guard.toBitVec _ _ n hN hguard] at h
    exact Bool.noConfusion h
  simp only [Effects.All]
  kwnx hq he 4
  kwat hq he encProL 5
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1' H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kwnx hq he 5
  kwat hq he encProL 6
  kwend hq he 6 hend
  exact hk m1' (by ecancel) _

set_option maxRecDepth 100000 in
/-- **Encode call block, any length**: at `callq runtime.memmove` (directive `jc`) with `rax = d`, `rbx = p`,
`rcx = n`, the `n` bytes `src` at `p` are copied over the `n` bytes at `d`; control is at `jc + 1`; rsp, rbp
and r14 are kept; the return slot holds the address of `jc + 1`. `enc32_call` is the case `n = 32`. -/
theorem encn_call (jc : Nat) (hc : callMemmove.IsInfixAt Host.prog jc)
    (sp d p aRet aLo : BitVec 64) (S : Nat)
    (hRet : sp - 8 = aRet) (hLo : sp - 8 - BitVec.ofNat 64 S = aLo)
    (src e rslot scratch : List UInt8) (he : e.length = src.length)
    (hrs : rslot.length = 8) (hsc : scratch.length = S)
    (R : DataMem → Prop) (s : MachineData)
    (hrsp : s.regs.rsp = { toBitVec := sp }) (hrax : s.regs.rax.toBitVec = d)
    (hrbx : s.regs.rbx.toBitVec = p) (hrcx : s.regs.rcx.toNat = src.length)
    (h_mem : s.dmem =⋆ Eq (rslot.At aRet) ⋆ Eq (scratch.At aLo) ⋆ Eq (src.At p) ⋆ Eq (e.At d) ⋆ R)
    (hmm : MemmoveC S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (jc + 1) ∧ st.data.regs.rsp = { toBitVec := sp }
        ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ scr : List UInt8, scr.length = S ∧
        (Eq ((Int.toBytes 8 (Host.addrOf (jc + 1)).toBitVec.toInt).At aRet) ⋆ Eq (scr.At aLo)
          ⋆ Eq (src.At p) ⋆ Eq (src.At d) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf jc⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp hrax hrbx hrcx h_mem ⊢
  subst rsp hrax hrbx hRet hLo
  kat hc callMemmove 0
  apply store_step_at _ _ (sp - 8) _ _ _ rslot _ _ (by segment_addr) (by ecancel) (by exact hrs)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  try rw [show sp - 8#64 = sp - 8 from rfl] at *
  rw [show jc + 0 + 1 = jc + 1 from rfl] at H4
  refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (jc + 1)) src e scratch _
    hrcx he hsc (by dsimp only; ecancel)) ?_
  rintro ⟨e1, pc1⟩ ⟨hpc1, hrsp1, hr141, hrbp1, stk1, hstk1, Hm1⟩
  dsimp only at hpc1 hrsp1 hr141 hrbp1 Hm1
  apply Eventually.done
  refine ⟨hpc1, ?_, hrbp1, hr141, stk1, hstk1, by ecancel⟩
  exact hrsp1.trans (by
    apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega)

end Codec
