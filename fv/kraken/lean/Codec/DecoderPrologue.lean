import Codec.WindowSteps
import Codec.DecoderHeadEpilogue

/-!
# Frame-parametric prologue, return and nil-check step

The prologue of every development decoder (directives 0–10) is the same up to the frame size `F`, the
displacement `dB` of the first rbx spill, the SSZ size `sz` and the labels. The `--gen2` and `--gen3` methods had one head lemma for
the frame `0x20` (`Codec.dechead_seg`) and one hand lemma per call-field type (`pw_head`, `bh_head0`,
`sm_head0`, `pc_head`; epilogues `pw_epi`, `pc_epi`). Here:

* `decpro_seg fn l0 lmore lerr F dB sz` — the prologue over a window (`Codec/NopWindow.lean`; the `nop` at directive
  8 is a window nop), with `F`, `dB`, `sz` symbolic; every register except rsp / rbp is kept (register clause);
* `kstep_nilchk rB` — the step `test %al,(%rB)`;
* `decret_seg` — `pop %rbp; retq` over a window.
The spills after the prologue (2–3, order differs per type) are `kstep_st` steps; the epilogue reloads and the
`add $F,%rsp` are `kstep_ld*` / `kstep_add` steps (`Codec/WindowSteps.lean`). `Prysm/SyncCommitteeMessage/DecoderPrologueInstances.lean` re-proves the per-type hand
lemmas with their committed statements from these. No runtime contract is used.
-/

open Machine Runtime

namespace Codec

/-- The fixed prologue of a decoder (directives 0–10 of the development decoders without the padding `nop`):
two labels, stack-guard check, `push %rbp; mov %rsp,%rbp; sub $F,%rsp`, the first spill `mov %rbx,dB(%rsp)`,
the size check `cmp $sz,%rcx; jne lerr`. Frame size `F`, spill displacement `dB` and SSZ size `sz` are parameters. -/
def decPro (fn l0 lmore lerr : String) (F dB sz : Int64) : Program :=
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
       (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rsp Width.W64))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.sub (RegOrMem.reg (Reg.low Reg64.rsp Width.W64)) (Operand.imm (ConstExpr.int64 F)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rsp)) none (ConstExpr.int64 dB)))
       (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rbx Width.W64))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.cmp (RegOrMem.reg (Reg.low Reg64.rcx Width.W64)) (Operand.imm (ConstExpr.int64 sz)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64 (Operation.jcc CondCode.nz lerr))]

/-- `pop %rbp; retq`. -/
def decRet : Program :=
  [Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.pop (RegOrMem.reg (Reg.low Reg64.rbp Width.W64)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64 Operation.ret)]

/-- `test %al,(%rB)`: the nil check of the receiver. -/
def iNilChk (rB : Reg64) : Directive :=
  Kraken.Directive.instr (Instr.regular Width.W64 Width.W8
    (Operation.test (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg rB)) none (ConstExpr.int64 0)))
      (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rax Width.W8)))))

variable [Host]

/-- Closing step for register equations of the frame lemmas. -/
local macro "g4_regclose" : tactic => `(tactic| first
  | rfl
  | (apply UInt64.toBitVec_inj.mp; rfl)
  | (apply UInt64.toBitVec_inj.mp; bv_omega)
  | (apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_sub, UInt64.toBitVec_ofNat]; bv_omega))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Prologue segment, frame-parametric**: the window `q` at `j` holds `decPro …` and nops. With `rcx = sz`
and the stack guard below rsp: rsp = `sp = rsp₀ − 8 − F`, rbp = `rsp₀ − 8`, the caller's rbp is saved at
`rsp₀ − 8`, rbx is spilled to `aS = sp + dB`; every register except rsp and rbp is kept. -/
theorem decpro_seg (fn l0 lmore lerr : String) (F dB sz : Int64) (q : Program) (j e : Nat)
    (hq : q.IsInfixAt Host.prog j) (he : eraseNop q = decPro fn l0 lmore lerr F dB sz) (hend : j + q.length = e)
    (s : MachineData) (ra guard : UInt64) (sp aS : BitVec 64)
    (hsp : s.regs.rsp.toBitVec - 8 - F.toBitVec = sp) (hS : sp + dB.toBitVec = aS)
    (fp s2 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At aS)
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16)) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx = { toBitVec := sz.toBitVec }) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf e ∧ st.data.regs.rsp = { toBitVec := sp }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ (∀ r : Reg64, r ≠ Reg64.rsp → r ≠ Reg64.rbp → st.data.regs.get64 r = s.regs.get64 r) ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At aS)
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf j⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen hsp ⊢
  subst hlen hsp hS
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; simp only [UInt64.size] at *
  kwin hq
  kwat hq he decPro 0
  kwnx hq he 0
  kwat hq he decPro 1
  kwnx hq he 1
  kwat hq he decPro 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kwnx hq he 2
  kwat hq he decPro 3
  split
  · rename_i h; exfalso
    simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kwnx hq he 3
  kwat hq he decPro 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1' H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kwnx hq he 4
  kwat hq he decPro 5
  kwnx hq he 5
  kwat hq he decPro 6
  kwnx hq he 6
  kwat hq he decPro 7
  apply store_step_at _ _ (rsp.toBitVec - 8 - F.toBitVec + dB.toBitVec) _ _ _ s2 _ _ (by first | rfl | bv_omega)
    (by ecancel) (by exact h2)
  intro m2' H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kwnx hq he 7
  kwat hq he decPro 8
  kwnx hq he 8
  kwat hq he decPro 9
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kwend hq he 9 hend
  apply Eventually.done
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · g4_regclose
  · g4_regclose
  · intro r h1 h2
    cases r <;> first | rfl | exact absurd rfl h1 | exact absurd rfl h2
  · ecancel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Return segment**: the window `q` at `j` holds `pop %rbp; retq` and nops. With rsp = `sp`, the saved frame
pointer `fp0` at `sp` and the return address `ra` at `aRa = sp + 8`: the pc is `ra`, rsp = `sp + 16`,
rbp = `fp0`; every other register and the memory are kept. -/
theorem decret_seg (q : Program) (j : Nat) (hq : q.IsInfixAt Host.prog j) (he : eraseNop q = decRet)
    (sp aRa : BitVec 64) (hRa : sp + 8 = aRa) (fp0 ra : UInt64) (R : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp })
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 fp0.toBitVec.toInt).At sp)
      ⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At aRa) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rsp = { toBitVec := sp + 16 }
        ∧ st.data.regs.rbp = fp0
        ∧ (∀ r : Reg64, r ≠ Reg64.rsp → r ≠ Reg64.rbp → st.data.regs.get64 r = s.regs.get64 r)
        ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf j⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp h_mem ⊢
  subst rsp hRa
  kwin hq
  kwat hq he decRet 0
  apply load_step_at _ _ sp _ _ (Int.toBytes 8 fp0.toBitVec.toInt) _ _ (by first | rfl | saddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kwnx hq he 0
  kwat hq he decRet 1
  apply load_step_at _ _ (sp + 8) _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by first | rfl | saddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · first
    | exact trivial
    | with_reducible rfl
    | rfl
  · first
    | rfl
    | (apply UInt64.toBitVec_inj.mp
       simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, Width.bits]
       done)
    | (apply UInt64.toBitVec_inj.mp; saddr)
  · first | rfl | (apply UInt64.toBitVec_inj.mp; rfl)
  · intro r h1 h2
    cases r <;> first | rfl | exact absurd rfl h1 | exact absurd rfl h2
  · rfl

/-- **Step: `test %al,(%rB)`** (nil check): one byte `bs` at `base` (the value of `rB`) is read; the status
flags after it are not stated (`∀ fl`). -/
theorem kstep_nilchk (rB : Reg64) (q : Program) (j e : Nat) (hq : q.IsInfixAt Host.prog j)
    (he : eraseNop q = [iNilChk rB]) (hend : j + q.length = e)
    (base : BitVec 64) (bs : List UInt8) (hbs : bs.length = 1)
    (F : DataMem → Prop) (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 rB = base) (hm : (Eq (bs.At base) ⋆ F) s.dmem)
    (hk : ∀ fl : StatusFlags, Eventually (step1 Host.exe) final
      ⟨{ regs := s.regs, zmms := s.zmms, status := fl, dmem := s.dmem }, Host.addrOf e⟩) :
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf j⟩ := by
  subst hb
  kwin hq
  have hd : [iNilChk rB].IsInfixAt Host.prog (j + nopPos q 0) := wat hq he 0
  unfold iNilChk at hd
  apply Machine.estep hd
  kunf
  apply load_step_at _ _ (s.regs.get64 rB) _ _ bs _ _ (by first | rfl | simp) hm (by exact hbs)
  kunf
  intro _
  kwend hq he 0 hend
  exact hk _

end Codec
