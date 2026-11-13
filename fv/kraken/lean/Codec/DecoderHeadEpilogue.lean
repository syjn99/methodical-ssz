import Codec.InlineUint64

/-!
# GEN2 L3: shared segments for the composition of a container decoder accept path

The accept path of a protoc container decoder with the frame of the development sites (`sub $0x20,%rsp`,
receiver spill `0x30(%rsp)`, buffer spill `0x38(%rsp)`) is: head, then per field its decode segment
(`bytesdec_seg` / `bytesdec_seg_z` followed by the pointer tail below, or `u64dec_inline_seg`), then the
epilogue. This file has the three pieces that are not a field segment. Each one is a segment lemma of the
form of `Codec/SegmentTemplate.lean` (template + `IsInfixAt` hypothesis); none uses a runtime contract.

* `dechead_seg` — `decHead fn l0 lmore lerr sz` (13 directives: two labels, stack guard, prologue,
  `cmp $sz,%rcx; jne lerr`, the two spills). Statement = the statement of `Prysm.BlobIdentifier.Decode.head` with the
  size `sz` (`hlen : rcx = sz`). The frame size and the spill displacements are literals (the three
  development decoders agree); another frame is not covered.
* `bytesdec_tail_seg` — the code after the `jne lwb` of a byte-vector segment when the write barrier is
  off: `bytesDecTailA rY l dS` = `mov dS(%rsp),%rY; jmp l` and `bytesDecTailB rY l fP` =
  `l: mov %rY,fP(%rdx)` (the write-barrier block between them is skipped). `rY` is rsi or rdi at the
  development sites; the lemma takes any register of `U64InlineReg`.
* `decepi_seg` — `decEpi` = `xor %eax,%eax; xor %ebx,%ebx; add $0x20,%rsp; pop %rbp; retq`.

A composed accept theorem is a chain of `eventually_trans` over these lemmas; the frame of each step is an
explicit instance (`Prysm/BlobIdentifier/DecodeAcceptComposedExample.lean` has one worked example). There is no generic combinator over a list
of segments.
-/

open Machine Runtime

namespace Codec

/-- Head of a container decoder (directives 0–12 of the development decoders), SSZ size `sz`. -/
def decHead (fn l0 lmore lerr : String) (sz : Int64) : Program :=
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
     (Operation.sub (RegOrMem.reg (Reg.low Reg64.rsp Width.W64)) (Operand.imm (ConstExpr.int64 32)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rsp)) none (ConstExpr.int64 56)))
       (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rbx Width.W64))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64 (Operation.nop 1)),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.cmp (RegOrMem.reg (Reg.low Reg64.rcx Width.W64)) (Operand.imm (ConstExpr.int64 sz)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64 (Operation.jcc CondCode.nz lerr)),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rsp)) none (ConstExpr.int64 48)))
       (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rax Width.W64))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rsp)) none (ConstExpr.int64 56)))
       (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rbx Width.W64)))))]

/-- Pointer tail of a byte-vector segment, first part: `mov dS(%rsp),%rY; jmp l`. -/
def bytesDecTailA (rY : Reg64) (l : String) (dS : Int64) : Program :=
  [Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.reg (Reg.low rY Width.W64))
       (Operand.regOrMem (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rsp)) none (ConstExpr.int64 dS)))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.jmp (RelRegOrMem.rel ((ConstExpr.label l).sub ConstExpr.after_current_instruction))))]

/-- Pointer tail of a byte-vector segment, second part: `l: mov %rY,fP(%rdx)`. -/
def bytesDecTailB (rY : Reg64) (l : String) (fP : Int64) : Program :=
  [Kraken.Directive.label l,
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rdx)) none (ConstExpr.int64 fP)))
       (Operand.regOrMem (RegOrMem.reg (Reg.low rY Width.W64)))))]

/-- Epilogue of a container decoder on the accept path (5 directives), frame `0x20`. -/
def decEpi : Program :=
  [Kraken.Directive.instr (Instr.regular Width.W64 Width.W32
     (Operation.xor (RegOrMem.reg (Reg.low Reg64.rax Width.W32))
       (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rax Width.W32))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W32
     (Operation.xor (RegOrMem.reg (Reg.low Reg64.rbx Width.W32))
       (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rbx Width.W32))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.add (RegOrMem.reg (Reg.low Reg64.rsp Width.W64)) (Operand.imm (ConstExpr.int64 32)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.pop (RegOrMem.reg (Reg.low Reg64.rbp Width.W64)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64 Operation.ret)]

variable [Host]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Head segment**: from the entry through the stack guard, the prologue, the size check
(`rcx = sz`) and the two spills to directive `j + 13`. The statement is that of
`Prysm.BlobIdentifier.Decode.head` with the template and the size as parameters. -/
theorem dechead_seg (fn l0 lmore lerr : String) (sz : Int64) (j : Nat)
    (hA : (decHead fn l0 lmore lerr sz).IsInfixAt Host.prog j)
    (s : MachineData) (ra guard : UInt64) (fp s1 s2 : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16)) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx = { toBitVec := sz.toBitVec }) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (j + 13) ∧ st.data.regs.rsp = s.regs.rsp - 40
        ∧ st.data.regs.rbp = s.regs.rsp - 8 ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.rax = s.regs.rax ∧ st.data.regs.rbx = s.regs.rbx ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf j⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  subst hlen
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; simp only [UInt64.size] at *
  kat hA decHead 0
  kat hA decHead 1
  kat hA decHead 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hA decHead 3
  split
  · rename_i h; exfalso
    simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hA decHead 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1' H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hA decHead 5
  kat hA decHead 6
  kat hA decHead 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by bv_omega) (by ecancel) (by exact h2)
  intro m2' H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hA decHead 8
  kat hA decHead 9
  kat hA decHead 10
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hA decHead 11
  apply store_step_at _ _ (rsp.toBitVec + 8) _ _ _ s1 _ _ (by bv_omega) (by ecancel) (by exact h1)
  intro m3' H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hA decHead 12
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by bv_omega) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m4' H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  apply Eventually.done
  refine ⟨rfl, ?_, ?_, rfl, rfl, rfl, ?_⟩
  rotate_right
  · ecancel
  all_goals (apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_sub, UInt64.toBitVec_ofNat]; try rfl)
  all_goals segment_addr

set_option hygiene false in
/-- Proof text of one register case of `bytesdec_tail_seg`. Local to this file. -/
local macro "bytestail_case" : tactic => `(tactic| (
  kat hA bytesDecTailA 0
  apply load_step_at _ _ aS _ _ (Int.toBytes 8 p.toInt) _ _ (by rw [← hS]) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hA bytesDecTailA 1
  rw [hl]
  kat hB bytesDecTailB 0
  kat hB bytesDecTailB 1
  apply store_step_at _ _ aP _ _ _ vP _ _ (by rw [← hP, ← hrdx]) (by ecancel) (by exact hvP)
  intro m1' H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  apply Eventually.done
  exact ⟨rfl, rfl, rfl, rfl, hrdx, by ecancel⟩))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Pointer tail segment** of a byte-vector field: from `mov dS(%rsp),%rY` (at `j3`) over the jump to
`l` (at `j4`, `label l = Host.addrOf j4`) through `mov %rY,fP(%rdx)`. The pointer `p` in the slot
`aS = sp + dS` is stored to the field pointer slot `aP = rcv + fP`; rsp, rbp, r14 and rdx are kept. -/
theorem bytesdec_tail_seg (rY : Reg64) (hY : U64InlineReg rY) (l : String) (dS fP : Int64) (j3 j4 : Nat)
    (hA : (bytesDecTailA rY l dS).IsInfixAt Host.prog j3)
    (hB : (bytesDecTailB rY l fP).IsInfixAt Host.prog j4)
    (hl : label l = Host.addrOf j4)
    (sp rcv p aS aP : BitVec 64) (hS : sp + dS.toBitVec = aS) (hP : rcv + fP.toBitVec = aP)
    (rbp0 r140 : UInt64) (vP : List UInt8) (hvP : vP.length = 8)
    (R : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140) (hrdx : s.regs.rdx.toBitVec = rcv)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 p.toInt).At aS) ⋆ Eq (vP.At aP) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (j4 + 2) ∧ st.data.regs.rsp = { toBitVec := sp }
        ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧ st.data.regs.rdx.toBitVec = rcv ∧
        (Eq ((Int.toBytes 8 p.toInt).At aS) ⋆ Eq ((Int.toBytes 8 p.toInt).At aP) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf j3⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp hrbp hr14 hrdx h_mem ⊢
  subst rsp rbp r14
  rcases hY with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals bytestail_case

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Epilogue segment**: `xor %eax,%eax; xor %ebx,%ebx; add $0x20,%rsp; pop %rbp; retq` at `j`. With
rsp = `sp`, the saved frame pointer `fp0` at `aFp = sp + 32` and the return address `ra` at
`aRa = sp + 40`, it returns to `ra` with rax = rbx = 0, rsp = `sp + 48`, rbp = `fp0`, r14 kept and the
memory unchanged. -/
theorem decepi_seg (j : Nat) (hA : decEpi.IsInfixAt Host.prog j)
    (sp aFp aRa : BitVec 64) (hFp : sp + 32 = aFp) (hRa : sp + 40 = aRa)
    (fp0 ra r140 : UInt64) (R : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hr14 : s.regs.r14 = r140)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 fp0.toBitVec.toInt).At aFp)
      ⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At aRa) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = { toBitVec := sp + 48 } ∧ st.data.regs.rbp = fp0 ∧ st.data.regs.r14 = r140 ∧
        (Eq ((Int.toBytes 8 fp0.toBitVec.toInt).At aFp)
          ⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At aRa) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf j⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp hr14 h_mem ⊢
  subst rsp r14 hFp hRa
  kat hA decEpi 0
  intro _
  kat hA decEpi 1
  intro _
  kat hA decEpi 2
  kat hA decEpi 3
  apply load_step_at _ _ (sp + 32) _ _ (Int.toBytes 8 fp0.toBitVec.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hA decEpi 4
  apply load_step_at _ _ (sp + 40) _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_right
  · ecancel
  all_goals first
    | exact trivial
    | with_reducible rfl
    | (apply UInt64.toBitVec_inj.mp
       simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, Width.bits]
       done)
    | (apply UInt64.toBitVec_inj.mp; segment_addr)
    | (apply UInt64.toBitVec_inj.mp; simp [BitVec.xor_self])

end Codec
