import Codec.SegmentTemplate

/-!
# uint64 decoder pattern: the uint64 primitive decoder body, accept path (parameterized)

The Go 1.26.10 code of a hand-written Prysm `uint64` primitive `UnmarshalSSZ`
(`primitives.Epoch`, `Slot`, `CommitteeIndex`: `if len(buf) != 8 { return fmt.Errorf(...) };
*e = Epoch(binary.LittleEndian.Uint64(buf)); return nil`) has, on the accept path, two code
blocks:

* `u64DecHead fn l0 lcc lbb fs dsp` (11 directives): the function label `fn`, the loop label
  `l0`, the stack-guard test (`jbe lcc`), the prologue `push %rbp; mov %rsp,%rbp; sub $fs,%rsp`,
  the rbx spill `mov %rbx,dsp(%rsp)`, `nop`, the length test `cmp $0x8,%rcx; je lbb`;
* `u64DecTail lbb fs` (9 directives): `lbb:`, the 8-byte load and store, `xor %eax,%eax;
  xor %ebx,%ebx`, the epilogue `add $fs,%rsp; pop %rbp; retq`.

The reject block between them (format string and `convT64` / `fmt.Errorf` calls) differs per
type and is not read on this path. Parameters: the four labels, the frame size `fs`, the
spill displacement `dsp` (`dsp = fs + 24`: the caller's rbx slot at entry rsp + 16), the
place `j` of the head block, the place `jb` of the tail block and the address of `lbb`.

`u64dec_accept` is proved once from these templates. Its statement is the statement of
`Prysm.Epoch.Decode.accept` / `Prysm.Slot.Decode.accept` /
`Prysm.CommitteeIndex.Decode.accept` with the code hypotheses replaced by the template
hypotheses.
-/

open Machine

namespace Codec

/-- Head block of the uint64 decoder pattern (directives 0–10 of the dev instances). -/
def u64DecHead (fn l0 lcc lbb : String) (fs dsp : Int64) : Program :=
  [Kraken.Directive.label fn,
   Kraken.Directive.label l0,
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.cmp (RegOrMem.reg (Reg.low Reg64.rsp Width.W64))
       (Operand.regOrMem (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.r14)) none (ConstExpr.int64 16)))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64 (Operation.jcc CondCode.be lcc)),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.push (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rbp Width.W64))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.reg (Reg.low Reg64.rbp Width.W64))
       (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rsp Width.W64))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.sub (RegOrMem.reg (Reg.low Reg64.rsp Width.W64)) (Operand.imm (ConstExpr.int64 fs)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rsp)) none (ConstExpr.int64 dsp)))
       (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rbx Width.W64))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64 (Operation.nop 1)),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.cmp (RegOrMem.reg (Reg.low Reg64.rcx Width.W64)) (Operand.imm (ConstExpr.int64 8)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64 (Operation.jcc CondCode.z lbb))]

/-- Tail block of the uint64 decoder pattern (from the label `lbb`). -/
def u64DecTail (lbb : String) (fs : Int64) : Program :=
  [Kraken.Directive.label lbb,
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.reg (Reg.low Reg64.rcx Width.W64))
       (Operand.regOrMem (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rbx)) none (ConstExpr.int64 0)))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64 (Operation.nop 1)),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rax)) none (ConstExpr.int64 0)))
       (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rcx Width.W64))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W32
     (Operation.xor (RegOrMem.reg (Reg.low Reg64.rax Width.W32))
       (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rax Width.W32))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W32
     (Operation.xor (RegOrMem.reg (Reg.low Reg64.rbx Width.W32))
       (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rbx Width.W32))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.add (RegOrMem.reg (Reg.low Reg64.rsp Width.W64)) (Operand.imm (ConstExpr.int64 fs)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.pop (RegOrMem.reg (Reg.low Reg64.rbp Width.W64)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64 Operation.ret)]

variable [Host]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **uint64 decoder segment lemma**: accept path of a uint64 primitive decoder whose head and tail
blocks are the templates at `j` and `jb` (`label lbb = Host.addrOf jb`), for any frame
size `fs` with the spill displacement `dsp = fs + 24`. -/
theorem u64dec_accept (fn l0 lcc lbb : String) (fs dsp : Int64)
    (hdsp : dsp.toBitVec = fs.toBitVec + 24)
    (j jb : Nat) (hA : (u64DecHead fn l0 lcc lbb fs dsp).IsInfixAt Host.prog j)
    (hB : (u64DecTail lbb fs).IsInfixAt Host.prog jb) (hl : label lbb = Host.addrOf jb)
    (e8 : List UInt8) (he8 : e8.length = 8)
    (s : MachineData) (ra guard : UInt64) (fp s2 c0 : List UInt8)
    (hfp : fp.length = 8) (h2 : s2.length = 8) (hc0 : c0.length = 8) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (e8.At s.regs.rbx.toBitVec) ⋆ Eq (c0.At s.regs.rax.toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx = 8) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (e8.At s.regs.rbx.toBitVec) ⋆ Eq (e8.At s.regs.rax.toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf j⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  subst hlen
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; simp only [UInt64.size] at *
  kat hA u64DecHead 0
  kat hA u64DecHead 1
  kat hA u64DecHead 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hA u64DecHead 3
  split
  · rename_i h; exfalso
    simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hA u64DecHead 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hA u64DecHead 5
  kat hA u64DecHead 6
  kat hA u64DecHead 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by rw [hdsp]; bv_omega) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hA u64DecHead 8
  kat hA u64DecHead 9
  kat hA u64DecHead 10
  split
  case isFalse h => exact absurd h (by decide)
  simp only [Effects.All]
  rw [hl]
  kat hB u64DecTail 0
  kat hB u64DecTail 1
  apply load_step _ _ _ _ e8 _ _ (by ecancel) (by exact he8)
  kunfold
  kat hB u64DecTail 2
  kat hB u64DecTail 3
  apply store_step_at _ _ rax.toBitVec _ _ _ c0 _ _ (by bv_omega) (by ecancel) (by exact hc0)
  intro m3 H3
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl e8 he8] at H3
  kunfold
  kat hB u64DecTail 4
  intro _
  kat hB u64DecTail 5
  intro _
  kat hB u64DecTail 6
  kat hB u64DecTail 7
  rw [show fs.toBitVec + (rsp.toBitVec - 8#64 - fs.toBitVec) = rsp.toBitVec - 8 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hB u64DecTail 8
  rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_right
  · ecancel
  all_goals first
    | trivial
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (apply UInt64.toBitVec_inj.mp; simp; bv_omega)

end Codec
