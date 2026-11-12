import Codec.Bytes32Decode

/-!
# Reusable encode block: the `return nil, ssz.ErrBytesLength` tail of a generated `MarshalSSZTo`

The reject tail returns in the ABI result registers, so its instruction text is the same in every
generated encoder up to three parameters (read from the `.S` files of Checkpoint, BeaconBlockHeader and
Eth1Data): the frame release (`add $c,%rsp` or `sub $c,%rsp`), the constant `c`, and an optional `nop`
before `retq`:

    mov ssz.ErrBytesLength(%rip),%rdi; mov ssz.ErrBytesLength+8(%rip),%rsi
    xor %eax,%eax; xor %ebx,%ebx; mov %rbx,%rcx
    add $c,%rsp | sub $c,%rsp;  pop %rbp;  [nop;]  retq

`rejTail sub nop c` is that template (after the label). `enc_reject_tail` is the block: from the first
`mov` it returns to the caller with `rax = rbx = rcx = 0` (nil slice), `rdi, rsi` = the two words of
`ssz.ErrBytesLength`, the saved rbp restored, memory unchanged. Parameters: the two template flags, `c`,
the place `j`, rsp at the block `sp`, the saved-rbp address `aFp` (`relAddr sub c sp = aFp`) and the
return-slot address `aRa` (`aFp + 8 = aRa`). The initialised error words are a premise (as in
`Prysm.Checkpoint.Encode.reject_length`). No runtime contract is used.
-/

open Machine Runtime TestTarget

namespace Codec

/-- Frame release of the reject tail: `add $c,%rsp` (`false`) or `sub $c,%rsp` (`true`). -/
def relRsp : Bool → Int64 → Directive
  | false, c => Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
      (Operation.add (RegOrMem.reg (Reg.low Reg64.rsp Width.W64)) (Operand.imm (ConstExpr.int64 c))))
  | true, c => Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
      (Operation.sub (RegOrMem.reg (Reg.low Reg64.rsp Width.W64)) (Operand.imm (ConstExpr.int64 c))))

/-- The optional `nop` before `retq`. -/
def nopOpt : Bool → Program
  | false => []
  | true => [Kraken.Directive.instr (Instr.regular Width.W64 Width.W64 (Operation.nop 1))]

/-- rsp after the frame release. -/
def relAddr : Bool → Int64 → BitVec 64 → BitVec 64
  | false, c, sp => sp + c.toBitVec
  | true, c, sp => sp - c.toBitVec

/-- The reject tail after its label. -/
def rejTail (sub nop : Bool) (c : Int64) : Program :=
  [Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.reg (Reg.low Reg64.rdi Width.W64))
       (Operand.regOrMem (RegOrMem.mem (AddrExpr.mk (some RegOrRip.rip) none
         ((ConstExpr.label "ssz.ErrBytesLength").sub ConstExpr.after_current_instruction)))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.reg (Reg.low Reg64.rsi Width.W64))
       (Operand.regOrMem (RegOrMem.mem (AddrExpr.mk (some RegOrRip.rip) none
         (((ConstExpr.label "ssz.ErrBytesLength").add (ConstExpr.int64 8)).sub ConstExpr.after_current_instruction)))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W32
     (Operation.xor (RegOrMem.reg (Reg.low Reg64.rax Width.W32))
       (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rax Width.W32))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W32
     (Operation.xor (RegOrMem.reg (Reg.low Reg64.rbx Width.W32))
       (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rbx Width.W32))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.reg (Reg.low Reg64.rcx Width.W64))
       (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rbx Width.W64))))),
   relRsp sub c,
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.pop (RegOrMem.reg (Reg.low Reg64.rbp Width.W64))))]
  ++ nopOpt nop
  ++ [Kraken.Directive.instr (Instr.regular Width.W64 Width.W64 Operation.ret)]

variable [Host]

/-- Step directive `n` of a fragment fact `h` whose list is already a literal. -/
local macro "rstep " h:ident n:num : tactic => `(tactic| (
  have hkat := Machine.isInfixAt_drop $h $n
  simp only [List.drop_succ_cons, List.drop_zero] at hkat
  apply Machine.estep hkat
  clear hkat
  kunfold))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Reject block**: the tail `rejTail sub nop c` at `j` returns `(nil, ssz.ErrBytesLength)`: pc = the
return address `ra`, `rax = rbx = rcx = 0`, `rdi = e0`, `rsi = e1`, rsp = `aRa + 8`, rbp = the saved
`rbp0`, r14 kept, memory unchanged. -/
theorem enc_reject_tail (sub nop : Bool) (c : Int64) (j : Nat)
    (hA : (rejTail sub nop c).IsInfixAt Host.prog j)
    (sp aFp aRa : BitVec 64) (hFp : relAddr sub c sp = aFp) (hRa : aFp + 8 = aRa)
    (ra rbp0 e0 e1 : UInt64) (R : DataMem → Prop) (s : MachineData)
    (hrsp : s.regs.rsp = { toBitVec := sp })
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At aRa)
      ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At aFp)
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrBytesLength").toBitVec)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrBytesLength" + 8).toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rcx = 0 ∧ st.data.regs.rdi = e0 ∧ st.data.regs.rsi = e1
        ∧ st.data.regs.rsp.toBitVec = aRa + 8 ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = s.regs.r14 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At aRa)
          ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At aFp)
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrBytesLength").toBitVec)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrBytesLength" + 8).toBitVec) ⋆ R)
          st.data.dmem)
      ⟨s, Host.addrOf j⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp h_mem ⊢
  subst hrsp
  cases sub <;> cases nop <;>
    simp only [rejTail, relRsp, nopOpt, relAddr, List.cons_append, List.nil_append] at hA hFp
  all_goals (
    rstep hA 0
    apply load_step _ _ _ _ (Int.toBytes 8 e0.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    kunfold
    rstep hA 1
    apply load_step _ _ _ _ (Int.toBytes 8 e1.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    kunfold
    rstep hA 2
    intro _
    rstep hA 3
    intro _
    rstep hA 4
    rstep hA 5
    rstep hA 6
    apply load_step_at _ _ aFp _ _ (Int.toBytes 8 rbp0.toBitVec.toInt) _ _
      (by first | exact hFp | (rw [← hFp]; exact BitVec.add_comm _ _) | (rw [← hFp]; saddr))
      (by ecancel) (by exact Int.toBytes_length 8 _)
    kunfold
    rstep hA 7
    try (rstep hA 8)
    apply load_step_at _ _ aRa _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _
      (by rw [← hRa, ← hFp]; first | rfl | saddr)
      (by ecancel) (by exact Int.toBytes_length 8 _)
    kunfold
    apply Eventually.done
    try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?grsp, ?_, ?_, h_mem⟩
    case grsp => rw [← hRa, ← hFp]; first | rfl | saddr
    all_goals first
      | exact trivial
      | with_reducible rfl
      | (apply UInt64.toBitVec_inj.mp; simp; done))

end Codec
