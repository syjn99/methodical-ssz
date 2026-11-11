import E2eScal.P2Dec

/-!
# GEN2 L2: inline uint64 decode segment of a container decoder

Added after the H3 hold-out (FINDINGS SG-2, proposal P-H3-1). Go 1.26.10 compiles
`x.F = ssz.UnmarshallUint64(buf[src:src+8])` inside a protoc container decoder, after a byte-vector field
(the receiver is in rdx), to three directives:

    mov dB(%rsp),%rX      -- reload the buffer pointer from its spill slot
    mov src(%rX),%rX      -- the 8 source bytes
    mov %rX,f(%rdx)       -- store to the field at Go offset f of the receiver

`u64DecInline rX dB src f` is this template. The three development sites differ in the scratch register
only: `Eth1Data.DepositCount` uses rsi, `BlobIdentifier.Index` and `DepositMessage.Amount` use rcx; the
receiver register is rdx and the addressing forms are the same at the three sites. The scratch register is
a parameter `rX : Reg64`. The lemma holds for every register except rdx (the receiver), rsp, rbp and r14
(kept by the statement); the hypothesis `hX` lists the twelve others. The proof is a case split on `hX`,
since the machine step is computed for a concrete register. No runtime contract is used.
Not covered: a decoder that keeps the receiver in another register than rdx (not observed), and a form
without the reload from the spill slot.
-/

open Fk

namespace E2eScal

/-- The inline uint64 decode template (3 directives), scratch register `rX`. -/
def u64DecInline (rX : Reg64) (dB src f : Int64) : Program :=
  [Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.reg (Reg.low rX Width.W64))
       (Operand.regOrMem (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rsp)) none (ConstExpr.int64 dB)))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.reg (Reg.low rX Width.W64))
       (Operand.regOrMem (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg rX)) none (ConstExpr.int64 src)))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rdx)) none (ConstExpr.int64 f)))
       (Operand.regOrMem (RegOrMem.reg (Reg.low rX Width.W64)))))]

/-- The scratch registers of `u64dec_inline_seg`: every register except rdx, rsp, rbp, r14. -/
abbrev U64InlineReg (rX : Reg64) : Prop :=
  rX = Reg64.rax ∨ rX = Reg64.rbx ∨ rX = Reg64.rcx ∨ rX = Reg64.rsi ∨ rX = Reg64.rdi ∨ rX = Reg64.r8
    ∨ rX = Reg64.r9 ∨ rX = Reg64.r10 ∨ rX = Reg64.r11 ∨ rX = Reg64.r12 ∨ rX = Reg64.r13 ∨ rX = Reg64.r15

variable [Host]

set_option hygiene false in
/-- Proof text of one register case of `u64dec_inline_seg` (the names are the binders of the lemma; hygiene
is off so that they are captured). Local to this file. -/
local macro "u64inline_case" : tactic => `(tactic| (
  kat hA u64DecInline 0
  apply load_step_at _ _ aB _ _ (Int.toBytes 8 bf.toInt) _ _ (by rw [← hB']) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hA u64DecInline 1
  apply load_step_at _ _ aSrc _ _ v _ _ (by rw [← hSrc]) (by ecancel) (by exact hv)
  kunfold
  kat hA u64DecInline 2
  apply store_step_at _ _ aF _ _ _ vF _ _ (by rw [← hF, ← hrdx]) (by ecancel) (by exact hvF)
  intro m1' H1
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl v hv] at H1
  kunfold
  apply Eventually.done
  exact ⟨rfl, rfl, rfl, rfl, hrdx, by ecancel⟩))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Inline uint64 decode segment**: the three directives at `j`. With rsp = `sp`, the buffer pointer `bf`
in the spill slot `aB = sp + dB`, the 8 source bytes `v` at `aSrc = bf + src` and the receiver `rcv` in rdx,
the field slot `aF = rcv + f` gets `v`; the source, the spill slot and the frame `R` are unchanged; rsp, rbp,
r14 and rdx are kept. The scratch register `rX` is not in the statement. -/
theorem u64dec_inline_seg (rX : Reg64) (hX : U64InlineReg rX) (dB src f : Int64) (j : Nat)
    (hA : (u64DecInline rX dB src f).IsInfixAt Host.prog j)
    (sp rcv bf aB aSrc aF : BitVec 64)
    (hB' : sp + dB.toBitVec = aB) (hSrc : bf + src.toBitVec = aSrc) (hF : rcv + f.toBitVec = aF)
    (rbp0 r140 : UInt64) (v vF : List UInt8) (hv : v.length = 8) (hvF : vF.length = 8)
    (R : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140) (hrdx : s.regs.rdx.toBitVec = rcv)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 bf.toInt).At aB) ⋆ Eq (v.At aSrc) ⋆ Eq (vF.At aF) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (j + 3) ∧ st.data.regs.rsp = { toBitVec := sp }
        ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧ st.data.regs.rdx.toBitVec = rcv ∧
        (Eq ((Int.toBytes 8 bf.toInt).At aB) ⋆ Eq (v.At aSrc) ⋆ Eq (v.At aF) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf j⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp hrbp hr14 hrdx h_mem ⊢
  subst rsp rbp r14
  rcases hX with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals u64inline_case

end E2eScal
