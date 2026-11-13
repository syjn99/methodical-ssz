import Codec.Bytes32Decode

/-!
# Inline uint64 decode, two-directive form (register base, receiver in rax)

Added after the hold-out test of Deposit_Data and PendingPartialWithdrawal: the generator did not cover this form. In `(*v1alpha1.PendingPartialWithdrawal).UnmarshalSSZ` Go 1.26.10
compiles `p.Amount = ssz.UnmarshallUint64(buf[8:16])` between the argument set-up directives of the next
callee field to

    mov src(%rbx),%rX     -- the 8 source bytes; the buffer pointer is already in rbx
    mov %rX,f(%rax)       -- store to the field at Go offset f; the receiver is in rax

(`rX` = r8 at the one development site). `u64DecRR rX src f` is this template; it differs from
`u64DecInline` (`Codec/InlineUint64.lean`: reload from the spill slot, receiver in rdx, one scratch register for
both roles). The lemma holds for every scratch register except rax, rbx (the bases), rsp, rbp, r14; `hX`
lists the eleven others. Every register except `rX` is kept (the neighbouring set-up directives hold live
values in rdx, rsi, rdi). No runtime contract is used.
Not covered: other base registers (one site observed; no second form).
-/

open Machine Runtime

namespace Codec

/-- The two-directive inline uint64 decode template, scratch register `rX`. -/
def u64DecRR (rX : Reg64) (src f : Int64) : Program :=
  [Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.reg (Reg.low rX Width.W64))
       (Operand.regOrMem (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rbx)) none (ConstExpr.int64 src)))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rax)) none (ConstExpr.int64 f)))
       (Operand.regOrMem (RegOrMem.reg (Reg.low rX Width.W64)))))]

/-- The scratch registers of `u64dec_rr_seg`: every register except rax, rbx, rsp, rbp, r14. -/
abbrev U64RRReg (rX : Reg64) : Prop :=
  rX = Reg64.rcx ∨ rX = Reg64.rdx ∨ rX = Reg64.rsi ∨ rX = Reg64.rdi ∨ rX = Reg64.r8 ∨ rX = Reg64.r9
    ∨ rX = Reg64.r10 ∨ rX = Reg64.r11 ∨ rX = Reg64.r12 ∨ rX = Reg64.r13 ∨ rX = Reg64.r15

variable [Host]

set_option hygiene false in
/-- Proof text of one register case of `u64dec_rr_seg` (binders of the lemma). Local to this file. -/
local macro "uint64_register_case" : tactic => `(tactic| (
  kat hA u64DecRR 0
  apply load_step_at _ _ aSrc _ _ v _ _ (by rw [← hSrc, ← hrbx]) (by ecancel) (by exact hv)
  kunfold
  kat hA u64DecRR 1
  apply store_step_at _ _ aF _ _ _ vF _ _ (by rw [← hF, ← hrax]) (by ecancel) (by exact hvF)
  intro m1' H1
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl v hv] at H1
  kunfold
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, by ecancel⟩
  intro r hr
  cases r <;> first | rfl | exact absurd rfl hr))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Inline uint64 decode segment, two-directive form**: the two directives at `j`. With the buffer pointer
`bf` in rbx, the receiver `rcv` in rax, the 8 source bytes `v` at `aSrc = bf + src`, the field slot
`aF = rcv + f` gets `v`; the source and the frame `R` are unchanged; every register except the scratch
register `rX` is kept (rsp, rbp, r14, rax, rbx are listed; the others by the last register clause). -/
theorem u64dec_rr_seg (rX : Reg64) (hX : U64RRReg rX) (src f : Int64) (j : Nat)
    (hA : (u64DecRR rX src f).IsInfixAt Host.prog j)
    (bf rcv aSrc aF : BitVec 64) (hSrc : bf + src.toBitVec = aSrc) (hF : rcv + f.toBitVec = aF)
    (v vF : List UInt8) (hv : v.length = 8) (hvF : vF.length = 8)
    (R : DataMem → Prop)
    (s : MachineData) (hrbx : s.regs.rbx.toBitVec = bf) (hrax : s.regs.rax.toBitVec = rcv)
    (h_mem : s.dmem =⋆ Eq (v.At aSrc) ⋆ Eq (vF.At aF) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (j + 2) ∧ st.data.regs.rsp = s.regs.rsp
        ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.rax = s.regs.rax ∧ st.data.regs.rbx = s.regs.rbx
        ∧ (∀ r : Reg64, r ≠ rX → st.data.regs.get64 r = s.regs.get64 r)
        ∧ (Eq (v.At aSrc) ⋆ Eq (v.At aF) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf j⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrbx hrax h_mem ⊢
  rcases hX with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals uint64_register_case

end Codec
