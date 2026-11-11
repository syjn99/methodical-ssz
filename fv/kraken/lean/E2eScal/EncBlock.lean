import E2eScal.P2Dec

/-!
# Reusable encode block: the `runtime.memmove` call that appends a 32-byte field which fits

The compiled code that appends a 32-byte field (`dst = append(dst, f...)`, capacity sufficient) differs
at every known site in its registers and instruction forms (Checkpoint, three sites of
BeaconBlockHeader, two of Eth1Data: six instruction texts). A multi-directive code template therefore
has one instance per site. What the sites share is the machine state at the call:
`rax` = destination address, `rbx` = field pointer, `rcx` = 32, the return slot below `rsp` and the
scratch window of the contract. `enc32_call` states that part once.

Code-fact hypothesis: the directive at `jc` is `callq runtime.memmove` (`callMemmove`). Parameters: the
frame base `sp` (rsp at the call, any frame size), the destination `d`, the source `p`, the scratch size
`S`, the frame `R`. `aRet` and `aLo` are the return-slot and scratch addresses in the form of the
instance (`sp − 8 = aRet`, `sp − 8 − S = aLo`). The spilled pointer, length and capacity words and the
receiver words of an instance are in `R`. `MemmoveC` is the existing contract (a hypothesis, not proved).

The straight-line code before the call (length test, capacity test, spills) is stepped per site. The
stack-guard fact of the large-frame prologue is `E2eScal.lea_cmp_be_false` (`StackGuard.lean`), already
stated over the displacement.
-/

open Fk

namespace E2eScal

/-- The one directive of the block: `callq runtime.memmove`. -/
def callMemmove : Program :=
  [Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.call (RelRegOrMem.rel ((ConstExpr.label "runtime.memmove").sub ConstExpr.after_current_instruction))))]

variable [Host]

set_option maxRecDepth 100000 in
/-- **Encode block**: at `callq runtime.memmove` (directive `jc`) with `rax = d`, `rbx = p`, `rcx = 32`,
the 32 bytes `root` at `p` are copied over the 32 bytes at `d`; control is at `jc + 1`; rsp, rbp and r14
are kept; the return slot holds the address of `jc + 1`; the source and the frame `R` are unchanged. -/
theorem enc32_call (jc : Nat) (hc : callMemmove.IsInfixAt Host.prog jc)
    (sp d p aRet aLo : BitVec 64) (S : Nat)
    (hRet : sp - 8 = aRet) (hLo : sp - 8 - BitVec.ofNat 64 S = aLo)
    (root e rslot scratch : List UInt8) (hroot : root.length = 32) (he : e.length = 32)
    (hrs : rslot.length = 8) (hsc : scratch.length = S)
    (R : DataMem → Prop) (s : MachineData)
    (hrsp : s.regs.rsp = { toBitVec := sp }) (hrax : s.regs.rax.toBitVec = d)
    (hrbx : s.regs.rbx.toBitVec = p) (hrcx : s.regs.rcx.toNat = 32)
    (h_mem : s.dmem =⋆ Eq (rslot.At aRet) ⋆ Eq (scratch.At aLo) ⋆ Eq (root.At p) ⋆ Eq (e.At d) ⋆ R)
    (hmm : MemmoveC S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (jc + 1) ∧ st.data.regs.rsp = { toBitVec := sp }
        ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ scr : List UInt8, scr.length = S ∧
        (Eq ((Int.toBytes 8 (Host.addrOf (jc + 1)).toBitVec.toInt).At aRet) ⋆ Eq (scr.At aLo)
          ⋆ Eq (root.At p) ⋆ Eq (root.At d) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf jc⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp hrax hrbx hrcx h_mem ⊢
  subst rsp hrax hrbx hRet hLo
  kat hc callMemmove 0
  apply store_step_at _ _ (sp - 8) _ _ _ rslot _ _ (by saddr) (by ecancel) (by exact hrs)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  try rw [show sp - 8#64 = sp - 8 from rfl] at *
  rw [show jc + 0 + 1 = jc + 1 from rfl] at H4
  refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (jc + 1)) root e scratch _
    (by rw [hroot]; exact hrcx) (by rw [hroot, he]) hsc (by dsimp only; ecancel)) ?_
  rintro ⟨e1, pc1⟩ ⟨hpc1, hrsp1, hr141, hrbp1, stk1, hstk1, Hm1⟩
  dsimp only at hpc1 hrsp1 hr141 hrbp1 Hm1
  apply Eventually.done
  refine ⟨hpc1, ?_, hrbp1, hr141, stk1, hstk1, by ecancel⟩
  exact hrsp1.trans (by
    apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega)

end E2eScal
