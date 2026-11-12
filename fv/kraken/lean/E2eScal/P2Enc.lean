import E2eScal.P2Dec

/-!
# 32-byte field pattern, encode segment: `if len(f) != 32 { reject }; dst = append(dst, f...)` (fits case)

Go 1.26.10 compiles the 32-byte field encode of a protoc container (`Checkpoint.Root`) to two
code blocks (the growslice block between them is not taken when the field fits):

* `rootEncHead lrej lcf fP fL` (6 directives): `mov fP(%rax),%r8` (field pointer),
  `cmpq $0x20,fL(%rax); jne lrej` (length test), `lea 0x20(%rdx),%r9; cmp %r9,%rdi; jae lcf`
  (capacity test);
* `rootEncTail lcf dCap dLen dPtr` (8 directives): `lcf:`, spills of the capacity, the new
  length and the base `mov %rdi,dCap(%rsp); mov %r9,dLen(%rsp); mov %rbx,dPtr(%rsp)`,
  `lea (%rbx,%rdx,1),%rax; mov %r8,%rbx; mov $0x20,%ecx; callq runtime.memmove`.

Registers at the segment: rax = receiver `rcv`, rbx = destination base `dstp`, rdx = current
length `off`, rdi = capacity `cap`. Parameters: labels `lrej`, `lcf`; field displacements
`fP`, `fL`; stack displacements `dCap`, `dLen`, `dPtr`; the places `j1`, `j2`; the address of
`lcf`; addresses with equations as in `rootdec_seg`. The lemma ends at the return of
`memmove` (directive `j2 + 8`).
-/

open Fk

namespace E2eScal

/-- First block of the 32-byte field encode segment (length test, capacity test). -/
def rootEncHead (lrej lcf : String) (fP fL : Int64) : Program :=
  [Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.reg (Reg.low Reg64.r8 Width.W64))
       (Operand.regOrMem (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rax)) none (ConstExpr.int64 fP)))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.cmp (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rax)) none (ConstExpr.int64 fL)))
       (Operand.imm (ConstExpr.int64 32)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64 (Operation.jcc CondCode.nz lrej)),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.lea (Reg.low Reg64.r9 Width.W64) (AddrExpr.mk (some (RegOrRip.reg Reg64.rdx)) none (ConstExpr.int64 32)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.cmp (RegOrMem.reg (Reg.low Reg64.rdi Width.W64))
       (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.r9 Width.W64))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64 (Operation.jcc CondCode.nc lcf))]

/-- Second block of the 32-byte field encode segment (from `lcf:` to the `memmove` call). -/
def rootEncTail (lcf : String) (dCap dLen dPtr : Int64) : Program :=
  [Kraken.Directive.label lcf,
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rsp)) none (ConstExpr.int64 dCap)))
       (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rdi Width.W64))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rsp)) none (ConstExpr.int64 dLen)))
       (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.r9 Width.W64))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rsp)) none (ConstExpr.int64 dPtr)))
       (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rbx Width.W64))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.lea (Reg.low Reg64.rax Width.W64)
       (AddrExpr.mk (some (RegOrRip.reg Reg64.rbx)) (some (AddrIndex.mk Reg64.rdx Width.W8)) (ConstExpr.int64 0)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.reg (Reg.low Reg64.rbx Width.W64))
       (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.r8 Width.W64))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W32
     (Operation.mov (RegOrMem.reg (Reg.low Reg64.rcx Width.W32)) (Operand.imm (ConstExpr.int64 32)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.call (RelRegOrMem.rel ((ConstExpr.label "runtime.memmove").sub ConstExpr.after_current_instruction))))]

variable [Host]

theorem penc_mul (x y : BitVec 64) : x + y * 1#64 = x + y := by rw [BitVec.mul_one]

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- **32-byte field encode segment lemma** (the field fits: `off + 32 ≤ cap`): `len(f) = 32` is read, the
capacity, new length and base are spilled, and `memmove` copies the 32 bytes at the field
pointer `p` to `dstp + off`. Ends at the return of `memmove`. -/
theorem rootenc_seg (lrej lcf : String) (fP fL dCap dLen dPtr : Int64) (j1 j2 : Nat)
    (hA : (rootEncHead lrej lcf fP fL).IsInfixAt Host.prog j1)
    (hB : (rootEncTail lcf dCap dLen dPtr).IsInfixAt Host.prog j2)
    (hl : label lcf = Host.addrOf j2)
    (sp rcv off dstp cap p aP aL aCap aLen aPtr aRet aLo aDst : BitVec 64) (St : Nat)
    (hP : rcv + fP.toBitVec = aP) (hL : rcv + fL.toBitVec = aL)
    (hCap : sp + dCap.toBitVec = aCap) (hLen : sp + dLen.toBitVec = aLen) (hPtr : sp + dPtr.toBitVec = aPtr)
    (hRet : sp - 8 = aRet) (hLo : sp - 8 - BitVec.ofNat 64 St = aLo) (hDst : dstp + off = aDst)
    (hfit : off.toNat + 32 ≤ cap.toNat)
    (root d1 vCap vLen vPtr rslot scratch : List UInt8) (hroot : root.length = 32) (hd1 : d1.length = 32)
    (hvCap : vCap.length = 8) (hvLen : vLen.length = 8) (hvPtr : vPtr.length = 8) (hrs : rslot.length = 8)
    (hsc : scratch.length = St)
    (rbp0 r140 : UInt64) (R : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140)
    (hrax : s.regs.rax.toBitVec = rcv) (hrbx : s.regs.rbx.toBitVec = dstp) (hrdx : s.regs.rdx.toBitVec = off)
    (hrdi : s.regs.rdi.toBitVec = cap)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 p.toInt).At aP) ⋆ Eq ((Int.toBytes 8 32).At aL)
      ⋆ Eq (vCap.At aCap) ⋆ Eq (vLen.At aLen) ⋆ Eq (vPtr.At aPtr)
      ⋆ Eq (rslot.At aRet) ⋆ Eq (scratch.At aLo)
      ⋆ Eq (root.At p) ⋆ Eq (d1.At aDst) ⋆ R)
    (hmm : MemmoveC St) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (j2 + 7 + 1) ∧ st.data.regs.rsp = { toBitVec := sp }
        ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        ∃ scr : List UInt8, scr.length = St ∧
        (Eq ((Int.toBytes 8 p.toInt).At aP) ⋆ Eq ((Int.toBytes 8 32).At aL)
          ⋆ Eq ((Int.toBytes 8 cap.toInt).At aCap) ⋆ Eq ((Int.toBytes 8 (off + 32).toInt).At aLen)
          ⋆ Eq ((Int.toBytes 8 dstp.toInt).At aPtr)
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (j2 + 7 + 1)).toBitVec.toInt).At aRet) ⋆ Eq (scr.At aLo)
          ⋆ Eq (root.At p) ⋆ Eq (root.At aDst) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf j1⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp hrbp hr14 hrax hrbx hrdx hrdi h_mem ⊢
  subst rsp rbp r14 hrax hrbx hrdx hrdi hRet hLo
  have := rdi.toNat_lt_size; have := rdx.toNat_lt_size
  simp only [UInt64.size] at *
  try simp only [UInt64.toNat_toBitVec] at hfit
  kat hA rootEncHead 0
  apply load_step_at _ _ aP _ _ (Int.toBytes 8 p.toInt) _ _ (by rw [← hP]) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hA rootEncHead 1
  apply load_step_at _ _ aL _ _ (Int.toBytes 8 32) _ _ (by rw [← hL]) (by ecancel) (by rfl)
  simp only [show Int.ofBytes (Int.toBytes 8 32) = 32 by decide]
  kunfold
  kat hA rootEncHead 2
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hA rootEncHead 3
  kat hA rootEncHead 4
  kat hA rootEncHead 5
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  rw [hl]
  kat hB rootEncTail 0
  kat hB rootEncTail 1
  apply store_step_at _ _ aCap _ _ _ vCap _ _ (by rw [← hCap]) (by ecancel) (by exact hvCap)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hB rootEncTail 2
  apply store_step_at _ _ aLen _ _ _ vLen _ _ (by rw [← hLen]) (by ecancel) (by exact hvLen)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hB rootEncTail 3
  apply store_step_at _ _ aPtr _ _ _ vPtr _ _ (by rw [← hPtr]) (by ecancel) (by exact hvPtr)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hB rootEncTail 4
  kat hB rootEncTail 5
  kat hB rootEncTail 6
  kat hB rootEncTail 7
  apply store_step_at _ _ (sp - 8) _ _ _ rslot _ _ (by saddr) (by ecancel) (by exact hrs)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  try rw [show sp - 8#64 = sp - 8 from rfl] at *
  rw [penc_mul, hDst] at *
  refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (j2 + 7 + 1)) root d1 scratch _
    (by rw [hroot]; rfl) (by rw [hroot, hd1]) hsc (by dsimp only; ecancel)) ?_
  rintro ⟨e1, pc1⟩ ⟨hpc1, hrsp1, hr141, hrbp1, stk1, hstk1, Hm1⟩
  dsimp only at hpc1 hrsp1 hr141 hrbp1 Hm1
  subst hpc1
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩,
    zmms1, flags1, mem1⟩ := e1
  simp only at hrsp1 hr141 hrbp1 Hm1
  rw [show ({ toBitVec := sp - 8 } + 8 : UInt64) = { toBitVec := sp } by
    apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega] at hrsp1
  subst hrsp1 hr141 hrbp1
  apply Eventually.done
  exact ⟨rfl, rfl, rfl, rfl, stk1, hstk1, by ecancel⟩

end E2eScal
