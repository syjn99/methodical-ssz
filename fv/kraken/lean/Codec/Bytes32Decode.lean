import Codec.SegmentTemplate
import Runtime.Contracts
import Prysm.ElfData.PrysmTarget

/-!
# The 32-byte field decode segment: `f = make([]byte, 0, 32); f = append(f, buf[src:src+32]...)`

Go 1.26.10 compiles the 32-byte field decode of a protoc container (`Checkpoint.Root`,
`AttestationData.BeaconBlockRoot`) to two code blocks:

* `rootDecodeHead lff dR fL fC` (9 directives): `lea type:uint8,%rax; xor %ebx,%ebx;
  mov $0x20,%ecx; callq runtime.makeslice; mov dR(%rsp),%rdx` (reload the receiver),
  `movq $0x0,fL(%rdx); movq $0x20,fC(%rdx)` (slice length and capacity),
  `cmpl $0x0,runtime.writeBarrier(%rip); je lff`;
* `rootDecodeMiddle lff lwb dR dB dS fP fL fC src` (12 directives): `lff:`, `mov %rax,dS(%rsp)` (save
  the new pointer), `mov %rax,fP(%rdx)` (slice pointer), `mov dB(%rsp),%rbx; add $src,%rbx;
  mov $0x20,%ecx; callq runtime.memmove`, reload the receiver, `movq $0x20,fL(%rdx);
  movq $0x20,fC(%rdx)`, `cmpl $0x0,runtime.writeBarrier(%rip); jne lwb`.

The write-barrier blocks between them (not taken when `runtime.writeBarrier` is 0) and the
code after the second test (which register gets the pointer back, `nop`, jump) differ per
instance and are not part of the template. Parameters: the labels `lff`, `lwb`; the stack
displacements of the receiver spill `dR`, the buffer spill `dB` and the pointer slot `dS`;
the field displacements `fP`, `fL`, `fC` (field offset, +8, +16); the source offset `src`;
the places `j1`, `j2` of the two blocks and the address of `lff`. Addresses in the statement
are parameters with equations (`sp + dR = aR`, `rcv + fP = aP`, …) so that an instance
states them in its own form.

`sp` is rsp at the segment (the bottom of the caller's frame); the callees get the 24-byte
argument area at `sp`, the return slot at `aRet = sp − 8` and `St` stack bytes below it
(`MakesliceContract` / `MemmoveContract` with stack `St`).
-/

open Machine Runtime

namespace Codec

/-- First block of the P2 decode segment (from the `lea` of `type:uint8` to `je lff`). -/
def rootDecodeHead (lff : String) (dR fL fC : Int64) : Program :=
  [Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.lea (Reg.low Reg64.rax Width.W64)
       (AddrExpr.mk (some RegOrRip.rip) none (((ConstExpr.label "type__").add (ConstExpr.int64 387072)).sub ConstExpr.after_current_instruction)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W32
     (Operation.xor (RegOrMem.reg (Reg.low Reg64.rbx Width.W32))
       (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rbx Width.W32))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W32
     (Operation.mov (RegOrMem.reg (Reg.low Reg64.rcx Width.W32)) (Operand.imm (ConstExpr.int64 32)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.call (RelRegOrMem.rel ((ConstExpr.label "runtime.makeslice").sub ConstExpr.after_current_instruction)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.reg (Reg.low Reg64.rdx Width.W64))
       (Operand.regOrMem (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rsp)) none (ConstExpr.int64 dR)))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rdx)) none (ConstExpr.int64 fL)))
       (Operand.imm (ConstExpr.int64 0)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rdx)) none (ConstExpr.int64 fC)))
       (Operand.imm (ConstExpr.int64 32)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W32
     (Operation.cmp (RegOrMem.mem (AddrExpr.mk (some RegOrRip.rip) none ((ConstExpr.label "runtime.writeBarrier").sub ConstExpr.after_current_instruction)))
       (Operand.imm (ConstExpr.int64 0)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64 (Operation.jcc CondCode.z lff))]

/-- Second block of the P2 decode segment (from `lff:` to `jne lwb`). -/
def rootDecodeMiddle (lff lwb : String) (dR dB dS fP fL fC src : Int64) : Program :=
  [Kraken.Directive.label lff,
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rsp)) none (ConstExpr.int64 dS)))
       (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rax Width.W64))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rdx)) none (ConstExpr.int64 fP)))
       (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rax Width.W64))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.reg (Reg.low Reg64.rbx Width.W64))
       (Operand.regOrMem (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rsp)) none (ConstExpr.int64 dB)))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.add (RegOrMem.reg (Reg.low Reg64.rbx Width.W64)) (Operand.imm (ConstExpr.int64 src)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W32
     (Operation.mov (RegOrMem.reg (Reg.low Reg64.rcx Width.W32)) (Operand.imm (ConstExpr.int64 32)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.call (RelRegOrMem.rel ((ConstExpr.label "runtime.memmove").sub ConstExpr.after_current_instruction)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.reg (Reg.low Reg64.rdx Width.W64))
       (Operand.regOrMem (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rsp)) none (ConstExpr.int64 dR)))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rdx)) none (ConstExpr.int64 fL)))
       (Operand.imm (ConstExpr.int64 32)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rdx)) none (ConstExpr.int64 fC)))
       (Operand.imm (ConstExpr.int64 32)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W32
     (Operation.cmp (RegOrMem.mem (AddrExpr.mk (some RegOrRip.rip) none ((ConstExpr.label "runtime.writeBarrier").sub ConstExpr.after_current_instruction)))
       (Operand.imm (ConstExpr.int64 0)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64 (Operation.jcc CondCode.nz lwb))]

variable [Host]

/-- Address equation by `toNat` and `omega`. -/
macro "segment_addr" : tactic => `(tactic| (
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_neg, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat,
    UInt64.toNat_toBitVec, UInt64.toBitVec_add, UInt64.toBitVec_ofNat, Width.bits, Nat.reducePow]
  all_goals omega))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- **P2 decode segment lemma**: from the first block (at `j1`) to the `jne` of the second
block (at `j2`, `label lff = Host.addrOf j2`), with `runtime.writeBarrier` = 0. The field gets
a new 32-byte heap chunk `p` holding the source bytes, length and capacity 32; `p` is also in
the slot `aS`; rdx holds the receiver. -/
theorem root_decode_segment (lff lwb : String) (dR dB dS fP fL fC src : Int64) (j1 j2 : Nat)
    (hA : (rootDecodeHead lff dR fL fC).IsInfixAt Host.prog j1)
    (hB : (rootDecodeMiddle lff lwb dR dB dS fP fL fC src).IsInfixAt Host.prog j2)
    (hl : label lff = Host.addrOf j2)
    (sp rcv bf aR aB aS aRet aLo aP aL aC aSrc : BitVec 64) (St : Nat)
    (hR : sp + dR.toBitVec = aR) (hB' : sp + dB.toBitVec = aB) (hS : sp + dS.toBitVec = aS)
    (hRet : sp - 8 = aRet) (hLo : sp - 8 - BitVec.ofNat 64 St = aLo)
    (hP : rcv + fP.toBitVec = aP) (hL : rcv + fL.toBitVec = aL) (hC : rcv + fC.toBitVec = aC)
    (hSrc : bf + src.toBitVec = aSrc)
    (rbp0 r140 : UInt64) (root : List UInt8) (hroot : root.length = 32)
    (spl rslot lo lS vP vL vC : List UInt8)
    (hspl : spl.length = 24) (hrs : rslot.length = 8) (hlo : lo.length = St) (hlS : lS.length = 8)
    (hvP : vP.length = 8) (hvL : vL.length = 8) (hvC : vC.length = 8)
    (R : DataMem → Prop) (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 32 ≤ avail)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
      ⋆ Eq (spl.At sp) ⋆ Eq (rslot.At aRet) ⋆ Eq (lo.At aLo) ⋆ Eq (lS.At aS)
      ⋆ Heap avail
      ⋆ Eq (vP.At aP) ⋆ Eq (vL.At aL) ⋆ Eq (vC.At aC)
      ⋆ Eq (root.At aSrc)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hms : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 St) (hmm : MemmoveContract St) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (j2 + 12) ∧ st.data.regs.rsp = { toBitVec := sp }
        ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        ∃ (p : BitVec 64) (spl' lo' : List UInt8), spl'.length = 24 ∧ lo'.length = St
          ∧ st.data.regs.rdx.toBitVec = rcv ∧
        (Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
          ⋆ Eq (spl'.At sp)
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (j2 + 6 + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq (lo'.At aLo)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aS)
          ⋆ Heap (avail - 32)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aP) ⋆ Eq ((Int.toBytes 8 32).At aL)
          ⋆ Eq ((Int.toBytes 8 32).At aC) ⋆ Eq (root.At p)
          ⋆ Eq (root.At aSrc)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf j1⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp hrbp hr14 h_mem ⊢
  subst rsp rbp r14 hRet hLo
  step_directive hA rootDecodeHead 0
  step_directive hA rootDecodeHead 1
  intro _
  step_directive hA rootDecodeHead 2
  step_directive hA rootDecodeHead 3
  apply store_step_at _ _ (sp - 8) _ _ _ rslot _ _ (by segment_addr) (by ecancel) (by exact hrs)
  intro m1' H1
  simp only [Width.bytes, Width.bits] at H1
  unfold_step
  try rw [show sp - 8#64 = sp - 8 from rfl] at *
  refine eventually_trans _ _ _ _ (hms _ (Host.addrOf (j1 + 3 + 1)) 32 avail lo spl _
    rfl (by simp) (by rfl) (by omega) (by unfold maxAlloc; omega) (by omega) hlo hspl
    (by dsimp only; rw [show sp - 8 + 8 = sp by bv_omega]; ecancel)) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrsp3, hr143, hrbp3, stk3, spm3, hstk3, hspm3, Hm3⟩
  dsimp only at hpc3 hrsp3 hr143 hrbp3 Hm3
  subst hpc3
  obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,
    zmms3, flags3, mem3⟩ := d3
  simp only at hrsp3 hr143 hrbp3 Hm3
  rw [show ({ toBitVec := sp - 8 } + 8 : UInt64) = { toBitVec := sp } by
    apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega] at hrsp3
  subst hrsp3 hr143 hrbp3
  rw [show sp - 8 + 8 = sp by bv_omega] at Hm3
  simp only [Nat.one_mul] at Hm3
  step_directive hA rootDecodeHead 4
  apply load_step_at _ _ aR _ _ (Int.toBytes 8 rcv.toInt) _ _ (by rw [← hR]) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hA rootDecodeHead 5
  apply store_step_at _ _ aL _ _ _ vL _ _ (by rw [← hL]) (by ecancel) (by exact hvL)
  intro m2' H2
  simp only [Width.bytes, Width.bits] at H2
  unfold_step
  step_directive hA rootDecodeHead 6
  apply store_step_at _ _ aC _ _ _ vC _ _ (by rw [← hC]) (by ecancel) (by exact hvC)
  intro m3' H3
  simp only [Width.bytes, Width.bits] at H3
  unfold_step
  step_directive hA rootDecodeHead 7
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  unfold_step
  step_directive hA rootDecodeHead 8
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  rw [hl]
  step_directive hB rootDecodeMiddle 0
  step_directive hB rootDecodeMiddle 1
  apply store_step_at _ _ aS _ _ _ lS _ _ (by rw [← hS]) (by ecancel) (by exact hlS)
  intro m4' H4
  simp only [Width.bytes, Width.bits] at H4
  unfold_step
  step_directive hB rootDecodeMiddle 2
  apply store_step_at _ _ aP _ _ _ vP _ _ (by rw [← hP]) (by ecancel) (by exact hvP)
  intro m5' H5
  simp only [Width.bytes, Width.bits] at H5
  unfold_step
  step_directive hB rootDecodeMiddle 3
  apply load_step_at _ _ aB _ _ (Int.toBytes 8 bf.toInt) _ _ (by rw [← hB']) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hB rootDecodeMiddle 4
  step_directive hB rootDecodeMiddle 5
  step_directive hB rootDecodeMiddle 6
  apply store_step_at _ _ (sp - 8) _ _ _ (Int.toBytes 8 (Host.addrOf (j1 + 3 + 1)).toBitVec.toInt) _ _
    (by segment_addr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m6' H6
  simp only [Width.bytes, Width.bits] at H6
  unfold_step
  try rw [show sp - 8#64 = sp - 8 from rfl] at *
  refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (j2 + 6 + 1)) root (List.replicate 32 0) stk3 _
    (by rw [hroot]; rfl) (by simp [hroot]) hstk3
    (by dsimp only; rw [show src.toBitVec + bf = aSrc by rw [← hSrc]; exact BitVec.add_comm _ _]; ecancel)) ?_
  rintro ⟨d4, pc4⟩ ⟨hpc4, hrsp4, hr144, hrbp4, stk4, hstk4, Hm4⟩
  dsimp only at hpc4 hrsp4 hr144 hrbp4 Hm4
  subst hpc4
  obtain ⟨⟨rax4, rbx4, rcx4, rdx4, rsi4, rdi4, rsp4, rbp4, r84, r94, r104, r114, r124, r134, r144, r154⟩,
    zmms4, flags4, mem4⟩ := d4
  simp only at hrsp4 hr144 hrbp4 Hm4
  rw [show ({ toBitVec := sp - 8 } + 8 : UInt64) = { toBitVec := sp } by
    apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega] at hrsp4
  subst hrsp4 hr144 hrbp4
  rw [show src.toBitVec + bf = aSrc by rw [← hSrc]; exact BitVec.add_comm _ _] at Hm4
  step_directive hB rootDecodeMiddle 7
  apply load_step_at _ _ aR _ _ (Int.toBytes 8 rcv.toInt) _ _ (by rw [← hR]) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hB rootDecodeMiddle 8
  apply store_step_at _ _ aL _ _ _ (Int.toBytes 8 (BitVec.toInt (0 : BitVec 64))) _ _ (by rw [← hL])
    (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m7' H7
  simp only [Width.bytes, Width.bits] at H7
  unfold_step
  step_directive hB rootDecodeMiddle 9
  apply store_step_at _ _ aC _ _ _ (Int.toBytes 8 (BitVec.toInt (32 : BitVec 64))) _ _ (by rw [← hC])
    (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m8' H8
  simp only [Width.bytes, Width.bits] at H8
  unfold_step
  step_directive hB rootDecodeMiddle 10
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  unfold_step
  step_directive hB rootDecodeMiddle 11
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  apply Eventually.done
  simp only [show Int.toBytes 8 (BitVec.toInt (32 : BitVec 64)) = Int.toBytes 8 32 by decide] at H8
  exact ⟨rfl, rfl, rfl, rfl, rax3.toBitVec, spm3, stk4, hspm3, hstk4, rfl, by ecancel⟩

end Codec
