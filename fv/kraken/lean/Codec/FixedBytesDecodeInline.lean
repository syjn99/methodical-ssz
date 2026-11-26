import Codec.FixedBytesDecodeWindow
import Machine.Bytes

/-!
# The 4-byte fixed-bytes decode segment with an inline copy, over windows

Go 1.26.10 compiles `f = append(make([]byte, 0, 4), buf[src:src+4]...)` without a `runtime.memmove` call.
The copy is one 32-bit load and one 32-bit store (`mov src(%rB),%eT; mov %eT,(%rax)`).
The code has three blocks with write-barrier blocks between them (not taken when `runtime.writeBarrier` is 0):

* `bytesDecodeHeadRegister rX 4 …` (`Codec/FixedBytesDecodeWindow.lean`): `makeslice` of 4 bytes, `je lff`;
* `bytesDecodeInlineMiddle rX rB rT …`: from `lff:` to `je lwb` (the jump is taken);
* `bytesDecodeInlineTail rX …`: from `lwb:`, the pointer store `mov %rax,fP(%rX)`.

`rX` holds the receiver, `rB` the buffer, `rT` is the 32-bit temporary.
Each block is a window (`Codec/NopWindow.lean`): a `nop` may stand anywhere.
`jl` and `jw` are the indices of the labels `lff` and `lwb`, `jc` the index of `callq runtime.makeslice`.
Its return address stays in the return slot.
`e` is the end of the third window.

Statement `BytesDecodeInlineWindow rX rB rT`: the field gets a new 4-byte heap chunk `p` with the source bytes.
Length and capacity are 4.
At the end `rX` holds the receiver and `rB` the buffer.
Contract: `MakesliceContract` with stack `St`; no `MemmoveContract`.
Proof: one theorem per register case; `bytes_decode_inline_segment_window` collects them.
The register sets (`rX` = rdx; (`rB`, `rT`) = (rsi, rdi) or (rbx, rsi)) are the forms of the link set.
They are a limit of the proof method (literal registers in the machine steps), not of the code shape.
-/

open Machine Runtime

namespace Codec

/-- Second block (from `lff:` to `je lwb`): the pointer store, the buffer reload into `rB`, the 4-byte copy
through the 32-bit register `rT`, the length and capacity stores of 4, the write-barrier test. -/
def bytesDecodeInlineMiddle (rX rB rT : Reg64) (lff lwb : String) (dB fP fL fC src : Int64) : Program :=
  [Kraken.Directive.label lff,
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg rX)) none (ConstExpr.int64 fP)))
       (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rax Width.W64))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.reg (Reg.low rB Width.W64))
       (Operand.regOrMem (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rsp)) none (ConstExpr.int64 dB)))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W32
     (Operation.mov (RegOrMem.reg (Reg.low rT Width.W32))
       (Operand.regOrMem (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg rB)) none (ConstExpr.int64 src)))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W32
     (Operation.mov (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rax)) none (ConstExpr.int64 0)))
       (Operand.regOrMem (RegOrMem.reg (Reg.low rT Width.W32))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg rX)) none (ConstExpr.int64 fL)))
       (Operand.imm (ConstExpr.int64 4)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg rX)) none (ConstExpr.int64 fC)))
       (Operand.imm (ConstExpr.int64 4)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W32
     (Operation.cmp (RegOrMem.mem (AddrExpr.mk (some RegOrRip.rip) none ((ConstExpr.label "runtime.writeBarrier").sub ConstExpr.after_current_instruction)))
       (Operand.imm (ConstExpr.int64 0)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64 (Operation.jcc CondCode.z lwb))]

/-- Third block (from `lwb:`): the pointer store after the write-barrier block. -/
def bytesDecodeInlineTail (rX : Reg64) (lwb : String) (fP : Int64) : Program :=
  [Kraken.Directive.label lwb,
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg rX)) none (ConstExpr.int64 fP)))
       (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rax Width.W64)))))]

variable [Host]

set_option linter.unusedVariables false in
/-- Statement of the 4-byte inline decode segment over three windows with the registers `rX`, `rB`, `rT`. -/
abbrev BytesDecodeInlineWindow (rX rB rT : Reg64) : Prop :=
  ∀ (lff lwb : String) (dR dB fP fL fC src : Int64) (qA qB qC : Program) (j1 j2 j3 jl jw jc e : Nat)
    (hqA : qA.IsInfixAt Host.prog j1) (heA : eraseNop qA = bytesDecodeHeadRegister rX 4 lff dR fL fC)
    (hqB : qB.IsInfixAt Host.prog j2) (heB : eraseNop qB = bytesDecodeInlineMiddle rX rB rT lff lwb dB fP fL fC src)
    (hqC : qC.IsInfixAt Host.prog j3) (heC : eraseNop qC = bytesDecodeInlineTail rX lwb fP)
    (hjl : j2 + nonNopIndex qB 0 = jl) (hl : label lff = Host.addrOf jl)
    (hjw : j3 + nonNopIndex qC 0 = jw) (hw : label lwb = Host.addrOf jw)
    (hjc : j1 + nonNopIndex qA 3 = jc) (hend : j3 + qC.length = e)
    (sp rcv bf aR aB aRet aLo aP aL aC aSrc : BitVec 64) (St : Nat)
    (hR : sp + dR.toBitVec = aR) (hB' : sp + dB.toBitVec = aB)
    (hRet : sp - 8 = aRet) (hLo : sp - 8 - BitVec.ofNat 64 St = aLo)
    (hP : rcv + fP.toBitVec = aP) (hL : rcv + fL.toBitVec = aL) (hC : rcv + fC.toBitVec = aC)
    (hSrc : bf + src.toBitVec = aSrc)
    (rbp0 r140 : UInt64) (root : List UInt8) (hroot : root.length = 4)
    (spl rslot lo vP vL vC : List UInt8)
    (hspl : spl.length = 24) (hrs : rslot.length = 8) (hlo : lo.length = St)
    (hvP : vP.length = 8) (hvL : vL.length = 8) (hvC : vC.length = 8)
    (R : DataMem → Prop) (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 4 ≤ avail)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
      ⋆ Eq (spl.At sp) ⋆ Eq (rslot.At aRet) ⋆ Eq (lo.At aLo)
      ⋆ Heap avail
      ⋆ Eq (vP.At aP) ⋆ Eq (vL.At aL) ⋆ Eq (vC.At aC)
      ⋆ Eq (root.At aSrc)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hms : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 St),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf e ∧ st.data.regs.rsp = { toBitVec := sp }
        ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        ∃ (p : BitVec 64) (spl' lo' : List UInt8), spl'.length = 24 ∧ lo'.length = St
          ∧ st.data.regs.get64 rX = rcv ∧ st.data.regs.get64 rB = bf ∧
        (Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
          ⋆ Eq (spl'.At sp)
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (jc + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq (lo'.At aLo)
          ⋆ Heap (avail - 4)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aP) ⋆ Eq ((Int.toBytes 8 4).At aL)
          ⋆ Eq ((Int.toBytes 8 4).At aC) ⋆ Eq (root.At p)
          ⋆ Eq (root.At aSrc)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf j1⟩

set_option hygiene false in
/-- Proof text of one register case; the names are the binders of `BytesDecodeInlineWindow`. -/
local macro "bytes_decode_inline_window_case" : tactic => `(tactic| (
    obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
    simp only at hrsp hrbp hr14 h_mem ⊢
    subst rsp rbp r14 hRet hLo hjl hjw hjc
    window_skip_leading_nops hqA
    window_step_directive hqA heA bytesDecodeHeadRegister 0
    window_skip_nops hqA heA 0
    window_step_directive hqA heA bytesDecodeHeadRegister 1
    intro _
    window_skip_nops hqA heA 1
    window_step_directive hqA heA bytesDecodeHeadRegister 2
    window_skip_nops hqA heA 2
    window_step_directive hqA heA bytesDecodeHeadRegister 3
    apply store_step_at _ _ (sp - 8) _ _ _ rslot _ _ (by segment_addr) (by ecancel) (by exact hrs)
    intro m1' H1
    simp only [Width.bytes, Width.bits] at H1
    unfold_step
    try rw [show sp - 8#64 = sp - 8 from rfl] at *
    refine eventually_trans _ _ _ _ (hms _ (Host.addrOf (j1 + nonNopIndex qA 3 + 1)) 4 avail lo spl _
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
    window_skip_nops hqA heA 3
    window_step_directive hqA heA bytesDecodeHeadRegister 4
    apply load_step_at _ _ aR _ _ (Int.toBytes 8 rcv.toInt) _ _ (by rw [← hR]) (by ecancel)
      (by exact Int.toBytes_length 8 _)
    unfold_step
    window_skip_nops hqA heA 4
    window_step_directive hqA heA bytesDecodeHeadRegister 5
    apply store_step_at _ _ aL _ _ _ vL _ _ (by rw [← hL]) (by ecancel) (by exact hvL)
    intro m2' H2
    simp only [Width.bytes, Width.bits] at H2
    unfold_step
    window_skip_nops hqA heA 5
    window_step_directive hqA heA bytesDecodeHeadRegister 6
    apply store_step_at _ _ aC _ _ _ vC _ _ (by rw [← hC]) (by ecancel) (by exact hvC)
    intro m3' H3
    simp only [Width.bytes, Width.bits] at H3
    unfold_step
    window_skip_nops hqA heA 6
    window_step_directive hqA heA bytesDecodeHeadRegister 7
    apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
    simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
    unfold_step
    window_skip_nops hqA heA 7
    window_step_directive hqA heA bytesDecodeHeadRegister 8
    split
    case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    simp only [Effects.All]
    rw [hl]
    window_step_directive hqB heB bytesDecodeInlineMiddle 0
    window_skip_nops hqB heB 0
    window_step_directive hqB heB bytesDecodeInlineMiddle 1
    apply store_step_at _ _ aP _ _ _ vP _ _ (by rw [← hP]) (by ecancel) (by exact hvP)
    intro m4' H4
    simp only [Width.bytes, Width.bits] at H4
    unfold_step
    window_skip_nops hqB heB 1
    window_step_directive hqB heB bytesDecodeInlineMiddle 2
    apply load_step_at _ _ aB _ _ (Int.toBytes 8 bf.toInt) _ _ (by rw [← hB']) (by ecancel)
      (by exact Int.toBytes_length 8 _)
    unfold_step
    window_skip_nops hqB heB 2
    window_step_directive hqB heB bytesDecodeInlineMiddle 3
    apply load_step_at _ _ aSrc _ _ root _ _ (by rw [← hSrc]) (by ecancel) (by exact hroot)
    unfold_step
    window_skip_nops hqB heB 3
    window_step_directive hqB heB bytesDecodeInlineMiddle 4
    apply store_step_at _ _ rax3.toBitVec _ _ _ (List.replicate 4 0) _ _ rfl (by ecancel) (by simp)
    intro m5' H5
    simp only [Width.bytes, Width.bits, Machine.zx32, toBytes_ofInt_ofBytes 32 4 rfl root hroot] at H5
    unfold_step
    window_skip_nops hqB heB 4
    window_step_directive hqB heB bytesDecodeInlineMiddle 5
    apply store_step_at _ _ aL _ _ _ (Int.toBytes 8 (BitVec.toInt (0 : BitVec 64))) _ _ (by rw [← hL])
      (by ecancel) (by exact Int.toBytes_length 8 _)
    intro m6' H6
    simp only [Width.bytes, Width.bits] at H6
    unfold_step
    window_skip_nops hqB heB 5
    window_step_directive hqB heB bytesDecodeInlineMiddle 6
    apply store_step_at _ _ aC _ _ _ (Int.toBytes 8 (BitVec.toInt (4 : BitVec 64))) _ _ (by rw [← hC])
      (by ecancel) (by exact Int.toBytes_length 8 _)
    intro m7' H7
    simp only [Width.bytes, Width.bits] at H7
    unfold_step
    window_skip_nops hqB heB 6
    window_step_directive hqB heB bytesDecodeInlineMiddle 7
    apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
    simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
    unfold_step
    window_skip_nops hqB heB 7
    window_step_directive hqB heB bytesDecodeInlineMiddle 8
    split
    case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    simp only [Effects.All]
    rw [hw]
    window_step_directive hqC heC bytesDecodeInlineTail 0
    window_skip_nops hqC heC 0
    window_step_directive hqC heC bytesDecodeInlineTail 1
    apply store_step_at _ _ aP _ _ _ (Int.toBytes 8 rax3.toBitVec.toInt) _ _ (by rw [← hP]) (by ecancel)
      (by exact Int.toBytes_length 8 _)
    intro m8' H8
    simp only [Width.bytes, Width.bits] at H8
    unfold_step
    window_skip_to_end hqC heC 1 hend
    apply Eventually.done
    simp only [show Int.toBytes 8 (BitVec.toInt (4 : BitVec 64)) = Int.toBytes 8 4 by decide] at H8
    exact ⟨rfl, rfl, rfl, rfl, rax3.toBitVec, spm3, stk3, hspm3, hstk3, rfl, rfl, by ecancel⟩))

theorem bytes_decode_inline_window_rdx_rsi_rdi : BytesDecodeInlineWindow Reg64.rdx Reg64.rsi Reg64.rdi := by
  intro lff lwb dR dB fP fL fC src qA qB qC j1 j2 j3 jl jw jc e hqA heA hqB heB hqC heC hjl hl hjw hw hjc hend sp rcv bf aR aB aRet aLo aP aL aC aSrc St hR hB' hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo vP vL vC hspl hrs hlo hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms
  bytes_decode_inline_window_case

theorem bytes_decode_inline_window_rdx_rbx_rsi : BytesDecodeInlineWindow Reg64.rdx Reg64.rbx Reg64.rsi := by
  intro lff lwb dR dB fP fL fC src qA qB qC j1 j2 j3 jl jw jc e hqA heA hqB heB hqC heC hjl hl hjw hw hjc hend sp rcv bf aR aB aRet aLo aP aL aC aSrc St hR hB' hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo vP vL vC hspl hrs hlo hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms
  bytes_decode_inline_window_case

/-- **4-byte fixed-bytes decode segment with an inline copy, over windows** (registers as parameters). -/
theorem bytes_decode_inline_segment_window (rX rB rT : Reg64) (hX : rX = Reg64.rdx)
    (hBT : (rB = Reg64.rsi ∧ rT = Reg64.rdi) ∨ (rB = Reg64.rbx ∧ rT = Reg64.rsi)) :
    BytesDecodeInlineWindow rX rB rT := by
  subst hX
  rcases hBT with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact bytes_decode_inline_window_rdx_rsi_rdi
  · exact bytes_decode_inline_window_rdx_rbx_rsi

end Codec
