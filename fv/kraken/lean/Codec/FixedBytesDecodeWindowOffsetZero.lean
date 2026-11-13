import Codec.FixedBytesDecodeWindow
import Machine.Labels

/-!
# The fixed-bytes decode segment, offset-0 form, over windows with the receiver registers as parameters

`f = append(make([]byte, 0, n), buf[0:n]...)` (the first SSZ field: no `add $src,%rbx`). The first block is
`bytesDecHeadRegister rX …` (`Codec/FixedBytesDecodeWindow.lean`); the second is `bytesDecMidOffsetZeroRegisters rX rY …` = `bytesDecMidOffsetZero` (`Codec/FixedBytesDecode.lean`) with
the receiver registers as parameters. Statement `BytesDecOffsetZeroWindow n rX rY` = the statement of `bytesdec_seg_offset_zero` over
two windows (`jl` = index of the label, `jm` = index of `callq runtime.memmove`, `e` = end), register fact
`regs.get64 rY = rcv`. Proof: one theorem per case (the proof text of `bytesdec_seg_offset_zero` with the window tactics).
Same limits as `Codec/FixedBytesDecodeWindow.lean` (`rX` ∈ {rdx, rsi}, `rY` ∈ {rax, rcx, rdx, rsi, rdi}, `n` ∈ {32, 48, 96}). At the
four development sites of this form the code is dense with rdx (no observed variation): the instance of the
dense lemma is `bytesdec_seg_offset_zero_inst`.
-/

open Machine Runtime

namespace Codec

/-- Second block, offset-0 form: `bytesDecMidOffsetZero` with the receiver registers `rX` (before the copy) and `rY` (after). -/
def bytesDecMidOffsetZeroRegisters (rX rY : Reg64) (n : Int64) (lff lwb : String) (dR dB dS fP fL fC : Int64) : Program :=
  [Kraken.Directive.label lff,
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rsp)) none (ConstExpr.int64 dS)))
       (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rax Width.W64))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg rX)) none (ConstExpr.int64 fP)))
       (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rax Width.W64))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.reg (Reg.low Reg64.rbx Width.W64))
       (Operand.regOrMem (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rsp)) none (ConstExpr.int64 dB)))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W32
     (Operation.mov (RegOrMem.reg (Reg.low Reg64.rcx Width.W32)) (Operand.imm (ConstExpr.int64 n)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.call (RelRegOrMem.rel ((ConstExpr.label "runtime.memmove").sub ConstExpr.after_current_instruction)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.reg (Reg.low rY Width.W64))
       (Operand.regOrMem (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rsp)) none (ConstExpr.int64 dR)))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg rY)) none (ConstExpr.int64 fL)))
       (Operand.imm (ConstExpr.int64 n)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg rY)) none (ConstExpr.int64 fC)))
       (Operand.imm (ConstExpr.int64 n)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W32
     (Operation.cmp (RegOrMem.mem (AddrExpr.mk (some RegOrRip.rip) none ((ConstExpr.label "runtime.writeBarrier").sub ConstExpr.after_current_instruction)))
       (Operand.imm (ConstExpr.int64 0)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64 (Operation.jcc CondCode.nz lwb))]

variable [Host]

/-- Statement of the offset-0 fixed-bytes decode segment over two windows with the receiver registers. -/
abbrev BytesDecOffsetZeroWindow (n : Nat) (rX rY : Reg64) : Prop :=
  ∀ (lff lwb : String) (dR dB dS fP fL fC : Int64) (qA qB : Program) (j1 j2 jl jm e : Nat)
    (hqA : qA.IsInfixAt Host.prog j1) (heA : eraseNop qA = bytesDecHeadRegister rX (OfNat.ofNat n) lff dR fL fC)
    (hqB : qB.IsInfixAt Host.prog j2)
    (heB : eraseNop qB = bytesDecMidOffsetZeroRegisters rX rY (OfNat.ofNat n) lff lwb dR dB dS fP fL fC)
    (hjl : j2 + nonNopIndex qB 0 = jl) (hl : label lff = Host.addrOf jl)
    (hjm : j2 + nonNopIndex qB 5 = jm) (hend : j2 + qB.length = e)
    (sp rcv bf aR aB aS aRet aLo aP aL aC : BitVec 64) (St : Nat)
    (hR : sp + dR.toBitVec = aR) (hB' : sp + dB.toBitVec = aB) (hS : sp + dS.toBitVec = aS)
    (hRet : sp - 8 = aRet) (hLo : sp - 8 - BitVec.ofNat 64 St = aLo)
    (hP : rcv + fP.toBitVec = aP) (hL : rcv + fL.toBitVec = aL) (hC : rcv + fC.toBitVec = aC)
    (rbp0 r140 : UInt64) (root : List UInt8) (hroot : root.length = n)
    (spl rslot lo lS vP vL vC : List UInt8)
    (hspl : spl.length = 24) (hrs : rslot.length = 8) (hlo : lo.length = St) (hlS : lS.length = 8)
    (hvP : vP.length = 8) (hvL : vL.length = 8) (hvC : vC.length = 8)
    (R : DataMem → Prop) (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : n ≤ avail)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
      ⋆ Eq (spl.At sp) ⋆ Eq (rslot.At aRet) ⋆ Eq (lo.At aLo) ⋆ Eq (lS.At aS)
      ⋆ Heap avail
      ⋆ Eq (vP.At aP) ⋆ Eq (vL.At aL) ⋆ Eq (vC.At aC)
      ⋆ Eq (root.At bf)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hms : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 St) (hmm : MemmoveContract St),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf e ∧ st.data.regs.rsp = { toBitVec := sp }
        ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        ∃ (p : BitVec 64) (spl' lo' : List UInt8), spl'.length = 24 ∧ lo'.length = St
          ∧ st.data.regs.get64 rY = rcv ∧
        (Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
          ⋆ Eq (spl'.At sp)
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (jm + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq (lo'.At aLo)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aS)
          ⋆ Heap (avail - n)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aP) ⋆ Eq ((Int.toBytes 8 (OfNat.ofNat n)).At aL)
          ⋆ Eq ((Int.toBytes 8 (OfNat.ofNat n)).At aC) ⋆ Eq (root.At p)
          ⋆ Eq (root.At bf)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf j1⟩

set_option hygiene false in
/-- Proof text of one case (size, registers literal); the names are the binders of `BytesDecOffsetZeroWindow`. -/
local macro "bytes_decode_window_offset_zero_case " n:num rX:term:max rY:term:max : tactic => `(tactic| (
    replace heA : eraseNop qA = bytesDecHeadRegister $rX ($n : Int64) lff dR fL fC := heA
    replace heB : eraseNop qB = bytesDecMidOffsetZeroRegisters $rX $rY ($n : Int64) lff lwb dR dB dS fP fL fC := heB
    rw [show (OfNat.ofNat ($n : Nat) : Int) = ($n : Int) from rfl]
    obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
    simp only at hrsp hrbp hr14 h_mem ⊢
    subst rsp rbp r14 hRet hLo hjl hjm
    window_skip_leading_nops hqA
    window_step_directive hqA heA bytesDecHeadRegister 0
    window_skip_nops hqA heA 0
    window_step_directive hqA heA bytesDecHeadRegister 1
    intro _
    window_skip_nops hqA heA 1
    window_step_directive hqA heA bytesDecHeadRegister 2
    window_skip_nops hqA heA 2
    window_step_directive hqA heA bytesDecHeadRegister 3
    apply store_step_at _ _ (sp - 8) _ _ _ rslot _ _ (by segment_addr) (by ecancel) (by exact hrs)
    intro m1' H1
    simp only [Width.bytes, Width.bits] at H1
    unfold_step
    try rw [show sp - 8#64 = sp - 8 from rfl] at *
    refine eventually_trans _ _ _ _ (hms _ (Host.addrOf (j1 + nonNopIndex qA 3 + 1)) $n avail lo spl _
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
    window_step_directive hqA heA bytesDecHeadRegister 4
    apply load_step_at _ _ aR _ _ (Int.toBytes 8 rcv.toInt) _ _ (by rw [← hR]) (by ecancel)
      (by exact Int.toBytes_length 8 _)
    unfold_step
    window_skip_nops hqA heA 4
    window_step_directive hqA heA bytesDecHeadRegister 5
    apply store_step_at _ _ aL _ _ _ vL _ _ (by rw [← hL]) (by ecancel) (by exact hvL)
    intro m2' H2
    simp only [Width.bytes, Width.bits] at H2
    unfold_step
    window_skip_nops hqA heA 5
    window_step_directive hqA heA bytesDecHeadRegister 6
    apply store_step_at _ _ aC _ _ _ vC _ _ (by rw [← hC]) (by ecancel) (by exact hvC)
    intro m3' H3
    simp only [Width.bytes, Width.bits] at H3
    unfold_step
    window_skip_nops hqA heA 6
    window_step_directive hqA heA bytesDecHeadRegister 7
    apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
    simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
    unfold_step
    window_skip_nops hqA heA 7
    window_step_directive hqA heA bytesDecHeadRegister 8
    split
    case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    simp only [Effects.All]
    rw [hl]
    window_step_directive hqB heB bytesDecMidOffsetZeroRegisters 0
    window_skip_nops hqB heB 0
    window_step_directive hqB heB bytesDecMidOffsetZeroRegisters 1
    apply store_step_at _ _ aS _ _ _ lS _ _ (by rw [← hS]) (by ecancel) (by exact hlS)
    intro m4' H4
    simp only [Width.bytes, Width.bits] at H4
    unfold_step
    window_skip_nops hqB heB 1
    window_step_directive hqB heB bytesDecMidOffsetZeroRegisters 2
    apply store_step_at _ _ aP _ _ _ vP _ _ (by rw [← hP]) (by ecancel) (by exact hvP)
    intro m5' H5
    simp only [Width.bytes, Width.bits] at H5
    unfold_step
    window_skip_nops hqB heB 2
    window_step_directive hqB heB bytesDecMidOffsetZeroRegisters 3
    apply load_step_at _ _ aB _ _ (Int.toBytes 8 bf.toInt) _ _ (by rw [← hB']) (by ecancel)
      (by exact Int.toBytes_length 8 _)
    unfold_step
    window_skip_nops hqB heB 3
    window_step_directive hqB heB bytesDecMidOffsetZeroRegisters 4
    window_skip_nops hqB heB 4
    window_step_directive hqB heB bytesDecMidOffsetZeroRegisters 5
    apply store_step_at _ _ (sp - 8) _ _ _ (Int.toBytes 8 (Host.addrOf (j1 + nonNopIndex qA 3 + 1)).toBitVec.toInt) _ _
      (by segment_addr) (by ecancel) (by exact Int.toBytes_length 8 _)
    intro m6' H6
    simp only [Width.bytes, Width.bits] at H6
    unfold_step
    try rw [show sp - 8#64 = sp - 8 from rfl] at *
    refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (j2 + nonNopIndex qB 5 + 1)) root (List.replicate $n 0) stk3 _
      (by rw [hroot]; rfl) (by simp [hroot]) hstk3
      (by dsimp only; ecancel)) ?_
    rintro ⟨d4, pc4⟩ ⟨hpc4, hrsp4, hr144, hrbp4, stk4, hstk4, Hm4⟩
    dsimp only at hpc4 hrsp4 hr144 hrbp4 Hm4
    subst hpc4
    obtain ⟨⟨rax4, rbx4, rcx4, rdx4, rsi4, rdi4, rsp4, rbp4, r84, r94, r104, r114, r124, r134, r144, r154⟩,
      zmms4, flags4, mem4⟩ := d4
    simp only at hrsp4 hr144 hrbp4 Hm4
    rw [show ({ toBitVec := sp - 8 } + 8 : UInt64) = { toBitVec := sp } by
      apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega] at hrsp4
    subst hrsp4 hr144 hrbp4
    window_skip_nops hqB heB 5
    window_step_directive hqB heB bytesDecMidOffsetZeroRegisters 6
    apply load_step_at _ _ aR _ _ (Int.toBytes 8 rcv.toInt) _ _ (by rw [← hR]) (by ecancel)
      (by exact Int.toBytes_length 8 _)
    unfold_step
    window_skip_nops hqB heB 6
    window_step_directive hqB heB bytesDecMidOffsetZeroRegisters 7
    apply store_step_at _ _ aL _ _ _ (Int.toBytes 8 (BitVec.toInt (0 : BitVec 64))) _ _ (by rw [← hL])
      (by ecancel) (by exact Int.toBytes_length 8 _)
    intro m7' H7
    simp only [Width.bytes, Width.bits] at H7
    unfold_step
    window_skip_nops hqB heB 7
    window_step_directive hqB heB bytesDecMidOffsetZeroRegisters 8
    apply store_step_at _ _ aC _ _ _ (Int.toBytes 8 (BitVec.toInt ($n : BitVec 64))) _ _ (by rw [← hC])
      (by ecancel) (by exact Int.toBytes_length 8 _)
    intro m8' H8
    simp only [Width.bytes, Width.bits] at H8
    unfold_step
    window_skip_nops hqB heB 8
    window_step_directive hqB heB bytesDecMidOffsetZeroRegisters 9
    apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
    simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
    unfold_step
    window_skip_nops hqB heB 9
    window_step_directive hqB heB bytesDecMidOffsetZeroRegisters 10
    split
    case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    simp only [Effects.All]
    window_skip_to_end hqB heB 10 hend
    apply Eventually.done
    simp only [show Int.toBytes 8 (BitVec.toInt ($n : BitVec 64)) = Int.toBytes 8 $n by decide] at H8
    exact ⟨rfl, rfl, rfl, rfl, rax3.toBitVec, spm3, stk4, hspm3, hstk4, rfl, by ecancel⟩))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_offset_zero_32_rdx_rax : BytesDecOffsetZeroWindow 32 Reg64.rdx Reg64.rax := by
  intro lff lwb dR dB dS fP fL fC qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window_offset_zero_case 32 Reg64.rdx Reg64.rax

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_offset_zero_32_rdx_rcx : BytesDecOffsetZeroWindow 32 Reg64.rdx Reg64.rcx := by
  intro lff lwb dR dB dS fP fL fC qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window_offset_zero_case 32 Reg64.rdx Reg64.rcx

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_offset_zero_32_rdx_rdx : BytesDecOffsetZeroWindow 32 Reg64.rdx Reg64.rdx := by
  intro lff lwb dR dB dS fP fL fC qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window_offset_zero_case 32 Reg64.rdx Reg64.rdx

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_offset_zero_32_rdx_rsi : BytesDecOffsetZeroWindow 32 Reg64.rdx Reg64.rsi := by
  intro lff lwb dR dB dS fP fL fC qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window_offset_zero_case 32 Reg64.rdx Reg64.rsi

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_offset_zero_32_rdx_rdi : BytesDecOffsetZeroWindow 32 Reg64.rdx Reg64.rdi := by
  intro lff lwb dR dB dS fP fL fC qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window_offset_zero_case 32 Reg64.rdx Reg64.rdi

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_offset_zero_32_rsi_rax : BytesDecOffsetZeroWindow 32 Reg64.rsi Reg64.rax := by
  intro lff lwb dR dB dS fP fL fC qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window_offset_zero_case 32 Reg64.rsi Reg64.rax

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_offset_zero_32_rsi_rcx : BytesDecOffsetZeroWindow 32 Reg64.rsi Reg64.rcx := by
  intro lff lwb dR dB dS fP fL fC qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window_offset_zero_case 32 Reg64.rsi Reg64.rcx

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_offset_zero_32_rsi_rdx : BytesDecOffsetZeroWindow 32 Reg64.rsi Reg64.rdx := by
  intro lff lwb dR dB dS fP fL fC qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window_offset_zero_case 32 Reg64.rsi Reg64.rdx

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_offset_zero_32_rsi_rsi : BytesDecOffsetZeroWindow 32 Reg64.rsi Reg64.rsi := by
  intro lff lwb dR dB dS fP fL fC qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window_offset_zero_case 32 Reg64.rsi Reg64.rsi

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_offset_zero_32_rsi_rdi : BytesDecOffsetZeroWindow 32 Reg64.rsi Reg64.rdi := by
  intro lff lwb dR dB dS fP fL fC qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window_offset_zero_case 32 Reg64.rsi Reg64.rdi

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_offset_zero_48_rdx_rax : BytesDecOffsetZeroWindow 48 Reg64.rdx Reg64.rax := by
  intro lff lwb dR dB dS fP fL fC qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window_offset_zero_case 48 Reg64.rdx Reg64.rax

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_offset_zero_48_rdx_rcx : BytesDecOffsetZeroWindow 48 Reg64.rdx Reg64.rcx := by
  intro lff lwb dR dB dS fP fL fC qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window_offset_zero_case 48 Reg64.rdx Reg64.rcx

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_offset_zero_48_rdx_rdx : BytesDecOffsetZeroWindow 48 Reg64.rdx Reg64.rdx := by
  intro lff lwb dR dB dS fP fL fC qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window_offset_zero_case 48 Reg64.rdx Reg64.rdx

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_offset_zero_48_rdx_rsi : BytesDecOffsetZeroWindow 48 Reg64.rdx Reg64.rsi := by
  intro lff lwb dR dB dS fP fL fC qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window_offset_zero_case 48 Reg64.rdx Reg64.rsi

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_offset_zero_48_rdx_rdi : BytesDecOffsetZeroWindow 48 Reg64.rdx Reg64.rdi := by
  intro lff lwb dR dB dS fP fL fC qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window_offset_zero_case 48 Reg64.rdx Reg64.rdi

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_offset_zero_48_rsi_rax : BytesDecOffsetZeroWindow 48 Reg64.rsi Reg64.rax := by
  intro lff lwb dR dB dS fP fL fC qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window_offset_zero_case 48 Reg64.rsi Reg64.rax

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_offset_zero_48_rsi_rcx : BytesDecOffsetZeroWindow 48 Reg64.rsi Reg64.rcx := by
  intro lff lwb dR dB dS fP fL fC qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window_offset_zero_case 48 Reg64.rsi Reg64.rcx

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_offset_zero_48_rsi_rdx : BytesDecOffsetZeroWindow 48 Reg64.rsi Reg64.rdx := by
  intro lff lwb dR dB dS fP fL fC qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window_offset_zero_case 48 Reg64.rsi Reg64.rdx

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_offset_zero_48_rsi_rsi : BytesDecOffsetZeroWindow 48 Reg64.rsi Reg64.rsi := by
  intro lff lwb dR dB dS fP fL fC qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window_offset_zero_case 48 Reg64.rsi Reg64.rsi

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_offset_zero_48_rsi_rdi : BytesDecOffsetZeroWindow 48 Reg64.rsi Reg64.rdi := by
  intro lff lwb dR dB dS fP fL fC qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window_offset_zero_case 48 Reg64.rsi Reg64.rdi

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_offset_zero_96_rdx_rax : BytesDecOffsetZeroWindow 96 Reg64.rdx Reg64.rax := by
  intro lff lwb dR dB dS fP fL fC qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window_offset_zero_case 96 Reg64.rdx Reg64.rax

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_offset_zero_96_rdx_rcx : BytesDecOffsetZeroWindow 96 Reg64.rdx Reg64.rcx := by
  intro lff lwb dR dB dS fP fL fC qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window_offset_zero_case 96 Reg64.rdx Reg64.rcx

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_offset_zero_96_rdx_rdx : BytesDecOffsetZeroWindow 96 Reg64.rdx Reg64.rdx := by
  intro lff lwb dR dB dS fP fL fC qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window_offset_zero_case 96 Reg64.rdx Reg64.rdx

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_offset_zero_96_rdx_rsi : BytesDecOffsetZeroWindow 96 Reg64.rdx Reg64.rsi := by
  intro lff lwb dR dB dS fP fL fC qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window_offset_zero_case 96 Reg64.rdx Reg64.rsi

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_offset_zero_96_rdx_rdi : BytesDecOffsetZeroWindow 96 Reg64.rdx Reg64.rdi := by
  intro lff lwb dR dB dS fP fL fC qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window_offset_zero_case 96 Reg64.rdx Reg64.rdi

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_offset_zero_96_rsi_rax : BytesDecOffsetZeroWindow 96 Reg64.rsi Reg64.rax := by
  intro lff lwb dR dB dS fP fL fC qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window_offset_zero_case 96 Reg64.rsi Reg64.rax

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_offset_zero_96_rsi_rcx : BytesDecOffsetZeroWindow 96 Reg64.rsi Reg64.rcx := by
  intro lff lwb dR dB dS fP fL fC qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window_offset_zero_case 96 Reg64.rsi Reg64.rcx

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_offset_zero_96_rsi_rdx : BytesDecOffsetZeroWindow 96 Reg64.rsi Reg64.rdx := by
  intro lff lwb dR dB dS fP fL fC qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window_offset_zero_case 96 Reg64.rsi Reg64.rdx

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_offset_zero_96_rsi_rsi : BytesDecOffsetZeroWindow 96 Reg64.rsi Reg64.rsi := by
  intro lff lwb dR dB dS fP fL fC qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window_offset_zero_case 96 Reg64.rsi Reg64.rsi

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_offset_zero_96_rsi_rdi : BytesDecOffsetZeroWindow 96 Reg64.rsi Reg64.rdi := by
  intro lff lwb dR dB dS fP fL fC qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window_offset_zero_case 96 Reg64.rsi Reg64.rdi

/-- **Fixed-bytes decode segment over windows, offset-0 form, receiver registers as parameters**. -/
theorem bytesdec_seg_offset_zero_window (n : Nat) (hn : n = 32 ∨ n = 48 ∨ n = 96) (rX rY : Reg64)
    (hX : rX = Reg64.rdx ∨ rX = Reg64.rsi)
    (hY : rY = Reg64.rax ∨ rY = Reg64.rcx ∨ rY = Reg64.rdx ∨ rY = Reg64.rsi ∨ rY = Reg64.rdi) :
    BytesDecOffsetZeroWindow n rX rY := by
  rcases hn with rfl | rfl | rfl <;> rcases hX with rfl | rfl <;> rcases hY with rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact bytesdec_window_offset_zero_32_rdx_rax
    | exact bytesdec_window_offset_zero_32_rdx_rcx
    | exact bytesdec_window_offset_zero_32_rdx_rdx
    | exact bytesdec_window_offset_zero_32_rdx_rsi
    | exact bytesdec_window_offset_zero_32_rdx_rdi
    | exact bytesdec_window_offset_zero_32_rsi_rax
    | exact bytesdec_window_offset_zero_32_rsi_rcx
    | exact bytesdec_window_offset_zero_32_rsi_rdx
    | exact bytesdec_window_offset_zero_32_rsi_rsi
    | exact bytesdec_window_offset_zero_32_rsi_rdi
    | exact bytesdec_window_offset_zero_48_rdx_rax
    | exact bytesdec_window_offset_zero_48_rdx_rcx
    | exact bytesdec_window_offset_zero_48_rdx_rdx
    | exact bytesdec_window_offset_zero_48_rdx_rsi
    | exact bytesdec_window_offset_zero_48_rdx_rdi
    | exact bytesdec_window_offset_zero_48_rsi_rax
    | exact bytesdec_window_offset_zero_48_rsi_rcx
    | exact bytesdec_window_offset_zero_48_rsi_rdx
    | exact bytesdec_window_offset_zero_48_rsi_rsi
    | exact bytesdec_window_offset_zero_48_rsi_rdi
    | exact bytesdec_window_offset_zero_96_rdx_rax
    | exact bytesdec_window_offset_zero_96_rdx_rcx
    | exact bytesdec_window_offset_zero_96_rdx_rdx
    | exact bytesdec_window_offset_zero_96_rdx_rsi
    | exact bytesdec_window_offset_zero_96_rdx_rdi
    | exact bytesdec_window_offset_zero_96_rsi_rax
    | exact bytesdec_window_offset_zero_96_rsi_rcx
    | exact bytesdec_window_offset_zero_96_rsi_rdx
    | exact bytesdec_window_offset_zero_96_rsi_rsi
    | exact bytesdec_window_offset_zero_96_rsi_rdi

/-- The dense lemma `bytesdec_seg_offset_zero` is the rdx instance of `bytesdec_seg_offset_zero_window` (same statement). -/
theorem bytesdec_seg_offset_zero_inst : type_of% (@bytesdec_seg_offset_zero ‹Host›) := by
  intro n hn lff lwb dR dB dS fP fL fC j1 j2 hA hB hl
  exact bytesdec_seg_offset_zero_window n hn Reg64.rdx Reg64.rdx (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl)))
    lff lwb dR dB dS fP fL fC _ _ j1 j2 j2 (j2 + 5) (j2 + 11) hA rfl hB rfl rfl hl rfl rfl

set_option linter.unusedVariables false in
/-- Offset-0 fixed-bytes decode segment statement kind over windows (parameters as `bytesDecSegKindWindow`, no `src`). -/
abbrev bytesDecSegOffsetZeroKindWindow (n : Nat) (C : Program) (rY : Reg64) (j1 jm e : Nat) (dR dB dS fP fL fC : Int64) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k)
    (sp rcv bf aR aB aS aRet aLo aP aL aC : BitVec 64) (St : Nat)
    (hR : sp + dR.toBitVec = aR) (hB' : sp + dB.toBitVec = aB) (hS : sp + dS.toBitVec = aS)
    (hRet : sp - 8 = aRet) (hLo : sp - 8 - BitVec.ofNat 64 St = aLo)
    (hP : rcv + fP.toBitVec = aP) (hL : rcv + fL.toBitVec = aL) (hC : rcv + fC.toBitVec = aC)
    (rbp0 r140 : UInt64) (root : List UInt8) (hroot : root.length = n)
    (spl rslot lo lS vP vL vC : List UInt8)
    (hspl : spl.length = 24) (hrs : rslot.length = 8) (hlo : lo.length = St) (hlS : lS.length = 8)
    (hvP : vP.length = 8) (hvL : vL.length = 8) (hvC : vC.length = 8)
    (R : DataMem → Prop) (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : n ≤ avail)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
      ⋆ Eq (spl.At sp) ⋆ Eq (rslot.At aRet) ⋆ Eq (lo.At aLo) ⋆ Eq (lS.At aS)
      ⋆ Heap avail
      ⋆ Eq (vP.At aP) ⋆ Eq (vL.At aL) ⋆ Eq (vC.At aC)
      ⋆ Eq (root.At bf)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hms : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 St) (hmm : MemmoveContract St),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + e) ∧ st.data.regs.rsp = { toBitVec := sp }
        ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        ∃ (p : BitVec 64) (spl' lo' : List UInt8), spl'.length = 24 ∧ lo'.length = St
          ∧ st.data.regs.get64 rY = rcv ∧
        (Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
          ⋆ Eq (spl'.At sp)
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + jm + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq (lo'.At aLo)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aS)
          ⋆ Heap (avail - n)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aP) ⋆ Eq ((Int.toBytes 8 (OfNat.ofNat n)).At aL)
          ⋆ Eq ((Int.toBytes 8 (OfNat.ofNat n)).At aC) ⋆ Eq (root.At p)
          ⋆ Eq (root.At bf)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + j1)⟩

/-- `bytesDecSegOffsetZeroKindWindow` follows from `bytesdec_seg_offset_zero_window` and the window facts of an instance. -/
theorem bytesDecSegOffsetZeroKindWindow_of (n : Nat) (hn : n = 32 ∨ n = 48 ∨ n = 96) (C : Program) (rX rY : Reg64)
    (hX : rX = Reg64.rdx ∨ rX = Reg64.rsi)
    (hY : rY = Reg64.rax ∨ rY = Reg64.rcx ∨ rY = Reg64.rdx ∨ rY = Reg64.rsi ∨ rY = Reg64.rdi)
    (j1 j2 jl jm e : Nat) (lff lwb : String) (dR dB dS fP fL fC : Int64) (qA qB : Program)
    (hqA : ∀ k, C.IsInfixAt Host.prog k → qA.IsInfixAt Host.prog (k + j1))
    (heA : eraseNop qA = bytesDecHeadRegister rX (OfNat.ofNat n) lff dR fL fC)
    (hqB : ∀ k, C.IsInfixAt Host.prog k → qB.IsInfixAt Host.prog (k + j2))
    (heB : eraseNop qB = bytesDecMidOffsetZeroRegisters rX rY (OfNat.ofNat n) lff lwb dR dB dS fP fL fC)
    (hjl : j2 + nonNopIndex qB 0 = jl)
    (hl : ∀ k, C.IsInfixAt Host.prog k → LabelsFresh C k → label lff = Host.addrOf (k + jl))
    (hjm : j2 + nonNopIndex qB 5 = jm) (hend : j2 + qB.length = e) :
    bytesDecSegOffsetZeroKindWindow n C rY j1 jm e dR dB dS fP fL fC :=
  fun k hk hf => bytesdec_seg_offset_zero_window n hn rX rY hX hY lff lwb dR dB dS fP fL fC qA qB (k + j1) (k + j2) (k + jl)
    (k + jm) (k + e) (hqA k hk) heA (hqB k hk) heB (by omega) (hl k hk hf) (by omega) (by omega)

end Codec
