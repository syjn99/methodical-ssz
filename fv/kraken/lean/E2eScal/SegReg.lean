import E2eScal.SegN
import E2eScal.NopView

/-!
# GEN4: the fixed-bytes decode segment over windows, parametric in the receiver registers

`f = append(make([]byte, 0, n), buf[src:src+n]...)` (add form, `n` = 32, 48 or 96). The templates
`bytesDecHeadR rX …` / `bytesDecMidR rX rY …` are `bytesDecHead` / `bytesDecMid` (`SegN.lean`) with the register
of the receiver reload as a parameter: `rX` after `callq runtime.makeslice` (rdx at all 14 development
sites), `rY` after `callq runtime.memmove` (rdx at 13 sites, rax at SyncCommitteeMessage.BlockRoot, the H5
miss P-H5-1). Both blocks are WINDOWS (`NopView.lean`): a `nop` may stand anywhere, for example before
`callq runtime.makeslice` (finding SG-3). `jl` is the index of the label `lff`, `jm` the index of the
`callq runtime.memmove` (its return address stays in the return slot), `e` the end of the second window.

Statement `BytesDecG4 n rX rY` = the statement of `bytesdec_seg` with these changes and the register fact
`regs.get64 rY = rcv`. Proof: one theorem per case (the proof text of `bytesdec_seg` with the window tactics);
`bytesdec_seg_g4` collects them. The register sets (`rX` ∈ {rdx, rsi}, `rY` ∈ {rax, rcx, rdx, rsi, rdi}) and
the sizes are limits of the proof method (literal registers and immediates in the machine steps), not of the
code shape: another register or size is one more case line. Contracts `MakesliceC`, `MemmoveC` exactly as in
`bytesdec_seg`. Not here: the offset-0 form (`bytesdec_seg_z`).
-/

open Fk

namespace E2eScal

/-- First block: `bytesDecHead` with the receiver register `rX`. -/
def bytesDecHeadR (rX : Reg64) (n : Int64) (lff : String) (dR fL fC : Int64) : Program :=
  [Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.lea (Reg.low Reg64.rax Width.W64)
       (AddrExpr.mk (some RegOrRip.rip) none (((ConstExpr.label "type__").add (ConstExpr.int64 387072)).sub ConstExpr.after_current_instruction)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W32
     (Operation.xor (RegOrMem.reg (Reg.low Reg64.rbx Width.W32))
       (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rbx Width.W32))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W32
     (Operation.mov (RegOrMem.reg (Reg.low Reg64.rcx Width.W32)) (Operand.imm (ConstExpr.int64 n)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.call (RelRegOrMem.rel ((ConstExpr.label "runtime.makeslice").sub ConstExpr.after_current_instruction)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.reg (Reg.low rX Width.W64))
       (Operand.regOrMem (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rsp)) none (ConstExpr.int64 dR)))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg rX)) none (ConstExpr.int64 fL)))
       (Operand.imm (ConstExpr.int64 0)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg rX)) none (ConstExpr.int64 fC)))
       (Operand.imm (ConstExpr.int64 n)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W32
     (Operation.cmp (RegOrMem.mem (AddrExpr.mk (some RegOrRip.rip) none ((ConstExpr.label "runtime.writeBarrier").sub ConstExpr.after_current_instruction)))
       (Operand.imm (ConstExpr.int64 0)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64 (Operation.jcc CondCode.z lff))]

/-- Second block, add form: `bytesDecMid` with the receiver registers `rX` (before the copy) and `rY` (after). -/
def bytesDecMidR (rX rY : Reg64) (n : Int64) (lff lwb : String) (dR dB dS fP fL fC src : Int64) : Program :=
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
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.add (RegOrMem.reg (Reg.low Reg64.rbx Width.W64)) (Operand.imm (ConstExpr.int64 src)))),
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

/-- Statement of the fixed-bytes decode segment over two windows with the receiver registers `rX`, `rY`. -/
abbrev BytesDecG4 (n : Nat) (rX rY : Reg64) : Prop :=
  ∀ (lff lwb : String) (dR dB dS fP fL fC src : Int64) (qA qB : Program) (j1 j2 jl jm e : Nat)
    (hqA : qA.IsInfixAt Host.prog j1) (heA : eraseNop qA = bytesDecHeadR rX (OfNat.ofNat n) lff dR fL fC)
    (hqB : qB.IsInfixAt Host.prog j2)
    (heB : eraseNop qB = bytesDecMidR rX rY (OfNat.ofNat n) lff lwb dR dB dS fP fL fC src)
    (hjl : j2 + nopPos qB 0 = jl) (hl : label lff = Host.addrOf jl)
    (hjm : j2 + nopPos qB 6 = jm) (hend : j2 + qB.length = e)
    (sp rcv bf aR aB aS aRet aLo aP aL aC aSrc : BitVec 64) (St : Nat)
    (hR : sp + dR.toBitVec = aR) (hB' : sp + dB.toBitVec = aB) (hS : sp + dS.toBitVec = aS)
    (hRet : sp - 8 = aRet) (hLo : sp - 8 - BitVec.ofNat 64 St = aLo)
    (hP : rcv + fP.toBitVec = aP) (hL : rcv + fL.toBitVec = aL) (hC : rcv + fC.toBitVec = aC)
    (hSrc : bf + src.toBitVec = aSrc)
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
      ⋆ Eq (root.At aSrc)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hms : MakesliceC Heap E2e.Data.e2eU8Type_addr 1 St) (hmm : MemmoveC St),
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
          ⋆ Eq (root.At aSrc)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf j1⟩

set_option hygiene false in
/-- Proof text of one case (size, registers literal); the names are the binders of `BytesDecG4`. -/
local macro "bytesdec_g4c " n:num rX:term:max rY:term:max : tactic => `(tactic| (
    replace heA : eraseNop qA = bytesDecHeadR $rX ($n : Int64) lff dR fL fC := heA
    replace heB : eraseNop qB = bytesDecMidR $rX $rY ($n : Int64) lff lwb dR dB dS fP fL fC src := heB
    rw [show (OfNat.ofNat ($n : Nat) : Int) = ($n : Int) from rfl]
    obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
    simp only at hrsp hrbp hr14 h_mem ⊢
    subst rsp rbp r14 hRet hLo hjl hjm
    kwin hqA
    kwat hqA heA bytesDecHeadR 0
    kwnx hqA heA 0
    kwat hqA heA bytesDecHeadR 1
    intro _
    kwnx hqA heA 1
    kwat hqA heA bytesDecHeadR 2
    kwnx hqA heA 2
    kwat hqA heA bytesDecHeadR 3
    apply store_step_at _ _ (sp - 8) _ _ _ rslot _ _ (by saddr) (by ecancel) (by exact hrs)
    intro m1' H1
    simp only [Width.bytes, Width.bits] at H1
    kunfold
    try rw [show sp - 8#64 = sp - 8 from rfl] at *
    refine eventually_trans _ _ _ _ (hms _ (Host.addrOf (j1 + nopPos qA 3 + 1)) $n avail lo spl _
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
    kwnx hqA heA 3
    kwat hqA heA bytesDecHeadR 4
    apply load_step_at _ _ aR _ _ (Int.toBytes 8 rcv.toInt) _ _ (by rw [← hR]) (by ecancel)
      (by exact Int.toBytes_length 8 _)
    kunfold
    kwnx hqA heA 4
    kwat hqA heA bytesDecHeadR 5
    apply store_step_at _ _ aL _ _ _ vL _ _ (by rw [← hL]) (by ecancel) (by exact hvL)
    intro m2' H2
    simp only [Width.bytes, Width.bits] at H2
    kunfold
    kwnx hqA heA 5
    kwat hqA heA bytesDecHeadR 6
    apply store_step_at _ _ aC _ _ _ vC _ _ (by rw [← hC]) (by ecancel) (by exact hvC)
    intro m3' H3
    simp only [Width.bytes, Width.bits] at H3
    kunfold
    kwnx hqA heA 6
    kwat hqA heA bytesDecHeadR 7
    apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
    simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
    kunfold
    kwnx hqA heA 7
    kwat hqA heA bytesDecHeadR 8
    split
    case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    simp only [Effects.All]
    rw [hl]
    kwat hqB heB bytesDecMidR 0
    kwnx hqB heB 0
    kwat hqB heB bytesDecMidR 1
    apply store_step_at _ _ aS _ _ _ lS _ _ (by rw [← hS]) (by ecancel) (by exact hlS)
    intro m4' H4
    simp only [Width.bytes, Width.bits] at H4
    kunfold
    kwnx hqB heB 1
    kwat hqB heB bytesDecMidR 2
    apply store_step_at _ _ aP _ _ _ vP _ _ (by rw [← hP]) (by ecancel) (by exact hvP)
    intro m5' H5
    simp only [Width.bytes, Width.bits] at H5
    kunfold
    kwnx hqB heB 2
    kwat hqB heB bytesDecMidR 3
    apply load_step_at _ _ aB _ _ (Int.toBytes 8 bf.toInt) _ _ (by rw [← hB']) (by ecancel)
      (by exact Int.toBytes_length 8 _)
    kunfold
    kwnx hqB heB 3
    kwat hqB heB bytesDecMidR 4
    kwnx hqB heB 4
    kwat hqB heB bytesDecMidR 5
    kwnx hqB heB 5
    kwat hqB heB bytesDecMidR 6
    apply store_step_at _ _ (sp - 8) _ _ _ (Int.toBytes 8 (Host.addrOf (j1 + nopPos qA 3 + 1)).toBitVec.toInt) _ _
      (by saddr) (by ecancel) (by exact Int.toBytes_length 8 _)
    intro m6' H6
    simp only [Width.bytes, Width.bits] at H6
    kunfold
    try rw [show sp - 8#64 = sp - 8 from rfl] at *
    refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (j2 + nopPos qB 6 + 1)) root (List.replicate $n 0) stk3 _
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
    kwnx hqB heB 6
    kwat hqB heB bytesDecMidR 7
    apply load_step_at _ _ aR _ _ (Int.toBytes 8 rcv.toInt) _ _ (by rw [← hR]) (by ecancel)
      (by exact Int.toBytes_length 8 _)
    kunfold
    kwnx hqB heB 7
    kwat hqB heB bytesDecMidR 8
    apply store_step_at _ _ aL _ _ _ (Int.toBytes 8 (BitVec.toInt (0 : BitVec 64))) _ _ (by rw [← hL])
      (by ecancel) (by exact Int.toBytes_length 8 _)
    intro m7' H7
    simp only [Width.bytes, Width.bits] at H7
    kunfold
    kwnx hqB heB 8
    kwat hqB heB bytesDecMidR 9
    apply store_step_at _ _ aC _ _ _ (Int.toBytes 8 (BitVec.toInt ($n : BitVec 64))) _ _ (by rw [← hC])
      (by ecancel) (by exact Int.toBytes_length 8 _)
    intro m8' H8
    simp only [Width.bytes, Width.bits] at H8
    kunfold
    kwnx hqB heB 9
    kwat hqB heB bytesDecMidR 10
    apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
    simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
    kunfold
    kwnx hqB heB 10
    kwat hqB heB bytesDecMidR 11
    split
    case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    simp only [Effects.All]
    kwend hqB heB 11 hend
    apply Eventually.done
    simp only [show Int.toBytes 8 (BitVec.toInt ($n : BitVec 64)) = Int.toBytes 8 $n by decide] at H8
    exact ⟨rfl, rfl, rfl, rfl, rax3.toBitVec, spm3, stk4, hspm3, hstk4, rfl, by ecancel⟩))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_g4_32_rdx_rax : BytesDecG4 32 Reg64.rdx Reg64.rax := by
  intro lff lwb dR dB dS fP fL fC src qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytesdec_g4c 32 Reg64.rdx Reg64.rax

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_g4_32_rdx_rcx : BytesDecG4 32 Reg64.rdx Reg64.rcx := by
  intro lff lwb dR dB dS fP fL fC src qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytesdec_g4c 32 Reg64.rdx Reg64.rcx

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_g4_32_rdx_rdx : BytesDecG4 32 Reg64.rdx Reg64.rdx := by
  intro lff lwb dR dB dS fP fL fC src qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytesdec_g4c 32 Reg64.rdx Reg64.rdx

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_g4_32_rdx_rsi : BytesDecG4 32 Reg64.rdx Reg64.rsi := by
  intro lff lwb dR dB dS fP fL fC src qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytesdec_g4c 32 Reg64.rdx Reg64.rsi

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_g4_32_rdx_rdi : BytesDecG4 32 Reg64.rdx Reg64.rdi := by
  intro lff lwb dR dB dS fP fL fC src qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytesdec_g4c 32 Reg64.rdx Reg64.rdi

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_g4_32_rsi_rax : BytesDecG4 32 Reg64.rsi Reg64.rax := by
  intro lff lwb dR dB dS fP fL fC src qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytesdec_g4c 32 Reg64.rsi Reg64.rax

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_g4_32_rsi_rcx : BytesDecG4 32 Reg64.rsi Reg64.rcx := by
  intro lff lwb dR dB dS fP fL fC src qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytesdec_g4c 32 Reg64.rsi Reg64.rcx

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_g4_32_rsi_rdx : BytesDecG4 32 Reg64.rsi Reg64.rdx := by
  intro lff lwb dR dB dS fP fL fC src qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytesdec_g4c 32 Reg64.rsi Reg64.rdx

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_g4_32_rsi_rsi : BytesDecG4 32 Reg64.rsi Reg64.rsi := by
  intro lff lwb dR dB dS fP fL fC src qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytesdec_g4c 32 Reg64.rsi Reg64.rsi

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_g4_32_rsi_rdi : BytesDecG4 32 Reg64.rsi Reg64.rdi := by
  intro lff lwb dR dB dS fP fL fC src qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytesdec_g4c 32 Reg64.rsi Reg64.rdi

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_g4_48_rdx_rax : BytesDecG4 48 Reg64.rdx Reg64.rax := by
  intro lff lwb dR dB dS fP fL fC src qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytesdec_g4c 48 Reg64.rdx Reg64.rax

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_g4_48_rdx_rcx : BytesDecG4 48 Reg64.rdx Reg64.rcx := by
  intro lff lwb dR dB dS fP fL fC src qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytesdec_g4c 48 Reg64.rdx Reg64.rcx

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_g4_48_rdx_rdx : BytesDecG4 48 Reg64.rdx Reg64.rdx := by
  intro lff lwb dR dB dS fP fL fC src qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytesdec_g4c 48 Reg64.rdx Reg64.rdx

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_g4_48_rdx_rsi : BytesDecG4 48 Reg64.rdx Reg64.rsi := by
  intro lff lwb dR dB dS fP fL fC src qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytesdec_g4c 48 Reg64.rdx Reg64.rsi

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_g4_48_rdx_rdi : BytesDecG4 48 Reg64.rdx Reg64.rdi := by
  intro lff lwb dR dB dS fP fL fC src qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytesdec_g4c 48 Reg64.rdx Reg64.rdi

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_g4_48_rsi_rax : BytesDecG4 48 Reg64.rsi Reg64.rax := by
  intro lff lwb dR dB dS fP fL fC src qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytesdec_g4c 48 Reg64.rsi Reg64.rax

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_g4_48_rsi_rcx : BytesDecG4 48 Reg64.rsi Reg64.rcx := by
  intro lff lwb dR dB dS fP fL fC src qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytesdec_g4c 48 Reg64.rsi Reg64.rcx

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_g4_48_rsi_rdx : BytesDecG4 48 Reg64.rsi Reg64.rdx := by
  intro lff lwb dR dB dS fP fL fC src qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytesdec_g4c 48 Reg64.rsi Reg64.rdx

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_g4_48_rsi_rsi : BytesDecG4 48 Reg64.rsi Reg64.rsi := by
  intro lff lwb dR dB dS fP fL fC src qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytesdec_g4c 48 Reg64.rsi Reg64.rsi

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_g4_48_rsi_rdi : BytesDecG4 48 Reg64.rsi Reg64.rdi := by
  intro lff lwb dR dB dS fP fL fC src qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytesdec_g4c 48 Reg64.rsi Reg64.rdi

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_g4_96_rdx_rax : BytesDecG4 96 Reg64.rdx Reg64.rax := by
  intro lff lwb dR dB dS fP fL fC src qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytesdec_g4c 96 Reg64.rdx Reg64.rax

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_g4_96_rdx_rcx : BytesDecG4 96 Reg64.rdx Reg64.rcx := by
  intro lff lwb dR dB dS fP fL fC src qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytesdec_g4c 96 Reg64.rdx Reg64.rcx

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_g4_96_rdx_rdx : BytesDecG4 96 Reg64.rdx Reg64.rdx := by
  intro lff lwb dR dB dS fP fL fC src qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytesdec_g4c 96 Reg64.rdx Reg64.rdx

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_g4_96_rdx_rsi : BytesDecG4 96 Reg64.rdx Reg64.rsi := by
  intro lff lwb dR dB dS fP fL fC src qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytesdec_g4c 96 Reg64.rdx Reg64.rsi

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_g4_96_rdx_rdi : BytesDecG4 96 Reg64.rdx Reg64.rdi := by
  intro lff lwb dR dB dS fP fL fC src qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytesdec_g4c 96 Reg64.rdx Reg64.rdi

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_g4_96_rsi_rax : BytesDecG4 96 Reg64.rsi Reg64.rax := by
  intro lff lwb dR dB dS fP fL fC src qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytesdec_g4c 96 Reg64.rsi Reg64.rax

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_g4_96_rsi_rcx : BytesDecG4 96 Reg64.rsi Reg64.rcx := by
  intro lff lwb dR dB dS fP fL fC src qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytesdec_g4c 96 Reg64.rsi Reg64.rcx

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_g4_96_rsi_rdx : BytesDecG4 96 Reg64.rsi Reg64.rdx := by
  intro lff lwb dR dB dS fP fL fC src qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytesdec_g4c 96 Reg64.rsi Reg64.rdx

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_g4_96_rsi_rsi : BytesDecG4 96 Reg64.rsi Reg64.rsi := by
  intro lff lwb dR dB dS fP fL fC src qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytesdec_g4c 96 Reg64.rsi Reg64.rsi

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_g4_96_rsi_rdi : BytesDecG4 96 Reg64.rsi Reg64.rdi := by
  intro lff lwb dR dB dS fP fL fC src qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytesdec_g4c 96 Reg64.rsi Reg64.rdi

/-- **Fixed-bytes decode segment over windows, receiver registers as parameters** (add form). -/
theorem bytesdec_seg_g4 (n : Nat) (hn : n = 32 ∨ n = 48 ∨ n = 96) (rX rY : Reg64)
    (hX : rX = Reg64.rdx ∨ rX = Reg64.rsi)
    (hY : rY = Reg64.rax ∨ rY = Reg64.rcx ∨ rY = Reg64.rdx ∨ rY = Reg64.rsi ∨ rY = Reg64.rdi) :
    BytesDecG4 n rX rY := by
  rcases hn with rfl | rfl | rfl <;> rcases hX with rfl | rfl <;> rcases hY with rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact bytesdec_g4_32_rdx_rax
    | exact bytesdec_g4_32_rdx_rcx
    | exact bytesdec_g4_32_rdx_rdx
    | exact bytesdec_g4_32_rdx_rsi
    | exact bytesdec_g4_32_rdx_rdi
    | exact bytesdec_g4_32_rsi_rax
    | exact bytesdec_g4_32_rsi_rcx
    | exact bytesdec_g4_32_rsi_rdx
    | exact bytesdec_g4_32_rsi_rsi
    | exact bytesdec_g4_32_rsi_rdi
    | exact bytesdec_g4_48_rdx_rax
    | exact bytesdec_g4_48_rdx_rcx
    | exact bytesdec_g4_48_rdx_rdx
    | exact bytesdec_g4_48_rdx_rsi
    | exact bytesdec_g4_48_rdx_rdi
    | exact bytesdec_g4_48_rsi_rax
    | exact bytesdec_g4_48_rsi_rcx
    | exact bytesdec_g4_48_rsi_rdx
    | exact bytesdec_g4_48_rsi_rsi
    | exact bytesdec_g4_48_rsi_rdi
    | exact bytesdec_g4_96_rdx_rax
    | exact bytesdec_g4_96_rdx_rcx
    | exact bytesdec_g4_96_rdx_rdx
    | exact bytesdec_g4_96_rdx_rsi
    | exact bytesdec_g4_96_rdx_rdi
    | exact bytesdec_g4_96_rsi_rax
    | exact bytesdec_g4_96_rsi_rcx
    | exact bytesdec_g4_96_rsi_rdx
    | exact bytesdec_g4_96_rsi_rsi
    | exact bytesdec_g4_96_rsi_rdi

end E2eScal
