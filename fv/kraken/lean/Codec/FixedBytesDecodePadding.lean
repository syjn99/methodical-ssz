import Codec.Kind.FixedBytesDecode
import Prysm.Deposit_Data.DecodeFieldSegmentPadding

/-!
# GEN3 L2: fixed-bytes decode segment tolerant of the compiler padding `nop`

Added after the H4 hold-out (FINDINGS SG-3, miss M2). Survey of the 13 byte segments of the development
decoders: one padding variant, a `nop` between `mov $n,%ecx` and `callq runtime.makeslice` (add form,
`Deposit_Data.WithdrawalCredentials`, n = 32). No `nop` before `callq runtime.memmove` and none in the
offset-0 form was observed, so only this position has a parameter.

* `bytesDecHeadPad n` = `bytesDecHead n` with one `nop` after directive 2 (10 directives);
  `bytesDecHeadP pad n` selects (`false` = `bytesDecHead n`).
* `bytesdec_seg_pad` — the statement of `bytesdec_seg` (`Codec/FixedBytesDecode.lean`) with the head `bytesDecHeadPad`,
  n = 32, 48, 96. Proof text = the `Codec/FixedBytesDecode.lean` text with the head indices ≥ 3 shifted by one and one more
  step (produced from `Codec/FixedBytesDecode.lean` by a script, as `Prysm/Deposit_Data/DecodeFieldSegmentPadding.lean` was by hand).
* `bytesdec_seg_p pad` — one lemma for both heads. Its statement does not depend on `pad` except in the code
  hypothesis `hA`, so the statement kind is the existing `bytesDecSegKind` (`Codec/Kind/FixedBytesDecode.lean`):
  `bytesDecSegKind_of_p`.
* Relations (`rfl`): `bytesDecHeadP false = bytesDecHead`, `bytesDecHeadPad 32 = Prysm.Deposit_Data.bytesDecHeadNop`, the
  declared type of `bytesdec_seg_p false` is that of `bytesdec_seg`, the declared type of
  `Prysm.Deposit_Data.bytes32dec_seg_nop` is that of `bytesdec_seg_pad 32 _`.
Contracts: `MakesliceC`, `MemmoveC` as in `bytesdec_seg`. Not done: offset-0 form with a pad (no site).
-/

open Machine Runtime

open Codec
namespace Codec

/-- `bytesDecHead n` with a `nop` after `mov $n,%ecx` (10 directives). -/
def bytesDecHeadPad (n : Int64) (lff : String) (dR fL fC : Int64) : Program :=
  [Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.lea (Reg.low Reg64.rax Width.W64)
       (AddrExpr.mk (some RegOrRip.rip) none (((ConstExpr.label "type__").add (ConstExpr.int64 387072)).sub ConstExpr.after_current_instruction)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W32
     (Operation.xor (RegOrMem.reg (Reg.low Reg64.rbx Width.W32))
       (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rbx Width.W32))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W32
     (Operation.mov (RegOrMem.reg (Reg.low Reg64.rcx Width.W32)) (Operand.imm (ConstExpr.int64 n)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64 (Operation.nop 1)),
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
       (Operand.imm (ConstExpr.int64 n)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W32
     (Operation.cmp (RegOrMem.mem (AddrExpr.mk (some RegOrRip.rip) none ((ConstExpr.label "runtime.writeBarrier").sub ConstExpr.after_current_instruction)))
       (Operand.imm (ConstExpr.int64 0)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64 (Operation.jcc CondCode.z lff))]

/-- Head block with or without the padding `nop`. -/
def bytesDecHeadP : Bool → Int64 → String → Int64 → Int64 → Int64 → Program
  | false, n, lff, dR, fL, fC => bytesDecHead n lff dR fL fC
  | true, n, lff, dR, fL, fC => bytesDecHeadPad n lff dR fL fC

variable [Host]

set_option hygiene false in
/-- Proof text for the literal size `n`, head with the `nop` (binders of the lemma below). Local to this file. -/
local macro "bytesdec_add_pad " n:num : tactic => `(tactic| (
    replace hA : (bytesDecHeadPad ($n : Int64) lff dR fL fC).IsInfixAt Host.prog j1 := hA
    replace hB : (bytesDecMid ($n : Int64) lff lwb dR dB dS fP fL fC src).IsInfixAt Host.prog j2 := hB
    rw [show (OfNat.ofNat ($n : Nat) : Int) = ($n : Int) from rfl]
    obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
    simp only at hrsp hrbp hr14 h_mem ⊢
    subst rsp rbp r14 hRet hLo
    kat hA bytesDecHeadPad 0
    kat hA bytesDecHeadPad 1
    intro _
    kat hA bytesDecHeadPad 2
    kat hA bytesDecHeadPad 3
    kat hA bytesDecHeadPad 4
    apply store_step_at _ _ (sp - 8) _ _ _ rslot _ _ (by segment_addr) (by ecancel) (by exact hrs)
    intro m1' H1
    simp only [Width.bytes, Width.bits] at H1
    kunfold
    try rw [show sp - 8#64 = sp - 8 from rfl] at *
    refine eventually_trans _ _ _ _ (hms _ (Host.addrOf (j1 + 4 + 1)) $n avail lo spl _
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
    kat hA bytesDecHeadPad 5
    apply load_step_at _ _ aR _ _ (Int.toBytes 8 rcv.toInt) _ _ (by rw [← hR]) (by ecancel)
      (by exact Int.toBytes_length 8 _)
    kunfold
    kat hA bytesDecHeadPad 6
    apply store_step_at _ _ aL _ _ _ vL _ _ (by rw [← hL]) (by ecancel) (by exact hvL)
    intro m2' H2
    simp only [Width.bytes, Width.bits] at H2
    kunfold
    kat hA bytesDecHeadPad 7
    apply store_step_at _ _ aC _ _ _ vC _ _ (by rw [← hC]) (by ecancel) (by exact hvC)
    intro m3' H3
    simp only [Width.bytes, Width.bits] at H3
    kunfold
    kat hA bytesDecHeadPad 8
    apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
    simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
    kunfold
    kat hA bytesDecHeadPad 9
    split
    case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    simp only [Effects.All]
    rw [hl]
    kat hB bytesDecMid 0
    kat hB bytesDecMid 1
    apply store_step_at _ _ aS _ _ _ lS _ _ (by rw [← hS]) (by ecancel) (by exact hlS)
    intro m4' H4
    simp only [Width.bytes, Width.bits] at H4
    kunfold
    kat hB bytesDecMid 2
    apply store_step_at _ _ aP _ _ _ vP _ _ (by rw [← hP]) (by ecancel) (by exact hvP)
    intro m5' H5
    simp only [Width.bytes, Width.bits] at H5
    kunfold
    kat hB bytesDecMid 3
    apply load_step_at _ _ aB _ _ (Int.toBytes 8 bf.toInt) _ _ (by rw [← hB']) (by ecancel)
      (by exact Int.toBytes_length 8 _)
    kunfold
    kat hB bytesDecMid 4
    kat hB bytesDecMid 5
    kat hB bytesDecMid 6
    apply store_step_at _ _ (sp - 8) _ _ _ (Int.toBytes 8 (Host.addrOf (j1 + 4 + 1)).toBitVec.toInt) _ _
      (by segment_addr) (by ecancel) (by exact Int.toBytes_length 8 _)
    intro m6' H6
    simp only [Width.bytes, Width.bits] at H6
    kunfold
    try rw [show sp - 8#64 = sp - 8 from rfl] at *
    refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (j2 + 6 + 1)) root (List.replicate $n 0) stk3 _
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
    kat hB bytesDecMid 7
    apply load_step_at _ _ aR _ _ (Int.toBytes 8 rcv.toInt) _ _ (by rw [← hR]) (by ecancel)
      (by exact Int.toBytes_length 8 _)
    kunfold
    kat hB bytesDecMid 8
    apply store_step_at _ _ aL _ _ _ (Int.toBytes 8 (BitVec.toInt (0 : BitVec 64))) _ _ (by rw [← hL])
      (by ecancel) (by exact Int.toBytes_length 8 _)
    intro m7' H7
    simp only [Width.bytes, Width.bits] at H7
    kunfold
    kat hB bytesDecMid 9
    apply store_step_at _ _ aC _ _ _ (Int.toBytes 8 (BitVec.toInt ($n : BitVec 64))) _ _ (by rw [← hC])
      (by ecancel) (by exact Int.toBytes_length 8 _)
    intro m8' H8
    simp only [Width.bytes, Width.bits] at H8
    kunfold
    kat hB bytesDecMid 10
    apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
    simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
    kunfold
    kat hB bytesDecMid 11
    split
    case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    simp only [Effects.All]
    apply Eventually.done
    simp only [show Int.toBytes 8 (BitVec.toInt ($n : BitVec 64)) = Int.toBytes 8 $n by decide] at H8
    exact ⟨rfl, rfl, rfl, rfl, rax3.toBitVec, spm3, stk4, hspm3, hstk4, rfl, by ecancel⟩))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- **Fixed-bytes decode segment, add form, head with a padding `nop`** (`n` = 32, 48 or 96): the statement
of `bytesdec_seg` with the head `bytesDecHeadPad`. -/
theorem bytesdec_seg_pad (n : Nat) (hn : n = 32 ∨ n = 48 ∨ n = 96) (lff lwb : String) (dR dB dS fP fL fC src : Int64) (j1 j2 : Nat)
    (hA : (bytesDecHeadPad (OfNat.ofNat n) lff dR fL fC).IsInfixAt Host.prog j1)
    (hB : (bytesDecMid (OfNat.ofNat n) lff lwb dR dB dS fP fL fC src).IsInfixAt Host.prog j2)
    (hl : label lff = Host.addrOf j2)
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
    (hms : MakesliceC Heap ElfData.PrysmTarget.e2eU8Type_addr 1 St) (hmm : MemmoveC St) :
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
          ⋆ Heap (avail - n)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aP) ⋆ Eq ((Int.toBytes 8 (OfNat.ofNat n)).At aL)
          ⋆ Eq ((Int.toBytes 8 (OfNat.ofNat n)).At aC) ⋆ Eq (root.At p)
          ⋆ Eq (root.At aSrc)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf j1⟩ := by
  rcases hn with rfl | rfl | rfl
  · bytesdec_add_pad 32
  · bytesdec_add_pad 48
  · bytesdec_add_pad 96

/-- **Fixed-bytes decode segment, add form, with or without the padding `nop`**: `pad = false` is
`bytesdec_seg`, `pad = true` is `bytesdec_seg_pad`. -/
theorem bytesdec_seg_p (pad : Bool) (n : Nat) (hn : n = 32 ∨ n = 48 ∨ n = 96) (lff lwb : String) (dR dB dS fP fL fC src : Int64) (j1 j2 : Nat)
    (hA : (bytesDecHeadP pad (OfNat.ofNat n) lff dR fL fC).IsInfixAt Host.prog j1)
    (hB : (bytesDecMid (OfNat.ofNat n) lff lwb dR dB dS fP fL fC src).IsInfixAt Host.prog j2)
    (hl : label lff = Host.addrOf j2)
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
    (hms : MakesliceC Heap ElfData.PrysmTarget.e2eU8Type_addr 1 St) (hmm : MemmoveC St) :
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
          ⋆ Heap (avail - n)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aP) ⋆ Eq ((Int.toBytes 8 (OfNat.ofNat n)).At aL)
          ⋆ Eq ((Int.toBytes 8 (OfNat.ofNat n)).At aC) ⋆ Eq (root.At p)
          ⋆ Eq (root.At aSrc)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf j1⟩ := by
  cases pad
  · exact bytesdec_seg n hn lff lwb dR dB dS fP fL fC src j1 j2 hA hB hl sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St
      hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC
      R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  · exact bytesdec_seg_pad n hn lff lwb dR dB dS fP fL fC src j1 j2 hA hB hl sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St
      hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC
      R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm

/-- The existing kind `bytesDecSegKind` follows from `bytesdec_seg_p` and the code facts of an instance. -/
theorem bytesDecSegKind_of_p (pad : Bool) (n : Nat) (hn : n = 32 ∨ n = 48 ∨ n = 96) (C : Program) (lff lwb : String)
    (dR dB dS fP fL fC src : Int64) (j1 j2 : Nat)
    (hA : ∀ k, C.IsInfixAt Host.prog k → (bytesDecHeadP pad (OfNat.ofNat n) lff dR fL fC).IsInfixAt Host.prog (k + j1))
    (hB : ∀ k, C.IsInfixAt Host.prog k →
      (bytesDecMid (OfNat.ofNat n) lff lwb dR dB dS fP fL fC src).IsInfixAt Host.prog (k + j2))
    (hl : ∀ k, C.IsInfixAt Host.prog k → LabelsFresh C k → label lff = Host.addrOf (k + j2)) :
    bytesDecSegKind n C j1 j2 dR dB dS fP fL fC src :=
  fun k hk hf => bytesdec_seg_p pad n hn lff lwb dR dB dS fP fL fC src (k + j1) (k + j2) (hA k hk) (hB k hk) (hl k hk hf)

theorem bytesDecHeadP_false : bytesDecHeadP false = bytesDecHead := rfl
theorem bytesDecHeadP_true : bytesDecHeadP true = bytesDecHeadPad := rfl
theorem bytesDecHeadPad32_eq_nop : bytesDecHeadPad 32 = Prysm.Deposit_Data.bytesDecHeadNop := rfl

theorem bytesdec_seg_p_false_is_bytesdec_seg : ∀ (h : Host),
    type_of% (@bytesdec_seg_p h false) = type_of% (@bytesdec_seg h) := by
  intro h; rfl

theorem bytes32dec_seg_nop_is_pad32 : ∀ (h : Host),
    type_of% (@Prysm.Deposit_Data.bytes32dec_seg_nop h) = type_of% (@bytesdec_seg_pad h 32 (Or.inl rfl)) := by
  intro h; rfl

theorem bytes32dec_seg_nop_is_p32 : ∀ (h : Host),
    type_of% (@Prysm.Deposit_Data.bytes32dec_seg_nop h) = type_of% (@bytesdec_seg_p h true 32 (Or.inl rfl)) := by
  intro h; rfl

end Codec
