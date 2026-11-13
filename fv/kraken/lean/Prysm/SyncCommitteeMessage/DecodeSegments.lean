import Prysm.BeaconBlockHeader.DecodeHeadFromCallSegments
import Codec.FixedBytesDecode
import Prysm.SyncCommitteeMessage.Code

/-!
# SyncCommitteeMessage hand lemmas (hold-out, class C; hand work after the raw generator output)

Hand-written for the directives of `(*v1alpha1.SyncCommitteeMessage).UnmarshalSSZ`
that the generator did not cover (`Prysm/SyncCommitteeMessage/GeneratedDecodeCallSegmentsPartial.lean`: Slot and Signature covered; BlockRoot and
ValidatorIndex not). No contract, no new hypothesis form; the runtime callees use `MakesliceContract` / `MemmoveContract` as
in `Codec/FixedBytesDecode.lean`.

* `Decode.head0`: directives 0–14 (the text of `Prysm.BeaconBlockHeader.Decode.head0`; the frame `sub $0x60` and the spill order are the same,
  the length immediate is `0x90`).
* `bytesDecMidRax` / `bytes32dec_seg_rax`: BlockRoot (47–71). The second block reloads the receiver into rax, not
  rdx (the generator's reason for BlockRoot); otherwise `bytesdec_seg` with `n = 32`.
* `Decode.validator_index_arg`: ValidatorIndex argument set-up 82–87 (the receiver stays in rax; the generator read it as the
  first-field form).
* `Decode.spill2`: the two nil-error spills 118–119 (the text of `Prysm.BeaconBlockHeader.Decode.spill2`).
-/

open Machine Runtime Prysm.SyncCommitteeMessage.Code Codec

namespace Prysm.SyncCommitteeMessage

/-- `bytesDecMid` with the receiver reloaded into rax (directives 7–9: `mov dR(%rsp),%rax; movq $n,fL(%rax);
movq $n,fC(%rax)`), as SyncCommitteeMessage.BlockRoot is compiled. -/
def bytesDecMidRax (n : Int64) (lff lwb : String) (dR dB dS fP fL fC src : Int64) : Program :=
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
     (Operation.mov (RegOrMem.reg (Reg.low Reg64.rcx Width.W32)) (Operand.imm (ConstExpr.int64 n)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.call (RelRegOrMem.rel ((ConstExpr.label "runtime.memmove").sub ConstExpr.after_current_instruction)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.reg (Reg.low Reg64.rax Width.W64))
       (Operand.regOrMem (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rsp)) none (ConstExpr.int64 dR)))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rax)) none (ConstExpr.int64 fL)))
       (Operand.imm (ConstExpr.int64 n)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rax)) none (ConstExpr.int64 fC)))
       (Operand.imm (ConstExpr.int64 n)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W32
     (Operation.cmp (RegOrMem.mem (AddrExpr.mk (some RegOrRip.rip) none ((ConstExpr.label "runtime.writeBarrier").sub ConstExpr.after_current_instruction)))
       (Operand.imm (ConstExpr.int64 0)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64 (Operation.jcc CondCode.nz lwb))]

variable [Host]

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- Head, directives 0–14: entry to the first argument set-up. -/
theorem Decode.head0 (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k)
    (s : MachineData) (ra guard : UInt64) (fp s1 s2 s4 ast : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h4 : s4.length = 8) (hast : ast.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx = 144) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 15) ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 104 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 } ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.rax = s.regs.rax ∧ st.data.regs.rbx = s.regs.rbx ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  subst hlen
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; simp only [UInt64.size] at *
  have hcs : Eq (ast.At rax.toBitVec) = Eq ((ast.take 1).At rax.toBitVec) ⋆ Eq ((ast.drop 1).At (rax.toBitVec + 1)) := by
    conv => lhs; rw [← List.take_append_drop 1 ast]
    exact at_app _ _ (by rw [List.length_take, hast]; rfl) (by simp [hast])
  rw [hcs] at h_mem
  step_directive hk unmarshalSSZ 0
  step_directive hk unmarshalSSZ 1
  step_directive hk unmarshalSSZ 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk unmarshalSSZ 3
  split
  · rename_i h; exfalso
    simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  step_directive hk unmarshalSSZ 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1' H1
  simp only [Width.bytes, Width.bits] at H1
  unfold_step
  step_directive hk unmarshalSSZ 5
  step_directive hk unmarshalSSZ 6
  step_directive hk unmarshalSSZ 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by bv_omega) (by ecancel) (by exact h2)
  intro m2' H2
  simp only [Width.bytes, Width.bits] at H2
  unfold_step
  step_directive hk unmarshalSSZ 8
  step_directive hk unmarshalSSZ 9
  step_directive hk unmarshalSSZ 10
  split
  case isTrue h => exact absurd h (by decide)
  simp only [Effects.All]
  step_directive hk unmarshalSSZ 11
  apply store_step_at _ _ (rsp.toBitVec + 8) _ _ _ s1 _ _ (by bv_omega) (by ecancel) (by exact h1)
  intro m3' H3
  simp only [Width.bytes, Width.bits] at H3
  unfold_step
  step_directive hk unmarshalSSZ 12
  apply store_step_at _ _ (rsp.toBitVec + 32) _ _ _ s4 _ _ (by bv_omega) (by ecancel) (by exact h4)
  intro m4' H4
  simp only [Width.bytes, Width.bits] at H4
  unfold_step
  step_directive hk unmarshalSSZ 13
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by bv_omega) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m5' H5
  simp only [Width.bytes, Width.bits] at H5
  unfold_step
  step_directive hk unmarshalSSZ 14
  apply load_step _ _ _ _ (ast.take 1) _ _ (by ecancel) (by simp [hast])
  unfold_step
  intro _
  apply Eventually.done
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_right
  · rw [hcs]; simp only [Std.ExtHashMap.sep_assoc]; ecancel
  all_goals first
    | rfl
    | exact congrArg UInt64.ofBitVec (Prysm.BeaconBlockHeader.Decode.head_stack_pointer _)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directives 118–119: `mov %rbx,0x30(%rsp); mov %rax,0x28(%rsp)`. -/
theorem Decode.spill2 (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k)
    (sp a28 a30 : BitVec 64) (h28 : sp + 40 = a28) (h30 : sp + 48 = a30)
    (s28 s30 : List UInt8) (hs28 : s28.length = 8) (hs30 : s30.length = 8) (R : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp })
    (h_mem : s.dmem =⋆ Eq (s28.At a28) ⋆ Eq (s30.At a30) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 120) ∧ st.data.regs.rsp = s.regs.rsp
        ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        (Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At a28)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At a30) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 118)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp h_mem ⊢
  subst rsp h28 h30
  step_directive hk unmarshalSSZ 118
  apply store_step_at _ _ (sp + 48) _ _ _ s30 _ _ (by segment_addr) (by ecancel) (by exact hs30)
  intro m1' H1
  simp only [Width.bytes, Width.bits] at H1
  unfold_step
  step_directive hk unmarshalSSZ 119
  apply store_step_at _ _ (sp + 40) _ _ _ s28 _ _ (by segment_addr) (by ecancel) (by exact hs28)
  intro m2' H2
  simp only [Width.bytes, Width.bits] at H2
  unfold_step
  apply Eventually.done
  exact ⟨rfl, rfl, rfl, rfl, by ecancel⟩

/-- Closing step of the set-up lemma: register equations (the text of `call_argument_close`, `Codec/CalleeDecode.lean`). -/
local macro "setup_argument_close" : tactic => `(tactic| (
  all_goals first
    | rfl
    | exact BitVec.add_comm _ _
    | (apply BitVec.eq_of_toNat_eq
       simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, UInt64.toNat_toBitVec,
         UInt64.toBitVec_add, UInt64.toBitVec_ofNat, Width.bits, Nat.reducePow, Nat.add_comm]
       done)))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- ValidatorIndex argument set-up, directives 82–87: `mov 0x78(%rsp),%rbx; add $0x28,%rbx; mov 0x88(%rsp),%rdi;
add $-0x28,%rdi; add $0x28,%rax; mov $0x8,%ecx` (the receiver is already in rax). The text of
`callarg_reload_seg` without the receiver reload. -/
theorem Decode.validator_index_arg (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k)
    (sp rcv bf aB aD aSrc aF : BitVec 64)
    (hB' : sp + (120 : Int64).toBitVec = aB) (hD : sp + (136 : Int64).toBitVec = aD)
    (hSrc : bf + (40 : Int64).toBitVec = aSrc) (hF : rcv + (40 : Int64).toBitVec = aF)
    (vD : List UInt8) (hvD : vD.length = 8) (R : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrax : s.regs.rax.toBitVec = rcv)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 bf.toInt).At aB) ⋆ Eq (vD.At aD) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 88) ∧ st.data.regs.rsp = s.regs.rsp
        ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.rbx.toBitVec = aSrc ∧ st.data.regs.rax.toBitVec = aF ∧ st.data.regs.rcx = 8
        ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf (k + 82)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp hrax h_mem ⊢
  subst rsp hSrc hF hrax
  step_directive hk unmarshalSSZ 82
  apply load_step_at _ _ aB _ _ (Int.toBytes 8 bf.toInt) _ _ (by rw [← hB']; rfl) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk unmarshalSSZ 83
  step_directive hk unmarshalSSZ 84
  apply load_step_at _ _ aD _ _ vD _ _ (by rw [← hD]; rfl) (by ecancel) (by exact hvD)
  unfold_step
  step_directive hk unmarshalSSZ 85
  step_directive hk unmarshalSSZ 86
  step_directive hk unmarshalSSZ 87
  apply Eventually.done
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  setup_argument_close

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `bytesdec_seg` (`Codec/FixedBytesDecode.lean`) for `n = 32` with the second block `bytesDecMidRax`: the same pre / post except
that rax (not rdx) holds the receiver at the end. Proof: the text of `bytes_decode_add_case 32` with the three changed
directives. -/
theorem bytes32dec_seg_rax (lff lwb : String) (dR dB dS fP fL fC src : Int64) (j1 j2 : Nat)
    (hA : (bytesDecHead 32 lff dR fL fC).IsInfixAt Host.prog j1)
    (hB : (bytesDecMidRax 32 lff lwb dR dB dS fP fL fC src).IsInfixAt Host.prog j2)
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
          ∧ st.data.regs.rax.toBitVec = rcv ∧
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
  step_directive hA bytesDecHead 0
  step_directive hA bytesDecHead 1
  intro _
  step_directive hA bytesDecHead 2
  step_directive hA bytesDecHead 3
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
  step_directive hA bytesDecHead 4
  apply load_step_at _ _ aR _ _ (Int.toBytes 8 rcv.toInt) _ _ (by rw [← hR]) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hA bytesDecHead 5
  apply store_step_at _ _ aL _ _ _ vL _ _ (by rw [← hL]) (by ecancel) (by exact hvL)
  intro m2' H2
  simp only [Width.bytes, Width.bits] at H2
  unfold_step
  step_directive hA bytesDecHead 6
  apply store_step_at _ _ aC _ _ _ vC _ _ (by rw [← hC]) (by ecancel) (by exact hvC)
  intro m3' H3
  simp only [Width.bytes, Width.bits] at H3
  unfold_step
  step_directive hA bytesDecHead 7
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  unfold_step
  step_directive hA bytesDecHead 8
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  rw [hl]
  step_directive hB bytesDecMidRax 0
  step_directive hB bytesDecMidRax 1
  apply store_step_at _ _ aS _ _ _ lS _ _ (by rw [← hS]) (by ecancel) (by exact hlS)
  intro m4' H4
  simp only [Width.bytes, Width.bits] at H4
  unfold_step
  step_directive hB bytesDecMidRax 2
  apply store_step_at _ _ aP _ _ _ vP _ _ (by rw [← hP]) (by ecancel) (by exact hvP)
  intro m5' H5
  simp only [Width.bytes, Width.bits] at H5
  unfold_step
  step_directive hB bytesDecMidRax 3
  apply load_step_at _ _ aB _ _ (Int.toBytes 8 bf.toInt) _ _ (by rw [← hB']) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hB bytesDecMidRax 4
  step_directive hB bytesDecMidRax 5
  step_directive hB bytesDecMidRax 6
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
  step_directive hB bytesDecMidRax 7
  apply load_step_at _ _ aR _ _ (Int.toBytes 8 rcv.toInt) _ _ (by rw [← hR]) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hB bytesDecMidRax 8
  apply store_step_at _ _ aL _ _ _ (Int.toBytes 8 (BitVec.toInt (0 : BitVec 64))) _ _ (by rw [← hL])
    (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m7' H7
  simp only [Width.bytes, Width.bits] at H7
  unfold_step
  step_directive hB bytesDecMidRax 9
  apply store_step_at _ _ aC _ _ _ (Int.toBytes 8 (BitVec.toInt (32 : BitVec 64))) _ _ (by rw [← hC])
    (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m8' H8
  simp only [Width.bytes, Width.bits] at H8
  unfold_step
  step_directive hB bytesDecMidRax 10
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  unfold_step
  step_directive hB bytesDecMidRax 11
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  apply Eventually.done
  simp only [show Int.toBytes 8 (BitVec.toInt (32 : BitVec 64)) = Int.toBytes 8 32 by decide] at H8
  exact ⟨rfl, rfl, rfl, rfl, rax3.toBitVec, spm3, stk4, hspm3, hstk4, rfl, by ecancel⟩

end Prysm.SyncCommitteeMessage
