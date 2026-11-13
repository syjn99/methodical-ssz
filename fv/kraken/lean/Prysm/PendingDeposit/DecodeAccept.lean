import Codec.DecoderPrologue
import Prysm.PendingDeposit.GeneratedDecodeSteps
import Prysm.BeaconBlockHeader.DecodeAcceptFromGeneratedCallSegments
import Prysm.PendingDeposit.Statements

/-!
# `(*v1alpha1.PendingDeposit).UnmarshalSSZ`, accept path from the GENERATED `p2dec --gen4` chains (hold-out, full-proof type)

Hand-written AFTER the raw generator output (`Prysm/PendingDeposit/GeneratedDecodeSteps.lean`, `p2dec --gen4`, exit 0,
5/5 walker-covered) was committed. Statement = the pre-committed hand statement `Prysm.PendingDeposit.Decode.accept_statement`
(`Prysm/PendingDeposit/Statements.lean`, unchanged). `--gen4 --compose` refuses by design, so every field composition is HAND text
(`pd_gg_*_field`) over the GENERATED theorems, used as emitted:
* head 0–13: `Decode.head` (hand; `decpro_seg` with F = 64, dB = 88, size 192, then the spills 11–13 as `kstep_st`);
* PublicKey 14–48: generated segment (offset-0 form) + generated tail steps 38, 39, 47, 48;
* WithdrawalCredentials 49–84: generated segment + generated tail steps 74, 75, 83, 84;
* Amount 85–87: generated steps 85, 86, 87;
* Signature 88–122: generated segment + generated tail steps 113, 114, 121, 122;
* Slot 123–160: generated steps 123–128 + generated call block (`hC` discharged by the proved `Prysm.Slot.Decode.accept_function_spec_holds`);
* epilogue 161–163: `Decode.epi` (hand; `kstep_add` and `decret_seg`).
-/

open Machine Runtime Prysm.AttestationData.Code Prysm.PendingDeposit.Code Codec
variable [Host]

namespace Prysm.PendingDeposit

theorem Decode.stack_low_eq (x : BitVec 64) (S : Nat) : x - 72 - 8 - BitVec.ofNat 64 (S + 8) = x - 88 - BitVec.ofNat 64 S := by
  have : BitVec.ofNat 64 (S + 8) = BitVec.ofNat 64 S + 8 := by
    apply BitVec.eq_of_toNat_eq; simp
  rw [this]; bv_omega

theorem Decode.lo8 (x : BitVec 64) (S : Nat) (hS : S < 2 ^ 60) (a f : List UInt8) (ha : a.length = S) (hf : f.length = 8) :
    Eq ((a ++ f).At (x - 88 - BitVec.ofNat 64 S)) = Eq (a.At (x - 88 - BitVec.ofNat 64 S)) ⋆ Eq (f.At (x - 88)) := by
  refine at_app _ _ ?_ (by simp only [ha, hf]; omega)
  rw [ha]; bv_omega

theorem Decode.j3 (x : BitVec 64) (a b c : List UInt8) (ha : a.length = 8) (hb : b.length = 8) (hc : c.length = 8) :
    Eq ((a ++ (b ++ c)).At (x - 72)) = Eq (a.At (x - 72)) ⋆ Eq (b.At (x - 64)) ⋆ Eq (c.At (x - 56)) := by
  rw [at_app _ _ (b := x - 64) (by rw [ha]; bv_omega) (by simp [ha, hb, hc]),
    at_app _ _ (b := x - 56) (by rw [hb]; bv_omega) (by simp [hb, hc])]
  simp only [Std.ExtHashMap.sep_assoc]

theorem Decode.guard_lt (x : BitVec 64) (g : Nat) (h : g + 80 < x.toNat) : g < (x - 80).toNat := by bv_omega

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- PendingDeposit head 0–13 (frame `0x40`, size 192): `decpro_seg`, then the spills rax → `0x50(%rsp)`,
rdi → `0x68(%rsp)`, rbx → `0x58(%rsp)` as `kstep_st` steps (no nil check in this decoder). -/
theorem Decode.head (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k)
    (s : MachineData) (ra guard : UInt64) (fp s1 s2 s4 : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h4 : s4.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16)) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx = 192) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 14) ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 72 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 } ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.rax = s.regs.rax ∧ st.data.regs.rbx = s.regs.rbx ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  refine eventually_trans _ _ _ _ (decpro_seg _ _ _ _ 64 88 192 _ k (k + 11) (win hk 0 11) (by rfl) (by rfl)
    s ra guard (s.regs.rsp.toBitVec - 72) (s.regs.rsp.toBitVec + 16)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    fp s2 hfp h2 _ (by ecancel) hguard (by rw [hlen]; rfl)) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hreg1, Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hreg1 Hm1
  subst hpc1
  have hrax1 := UInt64.toBitVec_inj.mp (hreg1 Reg64.rax (by decide) (by decide))
  have hrbx1 := UInt64.toBitVec_inj.mp (hreg1 Reg64.rbx (by decide) (by decide))
  have hrdi1 := UInt64.toBitVec_inj.mp (hreg1 Reg64.rdi (by decide) (by decide))
  have hr141 := UInt64.toBitVec_inj.mp (hreg1 Reg64.r14 (by decide) (by decide))
  clear hreg1
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d1
  simp only at hrsp1 hrbp1 hrax1 hrbx1 hrdi1 hr141 Hm1
  subst hrsp1 hrbp1 hrax1 hrbx1 hrdi1 hr141
  apply kstep_st Reg64.rax Reg64.rsp 80 _ (k + 11) (k + 12) (win hk 11 1) (by rfl) (by rfl)
    (s.regs.rsp.toBitVec - 72) (s.regs.rsp.toBitVec + 8) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    s1 h1 _ _ _ (by rfl) (by ecancel)
  intro m1 H1; kn; simp only [Reg64s.get64] at H1
  apply kstep_st Reg64.rdi Reg64.rsp 104 _ (k + 12) (k + 13) (win hk 12 1) (by rfl) (by rfl)
    (s.regs.rsp.toBitVec - 72) (s.regs.rsp.toBitVec + 32) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    s4 h4 _ _ _ (by rfl) (by ecancel)
  intro m2 H2; kn; simp only [Reg64s.get64] at H2
  apply kstep_st Reg64.rbx Reg64.rsp 88 _ (k + 13) (k + 14) (win hk 13 1) (by rfl) (by rfl)
    (s.regs.rsp.toBitVec - 72) (s.regs.rsp.toBitVec + 16) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (Int.toBytes 8 s.regs.rbx.toBitVec.toInt) (Int.toBytes_length 8 _) _ _ _ (by rfl) (by ecancel)
  intro m3 H3; kn; simp only [Reg64s.get64] at H3
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  dsimp only
  ecancel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- PendingDeposit epilogue 161–163 (frame `0x40`): `add $0x40,%rsp` as `kstep_add`, then `decret_seg`. -/
theorem Decode.epi (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k)
    (sp aFp aRa : BitVec 64) (hFp : sp + 64 = aFp) (hRa : sp + 72 = aRa)
    (fp0 ra : UInt64) (R : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp })
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 fp0.toBitVec.toInt).At aFp)
      ⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At aRa) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rax
        ∧ st.data.regs.rbx = s.regs.rbx ∧ st.data.regs.rsp = { toBitVec := sp + 80 }
        ∧ st.data.regs.rbp = fp0 ∧ st.data.regs.r14 = s.regs.r14 ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf (k + 161)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp h_mem ⊢
  subst rsp hFp hRa
  apply kstep_add Reg64.rsp 64 _ (k + 161) (k + 162) (win hk 161 1) (by rfl) (by rfl)
  intro fl; kn
  refine eventually_trans _ _ _ _ (decret_seg _ (k + 162) (win hk 162 2) (by rfl) (sp + 64) (sp + 72) (by bv_omega)
    fp0 ra R _ (by rfl) (by ecancel)) ?_
  rintro ⟨d, pc⟩ ⟨hpc, hrsp', hrbp', hreg, hmem⟩
  dsimp only at hpc hrsp' hrbp' hreg hmem
  apply Eventually.done
  refine ⟨hpc, ?_, ?_, ?_, hrbp', ?_, hmem⟩
  · exact UInt64.toBitVec_inj.mp (hreg Reg64.rax (by decide) (by decide))
  · exact UInt64.toBitVec_inj.mp (hreg Reg64.rbx (by decide) (by decide))
  · rw [hrsp']; exact congrArg UInt64.ofBitVec (by bv_omega)
  · exact UInt64.toBitVec_inj.mp (hreg Reg64.r14 (by decide) (by decide))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `PublicKey`: the WHOLE byte field 14–48 (generated segment, then the generated tail steps 38, 39, 47, 48). -/
theorem Decode.from_generated_steps_PublicKey_field (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k) :
    ∀
    (sp rcv bf aR aB aS aRet aLo aP aL aC : BitVec 64) (St : Nat)
    (hR : sp + (80 : Int64).toBitVec = aR) (hB' : sp + (88 : Int64).toBitVec = aB) (hS : sp + (40 : Int64).toBitVec = aS)
    (hRet : sp - 8 = aRet) (hLo : sp - 8 - BitVec.ofNat 64 St = aLo)
    (hP : rcv + (8 : Int64).toBitVec = aP) (hL : rcv + (16 : Int64).toBitVec = aL) (hC : rcv + (24 : Int64).toBitVec = aC)
    (rbp0 r140 : UInt64) (root : List UInt8) (hroot : root.length = 48)
    (spl rslot lo lS vP vL vC : List UInt8)
    (hspl : spl.length = 24) (hrs : rslot.length = 8) (hlo : lo.length = St) (hlS : lS.length = 8)
    (hvP : vP.length = 8) (hvL : vL.length = 8) (hvC : vC.length = 8)
    (R : DataMem → Prop) (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 48 ≤ avail)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
      ⋆ Eq (spl.At sp) ⋆ Eq (rslot.At aRet) ⋆ Eq (lo.At aLo) ⋆ Eq (lS.At aS)
      ⋆ Heap avail
      ⋆ Eq (vP.At aP) ⋆ Eq (vL.At aL) ⋆ Eq (vC.At aC)
      ⋆ Eq (root.At bf)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hms : MakesliceC Heap ElfData.PrysmTarget.e2eU8Type_addr 1 St) (hmm : MemmoveC St),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 49) ∧ st.data.regs.rsp = { toBitVec := sp }
        ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        ∃ (p : BitVec 64) (spl' lo' : List UInt8), spl'.length = 24 ∧ lo'.length = St
          ∧ st.data.regs.get64 Reg64.rdx = rcv ∧
        (Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
          ⋆ Eq (spl'.At sp)
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 32 + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq (lo'.At aLo)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aS)
          ⋆ Heap (avail - 48)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aP) ⋆ Eq ((Int.toBytes 8 48).At aL)
          ⋆ Eq ((Int.toBytes 8 48).At aC) ⋆ Eq (root.At p)
          ⋆ Eq (root.At bf)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 14)⟩ := by
  intro sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  refine eventually_trans _ _ _ _ (Decode.generated_step_PublicKey_seg k hk hf sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm) ?_
  rintro ⟨d, pc⟩ ⟨hpc, hrsp', hrbp', hr14', p, spl', lo', hspl', hlo', hrY, Hm⟩
  dsimp only at hpc hrsp' hrbp' hr14' hrY Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only at hrsp' hrbp' hr14' hrY Hm
  subst hrsp' hrbp' hr14'
  apply Decode.generated_step_s38 k hk hf sp aS p hS _ _ _ (by rfl) (by ecancel)
  kn
  apply Decode.generated_step_s39 k hk hf
  apply Decode.generated_step_s47 k hk hf
  apply Decode.generated_step_s48 k hk hf rcv aP hP (Int.toBytes 8 p.toInt) (Int.toBytes_length 8 _) _ _ _ (by exact hrY) (by ecancel)
  intro m' H
  kn
  simp only [Reg64s.get64] at H
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, p, spl', lo', hspl', hlo', hrY, ?_⟩
  dsimp only
  ecancel

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `WithdrawalCredentials`: the WHOLE byte field 49–84 (generated segment, then the generated tail steps 74, 75, 83, 84). -/
theorem Decode.from_generated_steps_WithdrawalCredentials_field (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k) :
    ∀
    (sp rcv bf aR aB aS aRet aLo aP aL aC aSrc : BitVec 64) (St : Nat)
    (hR : sp + (80 : Int64).toBitVec = aR) (hB' : sp + (88 : Int64).toBitVec = aB) (hS : sp + (40 : Int64).toBitVec = aS)
    (hRet : sp - 8 = aRet) (hLo : sp - 8 - BitVec.ofNat 64 St = aLo)
    (hP : rcv + (32 : Int64).toBitVec = aP) (hL : rcv + (40 : Int64).toBitVec = aL) (hC : rcv + (48 : Int64).toBitVec = aC)
    (hSrc : bf + (48 : Int64).toBitVec = aSrc)
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
    (hms : MakesliceC Heap ElfData.PrysmTarget.e2eU8Type_addr 1 St) (hmm : MemmoveC St),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 85) ∧ st.data.regs.rsp = { toBitVec := sp }
        ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        ∃ (p : BitVec 64) (spl' lo' : List UInt8), spl'.length = 24 ∧ lo'.length = St
          ∧ st.data.regs.get64 Reg64.rdx = rcv ∧
        (Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
          ⋆ Eq (spl'.At sp)
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 68 + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq (lo'.At aLo)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aS)
          ⋆ Heap (avail - 32)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aP) ⋆ Eq ((Int.toBytes 8 32).At aL)
          ⋆ Eq ((Int.toBytes 8 32).At aC) ⋆ Eq (root.At p)
          ⋆ Eq (root.At aSrc)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 49)⟩ := by
  intro sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  refine eventually_trans _ _ _ _ (Decode.generated_step_WithdrawalCredentials_seg k hk hf sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm) ?_
  rintro ⟨d, pc⟩ ⟨hpc, hrsp', hrbp', hr14', p, spl', lo', hspl', hlo', hrY, Hm⟩
  dsimp only at hpc hrsp' hrbp' hr14' hrY Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only at hrsp' hrbp' hr14' hrY Hm
  subst hrsp' hrbp' hr14'
  apply Decode.generated_step_s74 k hk hf sp aS p hS _ _ _ (by rfl) (by ecancel)
  kn
  apply Decode.generated_step_s75 k hk hf
  apply Decode.generated_step_s83 k hk hf
  apply Decode.generated_step_s84 k hk hf rcv aP hP (Int.toBytes 8 p.toInt) (Int.toBytes_length 8 _) _ _ _ (by exact hrY) (by ecancel)
  intro m' H
  kn
  simp only [Reg64s.get64] at H
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, p, spl', lo', hspl', hlo', hrY, ?_⟩
  dsimp only
  ecancel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `Amount`: the WHOLE uint64 field 85–87 (generated steps 85, 86, 87: buffer pointer reload, 8-byte load, store). -/
theorem Decode.from_generated_steps_Amount_field (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k) :
    ∀ (sp rcv bf aB : BitVec 64) (hB : sp + (88 : Int64).toBitVec = aB)
    (rbp0 r140 : UInt64) (v vF : List UInt8) (hv : v.length = 8) (hvF : vF.length = 8)
    (F : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140) (hrdx : s.regs.get64 Reg64.rdx = rcv)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 bf.toInt).At aB) ⋆ Eq (v.At (bf + 80)) ⋆ Eq (vF.At (rcv + 56)) ⋆ F),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 88) ∧ st.data.regs.rsp = { toBitVec := sp }
        ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        (Eq ((Int.toBytes 8 bf.toInt).At aB) ⋆ Eq (v.At (bf + 80)) ⋆ Eq (v.At (rcv + 56)) ⋆ F) st.data.dmem)
      ⟨s, Host.addrOf (k + 85)⟩ := by
  intro sp rcv bf aB hB rbp0 r140 v vF hv hvF F s hrsp hrbp hr14 hrdx h_mem
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only [Reg64s.get64] at hrsp hrbp hr14 hrdx h_mem ⊢
  subst rsp rbp r14 hrdx
  apply Decode.generated_step_s85 k hk hf sp aB bf hB _ _ _ (by rfl) (by ecancel)
  kn
  apply Decode.generated_step_s86 k hk hf bf (bf + 80) (by simp only [Int64.toBitVec_ofNat]) v hv _ _ _ (by rfl) (by ecancel)
  kn
  apply Decode.generated_step_s87 k hk hf rdx.toBitVec (rdx.toBitVec + 56) (by simp only [Int64.toBitVec_ofNat]) vF hvF _ _ _
    (by rfl) (by ecancel)
  intro m' H
  kn
  simp only [Reg64s.get64, toBytes_ofInt_ofBytes 64 8 rfl v hv] at H
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  dsimp only
  ecancel

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `Signature`: the WHOLE byte field 88–122 (generated segment, then the generated tail steps 113, 114, 121, 122). -/
theorem Decode.from_generated_steps_Signature_field (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k) :
    ∀
    (sp rcv bf aR aB aS aRet aLo aP aL aC aSrc : BitVec 64) (St : Nat)
    (hR : sp + (80 : Int64).toBitVec = aR) (hB' : sp + (88 : Int64).toBitVec = aB) (hS : sp + (40 : Int64).toBitVec = aS)
    (hRet : sp - 8 = aRet) (hLo : sp - 8 - BitVec.ofNat 64 St = aLo)
    (hP : rcv + (64 : Int64).toBitVec = aP) (hL : rcv + (72 : Int64).toBitVec = aL) (hC : rcv + (80 : Int64).toBitVec = aC)
    (hSrc : bf + (88 : Int64).toBitVec = aSrc)
    (rbp0 r140 : UInt64) (root : List UInt8) (hroot : root.length = 96)
    (spl rslot lo lS vP vL vC : List UInt8)
    (hspl : spl.length = 24) (hrs : rslot.length = 8) (hlo : lo.length = St) (hlS : lS.length = 8)
    (hvP : vP.length = 8) (hvL : vL.length = 8) (hvC : vC.length = 8)
    (R : DataMem → Prop) (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 96 ≤ avail)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
      ⋆ Eq (spl.At sp) ⋆ Eq (rslot.At aRet) ⋆ Eq (lo.At aLo) ⋆ Eq (lS.At aS)
      ⋆ Heap avail
      ⋆ Eq (vP.At aP) ⋆ Eq (vL.At aL) ⋆ Eq (vC.At aC)
      ⋆ Eq (root.At aSrc)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hms : MakesliceC Heap ElfData.PrysmTarget.e2eU8Type_addr 1 St) (hmm : MemmoveC St),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 123) ∧ st.data.regs.rsp = { toBitVec := sp }
        ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        ∃ (p : BitVec 64) (spl' lo' : List UInt8), spl'.length = 24 ∧ lo'.length = St
          ∧ st.data.regs.get64 Reg64.rax = rcv ∧
        (Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
          ⋆ Eq (spl'.At sp)
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 107 + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq (lo'.At aLo)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aS)
          ⋆ Heap (avail - 96)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aP) ⋆ Eq ((Int.toBytes 8 96).At aL)
          ⋆ Eq ((Int.toBytes 8 96).At aC) ⋆ Eq (root.At p)
          ⋆ Eq (root.At aSrc)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 88)⟩ := by
  intro sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  refine eventually_trans _ _ _ _ (Decode.generated_step_Signature_seg k hk hf sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm) ?_
  rintro ⟨d, pc⟩ ⟨hpc, hrsp', hrbp', hr14', p, spl', lo', hspl', hlo', hrY, Hm⟩
  dsimp only at hpc hrsp' hrbp' hr14' hrY Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only at hrsp' hrbp' hr14' hrY Hm
  subst hrsp' hrbp' hr14'
  apply Decode.generated_step_s113 k hk hf sp aS p hS _ _ _ (by rfl) (by ecancel)
  kn
  apply Decode.generated_step_s114 k hk hf
  apply Decode.generated_step_s121 k hk hf
  apply Decode.generated_step_s122 k hk hf rcv aP hP (Int.toBytes 8 p.toInt) (Int.toBytes_length 8 _) _ _ _ (by exact hrY) (by ecancel)
  intro m' H
  kn
  simp only [Reg64s.get64] at H
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, p, spl', lo', hspl', hlo', hrY, ?_⟩
  dsimp only
  ecancel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `Slot` (callee decoder field, Go offset 88, SSZ offset 184): the WHOLE call field 123–160 (generated steps
123–128 and the generated call block 129–132, continuation label 160). -/
theorem Decode.from_generated_steps_Slot_field (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Code.unmarshalSSZ k) :
    ∀ (hC : U64CalleeAcc "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ")
    (sp rcv bf aRet aFp aS2 aB aD : BitVec 64)
    (hRet : sp - 8 = aRet) (hFp : sp - 16 = aFp) (hS2 : sp + 8 = aS2)
    (hB : sp + (88 : Int64).toBitVec = aB) (hD : sp + (104 : Int64).toBitVec = aD)
    (rbp0 r140 guard : UInt64) (e8 rslot fp s2 c0 vD : List UInt8)
    (he8 : e8.length = 8) (hrs : rslot.length = 8) (hfp : fp.length = 8) (hs2 : s2.length = 8)
    (hc0 : c0.length = 8) (hvD : vD.length = 8) (hguard : guard.toNat < aRet.toNat)
    (F : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140) (hrax : s.regs.rax.toBitVec = rcv)
    (h_mem : s.dmem =⋆ Eq (rslot.At aRet) ⋆ Eq (fp.At aFp) ⋆ Eq (s2.At aS2)
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB) ⋆ Eq (vD.At aD)
      ⋆ Eq (e8.At (bf + 184)) ⋆ Eq (c0.At (rcv + 88)) ⋆ F),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 160 + 1) ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = { toBitVec := sp } ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        (Eq ((Int.toBytes 8 (Host.addrOf (k + 130 + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At aFp) ⋆ Eq ((Int.toBytes 8 (bf + 184).toInt).At aS2)
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB) ⋆ Eq (vD.At aD)
          ⋆ Eq (e8.At (bf + 184)) ⋆ Eq (e8.At (rcv + 88)) ⋆ F) st.data.dmem)
      ⟨s, Host.addrOf (k + 123)⟩ := by
  intro hC sp rcv bf aRet aFp aS2 aB aD hRet hFp hS2 hB hD rbp0 r140 guard e8 rslot fp s2 c0 vD he8 hrs hfp hs2 hc0 hvD
    hguard F s hrsp hrbp hr14 hrax h_mem
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp hrbp hr14 hrax h_mem ⊢
  subst rsp rbp r14 hrax
  apply Decode.generated_step_s123 k hk hf sp aB bf hB _ _ _ (by rfl) (by ecancel)
  kn
  apply Decode.generated_step_s124 k hk hf
  intro fl1; kn
  apply Decode.generated_step_s125 k hk hf sp aD hD vD hvD _ _ _ (by rfl) (by ecancel)
  kn
  apply Decode.generated_step_s126 k hk hf
  intro fl2; kn
  apply Decode.generated_step_s127 k hk hf
  intro fl3; kn
  apply Decode.generated_step_s128 k hk hf
  kn
  refine eventually_trans _ _ _ _ (Decode.generated_step_Slot_call k hk hf hC sp (rax.toBitVec + 88) (bf + 184) aRet aFp aS2 hRet hFp hS2 rbp0 r140 guard e8 rslot
    fp s2 c0 he8 hrs hfp hs2 hc0 hguard _ _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by first | rfl | decide)
    (by ecancel)) ?_
  rintro ⟨d, pc⟩ ⟨hpc, hrax', hrbx', hrsp', hrbp', hr14', Hm⟩
  dsimp only at hpc hrax' hrbx' hrsp' hrbp' hr14' Hm
  apply Eventually.done
  refine ⟨hpc, hrax', hrbx', hrsp', hrbp', hr14', ?_⟩
  dsimp only
  ecancel

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- **Accept path of the real `(*v1alpha1.PendingDeposit).UnmarshalSSZ` (Go 1.26.10) from the generated `p2dec --gen4`
chains**; statement = the hand statement `Decode.accept_statement` (unchanged). -/
theorem Decode.accept_from_generated_steps : Decode.accept_statement := by
  intro k hk hf kS hkS hfS pk wc amt sig sl hpk hwc hamt hsig hsl s ra guard
    fp s1 s2 s4 sp0 sp1 sp2 l28 rslot lo ast aP1 aL1 aC1 aP2 aL2 aC2 aN aP3 aL3 aC3 aSl
    hfp h1 h2 h4 hsp0 hsp1 hsp2 hl28 hrs hast haP1 haL1 haC1 haP2 haL2 haC2 haN haP3 haL3 haC3 haSl
    R S hS hlo Heap avail h_mem hguard hlen hav hms hmm
  have hslc : U64CalleeAcc Prysm.Slot.Code.unmarshalSSZLabel := Prysm.Slot.Decode.accept_function_spec_holds kS hkS hfS
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  have hrsp_lt : rsp.toNat < 2 ^ 64 := rsp.toNat_lt_size
  have hg : guard.toNat < (rsp.toBitVec - 80).toNat := Decode.guard_lt _ _ hguard
  -- head: entry → directive 14
  refine eventually_trans _ _ _ _ (Decode.head k hk _ ra guard fp s1 s2 s4 hfp h1 h2 h4 _
    (by dsimp only; ecancel) (Nat.lt_of_le_of_lt (Nat.le_add_right _ 80) hguard) hlen) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, hrax1, hrbx1, Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 hrax1 hrbx1 Hm1
  subst hpc1
  -- PublicKey: 14 → 49 (hand field composition: generated segment + generated tail steps 38, 39, 47, 48)
  refine eventually_trans _ _ _ _ (Decode.from_generated_steps_PublicKey_field k hk hf
    (rsp.toBitVec - 72) rax.toBitVec rbx.toBitVec
    (rsp.toBitVec + 8) (rsp.toBitVec + 16) (rsp.toBitVec - 32) (rsp.toBitVec - 80)
    (rsp.toBitVec - 88 - BitVec.ofNat 64 S) (rax.toBitVec + 8) (rax.toBitVec + 16) (rax.toBitVec + 24) (S + 8)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by bv_omega) (Decode.stack_low_eq _ _)
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    (by simp only [Int64.toBitVec_ofNat])
    { toBitVec := rsp.toBitVec - 8#64 } r14 pk hpk
    (sp0 ++ (sp1 ++ sp2)) rslot lo l28 aP1 aL1 aC1
    (by simp only [List.length_append, hsp0, hsp1, hsp2]) hrs hlo hl28 haP1 haL1 haC1
    _ Heap avail (by omega) d1 hrsp1 hrbp1 hr141
    (by rw [Decode.j3 _ _ _ _ hsp0 hsp1 hsp2]; ecancel) hms hmm) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrsp2, hrbp2, hr142, p1, spl1, lo1, hspl1, hlo1, hrdx2, Hm2⟩
  dsimp only at hpc2 hrsp2 hrbp2 hr142 hrdx2 Hm2
  subst hpc2
  -- WithdrawalCredentials: 49 → 85
  refine eventually_trans _ _ _ _ (Decode.from_generated_steps_WithdrawalCredentials_field k hk hf
    (rsp.toBitVec - 72) rax.toBitVec rbx.toBitVec
    (rsp.toBitVec + 8) (rsp.toBitVec + 16) (rsp.toBitVec - 32) (rsp.toBitVec - 80)
    (rsp.toBitVec - 88 - BitVec.ofNat 64 S) (rax.toBitVec + 32) (rax.toBitVec + 40) (rax.toBitVec + 48)
    (rbx.toBitVec + 48) (S + 8)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by bv_omega) (Decode.stack_low_eq _ _)
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    _ _ wc hwc spl1 (Int.toBytes 8 (Host.addrOf (k + 32 + 1)).toBitVec.toInt) lo1 (Int.toBytes 8 p1.toInt)
    aP2 aL2 aC2 hspl1 (Int.toBytes_length 8 _) hlo1 (Int.toBytes_length 8 _) haP2 haL2 haC2
    _ Heap (avail - 48) (by omega) d2 hrsp2 hrbp2 hr142 (by ecancel) hms hmm) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrsp3, hrbp3, hr143, p2, spl2, lo2, hspl2, hlo2, hrdx3, Hm3⟩
  dsimp only at hpc3 hrsp3 hrbp3 hr143 hrdx3 Hm3
  subst hpc3
  -- Amount: 85 → 88
  refine eventually_trans _ _ _ _ (Decode.from_generated_steps_Amount_field k hk hf
    (rsp.toBitVec - 72) rax.toBitVec rbx.toBitVec (rsp.toBitVec + 16)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    _ _ amt aN hamt haN _ d3 hrsp3 hrbp3 hr143 hrdx3 (by ecancel)) ?_
  rintro ⟨d4, pc4⟩ ⟨hpc4, hrsp4, hrbp4, hr144, Hm4⟩
  dsimp only at hpc4 hrsp4 hrbp4 hr144 Hm4
  subst hpc4
  -- Signature: 88 → 123
  refine eventually_trans _ _ _ _ (Decode.from_generated_steps_Signature_field k hk hf
    (rsp.toBitVec - 72) rax.toBitVec rbx.toBitVec
    (rsp.toBitVec + 8) (rsp.toBitVec + 16) (rsp.toBitVec - 32) (rsp.toBitVec - 80)
    (rsp.toBitVec - 88 - BitVec.ofNat 64 S) (rax.toBitVec + 64) (rax.toBitVec + 72) (rax.toBitVec + 80)
    (rbx.toBitVec + 88) (S + 8)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by bv_omega) (Decode.stack_low_eq _ _)
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    _ _ sig hsig spl2 (Int.toBytes 8 (Host.addrOf (k + 68 + 1)).toBitVec.toInt) lo2 (Int.toBytes 8 p2.toInt)
    aP3 aL3 aC3 hspl2 (Int.toBytes_length 8 _) hlo2 (Int.toBytes_length 8 _) haP3 haL3 haC3
    _ Heap (avail - 48 - 32) (by omega) d4 hrsp4 hrbp4 hr144 (by ecancel) hms hmm) ?_
  rintro ⟨d5, pc5⟩ ⟨hpc5, hrsp5, hrbp5, hr145, p3, spl3, lo3, hspl3, hlo3, hrax5, Hm5⟩
  dsimp only at hpc5 hrsp5 hrbp5 hr145 hrax5 Hm5
  subst hpc5
  -- split the spill area and the low stack for the Slot callee
  have hq0 : (spl3.take 8).length = 8 := by simp [hspl3]
  have hq1 : ((spl3.drop 8).take 8).length = 8 := by simp [hspl3]
  have hq2 : ((spl3.drop 8).drop 8).length = 8 := by simp [hspl3]
  have hlS3 : (lo3.take S).length = S := by simp [hlo3]
  have hl83 : (lo3.drop S).length = 8 := by simp [hlo3]
  have hsp3 : spl3 = spl3.take 8 ++ ((spl3.drop 8).take 8 ++ (spl3.drop 8).drop 8) := by
    rw [List.take_append_drop, List.take_append_drop]
  have hlo3' : lo3 = lo3.take S ++ lo3.drop S := (List.take_append_drop S lo3).symm
  rw [hsp3, hlo3', Decode.j3 _ _ _ _ hq0 hq1 hq2, Decode.lo8 _ S hS _ _ hlS3 hl83] at Hm5
  -- Slot: 123 → 161 (hand field composition: generated steps 123–128 + generated call block; hC = Prysm.Slot.Decode.accept_function_spec_holds)
  refine eventually_trans _ _ _ _ (Decode.from_generated_steps_Slot_field k hk hf hslc
    (rsp.toBitVec - 72) rax.toBitVec rbx.toBitVec (rsp.toBitVec - 80) (rsp.toBitVec - 88) (rsp.toBitVec - 64)
    (rsp.toBitVec + 16) (rsp.toBitVec + 32) (by bv_omega) (by bv_omega) (by bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    { toBitVec := rsp.toBitVec - 8#64 } r14 guard sl
    (Int.toBytes 8 (Host.addrOf (k + 107 + 1)).toBitVec.toInt) (lo3.drop S) ((spl3.drop 8).take 8) aSl
    (Int.toBytes 8 rdi.toBitVec.toInt)
    hsl (Int.toBytes_length 8 _) hl83 hq1 haSl (Int.toBytes_length 8 _) hg _ d5 hrsp5 hrbp5 hr145
    (by exact hrax5) (by ecancel)) ?_
  rintro ⟨d6, pc6⟩ ⟨hpc6, hrax6, hrbx6, hrsp6, hrbp6, hr146, Hm6⟩
  dsimp only at hpc6 hrax6 hrbx6 hrsp6 hrbp6 hr146 Hm6
  subst hpc6
  -- epilogue 161–163
  refine eventually_trans _ _ _ _ (Decode.epi k hk (rsp.toBitVec - 72) (rsp.toBitVec - 8) rsp.toBitVec
    (by bv_omega) (by bv_omega) rbp ra _ d6 hrsp6 (by ecancel)) ?_
  rintro ⟨d7, pc7⟩ ⟨hpc7, hrax7, hrbx7, hrsp7, hrbp7, hr147, hmem7⟩
  dsimp only at hpc7 hrax7 hrbx7 hrsp7 hrbp7 hr147 hmem7
  apply Eventually.done
  rw [show k + 130 + 1 = k + 131 from rfl] at Hm6
  rw [show avail - 48 - 32 - 96 = avail - 176 by omega] at Hm6
  refine ⟨hpc7, hrax7.trans hrax6, hrbx7.trans hrbx6, ?_, hrbp7, hr147.trans hr146, p1, p2, p3,
    spl3.take 8 ++ (Int.toBytes 8 (rbx.toBitVec + 184).toInt ++ (spl3.drop 8).drop 8),
    lo3.take S ++ Int.toBytes 8 (rsp.toBitVec - 8#64).toInt,
    (by simp only [List.length_append, hq0, hq2, Int.toBytes_length]),
    (by simp only [List.length_append, hlS3, Int.toBytes_length]), ?_⟩
  · dsimp only; rw [hrsp7]; apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
  · dsimp only; rw [hmem7, Decode.j3 _ _ _ _ hq0 (Int.toBytes_length 8 _) hq2,
      Decode.lo8 _ S hS _ _ hlS3 (Int.toBytes_length 8 _)]
    ecancel

end Prysm.PendingDeposit
