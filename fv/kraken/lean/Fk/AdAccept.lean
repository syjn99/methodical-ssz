import Fk.CpAccept
import Fk.NeAccept

/-!
# Prysm AttestationData.UnmarshalSSZ, accept path, on Kraken main

Input `buf` of 128 bytes: Slot (8), CommitteeIndex (8), BeaconBlockRoot (32),
Source = Epoch (8) ‖ Root (32), Target = Epoch (8) ‖ Root (32). The code checks
len = 128, copies Slot and CommitteeIndex, then three times (BeaconBlockRoot,
Source.Root, Target.Root): `makeslice(byte, 0, 32)`, header (p, 0, 32), the
write-barrier flag, `memmove` of 32 bytes, len = 32. Source and Target are new
objects (`runtime.newobject`, 32 bytes: Epoch, Root ptr, len, cap). Checkpoint
decoding is inlined.
Receiver layout (this module's struct): Slot @0, CommitteeIndex @8,
BeaconBlockRoot @16 (ptr), @24 (len), @32 (cap), Source @40, Target @48.
Premises the Go caller provides: separated receiver, input and stack chunks,
the stack guard below rsp − 48, the write barrier off (read 6 times), heap room
for 160 bytes, the three runtime contracts.
-/

open Fk Fk.Code
variable [Host]

theorem cpObj_sep (p : BitVec 64) :
    Eq ((List.replicate 32 (0 : UInt8)).At p) = Eq ((List.replicate 8 0).At p) ⋆ Eq ((List.replicate 8 0).At (p + 8))
      ⋆ Eq ((List.replicate 8 0).At (p + 16)) ⋆ Eq ((List.replicate 8 0).At (p + 24)) := by
  rw [show List.replicate 32 (0 : UInt8) = List.replicate 8 0 ++ (List.replicate 8 0 ++ (List.replicate 8 0
    ++ List.replicate 8 0)) by rfl]
  rw [at_app _ _ (b := p + 8) (by simp) (by simp), at_app _ _ (b := p + 16) (by simp; bv_omega) (by simp),
    at_app _ _ (b := p + 24) (by simp; bv_omega) (by simp)]
  simp only [Std.ExtHashMap.sep_assoc]

theorem ad_slot (x : BitVec 64) : x - 8#64 - 40 - 8#64 = x - 56 := by bv_omega
theorem ad_slot' (x : BitVec 64) : ({ toBitVec := x - 56 } + 8 : UInt64).toBitVec - 8#64 = x - 56 := by
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
theorem ad_g (x o : BitVec 64) : ({ toBitVec := x - 56 } + 8 : UInt64).toBitVec + o = x - 48 + o := by
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
theorem ad_pop (x : BitVec 64) : 40 + ({ toBitVec := x - 56 } + 8 : UInt64).toBitVec = x - 8 := by
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
theorem ad_8 (x : BitVec 64) : x - 48 + 56 = x + 8 := by bv_omega
theorem ad_sp (x : BitVec 64) : x - 56 + 8 = x - 48 := by bv_omega
/-- The 24-byte spill area of the calls (rsp − 48) as 8 + 16 bytes. -/
theorem ad_sp24 (x : BitVec 64) (l : List UInt8) (h : l.length = 24) :
    Eq (l.At (x - 48)) = Eq ((l.take 8).At (x - 48)) ⋆ Eq ((l.drop 8).At (x - 40)) := by
  conv => lhs; rw [← List.take_append_drop 8 l]
  exact at_app _ _ (by simp [h]; bv_omega) (by simp [h])
theorem ad_sp8 (x : BitVec 64) (a b : List UInt8) (ha : a.length = 8) (hb : b.length = 16) :
    Eq ((a ++ b).At (x - 48)) = Eq (a.At (x - 48)) ⋆ Eq (b.At (x - 40)) :=
  at_app _ _ (by rw [ha]; bv_omega) (by simp [ha, hb])
theorem ad_16 (x : BitVec 64) : x - 48 + 64 = x + 16 := by bv_omega
theorem ad_m16 (x : BitVec 64) : x - 48 + 32 = x - 16 := by bv_omega
theorem ad_m24 (x : BitVec 64) : x - 48 + 24 = x - 24 := by bv_omega

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
theorem ad_accept_main (k : Nat) (hk : PrysmAttestationDataUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh PrysmAttestationDataUnmarshalSSZ k)
    (in0 in1 root se sroot te troot : List UInt8) (h0 : in0.length = 8) (h1 : in1.length = 8)
    (hroot : root.length = 32) (hse : se.length = 8) (hsroot : sroot.length = 32) (hte : te.length = 8)
    (htroot : troot.length = 32)
    (s : MachineData) (ra guard : UInt64)
    (fp s8 s16 l16 l24 rslot c0 c8 cP cL cC cS cT : List UInt8)
    (hfp : fp.length = 8) (hs8 : s8.length = 8) (hs16 : s16.length = 8) (hl16 : l16.length = 8) (hl24 : l24.length = 8)
    (hrs : rslot.length = 8) (hc0 : c0.length = 8) (hc8 : c8.length = 8) (hcP : cP.length = 8) (hcL : cL.length = 8)
    (hcC : cC.length = 8) (hcS : cS.length = 8) (hcT : cT.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch spa spb : List UInt8) (hsc : scratch.length = S)
    (hspa : spa.length = 8) (hspb : spb.length = 16)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s8.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s16.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 56)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 56 - BitVec.ofNat 64 S))
      ⋆ Eq (spa.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (spb.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16)) ⋆ Heap avail
      ⋆ Eq (in0.At s.regs.rbx.toBitVec) ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 8))
      ⋆ Eq (root.At (s.regs.rbx.toBitVec + 16)) ⋆ Eq (se.At (s.regs.rbx.toBitVec + 48))
      ⋆ Eq (sroot.At (s.regs.rbx.toBitVec + 56)) ⋆ Eq (te.At (s.regs.rbx.toBitVec + 88))
      ⋆ Eq (troot.At (s.regs.rbx.toBitVec + 96))
      ⋆ Eq (c0.At s.regs.rax.toBitVec) ⋆ Eq (c8.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (cP.At (s.regs.rax.toBitVec + 16)) ⋆ Eq (cL.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32)) ⋆ Eq (cS.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (cT.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 56 ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rcx = 128) (hav : 160 ≤ avail)
    (hms : MakesliceC Heap (label "type__" + 48736).toBitVec 1 S) (hmm : MemmoveC S)
    (hno : NewobjectC Heap (label "type__" + 100288).toBitVec 32 S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (p ps pt p1 p2 : BitVec 64) (fp' s8' s16' l16' l24' rs' sc' spa' spb' : List UInt8),
          fp'.length = 8 ∧ s8'.length = 8 ∧ s16'.length = 8 ∧ l16'.length = 8 ∧ l24'.length = 8 ∧ rs'.length = 8
          ∧ sc'.length = S ∧ spa'.length = 8 ∧ spb'.length = 16 ∧
          (Eq (in0.At s.regs.rax.toBitVec) ⋆ Eq (in1.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 ps.toInt).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 pt.toInt).At (s.regs.rax.toBitVec + 48)) ⋆ Eq (root.At p)
          ⋆ Eq (se.At ps) ⋆ Eq ((Int.toBytes 8 p1.toInt).At (ps + 8)) ⋆ Eq ((Int.toBytes 8 32).At (ps + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (ps + 24)) ⋆ Eq (sroot.At p1)
          ⋆ Eq (te.At pt) ⋆ Eq ((Int.toBytes 8 p2.toInt).At (pt + 8)) ⋆ Eq ((Int.toBytes 8 32).At (pt + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (pt + 24)) ⋆ Eq (troot.At p2)
          ⋆ Heap (avail - 160)
          ⋆ Eq (in0.At s.regs.rbx.toBitVec) ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq (root.At (s.regs.rbx.toBitVec + 16)) ⋆ Eq (se.At (s.regs.rbx.toBitVec + 48))
          ⋆ Eq (sroot.At (s.regs.rbx.toBitVec + 56)) ⋆ Eq (te.At (s.regs.rbx.toBitVec + 88))
          ⋆ Eq (troot.At (s.regs.rbx.toBitVec + 96))
          ⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq (fp'.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s8'.At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq (s16'.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (l16'.At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq (l24'.At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (rs'.At (s.regs.rsp.toBitVec - 56)) ⋆ Eq (sc'.At (s.regs.rsp.toBitVec - 56 - BitVec.ofNat 64 S))
          ⋆ Eq (spa'.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (spb'.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hlen ⊢
  subst hlen
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; simp only [UInt64.size] at *
  kat hk PrysmAttestationDataUnmarshalSSZ 0
  kat hk PrysmAttestationDataUnmarshalSSZ 1
  kat hk PrysmAttestationDataUnmarshalSSZ 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 3
  split
  · rename_i h; exfalso
    simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk PrysmAttestationDataUnmarshalSSZ 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 5
  kat hk PrysmAttestationDataUnmarshalSSZ 6
  kat hk PrysmAttestationDataUnmarshalSSZ 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s16 _ _ (by bv_omega) (by ecancel) (by exact hs16)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 8
  kat hk PrysmAttestationDataUnmarshalSSZ 9
  kat hk PrysmAttestationDataUnmarshalSSZ 10
  split
  case isTrue h => exact absurd h (by decide)
  simp only [Effects.All]
  kat hk PrysmAttestationDataUnmarshalSSZ 11
  apply store_step_at _ _ (rsp.toBitVec + 8) _ _ _ s8 _ _ (by bv_omega) (by ecancel) (by exact hs8)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 12
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by bv_omega) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 13
  apply load_step _ _ _ _ in0 _ _ (by ecancel) (by exact h0)
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 14
  apply store_step_at _ _ rax.toBitVec _ _ _ c0 _ _ (by bv_omega) (by ecancel) (by exact hc0)
  intro m5 H5
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl in0 h0] at H5
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 15
  apply load_step_at _ _ (rbx.toBitVec + 8) _ _ in1 _ _ (by kaddr) (by ecancel) (by exact h1)
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 16
  apply store_step_at _ _ (rax.toBitVec + 8) _ _ _ c8 _ _ (by kaddr) (by ecancel) (by exact hc8)
  intro m6 H6
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl in1 h1] at H6
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 17
  kat hk PrysmAttestationDataUnmarshalSSZ 18
  intro _
  kat hk PrysmAttestationDataUnmarshalSSZ 19
  kat hk PrysmAttestationDataUnmarshalSSZ 20
  apply store_step_at _ _ (rsp.toBitVec - 56) _ _ _ rslot _ _ (ad_slot _) (by ecancel) (by exact hrs)
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  rw [ad_slot] at *
  refine eventually_trans _ _ _ _ (hms _ (Host.addrOf (k + 20 + 1)) 32 avail scratch (spa ++ spb) _ rfl (by simp) (by rfl) (by omega)
    (by unfold maxAlloc; omega) (by omega) hsc (by simp [hspa, hspb])
    (by dsimp only; rw [ad_sp, ad_sp8 _ _ _ hspa hspb]; ecancel)) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrsp2, hr14c2, -, stk2, sm2, hstk2, hsm2, Hm2⟩
  rw [ad_sp, ad_sp24 _ _ hsm2] at Hm2
  dsimp only at hpc2 hrsp2 Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := d2
  simp only at hrsp2 hr14c2 Hm2
  subst hrsp2 hr14c2
  simp only [Nat.one_mul] at Hm2
  kat hk PrysmAttestationDataUnmarshalSSZ 21
  rw [ad_g, ad_8]
  apply load_step _ _ _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 22
  apply store_step_at _ _ (rax.toBitVec + 24) _ _ _ cL _ _ (by kaddr) (by ecancel) (by exact hcL)
  intro m8 H8
  simp only [Width.bytes, Width.bits] at H8
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 23
  apply store_step_at _ _ (rax.toBitVec + 32) _ _ _ cC _ _ (by kaddr) (by ecancel) (by exact hcC)
  intro m9 H9
  simp only [Width.bytes, Width.bits] at H9
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 24
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 25
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf PrysmAttestationDataUnmarshalSSZ 30
  kat hk PrysmAttestationDataUnmarshalSSZ 30
  kat hk PrysmAttestationDataUnmarshalSSZ 31
  rw [ad_g, ad_m16]
  apply store_step _ _ _ _ _ l16 _ _ (by ecancel) (by exact hl16)
  intro m10 H10
  simp only [Width.bytes, Width.bits] at H10
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 32
  apply store_step_at _ _ (rax.toBitVec + 16) _ _ _ cP _ _ (by kaddr) (by ecancel) (by exact hcP)
  intro m11 H11
  simp only [Width.bytes, Width.bits] at H11
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 33
  rw [ad_g, ad_16]
  apply load_step _ _ _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 34
  kat hk PrysmAttestationDataUnmarshalSSZ 35
  kat hk PrysmAttestationDataUnmarshalSSZ 36
  kat hk PrysmAttestationDataUnmarshalSSZ 37
  apply store_step_at _ _ (rsp.toBitVec - 56) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 20 + 1)).toBitVec.toInt) _ _
    (ad_slot' _) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m12 H12
  simp only [Width.bytes, Width.bits] at H12
  kunfold
  rw [ad_slot'] at *
  refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (k + 37 + 1)) root (List.replicate 32 0) stk2 _
    (by rw [hroot]; rfl) (by simp [hroot]) hstk2
    (by dsimp only; rw [show (16 : BitVec 64) + rbx.toBitVec = rbx.toBitVec + 16 from BitVec.add_comm _ _]; ecancel)) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrsp3, _hmr143, _hmrbp3, stk3, hstk3, Hm3⟩
  dsimp only at hpc3 hrsp3 Hm3
  subst hpc3
  obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,
    zmms3, flags3, mem3⟩ := d3
  simp only at hrsp3 _hmr143 Hm3
  subst hrsp3 _hmr143
  rw [show (16 : BitVec 64) + rbx.toBitVec = rbx.toBitVec + 16 from BitVec.add_comm _ _] at Hm3
  kat hk PrysmAttestationDataUnmarshalSSZ 38
  rw [ad_g, ad_8]
  apply load_step _ _ _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 39
  apply store_step_at _ _ (rax.toBitVec + 24) _ _ _ (Int.toBytes 8 (BitVec.toInt (0 : BitVec 64))) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m13 H13
  simp only [Width.bytes, Width.bits] at H13
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 40
  apply store_step_at _ _ (rax.toBitVec + 32) _ _ _ (Int.toBytes 8 (BitVec.toInt (32 : BitVec 64))) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m14 H14
  simp only [Width.bytes, Width.bits] at H14
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 41
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 42
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk PrysmAttestationDataUnmarshalSSZ 43
  rw [ad_g, ad_m16]
  apply load_step _ _ _ _ (Int.toBytes 8 rax2.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 44
  klabel hk hf PrysmAttestationDataUnmarshalSSZ 51
  kat hk PrysmAttestationDataUnmarshalSSZ 51
  kat hk PrysmAttestationDataUnmarshalSSZ 52
  apply store_step_at _ _ (rax.toBitVec + 16) _ _ _ (Int.toBytes 8 rax2.toBitVec.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m15 H15
  simp only [Width.bytes, Width.bits, BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at H15
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 53
  kat hk PrysmAttestationDataUnmarshalSSZ 54
  apply store_step_at _ _ (rsp.toBitVec - 56) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 37 + 1)).toBitVec.toInt) _ _
    (ad_slot' _) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m16 H16
  simp only [Width.bytes, Width.bits] at H16
  kunfold
  rw [ad_slot'] at *
  refine eventually_trans _ _ _ _ (hno _ (Host.addrOf (k + 54 + 1)) (avail - 32) stk3 (sm2.take 8) _ rfl (by omega) hstk3
    (by simp [hsm2]) (by dsimp only; rw [ad_sp]; ecancel)) ?_
  rintro ⟨d4, pc4⟩ ⟨hpc4, hrsp4, hr14c4, -, stk4, sn4, hstk4, hsn4, Hm4⟩
  rw [ad_sp] at Hm4
  dsimp only at hpc4 hrsp4 Hm4
  subst hpc4
  obtain ⟨⟨rax4, rbx4, rcx4, rdx4, rsi4, rdi4, rsp4, rbp4, r84, r94, r104, r114, r124, r134, r144, r154⟩,
    zmms4, flags4, mem4⟩ := d4
  simp only at hrsp4 hr14c4 Hm4
  subst hrsp4 hr14c4
  rw [cpObj_sep] at Hm4
  kat hk PrysmAttestationDataUnmarshalSSZ 55
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 56
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk PrysmAttestationDataUnmarshalSSZ 57
  rw [ad_g, ad_8]
  apply load_step _ _ _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 58
  klabel hk hf PrysmAttestationDataUnmarshalSSZ 65
  kat hk PrysmAttestationDataUnmarshalSSZ 65
  kat hk PrysmAttestationDataUnmarshalSSZ 66
  rw [ad_g, ad_m24]
  apply store_step _ _ _ _ _ l24 _ _ (by ecancel) (by exact hl24)
  intro m17 H17
  simp only [Width.bytes, Width.bits] at H17
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 67
  apply store_step_at _ _ (rax.toBitVec + 40) _ _ _ cS _ _ (by kaddr) (by ecancel) (by exact hcS)
  intro m18 H18
  simp only [Width.bytes, Width.bits] at H18
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 68
  rw [ad_g, ad_16]
  apply load_step _ _ _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 69
  apply load_step_at _ _ (rbx.toBitVec + 48) _ _ se _ _ (by kaddr) (by ecancel) (by exact hse)
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 70
  kat hk PrysmAttestationDataUnmarshalSSZ 71
  apply store_step _ _ _ _ _ (List.replicate 8 0) _ _ (by ecancel) (by simp)
  intro m19 H19
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl se hse] at H19
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 72
  kat hk PrysmAttestationDataUnmarshalSSZ 73
  intro _
  kat hk PrysmAttestationDataUnmarshalSSZ 74
  kat hk PrysmAttestationDataUnmarshalSSZ 75
  apply store_step_at _ _ (rsp.toBitVec - 56) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 54 + 1)).toBitVec.toInt) _ _
    (ad_slot' _) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m20 H20
  simp only [Width.bytes, Width.bits] at H20
  kunfold
  rw [ad_slot'] at *
  refine eventually_trans _ _ _ _ (hms _ (Host.addrOf (k + 75 + 1)) 32 (avail - 32 - 32) stk4 (sn4 ++ sm2.drop 8) _ rfl (by simp) (by rfl)
    (by omega)
    (by unfold maxAlloc; omega) (by omega) hstk4 (by simp [hsn4, hsm2])
    (by dsimp only; rw [ad_sp, ad_sp8 _ _ _ hsn4 (by simp [hsm2])]; ecancel)) ?_
  rintro ⟨d5, pc5⟩ ⟨hpc5, hrsp5, hr14c5, -, stk5, sm5, hstk5, hsm5, Hm5⟩
  rw [ad_sp, ad_sp24 _ _ hsm5] at Hm5
  dsimp only at hpc5 hrsp5 Hm5
  subst hpc5
  obtain ⟨⟨rax5, rbx5, rcx5, rdx5, rsi5, rdi5, rsp5, rbp5, r85, r95, r105, r115, r125, r135, r145, r155⟩,
    zmms5, flags5, mem5⟩ := d5
  simp only at hrsp5 hr14c5 Hm5
  subst hrsp5 hr14c5
  simp only [Nat.one_mul] at Hm5
  kat hk PrysmAttestationDataUnmarshalSSZ 76
  rw [ad_g, ad_m24]
  apply load_step _ _ _ _ (Int.toBytes 8 rax4.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 77
  apply store_step_at _ _ (rax4.toBitVec + 16) _ _ _ (List.replicate 8 0) _ _ (by kaddr) (by ecancel) (by simp)
  intro m21 H21
  simp only [Width.bytes, Width.bits] at H21
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 78
  apply store_step_at _ _ (rax4.toBitVec + 24) _ _ _ (List.replicate 8 0) _ _ (by kaddr) (by ecancel) (by simp)
  intro m22 H22
  simp only [Width.bytes, Width.bits] at H22
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 79
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 80
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf PrysmAttestationDataUnmarshalSSZ 86
  kat hk PrysmAttestationDataUnmarshalSSZ 86
  kat hk PrysmAttestationDataUnmarshalSSZ 87
  rw [ad_g, ad_m16]
  apply store_step _ _ _ _ _ (Int.toBytes 8 rax2.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m23 H23
  simp only [Width.bytes, Width.bits] at H23
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 88
  apply store_step_at _ _ (rax4.toBitVec + 8) _ _ _ (List.replicate 8 0) _ _ (by kaddr) (by ecancel) (by simp)
  intro m24 H24
  simp only [Width.bytes, Width.bits] at H24
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 89
  rw [ad_g, ad_16]
  apply load_step _ _ _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 90
  kat hk PrysmAttestationDataUnmarshalSSZ 91
  kat hk PrysmAttestationDataUnmarshalSSZ 92
  apply store_step_at _ _ (rsp.toBitVec - 56) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 75 + 1)).toBitVec.toInt) _ _
    (ad_slot' _) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m25 H25
  simp only [Width.bytes, Width.bits] at H25
  kunfold
  rw [ad_slot'] at *
  refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (k + 92 + 1)) sroot (List.replicate 32 0) stk5 _
    (by rw [hsroot]; rfl) (by simp [hsroot]) hstk5
    (by dsimp only; rw [show (56 : BitVec 64) + rbx.toBitVec = rbx.toBitVec + 56 from BitVec.add_comm _ _]; ecancel)) ?_
  rintro ⟨d6, pc6⟩ ⟨hpc6, hrsp6, _hmr146, _hmrbp6, stk6, hstk6, Hm6⟩
  dsimp only at hpc6 hrsp6 Hm6
  subst hpc6
  obtain ⟨⟨rax6, rbx6, rcx6, rdx6, rsi6, rdi6, rsp6, rbp6, r86, r96, r106, r116, r126, r136, r146, r156⟩,
    zmms6, flags6, mem6⟩ := d6
  simp only at hrsp6 _hmr146 Hm6
  subst hrsp6 _hmr146
  rw [show (56 : BitVec 64) + rbx.toBitVec = rbx.toBitVec + 56 from BitVec.add_comm _ _] at Hm6
  kat hk PrysmAttestationDataUnmarshalSSZ 93
  rw [ad_g, ad_m24]
  apply load_step _ _ _ _ (Int.toBytes 8 rax4.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 94
  apply store_step_at _ _ (rax4.toBitVec + 16) _ _ _ (Int.toBytes 8 (BitVec.toInt (0 : BitVec 64))) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m26 H26
  simp only [Width.bytes, Width.bits] at H26
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 95
  apply store_step_at _ _ (rax4.toBitVec + 24) _ _ _ (Int.toBytes 8 (BitVec.toInt (32 : BitVec 64))) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m27 H27
  simp only [Width.bytes, Width.bits] at H27
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 96
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 97
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk PrysmAttestationDataUnmarshalSSZ 98
  rw [ad_g, ad_m16]
  apply load_step _ _ _ _ (Int.toBytes 8 rax5.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 99
  klabel hk hf PrysmAttestationDataUnmarshalSSZ 106
  kat hk PrysmAttestationDataUnmarshalSSZ 106
  kat hk PrysmAttestationDataUnmarshalSSZ 107
  apply store_step_at _ _ (rax4.toBitVec + 8) _ _ _ (Int.toBytes 8 rax5.toBitVec.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m28 H28
  simp only [Width.bytes, Width.bits, BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at H28
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 108
  kat hk PrysmAttestationDataUnmarshalSSZ 109
  apply store_step_at _ _ (rsp.toBitVec - 56) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 92 + 1)).toBitVec.toInt) _ _
    (ad_slot' _) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m29 H29
  simp only [Width.bytes, Width.bits] at H29
  kunfold
  rw [ad_slot'] at *
  refine eventually_trans _ _ _ _ (hno _ (Host.addrOf (k + 109 + 1)) (avail - 32 - 32 - 32) stk6 (sm5.take 8) _ rfl (by omega) hstk6
    (by simp [hsm5]) (by dsimp only; rw [ad_sp]; ecancel)) ?_
  rintro ⟨d7, pc7⟩ ⟨hpc7, hrsp7, hr14c7, -, stk7, sn7, hstk7, hsn7, Hm7⟩
  rw [ad_sp] at Hm7
  dsimp only at hpc7 hrsp7 Hm7
  subst hpc7
  obtain ⟨⟨rax7, rbx7, rcx7, rdx7, rsi7, rdi7, rsp7, rbp7, r87, r97, r107, r117, r127, r137, r147, r157⟩,
    zmms7, flags7, mem7⟩ := d7
  simp only at hrsp7 hr14c7 Hm7
  subst hrsp7 hr14c7
  rw [cpObj_sep] at Hm7
  kat hk PrysmAttestationDataUnmarshalSSZ 110
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 111
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk PrysmAttestationDataUnmarshalSSZ 112
  rw [ad_g, ad_8]
  apply load_step _ _ _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 113
  klabel hk hf PrysmAttestationDataUnmarshalSSZ 120
  kat hk PrysmAttestationDataUnmarshalSSZ 120
  kat hk PrysmAttestationDataUnmarshalSSZ 121
  rw [ad_g, ad_m24]
  apply store_step _ _ _ _ _ (Int.toBytes 8 rax4.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m30 H30
  simp only [Width.bytes, Width.bits] at H30
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 122
  apply store_step_at _ _ (rax.toBitVec + 48) _ _ _ cT _ _ (by kaddr) (by ecancel) (by exact hcT)
  intro m31 H31
  simp only [Width.bytes, Width.bits] at H31
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 123
  rw [ad_g, ad_16]
  apply load_step _ _ _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 124
  apply load_step_at _ _ (rbx.toBitVec + 88) _ _ te _ _ (by kaddr) (by ecancel) (by exact hte)
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 125
  kat hk PrysmAttestationDataUnmarshalSSZ 126
  apply store_step _ _ _ _ _ (List.replicate 8 0) _ _ (by ecancel) (by simp)
  intro m32 H32
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl te hte] at H32
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 127
  kat hk PrysmAttestationDataUnmarshalSSZ 128
  intro _
  kat hk PrysmAttestationDataUnmarshalSSZ 129
  kat hk PrysmAttestationDataUnmarshalSSZ 130
  kat hk PrysmAttestationDataUnmarshalSSZ 131
  apply store_step_at _ _ (rsp.toBitVec - 56) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 109 + 1)).toBitVec.toInt) _ _
    (ad_slot' _) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m33 H33
  simp only [Width.bytes, Width.bits] at H33
  kunfold
  rw [ad_slot'] at *
  refine eventually_trans _ _ _ _ (hms _ (Host.addrOf (k + 131 + 1)) 32 (avail - 32 - 32 - 32 - 32) stk7 (sn7 ++ sm5.drop 8) _ rfl (by simp)
    (by rfl) (by omega)
    (by unfold maxAlloc; omega) (by omega) hstk7 (by simp [hsn7, hsm5])
    (by dsimp only; rw [ad_sp, ad_sp8 _ _ _ hsn7 (by simp [hsm5])]; ecancel)) ?_
  rintro ⟨d8, pc8⟩ ⟨hpc8, hrsp8, hr14c8, -, stk8, sm8, hstk8, hsm8, Hm8⟩
  rw [ad_sp, ad_sp24 _ _ hsm8] at Hm8
  dsimp only at hpc8 hrsp8 Hm8
  subst hpc8
  obtain ⟨⟨rax8, rbx8, rcx8, rdx8, rsi8, rdi8, rsp8, rbp8, r88, r98, r108, r118, r128, r138, r148, r158⟩,
    zmms8, flags8, mem8⟩ := d8
  simp only at hrsp8 hr14c8 Hm8
  subst hrsp8 hr14c8
  simp only [Nat.one_mul] at Hm8
  kat hk PrysmAttestationDataUnmarshalSSZ 132
  rw [ad_g, ad_m24]
  apply load_step _ _ _ _ (Int.toBytes 8 rax7.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 133
  apply store_step_at _ _ (rax7.toBitVec + 16) _ _ _ (List.replicate 8 0) _ _ (by kaddr) (by ecancel) (by simp)
  intro m34 H34
  simp only [Width.bytes, Width.bits] at H34
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 134
  apply store_step_at _ _ (rax7.toBitVec + 24) _ _ _ (List.replicate 8 0) _ _ (by kaddr) (by ecancel) (by simp)
  intro m35 H35
  simp only [Width.bytes, Width.bits] at H35
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 135
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 136
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf PrysmAttestationDataUnmarshalSSZ 141
  kat hk PrysmAttestationDataUnmarshalSSZ 141
  kat hk PrysmAttestationDataUnmarshalSSZ 142
  rw [ad_g, ad_m16]
  apply store_step _ _ _ _ _ (Int.toBytes 8 rax5.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m36 H36
  simp only [Width.bytes, Width.bits] at H36
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 143
  apply store_step_at _ _ (rax7.toBitVec + 8) _ _ _ (List.replicate 8 0) _ _ (by kaddr) (by ecancel) (by simp)
  intro m37 H37
  simp only [Width.bytes, Width.bits] at H37
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 144
  rw [ad_g, ad_16]
  apply load_step _ _ _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 145
  kat hk PrysmAttestationDataUnmarshalSSZ 146
  kat hk PrysmAttestationDataUnmarshalSSZ 147
  apply store_step_at _ _ (rsp.toBitVec - 56) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 131 + 1)).toBitVec.toInt) _ _
    (ad_slot' _) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m38 H38
  simp only [Width.bytes, Width.bits] at H38
  kunfold
  rw [ad_slot'] at *
  refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (k + 147 + 1)) troot (List.replicate 32 0) stk8 _
    (by rw [htroot]; rfl) (by simp [htroot]) hstk8
    (by dsimp only; rw [show (96 : BitVec 64) + rbx.toBitVec = rbx.toBitVec + 96 from BitVec.add_comm _ _]; ecancel)) ?_
  rintro ⟨d9, pc9⟩ ⟨hpc9, hrsp9, _hmr149, _hmrbp9, stk9, hstk9, Hm9⟩
  dsimp only at hpc9 hrsp9 Hm9
  subst hpc9
  obtain ⟨⟨rax9, rbx9, rcx9, rdx9, rsi9, rdi9, rsp9, rbp9, r89, r99, r109, r119, r129, r139, r149, r159⟩,
    zmms9, flags9, mem9⟩ := d9
  simp only at hrsp9 _hmr149 Hm9
  subst hrsp9 _hmr149
  rw [show (96 : BitVec 64) + rbx.toBitVec = rbx.toBitVec + 96 from BitVec.add_comm _ _] at Hm9
  kat hk PrysmAttestationDataUnmarshalSSZ 148
  rw [ad_g, ad_m24]
  apply load_step _ _ _ _ (Int.toBytes 8 rax7.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 149
  apply store_step_at _ _ (rax7.toBitVec + 16) _ _ _ (Int.toBytes 8 (BitVec.toInt (0 : BitVec 64))) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m39 H39
  simp only [Width.bytes, Width.bits] at H39
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 150
  apply store_step_at _ _ (rax7.toBitVec + 24) _ _ _ (Int.toBytes 8 (BitVec.toInt (32 : BitVec 64))) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m40 H40
  simp only [Width.bytes, Width.bits] at H40
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 151
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 152
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk PrysmAttestationDataUnmarshalSSZ 153
  rw [ad_g, ad_m16]
  apply load_step _ _ _ _ (Int.toBytes 8 rax8.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 154
  klabel hk hf PrysmAttestationDataUnmarshalSSZ 161
  kat hk PrysmAttestationDataUnmarshalSSZ 161
  kat hk PrysmAttestationDataUnmarshalSSZ 162
  apply store_step_at _ _ (rax7.toBitVec + 8) _ _ _ (Int.toBytes 8 rax8.toBitVec.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m41 H41
  simp only [Width.bytes, Width.bits, BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at H41
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 163
  intro _
  kat hk PrysmAttestationDataUnmarshalSSZ 164
  intro _
  kat hk PrysmAttestationDataUnmarshalSSZ 165
  kat hk PrysmAttestationDataUnmarshalSSZ 166
  rw [ad_pop]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmAttestationDataUnmarshalSSZ 167
  rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [show Int.toBytes 8 (BitVec.toInt (32 : BitVec 64)) = Int.toBytes 8 32 by decide,
    show avail - 32 - 32 - 32 - 32 - 32 = avail - 160 by omega] at H41
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, rax2.toBitVec, rax4.toBitVec, rax7.toBitVec, rax5.toBitVec, rax8.toBitVec,
    Int.toBytes 8 rbp.toBitVec.toInt, Int.toBytes 8 rax.toBitVec.toInt, Int.toBytes 8 rbx.toBitVec.toInt,
    Int.toBytes 8 rax8.toBitVec.toInt, Int.toBytes 8 rax7.toBitVec.toInt,
    Int.toBytes 8 (Host.addrOf (k + 147 + 1)).toBitVec.toInt, stk9, sm8.take 8, sm8.drop 8,
    Int.toBytes_length 8 _, Int.toBytes_length 8 _, Int.toBytes_length 8 _, Int.toBytes_length 8 _,
    Int.toBytes_length 8 _, Int.toBytes_length 8 _, by assumption, by simp [*], by simp [*], ?_⟩
  all_goals first
    | trivial | rfl
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (apply UInt64.toBitVec_inj.mp; simp; bv_omega)
    | exact sep_true (by ecancel)
