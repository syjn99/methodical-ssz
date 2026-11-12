import E2eAd.AdHead
import Prysm.ElfData.CheckpointAndEpoch

/-!
# `(*v1alpha1.AttestationData).UnmarshalSSZ`, accept path, segment 2

    a.BeaconBlockRoot = make([]byte, 0, 32)
    a.BeaconBlockRoot = append(a.BeaconBlockRoot, buf[16:48]...)

Directive indices of `E2eAd.Code.AdUnmarshal`: 85 `L_167`, 86–89 `lea type:uint8; xor %ebx;
mov $0x20,%ecx; callq runtime.makeslice`, 90–94 `Root.len = 0`, `Root.cap = 32`,
writeBarrier test (`je L_1ac`), 100 `L_1ac`, 101–102 save the pointer at rsp − 16 and store
`Root.ptr`, 103–106 `callq runtime.memmove` (32 bytes from buf + 16), 107–111 `Root.len =
Root.cap = 32`, writeBarrier test (`jne`, not taken), 112 reload the pointer into rbx,
113 `jmp L_208`, 120 `L_208` (end of this segment).

`rsp0` is rsp at the entry of `UnmarshalSSZ`; the frame is rsp0 − 120 … rsp0 − 8. The
runtime calls get the 24-byte argument area at rsp0 − 120 and the `S + 96` stack bytes
`lo` below their return slot rsp0 − 128 (`MakesliceC` / `MemmoveC` with stack `S + 96`).
-/

open Machine Runtime TestTarget E2eAd.Code
variable [Host]

namespace E2eAd

theorem ada_lo (x : BitVec 64) (S : Nat) (hS : S < 2 ^ 60) :
    x - 128 - BitVec.ofNat 64 (S + 96) = x - 224 - BitVec.ofNat 64 S := by
  have : BitVec.ofNat 64 (S + 96) = BitVec.ofNat 64 S + 96 := by
    apply BitVec.eq_of_toNat_eq; simp
  rw [this]; bv_omega

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- Segment 2: from `L_167` (directive 85) to `L_208` (directive 120): the
BeaconBlockRoot slice (makeslice + memmove of buf[16:48]); rbx holds the new
slice pointer at the end. -/
theorem ad_e2e_root (k : Nat) (hk : AdUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh AdUnmarshal k)
    (rsp0 r140 : UInt64) (rcv bf : BitVec 64) (root : List UInt8) (hroot : root.length = 32)
    (spl rslot lo l68 aP aL aC : List UInt8)
    (hspl : spl.length = 24) (hrs : rslot.length = 8) (hl68 : l68.length = 8)
    (haP : aP.length = 8) (haL : aL.length = 8) (haC : aC.length = 8)
    (R : DataMem → Prop) (S : Nat) (hS : S < 2 ^ 60) (hlo : lo.length = S + 96)
    (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 32 ≤ avail)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := rsp0.toBitVec - 120 })
    (hrbp : s.regs.rbp = { toBitVec := rsp0.toBitVec - 8#64 }) (hr14 : s.regs.r14 = r140)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 rcv.toInt).At (rsp0.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 bf.toInt).At (rsp0.toBitVec + 16))
      ⋆ Eq (spl.At (rsp0.toBitVec - 120)) ⋆ Eq (rslot.At (rsp0.toBitVec - 128))
      ⋆ Eq (lo.At (rsp0.toBitVec - 224 - BitVec.ofNat 64 S)) ⋆ Eq (l68.At (rsp0.toBitVec - 16))
      ⋆ Heap avail
      ⋆ Eq (aP.At (rcv + 24)) ⋆ Eq (aL.At (rcv + 32)) ⋆ Eq (aC.At (rcv + 40))
      ⋆ Eq (root.At (bf + 16))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hms : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 (S + 96)) (hmm : MemmoveC (S + 96)) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 120) ∧ st.data.regs.rsp = { toBitVec := rsp0.toBitVec - 120 }
        ∧ st.data.regs.rbp = { toBitVec := rsp0.toBitVec - 8#64 } ∧ st.data.regs.r14 = r140 ∧
        ∃ (p : BitVec 64) (spl' lo' : List UInt8), spl'.length = 24 ∧ lo'.length = S + 96
          ∧ st.data.regs.rbx.toBitVec = p ∧ st.data.regs.rdx.toBitVec = rcv ∧
        (Eq ((Int.toBytes 8 rcv.toInt).At (rsp0.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 bf.toInt).At (rsp0.toBitVec + 16))
          ⋆ Eq (spl'.At (rsp0.toBitVec - 120))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 107)).toBitVec.toInt).At (rsp0.toBitVec - 128))
          ⋆ Eq (lo'.At (rsp0.toBitVec - 224 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (rsp0.toBitVec - 16))
          ⋆ Heap (avail - 32)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (rcv + 24)) ⋆ Eq ((Int.toBytes 8 32).At (rcv + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (rcv + 40)) ⋆ Eq (root.At p)
          ⋆ Eq (root.At (bf + 16))
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 85)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp hrbp hr14 h_mem ⊢
  subst rsp rbp r14
  kat hk AdUnmarshal 85
  kat hk AdUnmarshal 86
  kat hk AdUnmarshal 87
  intro _
  kat hk AdUnmarshal 88
  kat hk AdUnmarshal 89
  apply store_step_at _ _ (rsp0.toBitVec - 128) _ _ _ rslot _ _ (ada_call _) (by ecancel) (by exact hrs)
  intro m1' H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  rw [ada_call] at *
  refine eventually_trans _ _ _ _ (hms _ (Host.addrOf (k + 89 + 1)) 32 avail lo spl _
    rfl (by simp) (by rfl) (by omega) (by unfold maxAlloc; omega) (by omega) hlo hspl
    (by dsimp only; rw [ada_lo _ _ hS, show rsp0.toBitVec - 128 + 8 = rsp0.toBitVec - 120 by bv_omega]; ecancel)) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrsp3, hr143, hrbp3, stk3, spm3, hstk3, hspm3, Hm3⟩
  dsimp only at hpc3 hrsp3 hr143 hrbp3 Hm3
  subst hpc3
  obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,
    zmms3, flags3, mem3⟩ := d3
  simp only at hrsp3 hr143 hrbp3 Hm3
  rw [ada_ret] at hrsp3
  subst hrsp3 hr143 hrbp3
  rw [ada_lo _ _ hS, show rsp0.toBitVec - 128 + 8 = rsp0.toBitVec - 120 by bv_omega] at Hm3
  simp only [Nat.one_mul] at Hm3
  kat hk AdUnmarshal 90
  apply load_step_at _ _ (rsp0.toBitVec + 8) _ _ (Int.toBytes 8 rcv.toInt) _ _ (by adaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk AdUnmarshal 91
  apply store_step_at _ _ (rcv + 32) _ _ _ aL _ _ (by adaddr) (by ecancel) (by exact haL)
  intro m2' H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk AdUnmarshal 92
  apply store_step_at _ _ (rcv + 40) _ _ _ aC _ _ (by adaddr) (by ecancel) (by exact haC)
  intro m3' H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk AdUnmarshal 93
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk AdUnmarshal 94
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf AdUnmarshal 100
  kat hk AdUnmarshal 100
  kat hk AdUnmarshal 101
  apply store_step_at _ _ (rsp0.toBitVec - 16) _ _ _ l68 _ _ (by adaddr) (by ecancel) (by exact hl68)
  intro m4' H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  kat hk AdUnmarshal 102
  apply store_step_at _ _ (rcv + 24) _ _ _ aP _ _ (by adaddr) (by ecancel) (by exact haP)
  intro m5' H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  kat hk AdUnmarshal 103
  apply load_step_at _ _ (rsp0.toBitVec + 16) _ _ (Int.toBytes 8 bf.toInt) _ _ (by adaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk AdUnmarshal 104
  kat hk AdUnmarshal 105
  kat hk AdUnmarshal 106
  apply store_step_at _ _ (rsp0.toBitVec - 128) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 89 + 1)).toBitVec.toInt) _ _
    (ada_call _) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m6' H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  rw [ada_call] at *
  refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (k + 106 + 1)) root (List.replicate 32 0) stk3 _
    (by rw [hroot]; rfl) (by simp [hroot]) hstk3
    (by dsimp only; rw [ada_lo _ _ hS, show (16 : BitVec 64) + bf = bf + 16 from BitVec.add_comm _ _]; ecancel)) ?_
  rintro ⟨d4, pc4⟩ ⟨hpc4, hrsp4, hr144, hrbp4, stk4, hstk4, Hm4⟩
  dsimp only at hpc4 hrsp4 hr144 hrbp4 Hm4
  subst hpc4
  obtain ⟨⟨rax4, rbx4, rcx4, rdx4, rsi4, rdi4, rsp4, rbp4, r84, r94, r104, r114, r124, r134, r144, r154⟩,
    zmms4, flags4, mem4⟩ := d4
  simp only at hrsp4 hr144 hrbp4 Hm4
  rw [ada_ret] at hrsp4
  subst hrsp4 hr144 hrbp4
  rw [ada_lo _ _ hS, show (16 : BitVec 64) + bf = bf + 16 from BitVec.add_comm _ _] at Hm4
  kat hk AdUnmarshal 107
  apply load_step_at _ _ (rsp0.toBitVec + 8) _ _ (Int.toBytes 8 rcv.toInt) _ _ (by adaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk AdUnmarshal 108
  apply store_step_at _ _ (rcv + 32) _ _ _ (Int.toBytes 8 (BitVec.toInt (0 : BitVec 64))) _ _ (by adaddr)
    (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m7' H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  kat hk AdUnmarshal 109
  apply store_step_at _ _ (rcv + 40) _ _ _ (Int.toBytes 8 (BitVec.toInt (32 : BitVec 64))) _ _ (by adaddr)
    (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m8' H8
  simp only [Width.bytes, Width.bits] at H8
  kunfold
  kat hk AdUnmarshal 110
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk AdUnmarshal 111
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk AdUnmarshal 112
  apply load_step_at _ _ (rsp0.toBitVec - 16) _ _ (Int.toBytes 8 rax3.toBitVec.toInt) _ _ (by adaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk AdUnmarshal 113
  klabel hk hf AdUnmarshal 120
  apply Eventually.done
  simp only [show Int.toBytes 8 (BitVec.toInt (32 : BitVec 64)) = Int.toBytes 8 32 by decide] at H8
  rw [show k + 106 + 1 = k + 107 from rfl] at H8
  exact ⟨rfl, rfl, rfl, rfl, rax3.toBitVec, spm3, stk4, hspm3, hstk4, rfl, rfl, by ecancel⟩

end E2eAd
