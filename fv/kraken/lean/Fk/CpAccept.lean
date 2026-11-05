import Fk.FvAccept
import Fk.Bytes

/-!
# Prysm Checkpoint.UnmarshalSSZ, accept path, on Kraken main

    type Checkpoint struct { Epoch Epoch; Root []byte `ssz-size:"32"` }

Input `buf` of 40 bytes: `e8` (Epoch, 8 LE bytes) then `root` (32). The code
checks len = 40, copies Epoch, allocates Root with `runtime.makeslice(byte,
0, 32)` (contract `MakesliceC`), writes the header (p, 0, 32), copies the 32
bytes with `runtime.memmove` (contract `MemmoveC`), sets len = 32 and returns
nil (`append(c.Root[:0], buf[8:40]...)` without growslice: the capacity is 32).
Receiver layout (this module's struct, no protobuf fields): Epoch @0, Root
@8 (ptr), @16 (len), @24 (cap).
Premises the Go caller provides: separated receiver, input and stack chunks,
the stack guard below rsp − 40, the write barrier off, heap room for 32 bytes,
the two runtime contracts.
-/

open Fk Fk.Code
variable [Host]

theorem cp_slot (x : BitVec 64) : x - 8#64 - 32 - 8#64 = x - 48 := by bv_omega
theorem cp_slot' (x : BitVec 64) : ({ toBitVec := x - 48 } + 8 : UInt64).toBitVec - 8#64 = x - 48 := by
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
theorem cp_pop (x : BitVec 64) : 32 + ({ toBitVec := x - 48 } + 8 : UInt64).toBitVec = x - 8 := by
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem cp_accept_main (k : Nat) (hk : PrysmCheckpointUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh PrysmCheckpointUnmarshalSSZ k)
    (e8 root : List UInt8) (he8 : e8.length = 8) (hroot : root.length = 32)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 l16 rslot c0 cP cL cC : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (hl16 : l16.length = 8) (hrs : rslot.length = 8)
    (hc0 : c0.length = 8) (hcP : cP.length = 8) (hcL : cL.length = 8) (hcC : cC.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch spm : List UInt8) (hsc : scratch.length = S) (hspm : spm.length = 24)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 48 - BitVec.ofNat 64 S))
      ⋆ Eq (spm.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (e8.At s.regs.rbx.toBitVec) ⋆ Eq (root.At (s.regs.rbx.toBitVec + 8))
      ⋆ Eq (c0.At s.regs.rax.toBitVec) ⋆ Eq (cP.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (cL.At (s.regs.rax.toBitVec + 16)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 48 ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rcx = 40)
    (hav : 32 ≤ avail)
    (hms : MakesliceC Heap (label "type__" + 48736).toBitVec 1 S)
    (hmm : MemmoveC S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ p : BitVec 64, (Eq (e8.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (root.At p)
          ⋆ Eq (e8.At s.regs.rbx.toBitVec) ⋆ Eq (root.At (s.regs.rbx.toBitVec + 8))
          ⋆ Heap (avail - 32) ⋆ R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hlen ⊢
  subst hlen
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; simp only [UInt64.size] at *
  kat hk PrysmCheckpointUnmarshalSSZ 0
  kat hk PrysmCheckpointUnmarshalSSZ 1
  kat hk PrysmCheckpointUnmarshalSSZ 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmCheckpointUnmarshalSSZ 3
  split
  · rename_i h; exfalso
    simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk PrysmCheckpointUnmarshalSSZ 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk PrysmCheckpointUnmarshalSSZ 5
  kat hk PrysmCheckpointUnmarshalSSZ 6
  kat hk PrysmCheckpointUnmarshalSSZ 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by bv_omega) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk PrysmCheckpointUnmarshalSSZ 8
  kat hk PrysmCheckpointUnmarshalSSZ 9
  kat hk PrysmCheckpointUnmarshalSSZ 10
  split
  case isTrue h => exact absurd h (by decide)
  simp only [Effects.All]
  kat hk PrysmCheckpointUnmarshalSSZ 11
  apply store_step_at _ _ (rsp.toBitVec + 8) _ _ _ s1 _ _ (by bv_omega) (by ecancel) (by exact h1)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk PrysmCheckpointUnmarshalSSZ 12
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by bv_omega) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  kat hk PrysmCheckpointUnmarshalSSZ 13
  apply load_step _ _ _ _ e8 _ _ (by ecancel) (by exact he8)
  kunfold
  kat hk PrysmCheckpointUnmarshalSSZ 14
  apply store_step_at _ _ rax.toBitVec _ _ _ c0 _ _ (by bv_omega) (by ecancel) (by exact hc0)
  intro m5 H5
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl e8 he8] at H5
  kunfold
  kat hk PrysmCheckpointUnmarshalSSZ 15
  kat hk PrysmCheckpointUnmarshalSSZ 16
  intro _
  kat hk PrysmCheckpointUnmarshalSSZ 17
  kat hk PrysmCheckpointUnmarshalSSZ 18
  apply store_step_at _ _ (rsp.toBitVec - 48) _ _ _ rslot _ _ (cp_slot _) (by ecancel) (by exact hrs)
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  rw [cp_slot] at *
  refine eventually_trans _ _ _ _ (hms _ (Host.addrOf (k + 18 + 1)) 32 avail scratch spm _ rfl (by simp) (by rfl) (by omega) (by unfold maxAlloc; omega)
    (by omega) hsc hspm (by dsimp only; rw [show rsp.toBitVec - 48 + 8 = rsp.toBitVec - 40 by bv_omega]; ecancel)) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrsp2, hr14c2, -, stk2, spm2, hstk2, hspm2, Hm2⟩
  dsimp only at hpc2 hrsp2 Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := d2
  simp only at hrsp2 hr14c2 Hm2
  subst hrsp2 hr14c2
  kat hk PrysmCheckpointUnmarshalSSZ 19
  apply load_step_at _ _ (rsp.toBitVec + 8) _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmCheckpointUnmarshalSSZ 20
  apply store_step_at _ _ (rax.toBitVec + 16) _ _ _ cL _ _ (by kaddr) (by ecancel) (by exact hcL)
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  kat hk PrysmCheckpointUnmarshalSSZ 21
  apply store_step_at _ _ (rax.toBitVec + 24) _ _ _ cC _ _ (by kaddr) (by ecancel) (by exact hcC)
  intro m8 H8
  simp only [Width.bytes, Width.bits] at H8
  kunfold
  kat hk PrysmCheckpointUnmarshalSSZ 22
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk PrysmCheckpointUnmarshalSSZ 23
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf PrysmCheckpointUnmarshalSSZ 28
  kat hk PrysmCheckpointUnmarshalSSZ 28
  kat hk PrysmCheckpointUnmarshalSSZ 29
  apply store_step_at _ _ (rsp.toBitVec - 16) _ _ _ l16 _ _ (by kaddr) (by ecancel) (by exact hl16)
  intro m9 H9
  simp only [Width.bytes, Width.bits] at H9
  kunfold
  kat hk PrysmCheckpointUnmarshalSSZ 30
  apply store_step_at _ _ (rax.toBitVec + 8) _ _ _ cP _ _ (by kaddr) (by ecancel) (by exact hcP)
  intro m10 H10
  simp only [Width.bytes, Width.bits] at H10
  kunfold
  kat hk PrysmCheckpointUnmarshalSSZ 31
  apply load_step_at _ _ (rsp.toBitVec + 16) _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmCheckpointUnmarshalSSZ 32
  kat hk PrysmCheckpointUnmarshalSSZ 33
  kat hk PrysmCheckpointUnmarshalSSZ 34
  apply store_step_at _ _ (rsp.toBitVec - 48) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 18 + 1)).toBitVec.toInt) _ _
    (cp_slot' _) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m11 H11
  simp only [Width.bytes, Width.bits] at H11
  kunfold
  rw [cp_slot'] at *
  refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (k + 34 + 1)) root (List.replicate (1 * 32) 0) stk2 _
    (by rw [hroot]; rfl) (by simp [hroot]) hstk2
    (by dsimp only; rw [show (8 : BitVec 64) + rbx.toBitVec = rbx.toBitVec + 8 from BitVec.add_comm _ _]; ecancel)) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrsp3, _hmr143, _hmrbp3, stk3, hstk3, Hm3⟩
  dsimp only at hpc3 hrsp3 Hm3
  subst hpc3
  obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,
    zmms3, flags3, mem3⟩ := d3
  simp only at hrsp3 _hmr143 Hm3
  subst hrsp3 _hmr143
  kat hk PrysmCheckpointUnmarshalSSZ 35
  apply load_step_at _ _ (rsp.toBitVec + 8) _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmCheckpointUnmarshalSSZ 36
  apply store_step_at _ _ (rax.toBitVec + 16) _ _ _ (Int.toBytes 8 (BitVec.toInt (0 : BitVec 64))) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m12 H12
  simp only [Width.bytes, Width.bits] at H12
  kunfold
  kat hk PrysmCheckpointUnmarshalSSZ 37
  apply store_step_at _ _ (rax.toBitVec + 24) _ _ _ (Int.toBytes 8 (BitVec.toInt (32 : BitVec 64))) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m13 H13
  simp only [Width.bytes, Width.bits] at H13
  kunfold
  kat hk PrysmCheckpointUnmarshalSSZ 38
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk PrysmCheckpointUnmarshalSSZ 39
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk PrysmCheckpointUnmarshalSSZ 40
  apply load_step_at _ _ (rsp.toBitVec - 16) _ _ (Int.toBytes 8 rax2.toBitVec.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmCheckpointUnmarshalSSZ 41
  klabel hk hf PrysmCheckpointUnmarshalSSZ 48
  kat hk PrysmCheckpointUnmarshalSSZ 48
  kat hk PrysmCheckpointUnmarshalSSZ 49
  apply store_step_at _ _ (rax.toBitVec + 8) _ _ _ (Int.toBytes 8 rax2.toBitVec.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m14 H14
  simp only [Width.bytes, Width.bits] at H14
  kunfold
  kat hk PrysmCheckpointUnmarshalSSZ 50
  intro _
  kat hk PrysmCheckpointUnmarshalSSZ 51
  intro _
  kat hk PrysmCheckpointUnmarshalSSZ 52
  kat hk PrysmCheckpointUnmarshalSSZ 53
  rw [cp_pop]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmCheckpointUnmarshalSSZ 54
  rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  rw [show (8 : BitVec 64) + rbx.toBitVec = rbx.toBitVec + 8 from BitVec.add_comm _ _] at H14
  simp only [show Int.toBytes 8 (BitVec.toInt (32 : BitVec 64)) = Int.toBytes 8 32 by decide, Nat.one_mul] at H14
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, rax2.toBitVec, ?_⟩
  all_goals first
    | trivial | rfl
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (apply UInt64.toBitVec_inj.mp; simp; bv_omega)
    | exact sep_true (by ecancel)
