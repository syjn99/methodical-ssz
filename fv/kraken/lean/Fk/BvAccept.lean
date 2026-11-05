import Fk.FvAccept

/-!
# BitVec.UnmarshalSSZ (Bitvector[4]), on Kraken main

`bv_accept_main`: if `len(buf) = 1`, for **every** byte `b` (padding bits
included) the function allocates J with `runtime.makeslice(byte, 0, 1)`, sets
J = (p, 1, 1) with `b` at p, and returns nil. There is no padding-bit check.
`bv_reject_size_main`: `len(buf) ≠ 1` → `ssz.ErrSize`.

Receiver layout: J @0 (ptr), @8 (len), @16 (cap). Frame of 0x18 bytes, as
FixedVec.UnmarshalSSZ (same stack lemmas).
-/

open Fk Fk.Code
variable [Host]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem bv_accept_main (k : Nat) (hk : BitVecUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh BitVecUnmarshalSSZ k)
    (b : UInt8) (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 rslot cP cL cC : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (hrs : rslot.length = 8)
    (hcP : cP.length = 8) (hcL : cL.length = 8) (hcC : cC.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 40 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq ([b].At s.regs.rbx.toBitVec)
      ⋆ Eq (cP.At s.regs.rax.toBitVec) ⋆ Eq (cL.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 40 ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rcx = 1) (hav : 1 * 1 ≤ avail)
    (hms : MakesliceC Heap (label "type__" + 48736).toBitVec 1 S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧
        ∃ p : BitVec 64, (Eq ((Int.toBytes 8 p.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 1).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 1).At (s.regs.rax.toBitVec + 16)) ⋆ Eq ([b].At p)
          ⋆ Eq ([b].At s.regs.rbx.toBitVec) ⋆ Heap (avail - 1 * 1) ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hlen ⊢
  subst hlen
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; simp only [UInt64.size] at *
  kat hk BitVecUnmarshalSSZ 0
  kat hk BitVecUnmarshalSSZ 1
  kat hk BitVecUnmarshalSSZ 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitVecUnmarshalSSZ 3
  split
  · rename_i h; exfalso
    simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk BitVecUnmarshalSSZ 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk BitVecUnmarshalSSZ 5
  kat hk BitVecUnmarshalSSZ 6
  kat hk BitVecUnmarshalSSZ 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by bv_omega) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk BitVecUnmarshalSSZ 8
  kat hk BitVecUnmarshalSSZ 9
  kat hk BitVecUnmarshalSSZ 10
  split
  case isTrue h => exact absurd h (by decide)
  simp only [Effects.All]
  kat hk BitVecUnmarshalSSZ 11
  apply store_step_at _ _ (rsp.toBitVec + 8) _ _ _ s1 _ _ (by bv_omega) (by ecancel) (by exact h1)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk BitVecUnmarshalSSZ 12
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by bv_omega) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  kat hk BitVecUnmarshalSSZ 13
  kat hk BitVecUnmarshalSSZ 14
  intro _
  kat hk BitVecUnmarshalSSZ 15
  kat hk BitVecUnmarshalSSZ 16
  apply store_step_at _ _ (rsp.toBitVec - 40) _ _ _ rslot _ _ (slot40 _) (by ecancel) (by exact hrs)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  rw [slot40] at *
  refine eventually_trans _ _ _ _ (hms _ (Host.addrOf (k + 16 + 1)) 1 avail scratch _ rfl
    (by show (BitVec.zeroExtend 64 (BitVec.extractLsb' 0 32 rbx.toBitVec ^^^ BitVec.extractLsb' 0 32 rbx.toBitVec)).toNat ≤ 1; simp)
    (by rfl) hav hsc (by ecancel)) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrsp2, stk2, hstk2, Hm2⟩
  dsimp only at hpc2 hrsp2 Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := d2
  simp only at hrsp2 Hm2
  subst hrsp2
  kat hk BitVecUnmarshalSSZ 17
  apply load_step_at _ _ (rsp.toBitVec + 8) _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitVecUnmarshalSSZ 18
  apply store_step_at _ _ (rax.toBitVec + 8) _ _ _ cL _ _ (by kaddr) (by ecancel) (by exact hcL)
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  kat hk BitVecUnmarshalSSZ 19
  apply store_step_at _ _ (rax.toBitVec + 16) _ _ _ cC _ _ (by kaddr) (by ecancel) (by exact hcC)
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  kat hk BitVecUnmarshalSSZ 20
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk BitVecUnmarshalSSZ 21
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf BitVecUnmarshalSSZ 26
  kat hk BitVecUnmarshalSSZ 26
  kat hk BitVecUnmarshalSSZ 27
  apply store_step _ _ _ _ _ cP _ _ (by ecancel) (by exact hcP)
  intro m8 H8
  simp only [Width.bytes, Width.bits] at H8
  kunfold
  kat hk BitVecUnmarshalSSZ 28
  apply load_step_at _ _ (rsp.toBitVec + 16) _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitVecUnmarshalSSZ 29
  apply load_step _ _ _ _ [b] _ _ (by ecancel) (by rfl)
  kunfold
  kat hk BitVecUnmarshalSSZ 30
  apply store_step _ _ _ _ _ (List.replicate (1 * 1) 0) _ _ (by ecancel) (by rfl)
  intro m9 H9
  simp only [Width.bytes, Width.bits, zx8, toBytes_ofInt_ofBytes 8 1 rfl [b] rfl] at H9
  kunfold
  kat hk BitVecUnmarshalSSZ 31
  apply store_step_at _ _ (rax.toBitVec + 8) _ _ _ (Int.toBytes 8 (BitVec.toInt (0 : BitVec 64))) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m10 H10
  simp only [Width.bytes, Width.bits] at H10
  kunfold
  kat hk BitVecUnmarshalSSZ 32
  apply store_step_at _ _ (rax.toBitVec + 16) _ _ _ (Int.toBytes 8 (BitVec.toInt (1 : BitVec 64))) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m11 H11
  simp only [Width.bytes, Width.bits] at H11
  kunfold
  kat hk BitVecUnmarshalSSZ 33
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk BitVecUnmarshalSSZ 34
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf BitVecUnmarshalSSZ 40
  kat hk BitVecUnmarshalSSZ 40
  kat hk BitVecUnmarshalSSZ 41
  apply store_step _ _ _ _ _ (Int.toBytes 8 rax2.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m12 H12
  simp only [Width.bytes, Width.bits] at H12
  kunfold
  kat hk BitVecUnmarshalSSZ 42
  intro _
  kat hk BitVecUnmarshalSSZ 43
  intro _
  kat hk BitVecUnmarshalSSZ 44
  kat hk BitVecUnmarshalSSZ 45
  rw [slot8]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitVecUnmarshalSSZ 46
  rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Fk.ofInt_ofBytes_toBytes64] at *
  simp only [show Int.toBytes 8 (BitVec.toInt (1 : BitVec 64)) = Int.toBytes 8 1 by decide] at H12
  refine ⟨trivial, ?_, ?_, ?_, ?_, rax2.toBitVec, ?_⟩
  all_goals first
    | trivial | rfl
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (apply UInt64.toBitVec_inj.mp; simp; bv_omega)
    | exact sep_true (by ecancel)
