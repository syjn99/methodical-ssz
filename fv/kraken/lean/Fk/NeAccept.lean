import Fk.FunSpecs
import Fk.FvAccept

/-!
# Nested.UnmarshalSSZ, accept path (nested containers, C20), on Kraken main

    type Nested struct { A uint64; S *Scalars; L *ListU64 }

Input: A (8 bytes), S's encoding (16), the offset 28 (4), L's encoding
(offset 4 then 8n bytes). The function checks len ≥ 28 and offset = 28, stores
A, allocates S (`runtime.newobject`), calls Scalars.UnmarshalSSZ on buf[8:24]
(specification `ScUAccC`, derived from its machine theorem), allocates L,
calls ListU64.UnmarshalSSZ on buf[28:] (`LuUAccC`, derived from its machine
theorem under the makeslice contract), and returns nil.

Stack: Nested's frame is 0x58 bytes below the saved rbp; every call uses the
return slot at rsp − 104 and the block of 144 + S bytes below it; callees spill
their arguments into the 16 bytes at rsp − 96.
-/

open Fk Fk.Code Fv1
variable [Host]

theorem ne_s120 (x : BitVec 64) : x - 8#64 - 88 + 112 = x + 16 := by bv_omega
theorem dptr28 (y : BitVec 64) (h0 : 0 < y.toNat) (h1 : y.toNat < 2 ^ 63) :
    BitVec.zeroExtend 64 (BitVec.extractLsb' 0 32 (BitVec.sshiftRight (-y) 63) &&& BitVec.truncate 32 (28 : BitVec 64)) = 28 := by
  have hz : (-y).toInt = -(y.toNat : Int) := by
    rw [BitVec.toInt_neg, BitVec.toInt_eq_toNat_of_lt (by omega)]
    apply Int.bmod_eq_of_le <;> omega
  have hs : BitVec.sshiftRight (-y) 63 = BitVec.allOnes 64 := by
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_sshiftRight, hz, BitVec.toInt_allOnes]
    simp [Int.shiftRight_eq_div_pow]
    omega
  rw [hs]; decide

theorem ne_call (x : BitVec 64) : ({ toBitVec := x - 104 } + 8 : UInt64).toBitVec - 8#64 = x - 104 := by
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
theorem ne_m28 (x : BitVec 64) (h : 28 ≤ x.toNat) : (-28 + x).toNat = x.toNat - 28 := by
  rw [BitVec.add_comm, ← BitVec.sub_eq_add_neg, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simpa using h)]; rfl
theorem ne_m28' (x : BitVec 64) (h : 28 ≤ x.toNat) : (x + -28).toNat = x.toNat - 28 := by
  rw [← BitVec.sub_eq_add_neg, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simpa using h)]; rfl
theorem ne_m104 (x : BitVec 64) (h : 104 ≤ x.toNat) : (x - 104).toNat = x.toNat - 104 := by
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simpa using h)]; rfl
theorem ne_pop (x : BitVec 64) : 88 + ({ toBitVec := x - 104 } + 8 : UInt64).toBitVec = x - 8 := by
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
theorem ne_88 (x : BitVec 64) : x - 104 + 16 = x - 88 := by bv_omega
theorem ne_96 (x : BitVec 64) : x - 104 + 8 = x - 96 := by bv_omega
theorem ne_s104 (x : BitVec 64) : x - 96 - 8#64 = x - 104 := by bv_omega
theorem ne_slot (x : BitVec 64) : x - 8#64 - 88 - 8#64 = x - 104 := by bv_omega
theorem ne_blk (x : BitVec 64) (S : Nat) : x - 104 - BitVec.ofNat 64 (144 + S) = x - 104 - 144 - BitVec.ofNat 64 S := by
  rw [show BitVec.ofNat 64 (144 + S) = 144 + BitVec.ofNat 64 S by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]]
  bv_omega

/-- A zeroed Scalars object (24 bytes) as the receiver chunks of Scalars.UnmarshalSSZ and padding. -/
theorem scObj_sep (p : BitVec 64) :
    Eq ((List.replicate 24 (0 : UInt8)).At p) = Eq ([0].At p) ⋆ Eq ([0].At (p + 1)) ⋆ Eq ([0, 0].At (p + 2))
      ⋆ Eq ([0, 0, 0, 0].At (p + 4)) ⋆ Eq ((List.replicate 8 0).At (p + 8)) ⋆ Eq ([0].At (p + 16))
      ⋆ Eq ((List.replicate 7 0).At (p + 17)) := by
  rw [show List.replicate 24 (0 : UInt8) = [0] ++ ([0] ++ ([0, 0] ++ ([0, 0, 0, 0] ++ (List.replicate 8 0 ++ ([0] ++ List.replicate 7 0))))) by rfl]
  rw [at_app _ _ (b := p + 1) (by simp) (by simp), at_app _ _ (b := p + 2) (by simp; bv_omega) (by simp),
    at_app _ _ (b := p + 4) (by simp; bv_omega) (by simp), at_app _ _ (b := p + 8) (by simp; bv_omega) (by simp),
    at_app _ _ (b := p + 16) (by simp; bv_omega) (by simp), at_app _ _ (b := p + 17) (by simp; bv_omega) (by simp)]
  simp only [Std.ExtHashMap.sep_assoc]

/-- A zeroed ListU64 object (24 bytes) as three 8-byte words. -/
theorem luObj_sep (p : BitVec 64) :
    Eq ((List.replicate 24 (0 : UInt8)).At p) = Eq ((List.replicate 8 0).At p) ⋆ Eq ((List.replicate 8 0).At (p + 8))
      ⋆ Eq ((List.replicate 8 0).At (p + 16)) := by
  rw [show List.replicate 24 (0 : UInt8) = List.replicate 8 0 ++ (List.replicate 8 0 ++ List.replicate 8 0) by rfl]
  rw [at_app _ _ (b := p + 8) (by simp) (by simp), at_app _ _ (b := p + 16) (by simp; bv_omega) (by simp)]
  simp only [Std.ExtHashMap.sep_assoc]

theorem spill2 (x : BitVec 64) (l : List UInt8) (h : l.length = 16) :
    Eq (l.At (x - 96)) = Eq ((l.take 8).At (x - 96)) ⋆ Eq ((l.drop 8).At (x - 88)) := by
  conv => lhs; rw [← List.take_append_drop 8 l]
  rw [at_app _ _ (b := x - 88) (by simp [h]; bv_omega) (by simp; omega)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem ne_accept_main (k : Nat) (hk : NestedUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh NestedUnmarshalSSZ k)
    (a8 : List UInt8) (ha8 : a8.length = 8) (sg : Scalars) (lg : ListU64) (hlg : lg.ok)
    (s : MachineData) (ra guard : UInt64)
    (fp x8 x16 x24 x32 l56 l48 rslot cspill blk cA cS cL : List UInt8)
    (hfp : fp.length = 8) (hx8 : x8.length = 8) (hx16 : x16.length = 8) (hx24 : x24.length = 8)
    (hx32 : x32.length = 8) (hl56 : l56.length = 8) (hl48 : l48.length = 8) (hrs : rslot.length = 8)
    (hcs : cspill.length = 16) (S : Nat) (hS : S < 2 ^ 60) (hblk : blk.length = 144 + S)
    (hcA : cA.length = 8) (hcS : cS.length = 8) (hcL : cL.length = 8)
    (R : DataMem → Prop) (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (x8.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (x16.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (x24.At (s.regs.rsp.toBitVec + 24))
      ⋆ Eq (x32.At (s.regs.rsp.toBitVec + 32)) ⋆ Eq (l56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 104))
      ⋆ Eq (cspill.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (blk.At (s.regs.rsp.toBitVec - 104 - 144 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16)) ⋆ Heap avail
      ⋆ Eq (a8.At s.regs.rbx.toBitVec)
      ⋆ Eq ((scField sg 0).At (s.regs.rbx.toBitVec + 8)) ⋆ Eq ((scField sg 1).At (s.regs.rbx.toBitVec + 8 + 1))
      ⋆ Eq ((scField sg 2).At (s.regs.rbx.toBitVec + 8 + 3)) ⋆ Eq ((scField sg 3).At (s.regs.rbx.toBitVec + 8 + 7))
      ⋆ Eq ((scField sg 4).At (s.regs.rbx.toBitVec + 8 + 15))
      ⋆ Eq ([28, 0, 0, 0].At (s.regs.rbx.toBitVec + 24))
      ⋆ Eq ([4, 0, 0, 0].At (s.regs.rbx.toBitVec + 28)) ⋆ Eq ((u64Bytes lg.l).toList.At (s.regs.rbx.toBitVec + 28 + 4))
      ⋆ Eq (cA.At s.regs.rax.toBitVec) ⋆ Eq (cS.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (cL.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat + 112 < s.regs.rsp.toNat) (hsp : 104 + 144 + S ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rcx.toNat = 32 + 8 * lg.l.length) (hcap : s.regs.rcx.toNat ≤ s.regs.rdi.toNat)
    (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hav : 24 + 24 + 8 * 16 ≤ avail)
    (hnoS : NewobjectC Heap (label "type__" + 135104).toBitVec 24 (144 + S))
    (hnoL : NewobjectC Heap (label "type__" + 83104).toBitVec 24 (144 + S))
    (hsc : ScUAccC) (hlu : LuUAccC Heap S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧
        ∃ ps pl p : BitVec 64, (Eq (a8.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 ps.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 pl.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((scField sg 0).At ps) ⋆ Eq ((scField sg 1).At (ps + 2)) ⋆ Eq ((scField sg 2).At (ps + 4))
          ⋆ Eq ((scField sg 3).At (ps + 8)) ⋆ Eq ((scField sg 4).At (ps + 16))
          ⋆ Eq ((Int.toBytes 8 p.toInt).At pl) ⋆ Eq ((Int.toBytes 8 (lg.l.length : Int)).At (pl + 8))
          ⋆ Eq ((Int.toBytes 8 (lg.l.length : Int)).At (pl + 16)) ⋆ Eq ((u64Bytes lg.l).toList.At p)
          ⋆ R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hlen hcap hcap63 ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *
  have hlg' : lg.l.length ≤ 16 := hlg
  kat hk NestedUnmarshalSSZ 0
  kat hk NestedUnmarshalSSZ 1
  kat hk NestedUnmarshalSSZ 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk NestedUnmarshalSSZ 3
  split
  · rename_i h; exfalso
    simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk NestedUnmarshalSSZ 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk NestedUnmarshalSSZ 5
  kat hk NestedUnmarshalSSZ 6
  kat hk NestedUnmarshalSSZ 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ x16 _ _ (ne_s120 _) (by ecancel) (by exact hx16)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk NestedUnmarshalSSZ 8
  kat hk NestedUnmarshalSSZ 9
  kat hk NestedUnmarshalSSZ 10
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
  simp only [Effects.All]
  kat hk NestedUnmarshalSSZ 11
  apply load_step _ _ _ _ [28, 0, 0, 0] _ _ (by ecancel) (by rfl)
  simp only [show Int.ofBytes [28, 0, 0, 0] = 28 by simp [Int.ofBytes]]
  kunfold
  kat hk NestedUnmarshalSSZ 12
  kat hk NestedUnmarshalSSZ 13
  kat hk NestedUnmarshalSSZ 14
  kat hk NestedUnmarshalSSZ 15
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk NestedUnmarshalSSZ 16
  apply store_step_at _ _ (rsp.toBitVec + 8) _ _ _ x8 _ _ (by kaddr) (by ecancel) (by exact hx8)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk NestedUnmarshalSSZ 17
  apply store_step_at _ _ (rsp.toBitVec + 32) _ _ _ x32 _ _ (by kaddr) (by ecancel) (by exact hx32)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  kat hk NestedUnmarshalSSZ 18
  apply store_step_at _ _ (rsp.toBitVec + 24) _ _ _ x24 _ _ (by kaddr) (by ecancel) (by exact hx24)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  kat hk NestedUnmarshalSSZ 19
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  kat hk NestedUnmarshalSSZ 20
  kat hk NestedUnmarshalSSZ 21
  apply store_step_at _ _ (rsp.toBitVec - 56) _ _ _ l56 _ _ (by kaddr) (by ecancel) (by exact hl56)
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  kat hk NestedUnmarshalSSZ 22
  kat hk NestedUnmarshalSSZ 23
  kshl64 63
  kat hk NestedUnmarshalSSZ 24
  intro _
  kat hk NestedUnmarshalSSZ 25
  apply load_step _ _ _ _ a8 _ _ (by ecancel) (by exact ha8)
  kunfold
  kat hk NestedUnmarshalSSZ 26
  generalize hdV : rbx.toBitVec + BitVec.zeroExtend 64
      (BitVec.extractLsb' 0 32 (BitVec.sshiftRight (-(rdi.toBitVec + -28)) 63) &&& BitVec.truncate 32 28) = dV
  generalize hcV : rdi.toBitVec + -28 = cV at *
  kat hk NestedUnmarshalSSZ 27
  apply store_step_at _ _ (rsp.toBitVec - 48) _ _ _ l48 _ _ (by kaddr) (by ecancel) (by exact hl48)
  intro m8 H8
  simp only [Width.bytes, Width.bits] at H8
  kunfold
  kat hk NestedUnmarshalSSZ 28
  apply store_step _ _ _ _ _ cA _ _ (by ecancel) (by exact hcA)
  intro m9 H9
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl a8 ha8] at H9
  kunfold
  kat hk NestedUnmarshalSSZ 29
  kat hk NestedUnmarshalSSZ 30
  apply store_step_at _ _ (rsp.toBitVec - 104) _ _ _ rslot _ _ (ne_slot _) (by ecancel) (by exact hrs)
  intro m10 H10
  simp only [Width.bytes, Width.bits] at H10
  kunfold
  rw [ne_slot] at *
  rw [spill2 _ _ hcs] at H10
  refine eventually_trans _ _ _ _ (hnoS _ (Host.addrOf (k + 30 + 1)) avail blk (cspill.take 8) _ rfl (by omega) hblk
    (by simp [hcs]) (by dsimp only; rw [ne_blk, ne_96]; ecancel)) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hr141, -, stk1, sn1, hstk1, hsn1, Hm1⟩
  dsimp only at hpc1 hrsp1 hr141 Hm1
  subst hpc1
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩,
    zmms1, flags1, mem1⟩ := d1
  simp only at hrsp1 hr141 Hm1
  subst hrsp1 hr141
  rw [ne_blk, scObj_sep, ne_96] at Hm1
  have hrsp1 : ({ toBitVec := rsp.toBitVec - 104 } + 8 : UInt64) = { toBitVec := rsp.toBitVec - 96 } := by
    apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
  simp only [hrsp1]
  kat hk NestedUnmarshalSSZ 31
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk NestedUnmarshalSSZ 32
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk NestedUnmarshalSSZ 33
  apply load_step_at _ _ (rsp.toBitVec + 8) _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk NestedUnmarshalSSZ 34
  klabel hk hf NestedUnmarshalSSZ 41
  kat hk NestedUnmarshalSSZ 41
  kat hk NestedUnmarshalSSZ 42
  apply store_step_at _ _ (rax.toBitVec + 8) _ _ _ cS _ _ (by kaddr) (by ecancel) (by exact hcS)
  intro m11 H11
  simp only [Width.bytes, Width.bits] at H11
  kunfold
  kat hk NestedUnmarshalSSZ 43
  apply load_step_at _ _ (rsp.toBitVec + 16) _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk NestedUnmarshalSSZ 44
  kat hk NestedUnmarshalSSZ 45
  apply load_step_at _ _ (rsp.toBitVec + 32) _ _ (Int.toBytes 8 rdi.toBitVec.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk NestedUnmarshalSSZ 46
  kat hk NestedUnmarshalSSZ 47
  kat hk NestedUnmarshalSSZ 48
  apply store_step_at _ _ (rsp.toBitVec - 104) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 30 + 1)).toBitVec.toInt) _ _
    (ne_s104 _) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m12 H12
  simp only [Width.bytes, Width.bits] at H12
  kunfold
  rw [ne_s104] at *
  refine eventually_trans _ _ _ _ (hsc _ (Host.addrOf (k + 48 + 1)) sg (cspill.drop 8) [0] [0, 0] [0, 0, 0, 0]
    (List.replicate 8 0) [0] _ (by simp; omega) rfl rfl rfl (by simp) rfl (by rfl)
    (by dsimp only; rw [ne_88, BitVec.add_comm 8 rbx.toBitVec]
        simp only [Std.ExtHashMap.sep_emp, Width.bits, Width.bytes] at H12
        generalize scField sg 0 = f0 at H12 ⊢; generalize scField sg 1 = f1 at H12 ⊢
        generalize scField sg 2 = f2 at H12 ⊢; generalize scField sg 3 = f3 at H12 ⊢
        generalize scField sg 4 = f4 at H12 ⊢
        ecancel)) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrax2, hrbx2, hrsp2, hr142, Hm2⟩
  dsimp only at hpc2 hrax2 hrbx2 hrsp2 hr142 Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := d2
  simp only at hrax2 hrbx2 hrsp2 hr142 Hm2
  subst hrax2 hrbx2 hrsp2 hr142
  simp only [hrsp1] at *
  kat hk NestedUnmarshalSSZ 49
  intro _
  kat hk NestedUnmarshalSSZ 50
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf NestedUnmarshalSSZ 78
  kat hk NestedUnmarshalSSZ 78
  kat hk NestedUnmarshalSSZ 79
  kat hk NestedUnmarshalSSZ 80
  kat hk NestedUnmarshalSSZ 81
  apply store_step_at _ _ (rsp.toBitVec - 104) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 48 + 1)).toBitVec.toInt) _ _
    (ne_s104 _) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m13 H13
  simp only [Width.bytes, Width.bits] at H13
  kunfold
  rw [ne_s104] at *
  refine eventually_trans _ _ _ _ (hnoL _ (Host.addrOf (k + 81 + 1)) (avail - 24) stk1 sn1 _ rfl (by omega) hstk1 hsn1
    (by dsimp only; rw [ne_blk, ne_96]; simp only [Std.ExtHashMap.sep_emp, Width.bits, Width.bytes] at H13
        generalize scField sg 0 = f0 at H13 ⊢; generalize scField sg 1 = f1 at H13 ⊢
        generalize scField sg 2 = f2 at H13 ⊢; generalize scField sg 3 = f3 at H13 ⊢
        generalize scField sg 4 = f4 at H13 ⊢
        ecancel)) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrsp3, hr143, -, stk3, sn3, hstk3, hsn3, Hm3⟩
  dsimp only at hpc3 hrsp3 hr143 Hm3
  subst hpc3
  obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,
    zmms3, flags3, mem3⟩ := d3
  simp only at hrsp3 hr143 Hm3
  subst hrsp3 hr143
  rw [ne_blk, luObj_sep, ne_96] at Hm3
  try simp only [hrsp1]
  kat hk NestedUnmarshalSSZ 82
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk NestedUnmarshalSSZ 83
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk NestedUnmarshalSSZ 84
  apply load_step_at _ _ (rsp.toBitVec + 8) _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk NestedUnmarshalSSZ 85
  klabel hk hf NestedUnmarshalSSZ 93
  kat hk NestedUnmarshalSSZ 93
  kat hk NestedUnmarshalSSZ 94
  apply store_step_at _ _ (rax.toBitVec + 16) _ _ _ cL _ _ (by kaddr) (by ecancel) (by exact hcL)
  intro m14 H14
  simp only [Width.bytes, Width.bits] at H14
  kunfold
  kat hk NestedUnmarshalSSZ 95
  apply load_step_at _ _ (rsp.toBitVec + 24) _ _ (Int.toBytes 8 rcx.toBitVec.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk NestedUnmarshalSSZ 96
  kat hk NestedUnmarshalSSZ 97
  apply load_step_at _ _ (rsp.toBitVec - 48) _ _ (Int.toBytes 8 dV.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk NestedUnmarshalSSZ 98
  apply load_step_at _ _ (rsp.toBitVec - 56) _ _ (Int.toBytes 8 cV.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk NestedUnmarshalSSZ 99
  apply store_step_at _ _ (rsp.toBitVec - 104) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 81 + 1)).toBitVec.toInt) _ _
    (ne_call _) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m15 H15
  simp only [Width.bytes, Width.bits] at H15
  kunfold
  rw [ne_call] at *
  have hcVn : cV.toNat = rdi.toNat - 28 := by
    rw [← hcV, ne_m28' _ (by simp; omega)]; simp
  rw [dptr28 cV (by omega) (by omega)] at hdV
  subst hdV
  simp only [Std.ExtHashMap.sep_emp, Width.bits, Width.bytes] at H15
  generalize scField sg 0 = f0 at H15; generalize scField sg 1 = f1 at H15
  generalize scField sg 2 = f2 at H15; generalize scField sg 3 = f3 at H15; generalize scField sg 4 = f4 at H15
  generalize hr8 : (8 : BitVec 64) + rbx.toBitVec = r8b at H15
  refine eventually_trans _ _ _ _ (hlu _ (Host.addrOf (k + 99 + 1)) lg stk3
    sn3 (Int.toBytes 8 r8b.toInt) (List.replicate 8 0) (List.replicate 8 0)
    (List.replicate 8 0) guard (avail - 24 - 24) _ hlg hstk3 hsn3 (Int.toBytes_length 8 _) (by simp) (by simp) (by simp)
    (by show (-28 + rcx.toBitVec).toNat = _; rw [ne_m28 _ (by simp; omega)]; simp; omega)
    (by show (-28 + rcx.toBitVec).toNat ≤ cV.toNat; rw [ne_m28 _ (by simp; omega), hcVn]; simp; omega)
    (by show cV.toNat < 2 ^ 63; rw [hcVn]; omega)
    (by show guard.toNat < (rsp.toBitVec - 104).toNat - 8; rw [ne_m104 _ (by simp; omega)]; simp; omega)
    (by show 8 ≤ (rsp.toBitVec - 104).toNat; rw [ne_m104 _ (by simp; omega)]; simp; omega) (by omega)
    (by dsimp only; rw [ne_96]; ecancel)) ?_
  rintro ⟨d4, pc4⟩ ⟨hpc4, hrax4, hrbx4, hrsp4, hr144, pL, stk4, sp14, sp24, hstk4, hsp14, hsp24, Hm4⟩
  dsimp only at hpc4 hrax4 hrbx4 hrsp4 hr144 Hm4
  subst hpc4
  obtain ⟨⟨rax4, rbx4, rcx4, rdx4, rsi4, rdi4, rsp4, rbp4, r84, r94, r104, r114, r124, r134, r144, r154⟩,
    zmms4, flags4, mem4⟩ := d4
  simp only at hrax4 hrbx4 hrsp4 hr144 Hm4
  subst hrax4 hrbx4 hrsp4 hr144
  try simp only [Std.ExtHashMap.sep_emp, Width.bits, Width.bytes] at Hm4
  generalize scField sg 0 = f0 at Hm4; generalize scField sg 1 = f1 at Hm4
  generalize scField sg 2 = f2 at Hm4; generalize scField sg 3 = f3 at Hm4; generalize scField sg 4 = f4 at Hm4
  kat hk NestedUnmarshalSSZ 100
  intro _
  kat hk NestedUnmarshalSSZ 101
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf NestedUnmarshalSSZ 129
  kat hk NestedUnmarshalSSZ 129
  kat hk NestedUnmarshalSSZ 130
  kat hk NestedUnmarshalSSZ 131
  rw [ne_pop]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk NestedUnmarshalSSZ 132
  rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨trivial, ?_, ?_, rax1.toBitVec, rax3.toBitVec, pL, ?_⟩
  · first | trivial | rfl | (apply UInt64.toBitVec_inj.mp; simp)
  · first | trivial | rfl | (apply UInt64.toBitVec_inj.mp; simp)
  · try simp only [Std.ExtHashMap.sep_emp, Width.bits, Width.bytes] at Hm4
    generalize scField sg 0 = f0 at Hm4 ⊢; generalize scField sg 1 = f1 at Hm4 ⊢
    generalize scField sg 2 = f2 at Hm4 ⊢; generalize scField sg 3 = f3 at Hm4 ⊢
    generalize scField sg 4 = f4 at Hm4 ⊢
    generalize (u64Bytes lg.l).toList = ub at Hm4 ⊢
    exact sep_true (by ecancel)
