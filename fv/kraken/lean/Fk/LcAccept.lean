import Fk.LcLoop

/-!
# ListC.UnmarshalSSZ (List[ListU64, 4]), accept path, on Kraken main

`lc_accept_main`: input `buf = offset 4 ‖ tl` with n ≥ 1 elements (an empty
list takes another path, not proved here): the code checks the container
offset, the first element offset (4n: non-zero, multiple of 4, n ≤ 4, within
-/

open Fk Fk.Code Fv1 EthLib.Serialization.Ssz
variable [Host]

theorem lca_m4 (y : BitVec 64) (h : 4 ≤ y.toNat) : y + -4 = BitVec.ofNat 64 (y.toNat - 4) := by
  rw [← BitVec.sub_eq_add_neg]; apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simpa using h)]; simp; omega
theorem lca_m4' (y : BitVec 64) (h : 4 ≤ y.toNat) : -4 + y = BitVec.ofNat 64 (y.toNat - 4) := by
  rw [BitVec.add_comm]; exact lca_m4 y h

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
theorem lc_accept_main (k : Nat) (hk : ListCUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListCUnmarshalSSZ k)
    (tl : List UInt8) (T : Nat) (gs : List ListU64) (hgs : ∀ g ∈ gs, g.ok)
    (hT : tl.length = T) (hn1 : 1 ≤ gs.length) (hn : gs.length ≤ 4) (hT32 : T < 2 ^ 32)
    (hend : lcStart gs gs.length = T)
    (hfirst : tl.take 4 = (uintBytes 4 (4 * gs.length)).toList)
    (hparts : ∀ i (hi : i < gs.length), (tl.drop (lcStart gs i)).take (4 + 8 * gs[i].l.length)
      = [4, 0, 0, 0] ++ (u64Bytes gs[i].l).toList)
    (hnexts : ∀ i, i + 1 < gs.length → (tl.drop (4 * (i + 1))).take 4 = (uintBytes 4 (lcStart gs (i + 1))).toList)
    (s : MachineData) (ra guard : UInt64) (fp slot s8 s32 l128 l136 l144 l152 l160 l168 l176 l184 l208 l216 l224 rslot blk
      cP cL cC : List UInt8)
    (hfp : fp.length = 8) (hsl : slot.length = 8) (h8 : s8.length = 8) (h32 : s32.length = 8)
    (hl128 : l128.length = 8) (hl136 : l136.length = 8) (hl144 : l144.length = 8) (hl152 : l152.length = 8)
    (hl160 : l160.length = 8) (hl168 : l168.length = 8) (hl176 : l176.length = 8) (hl184 : l184.length = 8)
    (hl208 : l208.length = 8) (hl216 : l216.length = 8) (hl224 : l224.length = 8) (hrs : rslot.length = 8)
    (hcP : cP.length = 8) (hcL : cL.length = 8) (hcC : cC.length = 8)
    (S : Nat) (hS : S < 2 ^ 60) (hblk : blk.length = 144 + S)
    (R : DataMem → Prop) (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 8 * 4 + 152 * 4 ≤ avail)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s8.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s32.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq (l128.At (s.regs.rsp.toBitVec - 128)) ⋆ Eq (l136.At (s.regs.rsp.toBitVec - 136))
      ⋆ Eq (l144.At (s.regs.rsp.toBitVec - 144)) ⋆ Eq (l152.At (s.regs.rsp.toBitVec - 152))
      ⋆ Eq (l160.At (s.regs.rsp.toBitVec - 160)) ⋆ Eq (l168.At (s.regs.rsp.toBitVec - 168))
      ⋆ Eq (l176.At (s.regs.rsp.toBitVec - 176)) ⋆ Eq (l184.At (s.regs.rsp.toBitVec - 184))
      ⋆ Eq (l224.At (s.regs.rsp.toBitVec - 224)) ⋆ Eq (l216.At (s.regs.rsp.toBitVec - 216))
      ⋆ Eq (l208.At (s.regs.rsp.toBitVec - 208))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 232)) ⋆ Eq (blk.At (s.regs.rsp.toBitVec - 232 - 144 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16)) ⋆ Heap avail
      ⋆ Eq ([4, 0, 0, 0].At s.regs.rbx.toBitVec) ⋆ Eq ((tl.take 4).At (s.regs.rbx.toBitVec + 4))
      ⋆ Eq ((tl.drop 4).At (s.regs.rbx.toBitVec + 4 + 4))
      ⋆ Eq (cP.At s.regs.rax.toBitVec) ⋆ Eq (cL.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat + 400 + S < s.regs.rsp.toNat) (hsp : 400 + S ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rcx.toNat = 4 + T) (hcap : s.regs.rcx.toNat ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hms : MakesliceC Heap (label "type__" + 114368).toBitVec 8 (144 + S))
    (hno : NewobjectC Heap (label "type__" + 83104).toBitVec 24 (144 + S)) (hlu : LuUAccC Heap S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧
        ∃ (A : BitVec 64) (acc : List (BitVec 64 × BitVec 64 × ListU64)) (avail' : Nat),
          acc.reverse.map (fun t : BitVec 64 × BitVec 64 × ListU64 => t.2.2) = gs ∧
          (Eq ((Int.toBytes 8 A.toInt).At s.regs.rax.toBitVec)
            ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 gs.length).toInt).At (s.regs.rax.toBitVec + 8))
            ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 gs.length).toInt).At (s.regs.rax.toBitVec + 16))
            ⋆ Eq ((ptrBytes (acc.reverse.map (fun t : BitVec 64 × BitVec 64 × ListU64 => t.1))).At A)
            ⋆ lcObjs acc ⋆ Eq (tl.At (s.regs.rbx.toBitVec + 4)) ⋆ Heap avail'
            ⋆ Eq ([4, 0, 0, 0].At s.regs.rbx.toBitVec) ⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
            ⋆ R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  have hT4 : 4 ≤ T := by have := congrArg List.length hfirst; simp [Fv.uintBytes_size] at this; omega
  have ho4 : (tl.take 4).length = 4 := by simp; omega
  have hoff : Int.ofBytes (tl.take 4) = ((4 * gs.length : Nat) : Int) := by
    rw [hfirst, ofBytes_uintBytes4 _ (by omega)]
  have hle4n : 4 * gs.length ≤ T := by
    have := lcStart_le gs 0; rw [hend] at this; simp [lcStart] at this; omega
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hlen hcap hcap63 ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *
  kat hk ListCUnmarshalSSZ 0
  kat hk ListCUnmarshalSSZ 1
  kat hk ListCUnmarshalSSZ 2
  kat hk ListCUnmarshalSSZ 3
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListCUnmarshalSSZ 4
  split
  case isTrue h =>
    exfalso
    rw [cmp_be_false _ _ _ _ (by rw [toNat_add_neg96 _ (by simp; omega)]; simp; omega)] at h
    exact absurd h (by simp)
  simp only [Effects.All]
  kat hk ListCUnmarshalSSZ 5
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk ListCUnmarshalSSZ 6
  kat hk ListCUnmarshalSSZ 7
  kat hk ListCUnmarshalSSZ 8
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ slot _ _ (lc_s16 _) (by ecancel) (by exact hsl)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk ListCUnmarshalSSZ 9
  kat hk ListCUnmarshalSSZ 10
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
  simp only [Effects.All]
  kat hk ListCUnmarshalSSZ 11
  apply load_step_at _ _ rbx.toBitVec _ _ [4, 0, 0, 0] _ _ (by bv_omega) (by ecancel) (by simp)
  simp only [show Int.ofBytes [4, 0, 0, 0] = 4 by simp [Int.ofBytes]]
  kunfold
  kat hk ListCUnmarshalSSZ 12
  kat hk ListCUnmarshalSSZ 13
  kat hk ListCUnmarshalSSZ 14
  kat hk ListCUnmarshalSSZ 15
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk ListCUnmarshalSSZ 16
  kat hk ListCUnmarshalSSZ 17
  kat hk ListCUnmarshalSSZ 18
  kat hk ListCUnmarshalSSZ 19
  kshl64 63
  kat hk ListCUnmarshalSSZ 20
  intro _
  rw [lc_rdx4 _ (by simp; omega) (by simp; omega)]
  kat hk ListCUnmarshalSSZ 21
  kat hk ListCUnmarshalSSZ 22
  kat hk ListCUnmarshalSSZ 23
  kat hk ListCUnmarshalSSZ 24
  kat hk ListCUnmarshalSSZ 25
  kat hk ListCUnmarshalSSZ 26
  kat hk ListCUnmarshalSSZ 27
  rw [jle3_false _ _ (by rw [BitVec.add_comm, ← BitVec.sub_eq_add_neg, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp; omega)
    (by rw [BitVec.add_comm, ← BitVec.sub_eq_add_neg, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp; omega)]
  simp only [Bool.false_eq_true, ↓reduceIte, Effects.All]
  kat hk ListCUnmarshalSSZ 28
  apply load_step_at _ _ (rbx.toBitVec + 4) _ _ (tl.take 4) _ _ (by bv_omega) (by ecancel) (by exact ho4)
  rw [hoff]
  kunfold
  kat hk ListCUnmarshalSSZ 29
  kat hk ListCUnmarshalSSZ 30
  kat hk ListCUnmarshalSSZ 31
  intro _
  have ho32 : 4 * gs.length < 2 ^ 32 := by
    omega
  rw [zx_o (4 * gs.length) ho32]
  kat hk ListCUnmarshalSSZ 32
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    have := congrArg BitVec.toNat h; simp at this; omega
  simp only [Effects.All]
  kat hk ListCUnmarshalSSZ 33
  kat hk ListCUnmarshalSSZ 34
  intro _
  rw [and3_zero (4 * gs.length) ho32 (by omega)]
  kat hk ListCUnmarshalSSZ 35
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk ListCUnmarshalSSZ 36
  kat hk ListCUnmarshalSSZ 37
  kshl64 2
  rw [shr2_o (4 * gs.length) ho32]
  kat hk ListCUnmarshalSSZ 38
  kat hk ListCUnmarshalSSZ 39
  rw [ja4_false _ (by omega)]
  simp only [Bool.false_eq_true, ↓reduceIte, Effects.All]
  kat hk ListCUnmarshalSSZ 40
  kat hk ListCUnmarshalSSZ 41
  kat hk ListCUnmarshalSSZ 42
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf ListCUnmarshalSSZ 64
  kat hk ListCUnmarshalSSZ 64
  kat hk ListCUnmarshalSSZ 65
  rw [show rsp.toBitVec - 8#64 - 216 + 232 = rsp.toBitVec + 8 by bv_omega]
  apply store_step _ _ _ _ _ s8 _ _ (by ecancel) (by exact h8)
  intro n1 N1
  simp only [Width.bytes, Width.bits] at N1
  kunfold
  kat hk ListCUnmarshalSSZ 66
  rw [show rsp.toBitVec - 8#64 - 216 + 48 = rsp.toBitVec - 176 by bv_omega]
  apply store_step _ _ _ _ _ l176 _ _ (by ecancel) (by exact hl176)
  intro n2 N2
  simp only [Width.bytes, Width.bits] at N2
  kunfold
  kat hk ListCUnmarshalSSZ 67
  rw [show rsp.toBitVec - 8#64 - 216 + 80 = rsp.toBitVec - 144 by bv_omega]
  apply store_step _ _ _ _ _ l144 _ _ (by ecancel) (by exact hl144)
  intro n3 N3
  simp only [Width.bytes, Width.bits] at N3
  kunfold
  kat hk ListCUnmarshalSSZ 68
  rw [show rsp.toBitVec - 8#64 - 216 + 96 = rsp.toBitVec - 128 by bv_omega]
  apply store_step _ _ _ _ _ l128 _ _ (by ecancel) (by exact hl128)
  intro n4 N4
  simp only [Width.bytes, Width.bits] at N4
  kunfold
  kat hk ListCUnmarshalSSZ 69
  rw [show rsp.toBitVec - 8#64 - 216 + 56 = rsp.toBitVec - 168 by bv_omega]
  apply store_step _ _ _ _ _ l168 _ _ (by ecancel) (by exact hl168)
  intro n5 N5
  simp only [Width.bytes, Width.bits] at N5
  kunfold
  kat hk ListCUnmarshalSSZ 70
  rw [show rsp.toBitVec - 8#64 - 216 + 256 = rsp.toBitVec + 32 by bv_omega]
  apply store_step _ _ _ _ _ s32 _ _ (by ecancel) (by exact h32)
  intro n7 N7
  simp only [Width.bytes, Width.bits] at N7
  kunfold
  kat hk ListCUnmarshalSSZ 71
  rw [show rsp.toBitVec - 8#64 - 216 + 72 = rsp.toBitVec - 152 by bv_omega]
  apply store_step _ _ _ _ _ l152 _ _ (by ecancel) (by exact hl152)
  intro n6 N6
  simp only [Width.bytes, Width.bits] at N6
  kunfold
  kat hk ListCUnmarshalSSZ 72
  kat hk ListCUnmarshalSSZ 73
  kat hk ListCUnmarshalSSZ 74
  kat hk ListCUnmarshalSSZ 75
  apply store_step_at _ _ (rsp.toBitVec - 232) _ _ _ rslot _ _ (lcl_ret _) (by ecancel) (by exact hrs)
  intro n8 N8
  simp only [Width.bytes, Width.bits] at N8
  kunfold
  rw [lcl_ret] at *
  have hn4 : 4 * gs.length / 4 = gs.length := by omega
  rw [hn4]
  have hsp3 : ∀ (a b c : List UInt8), a.length = 8 → b.length = 8 → c.length = 8 →
      Eq ((a ++ (b ++ c)).At (rsp.toBitVec - 232 + 8)) = Eq (a.At (rsp.toBitVec - 224)) ⋆ Eq (b.At (rsp.toBitVec - 216))
        ⋆ Eq (c.At (rsp.toBitVec - 208)) := by
    intro a b c ha hb hc
    rw [at_app a _ (b := rsp.toBitVec - 216) (by rw [ha]; bv_omega) (by simp [*]),
      at_app b c (b := rsp.toBitVec - 208) (by rw [hb]; bv_omega) (by simp [*]), show rsp.toBitVec - 232 + 8 = rsp.toBitVec - 224 by bv_omega]
    simp only [Std.ExtHashMap.sep_assoc]
  refine eventually_trans _ _ _ _ (hms _ (Host.addrOf (k + 75 + 1)) gs.length avail blk (l224 ++ (l216 ++ l208)) _ rfl
    (by show (BitVec.ofNat 64 gs.length).toNat ≤ _; simp; omega)
    (by show (BitVec.ofNat 64 gs.length).toNat = _; simp; omega) (by omega) (by unfold maxAlloc; omega) (by omega) hblk
    (by simp [*]) (by dsimp only; rw [lcl_blk, hsp3 _ _ _ hl224 hl216 hl208]; ecancel)) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hr141, -, stk1, sm1, hstk1, hsm1, Hm1⟩
  dsimp only at hpc1 hrsp1 hr141 Hm1
  subst hpc1
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩,
    zmms1, flags1, mem1⟩ := d1
  simp only at hrsp1 hr141 Hm1
  subst hrsp1 hr141
  rw [lcl_blk, hn4, ← List.take_append_drop 8 sm1, ← List.take_append_drop 8 (sm1.drop 8),
    hsp3 _ _ _ (by simp [hsm1]) (by simp [hsm1]) (by simp [hsm1])] at Hm1
  kat hk ListCUnmarshalSSZ 76
  rw [lcl_g, show rsp.toBitVec - 224 + 56 = rsp.toBitVec - 168 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 (BitVec.ofNat 64 gs.length).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk ListCUnmarshalSSZ 77
  rw [lcl_g, show rsp.toBitVec - 224 + 232 = rsp.toBitVec + 8 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk ListCUnmarshalSSZ 78
  apply store_step_at _ _ (rax.toBitVec + 8) _ _ _ cL _ _ (by bv_omega) (by ecancel) (by exact hcL)
  intro n9 N9
  simp only [Width.bytes, Width.bits] at N9
  kunfold
  kat hk ListCUnmarshalSSZ 79
  apply store_step_at _ _ (rax.toBitVec + 16) _ _ _ cC _ _ (by bv_omega) (by ecancel) (by exact hcC)
  intro n10 N10
  simp only [Width.bytes, Width.bits] at N10
  kunfold
  kat hk ListCUnmarshalSSZ 80
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk ListCUnmarshalSSZ 81
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf ListCUnmarshalSSZ 86
  kat hk ListCUnmarshalSSZ 86
  kat hk ListCUnmarshalSSZ 87
  apply store_step_at _ _ rax.toBitVec _ _ _ cP _ _ (by bv_omega) (by ecancel) (by exact hcP)
  intro n11 N11
  simp only [Width.bytes, Width.bits] at N11
  kunfold
  kat hk ListCUnmarshalSSZ 88
  intro _
  kat hk ListCUnmarshalSSZ 89
  rw [lcl_g, show rsp.toBitVec - 224 + 72 = rsp.toBitVec - 152 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 (BitVec.ofNat 64 (4 * gs.length)).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk ListCUnmarshalSSZ 90
  intro _
  kat hk ListCUnmarshalSSZ 91
  intro _
  kat hk ListCUnmarshalSSZ 92
  klabel hk hf ListCUnmarshalSSZ 239
  have hrcx4 : 4 ≤ rcx.toNat := by omega
  have hrdi4 : 4 ≤ rdi.toNat := by omega
  rw [lca_m4 _ (by simpa using hrdi4), lca_m4' _ (by simpa using hrcx4), BitVec.mul_one,
    show rcx.toBitVec.toNat - 4 = T by simp; omega] at N11
  rw [show Int.toBytes 8 rdi.toBitVec.toInt = Int.toBytes 8 (BitVec.ofNat 64 rdi.toBitVec.toNat).toInt by simp] at N11
  have hstart : lcStart gs 0 = 4 * gs.length := by simp [lcStart]
  have htl : Eq (tl.At (rbx.toBitVec + 4)) = Eq ((tl.take 4).At (rbx.toBitVec + 4))
      ⋆ Eq ((tl.drop 4).At (rbx.toBitVec + 4 + 4)) := by
    conv => lhs; rw [← List.take_append_drop 4 tl]
    exact at_app _ _ (by rw [List.length_take, Nat.min_eq_left (by omega)]; rfl) (by simp; omega)
  refine eventually_trans _ _ _ _ (lcl_loop k hk hf rsp.toBitVec (rbx.toBitVec + 4) rax.toBitVec rax1.toBitVec tl T gs hgs
    hT hn hT32 hend hparts hnexts rdi.toBitVec.toNat (by simp; omega) (by simpa using hcap63) S hS ra rbp guard Heap
    (Eq ((Int.toBytes 8 rbx.toBitVec.toInt).At (rsp.toBitVec + 16)) ⋆ Eq ([4, 0, 0, 0].At rbx.toBitVec)
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 gs.length).toInt).At (rax.toBitVec + 16))
      ⋆ Eq (((sm1.drop 8).drop 8).At (rsp.toBitVec - 208)) ⋆ R)
    hguard hsp hno hlu gs.length 0 _ [] stk1
    (Int.toBytes 8 (Host.addrOf (k + 75 + 1)).toBitVec.toInt) (sm1.take 8) ((sm1.drop 8).take 8) l136
    (Int.toBytes 8 (BitVec.ofNat 64 (4 * gs.length)).toInt) l160 l184 (avail - 8 * gs.length)
    (by omega) rfl rfl hstk1 (Int.toBytes_length 8 _) (by simp [hsm1]) (by simp [hsm1]) hl136 (Int.toBytes_length 8 _) hl160 hl184
    (by omega) (by simp) (by show (BitVec.ofNat 64 gs.length).toNat = _; simp; omega)
    (by show (BitVec.ofNat 64 (4 * gs.length)).toNat = _; rw [hstart]; simp; omega)
    (by apply UInt64.toBitVec_inj.mp; simp) (by apply UInt64.toBitVec_inj.mp; simp)
    (by simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega)
    (by
      dsimp only
      simp only [List.reverse_nil, List.map_nil, show ptrBytes [] = [] from rfl, List.nil_append, Nat.sub_zero,
        lcObjs, Std.ExtHashMap.sep_emp]
      rw [htl]
      ecancel)) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrbx2, hrdi2, hrsp2, hr142, acc', av', hacc', Hm2⟩
  dsimp only at hpc2 hrbx2 hrdi2 hrsp2 hr142 Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := d2
  simp only at hrbx2 hrdi2 hrsp2 hr142 Hm2
  subst hrbx2 hrdi2 hrsp2
  kat hk ListCUnmarshalSSZ 407
  kat hk ListCUnmarshalSSZ 408
  kat hk ListCUnmarshalSSZ 409
  kat hk ListCUnmarshalSSZ 410
  klabel hk hf ListCUnmarshalSSZ 226
  kat hk ListCUnmarshalSSZ 226
  kat hk ListCUnmarshalSSZ 227
  kat hk ListCUnmarshalSSZ 228
  kat hk ListCUnmarshalSSZ 229
  rw [show (216 : BitVec 64) + ({ toBitVec := rsp.toBitVec - 232 } + 8 : UInt64).toBitVec = rsp.toBitVec - 8 by
    simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListCUnmarshalSSZ 230
  rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨trivial, rfl, rfl, ?_, rax1.toBitVec, acc', av', hacc', ?_⟩
  · apply UInt64.toBitVec_inj.mp; simp
  · exact sep_true (P := Eq ((Int.toBytes 8 rax1.toBitVec.toInt).At rax.toBitVec)
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 gs.length).toInt).At (rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 gs.length).toInt).At (rax.toBitVec + 16))
      ⋆ Eq ((ptrBytes (acc'.reverse.map (fun t : BitVec 64 × BitVec 64 × ListU64 => t.1))).At rax1.toBitVec)
      ⋆ lcObjs acc' ⋆ Eq (tl.At (rbx.toBitVec + 4)) ⋆ Heap av'
      ⋆ Eq ([4, 0, 0, 0].At rbx.toBitVec) ⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At rsp.toBitVec) ⋆ R) (by ecancel)
