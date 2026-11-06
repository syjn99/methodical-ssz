import Fk.LcReject
import Fk.FunSpecs
import Fk.NeAccept
import Fk.LuErr

/-!
# ListC.UnmarshalSSZ element loop, on Kraken main

Loop head `L_3c4` (directive 239).
-/

open Fk Fk.Code Fv1 EthLib.Serialization.Ssz
variable [Host]

theorem lcl_ret (x : BitVec 64) : x - 8#64 - 216 - 8#64 = x - 232 := by bv_omega
theorem lcl_g (x o : BitVec 64) : ({ toBitVec := x - 232 } + 8 : UInt64).toBitVec + o = x - 224 + o := by
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
theorem lcl_blk (x : BitVec 64) (S : Nat) : x - 232 - BitVec.ofNat 64 (144 + S) = x - 232 - 144 - BitVec.ofNat 64 S := by
  rw [show BitVec.ofNat 64 (144 + S) = 144 + BitVec.ofNat 64 S by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]]
  bv_omega

theorem ja_false (a b : BitVec 64) (af of' : Bool) (h : a.toNat ≤ b.toNat) :
    CondCode.a.interp (StatusFlags.from_result (a - b)
      { cf := BitVec.unsigned (a - b) != a.unsigned - b.unsigned, af := af, of := of' }) = false := by
  by_cases he : a = b
  · subst he; simp [CondCode.interp, StatusFlags.from_result]
  · have hlt : a.toNat < b.toNat := by
      have : a.toNat ≠ b.toNat := fun e => he (BitVec.eq_of_toNat_eq e)
      omega
    have hb := b.isLt
    have hs : (a - b).toNat = 2 ^ 64 - b.toNat + a.toNat := by rw [BitVec.toNat_sub]; omega
    simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, hs]
    simp; omega
theorem jb_false (a b : BitVec 64) (af of' : Bool) (h : b.toNat ≤ a.toNat) :
    CondCode.c.interp (StatusFlags.from_result (a - b)
      { cf := BitVec.unsigned (a - b) != a.unsigned - b.unsigned, af := af, of := of' }) = false := by
  have hs : (a - b).toNat = a.toNat - b.toNat := BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
  simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, hs]
  simp; omega

theorem ofBytes_uintBytes4 (e : Nat) (h : e < 2 ^ 32) : Int.ofBytes (uintBytes 4 e).toList = e := by
  have := ofBytes_readUint (uintBytes 4 e) 4 0 (by simp [Fv.uintBytes_size])
  rw [List.drop_zero, List.take_of_length_le (by simp [Fv.uintBytes_size])] at this
  rw [this, readUint_uintBytes 4 e (by simpa using h)]

theorem lc_mask (v y : BitVec 64) (h : 0 < y.toNat) (h2 : y.toNat < 2 ^ 63) :
    v &&& BitVec.sshiftRight (-y) 63 = v := by
  have hm : (-y).msb = true := by
    rw [BitVec.msb_eq_decide, BitVec.toNat_neg]; simp; omega
  have hs : BitVec.sshiftRight (-y) 63 = BitVec.allOnes 64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sshiftRight, ite_cond_eq_true _ _ (by simpa using hm)]
    rw [BitVec.msb_eq_decide] at hm; simp at hm
    simp [Nat.shiftRight_eq_div_pow]; omega
  rw [hs, BitVec.and_allOnes]

theorem lcl_y (c s : Nat) (h1 : s + 4 ≤ c) (h2 : c < 2 ^ 63) :
    (BitVec.ofNat 64 c - BitVec.ofNat 64 s + -4).toNat = c - s - 4 := by
  rw [← BitVec.sub_eq_add_neg]
  have h3 : BitVec.ofNat 64 c - BitVec.ofNat 64 s = BitVec.ofNat 64 (c - s) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega
  rw [h3, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]
  simp; omega

theorem jnc_false (a b : BitVec 64) (af of' : Bool) (h : a.toNat < b.toNat) :
    CondCode.nc.interp (StatusFlags.from_result (a - b)
      { cf := BitVec.unsigned (a - b) != a.unsigned - b.unsigned, af := af, of := of' }) = false := by
  have hs : (a - b).toNat = 2 ^ 64 - b.toNat + a.toNat := by
    rw [BitVec.toNat_sub]; have := b.isLt; omega
  simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, hs]
  simp; omega

theorem lcl_call (x : BitVec 64) : ({ toBitVec := x - 232 } + 8 : UInt64).toBitVec - 8#64 = x - 232 := by
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega

/-- The tail chunk split around `[o, o + w)`. -/
theorem tl_split3 (a : BitVec 64) (tl : List UInt8) (o w : Nat) (h : o + w ≤ tl.length) (hl : tl.length < 2 ^ 64) :
    Eq (tl.At a) = Eq ((tl.take o).At a) ⋆ Eq (((tl.drop o).take w).At (a + BitVec.ofNat 64 o))
      ⋆ Eq ((tl.drop (o + w)).At (a + BitVec.ofNat 64 o + BitVec.ofNat 64 w)) := by
  have e1 : tl = tl.take o ++ ((tl.drop o).take w ++ tl.drop (o + w)) := by
    rw [← List.drop_drop, List.take_append_drop, List.take_append_drop]
  conv => lhs; rw [e1]
  rw [Mem.At_append_sep _ _ _ (by simp; omega), Mem.At_append_sep _ _ _ (by simp; omega)]
  simp only [List.length_take, List.length_drop, Std.ExtHashMap.sep_assoc]
  rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
theorem lcl_iter (k : Nat) (hk : ListCUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListCUnmarshalSSZ k)
    (x base recv A : BitVec 64) (tl ptrs : List UInt8) (T n i s e : Nat) (g : ListU64) (hg : g.ok)
    (hT : tl.length = T) (hn : n ≤ 4) (hi : i < n) (hptrs : ptrs.length = 8 * i)
    (hse : s + (4 + 8 * g.l.length) = e) (heT : e ≤ T) (hs4 : 4 * n ≤ s)
    (hpart : (tl.drop s).take (4 + 8 * g.l.length) = [4, 0, 0, 0] ++ (u64Bytes g.l).toList)
    (hnext : i + 1 < n → (tl.drop (4 * (i + 1))).take 4 = (uintBytes 4 e).toList)
    (hlast : i + 1 = n → e = T)
    (hT32 : T < 2 ^ 32) (cap0 : Nat) (hcap : T + 4 ≤ cap0) (hcap63 : cap0 < 2 ^ 63)
    (S : Nat) (hS : S < 2 ^ 60) (blk rslot sp1 sp2 s136 s152 s160 s184 : List UInt8)
    (hblk : blk.length = 144 + S) (hrs : rslot.length = 8) (hsp1 : sp1.length = 8) (hsp2 : sp2.length = 8)
    (h136 : s136.length = 8) (h152 : s152.length = 8) (h160 : s160.length = 8) (h184 : s184.length = 8)
    (ra rbp0 guard : UInt64) (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 24 + 8 * 16 ≤ avail)
    (O R : DataMem → Prop) (s0 : MachineData)
    (hrax : s0.regs.rax.toNat = i) (hrdx : s0.regs.rdx.toNat = n) (hrcx : s0.regs.rcx.toNat = s)
    (hrsp : s0.regs.rsp.toBitVec = x - 8#64 - 216)
    (hguard : guard.toNat + 400 + S < x.toNat) (hx : 400 + S ≤ x.toNat)
    (h_mem : s0.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At x) ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (x - 8))
      ⋆ Eq ((Int.toBytes 8 recv.toInt).At (x + 8))
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 cap0).toInt).At (x + 32))
      ⋆ Eq ((Int.toBytes 8 base.toInt).At (x - 128)) ⋆ Eq (s136.At (x - 136))
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 (cap0 - 4)).toInt).At (x - 144))
      ⋆ Eq (s152.At (x - 152)) ⋆ Eq (s160.At (x - 160))
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 n).toInt).At (x - 168))
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 T).toInt).At (x - 176))
      ⋆ Eq (s184.At (x - 184))
      ⋆ Eq (sp1.At (x - 224)) ⋆ Eq (sp2.At (x - 216)) ⋆ Eq (rslot.At (x - 232))
      ⋆ Eq (blk.At (x - 232 - 144 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s0.regs.r14.toBitVec + 16)) ⋆ Heap avail
      ⋆ Eq (tl.At base)
      ⋆ Eq ((Int.toBytes 8 A.toInt).At recv) ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 n).toInt).At (recv + 8))
      ⋆ Eq ((ptrs ++ List.replicate (8 * (n - i)) 0).At A)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ O ⋆ R)
    (hno : NewobjectC Heap (label "type__" + 83104).toBitVec 24 (144 + S)) (hlu : LuUAccC Heap S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 239) ∧ st.data.regs.rax.toNat = i + 1 ∧ st.data.regs.rdx.toNat = n
        ∧ st.data.regs.rcx.toNat = e ∧ st.data.regs.rbx = 0 ∧ st.data.regs.rdi = 0
        ∧ st.data.regs.rsp = s0.regs.rsp ∧ st.data.regs.r14 = s0.regs.r14 ∧
        ∃ (p q : BitVec 64) (blk' rslot' sp1' sp2' s136' s152' s160' : List UInt8),
          blk'.length = 144 + S ∧ rslot'.length = 8 ∧ sp1'.length = 8 ∧ sp2'.length = 8 ∧ s136'.length = 8
          ∧ s152'.length = 8 ∧ s160'.length = 8 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At x) ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (x - 8))
          ⋆ Eq ((Int.toBytes 8 recv.toInt).At (x + 8))
          ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 cap0).toInt).At (x + 32))
          ⋆ Eq ((Int.toBytes 8 base.toInt).At (x - 128)) ⋆ Eq (s136'.At (x - 136))
          ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 (cap0 - 4)).toInt).At (x - 144))
          ⋆ Eq (s152'.At (x - 152)) ⋆ Eq (s160'.At (x - 160))
          ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 n).toInt).At (x - 168))
          ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 T).toInt).At (x - 176))
          ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 e).toInt).At (x - 184))
          ⋆ Eq (sp1'.At (x - 224)) ⋆ Eq (sp2'.At (x - 216)) ⋆ Eq (rslot'.At (x - 232))
          ⋆ Eq (blk'.At (x - 232 - 144 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s0.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 24 - 8 * g.l.length)
          ⋆ Eq (tl.At base)
          ⋆ Eq ((Int.toBytes 8 A.toInt).At recv) ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 n).toInt).At (recv + 8))
          ⋆ Eq ((ptrs ++ Int.toBytes 8 p.toInt ++ List.replicate (8 * (n - (i + 1))) 0).At A)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ (Eq ((Int.toBytes 8 q.toInt).At p) ⋆ Eq ((Int.toBytes 8 (g.l.length : Int)).At (p + 8))
            ⋆ Eq ((Int.toBytes 8 (g.l.length : Int)).At (p + 16)) ⋆ Eq ((u64Bytes g.l).toList.At q) ⋆ O) ⋆ R)
          st.data.dmem)
      ⟨s0, Host.addrOf (k + 239)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s0
  simp only at h_mem hrax hrdx hrcx hrsp ⊢
  have := rax.toNat_lt_size; have := rdx.toNat_lt_size; have := rcx.toNat_lt_size; have := x.isLt
  simp only [UInt64.size] at *
  kat hk ListCUnmarshalSSZ 239
  kat hk ListCUnmarshalSSZ 240
  kat hk ListCUnmarshalSSZ 241
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
  simp only [Effects.All]
  kat hk ListCUnmarshalSSZ 242
  rw [show rsp.toBitVec + 64 = x - 160 by rw [hrsp]; bv_omega]
  apply store_step _ _ _ _ _ s160 _ _ (by ecancel) (by exact h160)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk ListCUnmarshalSSZ 243
  rw [show rsp.toBitVec + 40 = x - 184 by rw [hrsp]; bv_omega]
  apply store_step _ _ _ _ _ s184 _ _ (by ecancel) (by exact h184)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk ListCUnmarshalSSZ 244
  kat hk ListCUnmarshalSSZ 245
  kat hk ListCUnmarshalSSZ 246
  apply store_step_at _ _ (x - 232) _ _ _ rslot _ _ (by rw [hrsp, lcl_ret]) (by ecancel) (by exact hrs)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  rw [show rsp.toBitVec - 8#64 = x - 232 by rw [hrsp, lcl_ret]] at *
  have hspA : x - 232 + 8 = x - 224 := by bv_omega
  refine eventually_trans _ _ _ _ (hno _ (Host.addrOf (k + 246 + 1)) avail blk sp1 _ rfl (by omega) hblk hsp1
    (by dsimp only; rw [lcl_blk, hspA]; ecancel)) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hr141, -, stk1, sn1, hstk1, hsn1, Hm1⟩
  dsimp only at hpc1 hrsp1 hr141 Hm1
  subst hpc1
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩,
    zmms1, flags1, mem1⟩ := d1
  simp only at hrsp1 hr141 Hm1
  subst hrsp1 hr141
  rw [lcl_blk, luObj_sep, hspA] at Hm1
  kat hk ListCUnmarshalSSZ 247
  rw [lcl_g, show x - 224 + 64 = x - 160 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk ListCUnmarshalSSZ 248
  kat hk ListCUnmarshalSSZ 249
  rw [lcl_g, show x - 224 + 56 = x - 168 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 (BitVec.ofNat 64 n).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk ListCUnmarshalSSZ 250
  kat hk ListCUnmarshalSSZ 251
  have hi1 : (rax.toBitVec + 1).toNat = i + 1 := by simp [BitVec.toNat_add]; omega
  by_cases hl : i + 1 = n
  · have heq := hlast hl
    subst heq
    split
    case isFalse h =>
      exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
      apply h; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub, BitVec.toNat_add]; omega
    simp only [Effects.All]
    klabel hk hf ListCUnmarshalSSZ 268
    kat hk ListCUnmarshalSSZ 268
    kat hk ListCUnmarshalSSZ 269
    rw [lcl_g, show x - 224 + 80 = x - 144 by bv_omega]
    apply load_step _ _ _ _ (Int.toBytes 8 (BitVec.ofNat 64 (cap0 - 4)).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
    kunfold
    kat hk ListCUnmarshalSSZ 270
    kat hk ListCUnmarshalSSZ 271
    rw [lcl_g, show x - 224 + 48 = x - 176 by bv_omega]
    apply load_step _ _ _ _ (Int.toBytes 8 (BitVec.ofNat 64 e).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
    kunfold
    kat hk ListCUnmarshalSSZ 272
    kat hk ListCUnmarshalSSZ 273
    rw [lcl_g, show x - 224 + 96 = x - 128 by bv_omega]
    apply load_step _ _ _ _ (Int.toBytes 8 base.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
    kunfold
    kat hk ListCUnmarshalSSZ 274
    kat hk ListCUnmarshalSSZ 275
    rw [lcl_g, show x - 224 + 40 = x - 184 by bv_omega]
    apply load_step _ _ _ _ (Int.toBytes 8 rcx.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
    kunfold
    kat hk ListCUnmarshalSSZ 276
    kat hk ListCUnmarshalSSZ 277
    rw [jb_false _ _ _ _ (by simp; omega)]
    simp only [Bool.false_eq_true, ↓reduceIte, Effects.All]
    kat hk ListCUnmarshalSSZ 278
    kat hk ListCUnmarshalSSZ 279
    kat hk ListCUnmarshalSSZ 280
    rw [ja_false _ _ _ _ (by simp; omega)]
    simp only [Bool.false_eq_true, ↓reduceIte, Effects.All]
    kat hk ListCUnmarshalSSZ 281
    rw [lcl_g, show x - 224 + 88 = x - 136 by bv_omega]
    apply store_step _ _ _ _ _ s136 _ _ (by ecancel) (by exact h136)
    intro m4 H4
    simp only [Width.bytes, Width.bits] at H4
    kunfold
    kat hk ListCUnmarshalSSZ 282
    rw [lcl_g, show x - 224 + 72 = x - 152 by bv_omega]
    apply store_step _ _ _ _ _ s152 _ _ (by ecancel) (by exact h152)
    intro m5 H5
    simp only [Width.bytes, Width.bits] at H5
    kunfold
    kat hk ListCUnmarshalSSZ 283
    rw [lcl_g, show x - 224 + 40 = x - 184 by bv_omega]
    apply store_step _ _ _ _ _ (Int.toBytes 8 rcx.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    intro m6 H6
    simp only [Width.bytes, Width.bits] at H6
    kunfold
    kat hk ListCUnmarshalSSZ 284
    rw [lcl_g, show x - 224 + 256 = x + 32 by bv_omega]
    apply load_step _ _ _ _ (Int.toBytes 8 (BitVec.ofNat 64 cap0).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
    kunfold
    kat hk ListCUnmarshalSSZ 285
    kat hk ListCUnmarshalSSZ 286
    kat hk ListCUnmarshalSSZ 287
    kat hk ListCUnmarshalSSZ 288
    kat hk ListCUnmarshalSSZ 289
    kat hk ListCUnmarshalSSZ 290
    kat hk ListCUnmarshalSSZ 291
    kat hk ListCUnmarshalSSZ 292
    kshl64 63
    kat hk ListCUnmarshalSSZ 293
    intro _
    kat hk ListCUnmarshalSSZ 294
    kat hk ListCUnmarshalSSZ 295
    have hrcx' : rcx.toBitVec = BitVec.ofNat 64 s := by apply BitVec.eq_of_toNat_eq; simp; omega
    have hy : (BitVec.ofNat 64 cap0 - rcx.toBitVec + -4).toNat = cap0 - s - 4 := by
      rw [hrcx']; exact lcl_y cap0 s (by omega) hcap63
    rw [lc_mask _ _ (by rw [hy]; omega) (by rw [hy]; omega)]
    rw [show rcx.toBitVec + base * 1#64 = base + BitVec.ofNat 64 s by rw [hrcx', BitVec.mul_one, BitVec.add_comm]]
    apply store_step_at _ _ (x - 232) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 246 + 1)).toBitVec.toInt) _ _
      (lcl_call _) (by ecancel) (by exact Int.toBytes_length 8 _)
    intro m7 H7
    simp only [Width.bytes, Width.bits] at H7
    kunfold
    rw [lcl_call] at *
    rw [tl_split3 base tl s (4 + 8 * g.l.length) (by omega) (by omega), hpart,
      at_app [4, 0, 0, 0] (u64Bytes g.l).toList (b := base + BitVec.ofNat 64 s + 4) (by rfl)
      (by have : g.l.length ≤ 16 := hg; simp [u64Bytes_size]; omega)] at H7
    have hx232 : (x - 232).toNat = x.toNat - 232 := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp
    refine eventually_trans _ _ _ _ (hlu _ (Host.addrOf (k + 295 + 1)) g stk1 sn1 sp2
      (List.replicate 8 0) (List.replicate 8 0) (List.replicate 8 0) guard (avail - 24) _ hg hstk1 hsn1 hsp2
      (by simp) (by simp) (by simp)
      (by show (BitVec.ofNat 64 e - rcx.toBitVec).toNat = _; rw [hrcx']; simp [BitVec.toNat_sub]; omega)
      (by show (BitVec.ofNat 64 e - rcx.toBitVec).toNat ≤ (BitVec.ofNat 64 cap0 - rcx.toBitVec + -4).toNat
          rw [hy, hrcx']; simp [BitVec.toNat_sub]; omega)
      (by show (BitVec.ofNat 64 cap0 - rcx.toBitVec + -4).toNat < 2 ^ 63; rw [hy]; omega)
      (by show guard.toNat < (x - 232).toNat - 8; rw [hx232]; omega)
      (by show 8 ≤ (x - 232).toNat; rw [hx232]; omega) (by omega)
      (by dsimp only; rw [show x - 232 + 8 = x - 224 by bv_omega, show x - 232 + 16 = x - 216 by bv_omega]; ecancel)) ?_
    rintro ⟨d2, pc2⟩ ⟨hpc2, hrax2, hrbx2, hrsp2, hr142, q, stk2, sp1', sp2', hstk2, hsp1', hsp2', Hm2⟩
    dsimp only at hpc2 hrax2 hrbx2 hrsp2 hr142 Hm2
    subst hpc2
    obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
      zmms2, flags2, mem2⟩ := d2
    simp only at hrax2 hrbx2 hrsp2 hr142 Hm2
    subst hrax2 hrbx2 hrsp2 hr142
    rw [show x - 232 + 8 = x - 224 by bv_omega, show x - 232 + 16 = x - 216 by bv_omega] at Hm2
    have hrsp2 : ({ toBitVec := x - 232 } + 8 : UInt64) = { toBitVec := x - 224 } := by
      apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
    simp only [hrsp2]
    kat hk ListCUnmarshalSSZ 296
    intro _
    kat hk ListCUnmarshalSSZ 297
    split
    case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    simp only [Effects.All]
    kat hk ListCUnmarshalSSZ 298
    rw [show x - 224 + 232 = x + 8 by bv_omega]
    apply load_step _ _ _ _ (Int.toBytes 8 recv.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
    kunfold
    kat hk ListCUnmarshalSSZ 299
    apply load_step_at _ _ (recv + 8) _ _ (Int.toBytes 8 (BitVec.ofNat 64 n).toInt) _ _ (by bv_omega) (by ecancel) (by exact Int.toBytes_length 8 _)
    simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
    kunfold
    kat hk ListCUnmarshalSSZ 300
    rw [show x - 224 + 64 = x - 160 by bv_omega]
    apply load_step _ _ _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
    kunfold
    kat hk ListCUnmarshalSSZ 301
    kat hk ListCUnmarshalSSZ 302
    rw [jnc_false _ _ _ _ (by simp; omega)]
    simp only [Bool.false_eq_true, ↓reduceIte, Effects.All]
    kat hk ListCUnmarshalSSZ 303
    apply load_step _ _ _ _ (Int.toBytes 8 A.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
    kunfold
    kat hk ListCUnmarshalSSZ 304
    apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
    simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
    kunfold
    kat hk ListCUnmarshalSSZ 305
    split
    case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    simp only [Effects.All]
    kat hk ListCUnmarshalSSZ 306
    rw [show x - 224 + 88 = x - 136 by bv_omega]
    apply load_step _ _ _ _ (Int.toBytes 8 rax1.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
    kunfold
    kat hk ListCUnmarshalSSZ 307
    klabel hk hf ListCUnmarshalSSZ 231
    kat hk ListCUnmarshalSSZ 231
    kat hk ListCUnmarshalSSZ 232
    have hrep : List.replicate (8 * (n - i)) (0 : UInt8) = List.replicate 8 0 ++ List.replicate (8 * (n - (i + 1))) 0 := by
      rw [List.replicate_append_replicate, show 8 + 8 * (n - (i + 1)) = 8 * (n - i) by omega]
    rw [hrep, at_app ptrs _ (b := A + BitVec.ofNat 64 (8 * i)) (by rw [hptrs]) (by simp [hptrs]; omega),
      at_app (List.replicate 8 0) _ (b := A + BitVec.ofNat 64 (8 * i) + 8) (by simp) (by simp; omega)] at Hm2
    rw [show A + rax.toBitVec * 8#64 = A + BitVec.ofNat 64 (8 * i) by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_mul]; omega]
    apply store_step _ _ _ _ _ (List.replicate 8 0) _ _ (by ecancel) (by simp)
    intro m8 H8
    simp only [Width.bytes, Width.bits] at H8
    kunfold
    kat hk ListCUnmarshalSSZ 233
    rw [show x - 224 + 56 = x - 168 by bv_omega]
    apply load_step _ _ _ _ (Int.toBytes 8 (BitVec.ofNat 64 n).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
    kunfold
    kat hk ListCUnmarshalSSZ 234
    kat hk ListCUnmarshalSSZ 235
    rw [show x - 224 + 40 = x - 184 by bv_omega]
    apply load_step _ _ _ _ (Int.toBytes 8 (BitVec.ofNat 64 e).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
    kunfold
    kat hk ListCUnmarshalSSZ 236
    kat hk ListCUnmarshalSSZ 237
    kat hk ListCUnmarshalSSZ 238
    rw [show x - 224 + 72 = x - 152 by bv_omega]
    apply load_step _ _ _ _ (Int.toBytes 8 (rax.toBitVec + 1).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
    kunfold
    apply Eventually.done
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rax1.toBitVec, q, stk2, Int.toBytes 8 (Host.addrOf (k + 295 + 1)).toBitVec.toInt,
      sp1', sp2', Int.toBytes 8 rax1.toBitVec.toInt, Int.toBytes 8 (rax.toBitVec + 1).toInt,
      Int.toBytes 8 rax.toBitVec.toInt, hstk2, Int.toBytes_length 8 _, hsp1', hsp2', Int.toBytes_length 8 _,
      Int.toBytes_length 8 _, Int.toBytes_length 8 _, ?_⟩
    · exact hi1
    · show (BitVec.ofNat 64 n).toNat = n; simp; omega
    · show (BitVec.ofNat 64 e).toNat = e; simp; omega
    · rfl
    · rfl
    · apply UInt64.toBitVec_inj.mp; simp only [hrsp]; bv_omega
    · dsimp only
      rw [tl_split3 base tl s (4 + 8 * g.l.length) (by omega) (by omega), hpart,
        at_app [4, 0, 0, 0] (u64Bytes g.l).toList (b := base + BitVec.ofNat 64 s + 4) (by rfl)
          (by have : g.l.length ≤ 16 := hg; simp [u64Bytes_size]; omega),
        List.append_assoc, at_app ptrs _ (b := A + BitVec.ofNat 64 (8 * i)) (by rw [hptrs])
          (by simp [hptrs, Int.toBytes_length]; omega),
        at_app (Int.toBytes 8 rax1.toBitVec.toInt) _ (b := A + BitVec.ofNat 64 (8 * i) + 8) (by simp [Int.toBytes_length])
          (by simp [Int.toBytes_length]; omega)]
      simp only [Std.ExtHashMap.sep_assoc] at H8 ⊢
      ecancel
  · split
    case isTrue h =>
      exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
      apply hl; have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
    simp only [Effects.All]
    kat hk ListCUnmarshalSSZ 252
    kat hk ListCUnmarshalSSZ 253
    kshl64 2
    kat hk ListCUnmarshalSSZ 254
    rw [lcl_g, show x - 224 + 80 = x - 144 by bv_omega]
    apply load_step _ _ _ _ (Int.toBytes 8 (BitVec.ofNat 64 (cap0 - 4)).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
    kunfold
    kat hk ListCUnmarshalSSZ 255
    kat hk ListCUnmarshalSSZ 256
    rw [ja_false _ _ _ _ (by
      simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_add]; omega)]
    simp only [Bool.false_eq_true, ↓reduceIte, Effects.All]
    kat hk ListCUnmarshalSSZ 257
    kat hk ListCUnmarshalSSZ 258
    kshl64 2
    kat hk ListCUnmarshalSSZ 259
    kat hk ListCUnmarshalSSZ 260
    rw [jb_false _ _ _ _ (by
      simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_add]; omega)]
    simp only [Bool.false_eq_true, ↓reduceIte, Effects.All]
    kat hk ListCUnmarshalSSZ 261
    rw [lcl_g, show x - 224 + 96 = x - 128 by bv_omega]
    apply load_step _ _ _ _ (Int.toBytes 8 base.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
    kunfold
    kat hk ListCUnmarshalSSZ 262
    rw [tl_split3 base tl (4 * (i + 1)) 4 (by omega) (by omega)] at Hm1
    rw [show base + rax.toBitVec * 4#64 + 4 = base + BitVec.ofNat 64 (4 * (i + 1)) by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_mul]; omega]
    apply load_step _ _ _ _ ((tl.drop (4 * (i + 1))).take 4) _ _ (by ecancel) (by simp; omega)
    rw [hnext (by omega), ofBytes_uintBytes4 e (by omega)]
    rw [← tl_split3 base tl (4 * (i + 1)) 4 (by omega) (by omega)] at Hm1
    kunfold
    kat hk ListCUnmarshalSSZ 263
    kat hk ListCUnmarshalSSZ 264
    rw [lcl_g, show x - 224 + 48 = x - 176 by bv_omega]
    apply load_step _ _ _ _ (Int.toBytes 8 (BitVec.ofNat 64 T).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
    kunfold
    kat hk ListCUnmarshalSSZ 265
    kat hk ListCUnmarshalSSZ 266
    rw [zx_o e (by omega)]
    split
    case isFalse h =>
      exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
    simp only [Effects.All]
    klabel hk hf ListCUnmarshalSSZ 274
    kat hk ListCUnmarshalSSZ 274
    kat hk ListCUnmarshalSSZ 275
    rw [lcl_g, show x - 224 + 40 = x - 184 by bv_omega]
    apply load_step _ _ _ _ (Int.toBytes 8 rcx.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
    kunfold
    kat hk ListCUnmarshalSSZ 276
    kat hk ListCUnmarshalSSZ 277
    rw [jb_false _ _ _ _ (by simp; omega)]
    simp only [Bool.false_eq_true, ↓reduceIte, Effects.All]
    kat hk ListCUnmarshalSSZ 278
    kat hk ListCUnmarshalSSZ 279
    kat hk ListCUnmarshalSSZ 280
    rw [ja_false _ _ _ _ (by simp; omega)]
    simp only [Bool.false_eq_true, ↓reduceIte, Effects.All]
    kat hk ListCUnmarshalSSZ 281
    rw [lcl_g, show x - 224 + 88 = x - 136 by bv_omega]
    apply store_step _ _ _ _ _ s136 _ _ (by ecancel) (by exact h136)
    intro m4 H4
    simp only [Width.bytes, Width.bits] at H4
    kunfold
    kat hk ListCUnmarshalSSZ 282
    rw [lcl_g, show x - 224 + 72 = x - 152 by bv_omega]
    apply store_step _ _ _ _ _ s152 _ _ (by ecancel) (by exact h152)
    intro m5 H5
    simp only [Width.bytes, Width.bits] at H5
    kunfold
    kat hk ListCUnmarshalSSZ 283
    rw [lcl_g, show x - 224 + 40 = x - 184 by bv_omega]
    apply store_step _ _ _ _ _ (Int.toBytes 8 rcx.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    intro m6 H6
    simp only [Width.bytes, Width.bits] at H6
    kunfold
    kat hk ListCUnmarshalSSZ 284
    rw [lcl_g, show x - 224 + 256 = x + 32 by bv_omega]
    apply load_step _ _ _ _ (Int.toBytes 8 (BitVec.ofNat 64 cap0).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
    kunfold
    kat hk ListCUnmarshalSSZ 285
    kat hk ListCUnmarshalSSZ 286
    kat hk ListCUnmarshalSSZ 287
    kat hk ListCUnmarshalSSZ 288
    kat hk ListCUnmarshalSSZ 289
    kat hk ListCUnmarshalSSZ 290
    kat hk ListCUnmarshalSSZ 291
    kat hk ListCUnmarshalSSZ 292
    kshl64 63
    kat hk ListCUnmarshalSSZ 293
    intro _
    kat hk ListCUnmarshalSSZ 294
    kat hk ListCUnmarshalSSZ 295
    have hrcx' : rcx.toBitVec = BitVec.ofNat 64 s := by apply BitVec.eq_of_toNat_eq; simp; omega
    have hy : (BitVec.ofNat 64 cap0 - rcx.toBitVec + -4).toNat = cap0 - s - 4 := by
      rw [hrcx']; exact lcl_y cap0 s (by omega) hcap63
    rw [lc_mask _ _ (by rw [hy]; omega) (by rw [hy]; omega)]
    rw [show rcx.toBitVec + base * 1#64 = base + BitVec.ofNat 64 s by rw [hrcx', BitVec.mul_one, BitVec.add_comm]]
    apply store_step_at _ _ (x - 232) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 246 + 1)).toBitVec.toInt) _ _
      (lcl_call _) (by ecancel) (by exact Int.toBytes_length 8 _)
    intro m7 H7
    simp only [Width.bytes, Width.bits] at H7
    kunfold
    rw [lcl_call] at *
    rw [tl_split3 base tl s (4 + 8 * g.l.length) (by omega) (by omega), hpart,
      at_app [4, 0, 0, 0] (u64Bytes g.l).toList (b := base + BitVec.ofNat 64 s + 4) (by rfl)
      (by have : g.l.length ≤ 16 := hg; simp [u64Bytes_size]; omega)] at H7
    have hx232 : (x - 232).toNat = x.toNat - 232 := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp
    refine eventually_trans _ _ _ _ (hlu _ (Host.addrOf (k + 295 + 1)) g stk1 sn1 sp2
      (List.replicate 8 0) (List.replicate 8 0) (List.replicate 8 0) guard (avail - 24) _ hg hstk1 hsn1 hsp2
      (by simp) (by simp) (by simp)
      (by show (BitVec.ofNat 64 e - rcx.toBitVec).toNat = _; rw [hrcx']; simp [BitVec.toNat_sub]; omega)
      (by show (BitVec.ofNat 64 e - rcx.toBitVec).toNat ≤ (BitVec.ofNat 64 cap0 - rcx.toBitVec + -4).toNat
          rw [hy, hrcx']; simp [BitVec.toNat_sub]; omega)
      (by show (BitVec.ofNat 64 cap0 - rcx.toBitVec + -4).toNat < 2 ^ 63; rw [hy]; omega)
      (by show guard.toNat < (x - 232).toNat - 8; rw [hx232]; omega)
      (by show 8 ≤ (x - 232).toNat; rw [hx232]; omega) (by omega)
      (by dsimp only; rw [show x - 232 + 8 = x - 224 by bv_omega, show x - 232 + 16 = x - 216 by bv_omega]; ecancel)) ?_
    rintro ⟨d2, pc2⟩ ⟨hpc2, hrax2, hrbx2, hrsp2, hr142, q, stk2, sp1', sp2', hstk2, hsp1', hsp2', Hm2⟩
    dsimp only at hpc2 hrax2 hrbx2 hrsp2 hr142 Hm2
    subst hpc2
    obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
      zmms2, flags2, mem2⟩ := d2
    simp only at hrax2 hrbx2 hrsp2 hr142 Hm2
    subst hrax2 hrbx2 hrsp2 hr142
    rw [show x - 232 + 8 = x - 224 by bv_omega, show x - 232 + 16 = x - 216 by bv_omega] at Hm2
    have hrsp2 : ({ toBitVec := x - 232 } + 8 : UInt64) = { toBitVec := x - 224 } := by
      apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
    simp only [hrsp2]
    kat hk ListCUnmarshalSSZ 296
    intro _
    kat hk ListCUnmarshalSSZ 297
    split
    case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    simp only [Effects.All]
    kat hk ListCUnmarshalSSZ 298
    rw [show x - 224 + 232 = x + 8 by bv_omega]
    apply load_step _ _ _ _ (Int.toBytes 8 recv.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
    kunfold
    kat hk ListCUnmarshalSSZ 299
    apply load_step_at _ _ (recv + 8) _ _ (Int.toBytes 8 (BitVec.ofNat 64 n).toInt) _ _ (by bv_omega) (by ecancel) (by exact Int.toBytes_length 8 _)
    simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
    kunfold
    kat hk ListCUnmarshalSSZ 300
    rw [show x - 224 + 64 = x - 160 by bv_omega]
    apply load_step _ _ _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
    kunfold
    kat hk ListCUnmarshalSSZ 301
    kat hk ListCUnmarshalSSZ 302
    rw [jnc_false _ _ _ _ (by simp; omega)]
    simp only [Bool.false_eq_true, ↓reduceIte, Effects.All]
    kat hk ListCUnmarshalSSZ 303
    apply load_step _ _ _ _ (Int.toBytes 8 A.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
    kunfold
    kat hk ListCUnmarshalSSZ 304
    apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
    simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
    kunfold
    kat hk ListCUnmarshalSSZ 305
    split
    case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    simp only [Effects.All]
    kat hk ListCUnmarshalSSZ 306
    rw [show x - 224 + 88 = x - 136 by bv_omega]
    apply load_step _ _ _ _ (Int.toBytes 8 rax1.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
    kunfold
    kat hk ListCUnmarshalSSZ 307
    klabel hk hf ListCUnmarshalSSZ 231
    kat hk ListCUnmarshalSSZ 231
    kat hk ListCUnmarshalSSZ 232
    have hrep : List.replicate (8 * (n - i)) (0 : UInt8) = List.replicate 8 0 ++ List.replicate (8 * (n - (i + 1))) 0 := by
      rw [List.replicate_append_replicate, show 8 + 8 * (n - (i + 1)) = 8 * (n - i) by omega]
    rw [hrep, at_app ptrs _ (b := A + BitVec.ofNat 64 (8 * i)) (by rw [hptrs]) (by simp [hptrs]; omega),
      at_app (List.replicate 8 0) _ (b := A + BitVec.ofNat 64 (8 * i) + 8) (by simp) (by simp; omega)] at Hm2
    rw [show A + rax.toBitVec * 8#64 = A + BitVec.ofNat 64 (8 * i) by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_mul]; omega]
    apply store_step _ _ _ _ _ (List.replicate 8 0) _ _ (by ecancel) (by simp)
    intro m8 H8
    simp only [Width.bytes, Width.bits] at H8
    kunfold
    kat hk ListCUnmarshalSSZ 233
    rw [show x - 224 + 56 = x - 168 by bv_omega]
    apply load_step _ _ _ _ (Int.toBytes 8 (BitVec.ofNat 64 n).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
    kunfold
    kat hk ListCUnmarshalSSZ 234
    kat hk ListCUnmarshalSSZ 235
    rw [show x - 224 + 40 = x - 184 by bv_omega]
    apply load_step _ _ _ _ (Int.toBytes 8 (BitVec.ofNat 64 e).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
    kunfold
    kat hk ListCUnmarshalSSZ 236
    kat hk ListCUnmarshalSSZ 237
    kat hk ListCUnmarshalSSZ 238
    rw [show x - 224 + 72 = x - 152 by bv_omega]
    apply load_step _ _ _ _ (Int.toBytes 8 (rax.toBitVec + 1).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
    kunfold
    apply Eventually.done
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rax1.toBitVec, q, stk2, Int.toBytes 8 (Host.addrOf (k + 295 + 1)).toBitVec.toInt,
      sp1', sp2', Int.toBytes 8 rax1.toBitVec.toInt, Int.toBytes 8 (rax.toBitVec + 1).toInt,
      Int.toBytes 8 rax.toBitVec.toInt, hstk2, Int.toBytes_length 8 _, hsp1', hsp2', Int.toBytes_length 8 _,
      Int.toBytes_length 8 _, Int.toBytes_length 8 _, ?_⟩
    · exact hi1
    · show (BitVec.ofNat 64 n).toNat = n; simp; omega
    · show (BitVec.ofNat 64 e).toNat = e; simp; omega
    · rfl
    · rfl
    · apply UInt64.toBitVec_inj.mp; simp only [hrsp]; bv_omega
    · dsimp only
      rw [tl_split3 base tl s (4 + 8 * g.l.length) (by omega) (by omega), hpart,
        at_app [4, 0, 0, 0] (u64Bytes g.l).toList (b := base + BitVec.ofNat 64 s + 4) (by rfl)
          (by have : g.l.length ≤ 16 := hg; simp [u64Bytes_size]; omega),
        List.append_assoc, at_app ptrs _ (b := A + BitVec.ofNat 64 (8 * i)) (by rw [hptrs])
          (by simp [hptrs, Int.toBytes_length]; omega),
        at_app (Int.toBytes 8 rax1.toBitVec.toInt) _ (b := A + BitVec.ofNat 64 (8 * i) + 8) (by simp [Int.toBytes_length])
          (by simp [Int.toBytes_length]; omega)]
      simp only [Std.ExtHashMap.sep_assoc] at H8 ⊢
      ecancel

/-- The objects decoded so far, newest first: (p, q, g) is a ListU64 object at
p with header (q, len, len) and the elements at q. -/
def lcObjs : List (BitVec 64 × BitVec 64 × ListU64) → DataMem → Prop
  | [] => Std.ExtHashMap.emp
  | (p, q, g) :: rest => Eq ((Int.toBytes 8 q.toInt).At p) ⋆ Eq ((Int.toBytes 8 (g.l.length : Int)).At (p + 8))
      ⋆ Eq ((Int.toBytes 8 (g.l.length : Int)).At (p + 16)) ⋆ Eq ((u64Bytes g.l).toList.At q) ⋆ lcObjs rest

/-- The items array: one 8-byte pointer per element. -/
def ptrBytes (ps : List (BitVec 64)) : List UInt8 := ps.flatMap fun p => Int.toBytes 8 p.toInt

theorem ptrBytes_length (ps : List (BitVec 64)) : (ptrBytes ps).length = 8 * ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [ptrBytes, Int.toBytes_length] at ih ⊢; omega

theorem ptrBytes_snoc (ps : List (BitVec 64)) (p : BitVec 64) :
    ptrBytes (ps ++ [p]) = ptrBytes ps ++ Int.toBytes 8 p.toInt := by
  simp [ptrBytes]

/-- Start offset of element i: the offset table (4n), then the encodings before i. -/
def lcStart (gs : List ListU64) (i : Nat) : Nat := 4 * gs.length + ((gs.take i).map fun g => 4 + 8 * g.l.length).sum

theorem lcStart_succ (gs : List ListU64) (i : Nat) (hi : i < gs.length) :
    lcStart gs (i + 1) = lcStart gs i + (4 + 8 * gs[i].l.length) := by
  simp only [lcStart, List.take_add_one, List.map_append, List.sum_append, List.getElem?_eq_getElem hi]
  simp; omega

theorem lcStart_le (gs : List ListU64) (i : Nat) : lcStart gs i ≤ lcStart gs gs.length := by
  simp only [lcStart, List.take_length]
  have : ((gs.take i).map fun g => 4 + 8 * g.l.length).sum ≤ (gs.map fun g => 4 + 8 * g.l.length).sum := by
    conv => rhs; rw [← List.take_append_drop i gs]
    rw [List.map_append, List.sum_append]; omega
  omega

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
theorem lcl_exit (k : Nat) (hk : ListCUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListCUnmarshalSSZ k) (P : MachineState → Prop) (s0 : MachineData)
    (hrr : s0.regs.rax = s0.regs.rdx)
    (hP : ∀ f : StatusFlags, P ⟨⟨s0.regs, s0.zmms, f, s0.dmem⟩, Host.addrOf (k + 407)⟩) :
    Eventually (step1 Host.exe) P ⟨s0, Host.addrOf (k + 239)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s0
  dsimp only at hrr
  subst hrr
  kat hk ListCUnmarshalSSZ 239
  kat hk ListCUnmarshalSSZ 240
  kat hk ListCUnmarshalSSZ 241
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
  simp only [Effects.All]
  klabel hk hf ListCUnmarshalSSZ 407
  exact Eventually.done _ (hP _)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
theorem lcl_loop (k : Nat) (hk : ListCUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListCUnmarshalSSZ k)
    (x base recv A : BitVec 64) (tl : List UInt8) (T : Nat) (gs : List ListU64) (hgs : ∀ g ∈ gs, g.ok)
    (hT : tl.length = T) (hn : gs.length ≤ 4) (hT32 : T < 2 ^ 32)
    (hend : lcStart gs gs.length = T)
    (hparts : ∀ i (hi : i < gs.length), (tl.drop (lcStart gs i)).take (4 + 8 * gs[i].l.length)
      = [4, 0, 0, 0] ++ (u64Bytes gs[i].l).toList)
    (hnexts : ∀ i, i + 1 < gs.length → (tl.drop (4 * (i + 1))).take 4 = (uintBytes 4 (lcStart gs (i + 1))).toList)
    (cap0 : Nat) (hcap : T + 4 ≤ cap0) (hcap63 : cap0 < 2 ^ 63)
    (S : Nat) (hS : S < 2 ^ 60) (ra rbp0 guard : UInt64) (Heap : Nat → DataMem → Prop) (R : DataMem → Prop)
    (hguard : guard.toNat + 400 + S < x.toNat) (hx : 400 + S ≤ x.toNat)
    (hno : NewobjectC Heap (label "type__" + 83104).toBitVec 24 (144 + S)) (hlu : LuUAccC Heap S) :
    ∀ j i (s0 : MachineData) (acc : List (BitVec 64 × BitVec 64 × ListU64))
      (blk rslot sp1 sp2 s136 s152 s160 s184 : List UInt8) (avail : Nat),
    i + j = gs.length → acc.length = i → acc.reverse.map (fun t : BitVec 64 × BitVec 64 × ListU64 => t.2.2) = gs.take i →
    blk.length = 144 + S → rslot.length = 8 → sp1.length = 8 → sp2.length = 8 → s136.length = 8 →
    s152.length = 8 → s160.length = 8 → s184.length = 8 → 152 * j ≤ avail →
    s0.regs.rax.toNat = i → s0.regs.rdx.toNat = gs.length → s0.regs.rcx.toNat = lcStart gs i →
    s0.regs.rbx = 0 → s0.regs.rdi = 0 → s0.regs.rsp.toBitVec = x - 8#64 - 216 →
    (s0.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At x) ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (x - 8))
      ⋆ Eq ((Int.toBytes 8 recv.toInt).At (x + 8))
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 cap0).toInt).At (x + 32))
      ⋆ Eq ((Int.toBytes 8 base.toInt).At (x - 128)) ⋆ Eq (s136.At (x - 136))
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 (cap0 - 4)).toInt).At (x - 144))
      ⋆ Eq (s152.At (x - 152)) ⋆ Eq (s160.At (x - 160))
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 gs.length).toInt).At (x - 168))
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 T).toInt).At (x - 176))
      ⋆ Eq (s184.At (x - 184))
      ⋆ Eq (sp1.At (x - 224)) ⋆ Eq (sp2.At (x - 216)) ⋆ Eq (rslot.At (x - 232))
      ⋆ Eq (blk.At (x - 232 - 144 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s0.regs.r14.toBitVec + 16)) ⋆ Heap avail
      ⋆ Eq (tl.At base)
      ⋆ Eq ((Int.toBytes 8 A.toInt).At recv) ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 gs.length).toInt).At (recv + 8))
      ⋆ Eq ((ptrBytes (acc.reverse.map (fun t : BitVec 64 × BitVec 64 × ListU64 => t.1)) ++ List.replicate (8 * (gs.length - i)) 0).At A)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ lcObjs acc ⋆ R) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 407) ∧ st.data.regs.rbx = 0 ∧ st.data.regs.rdi = 0
        ∧ st.data.regs.rsp = s0.regs.rsp ∧ st.data.regs.r14 = s0.regs.r14 ∧
        ∃ (acc' : List (BitVec 64 × BitVec 64 × ListU64)) (avail' : Nat),
          acc'.reverse.map (fun t : BitVec 64 × BitVec 64 × ListU64 => t.2.2) = gs ∧
          (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At x) ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (x - 8))
            ⋆ Eq ((Int.toBytes 8 A.toInt).At recv) ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 gs.length).toInt).At (recv + 8))
            ⋆ Eq ((ptrBytes (acc'.reverse.map (fun t : BitVec 64 × BitVec 64 × ListU64 => t.1))).At A) ⋆ lcObjs acc' ⋆ Eq (tl.At base) ⋆ Heap avail'
            ⋆ R ⋆ fun _ => True) st.data.dmem)
      ⟨s0, Host.addrOf (k + 239)⟩ := by
  intro j
  induction j with
  | zero =>
    intro i s0 acc blk rslot sp1 sp2 s136 s152 s160 s184 avail hij hacc hgsa _ _ _ _ _ _ _ _ _ hrax hrdx _ hrbx hrdi _ h_mem
    have hi : i = gs.length := by omega
    subst hi
    have hacc' : acc.reverse.map (fun t : BitVec 64 × BitVec 64 × ListU64 => t.2.2) = gs := by rw [hgsa, List.take_length]
    refine lcl_exit k hk hf _ s0 (UInt64.toNat_inj.mp (by omega)) fun _ => ⟨rfl, hrbx, hrdi, rfl, rfl, acc, avail, hacc', ?_⟩
    rw [Nat.sub_self, Nat.mul_zero, List.replicate_zero, List.append_nil] at h_mem
    exact sep_true (P := Eq ((Int.toBytes 8 ra.toBitVec.toInt).At x) ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (x - 8))
      ⋆ Eq ((Int.toBytes 8 A.toInt).At recv) ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 gs.length).toInt).At (recv + 8))
      ⋆ Eq ((ptrBytes (acc.reverse.map (fun t : BitVec 64 × BitVec 64 × ListU64 => t.1))).At A) ⋆ lcObjs acc ⋆ Eq (tl.At base) ⋆ Heap avail ⋆ R) (by ecancel)
  | succ j ih =>
    intro i s0 acc blk rslot sp1 sp2 s136 s152 s160 s184 avail hij hacc hgsa hblk hrs hsp1 hsp2 h136 h152 h160 h184 hav
      hrax hrdx hrcx hrbx hrdi hrsp h_mem
    have hi : i < gs.length := by omega
    have hg := hgs gs[i] (List.getElem_mem hi)
    have hse := lcStart_succ gs i hi
    have hle := lcStart_le gs (i + 1)
    refine eventually_trans _ _ _ _ (lcl_iter k hk hf x base recv A tl (ptrBytes (acc.reverse.map (fun t : BitVec 64 × BitVec 64 × ListU64 => t.1))) T
      gs.length i (lcStart gs i) (lcStart gs (i + 1)) gs[i] hg hT hn hi
      (by rw [ptrBytes_length]; simp [hacc]) hse.symm (by omega)
      (by simp only [lcStart]; omega) (hparts i hi) (hnexts i) (fun h => by rw [h, hend]) hT32 cap0 hcap hcap63
      S hS blk rslot sp1 sp2 s136 s152 s160 s184 hblk hrs hsp1 hsp2 h136 h152 h160 h184 ra rbp0 guard Heap avail (by omega)
      (lcObjs acc) R s0 hrax hrdx hrcx hrsp hguard hx h_mem hno hlu) ?_
    rintro ⟨d, pc⟩ ⟨hpc, h1, h2, h3, h4, h5, h6, h7, p, q, blk', rslot', sp1', sp2', s136', s152', s160',
      hb', hr', hs1', hs2', h136', h152', h160', Hm⟩
    dsimp only at hpc h1 h2 h3 h4 h5 h6 h7 Hm
    subst hpc
    have := ih (i + 1) d ((p, q, gs[i]) :: acc) blk' rslot' sp1' sp2' s136' s152' s160'
      (Int.toBytes 8 (BitVec.ofNat 64 (lcStart gs (i + 1))).toInt) (avail - 24 - 8 * gs[i].l.length)
      (by omega) (by simp [hacc])
      (by rw [List.reverse_cons, List.map_append, hgsa, List.take_add_one, List.getElem?_eq_getElem hi]; rfl)
      hb' hr' hs1' hs2' h136' h152' h160' (Int.toBytes_length 8 _) (by have : gs[i].l.length ≤ 16 := hg; omega) h1 h2 h3 h4 h5 (by rw [h6]; exact hrsp)
      (by
        rw [h7]
        simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, ptrBytes_snoc, lcObjs]
        exact Hm)
    refine eventually_trans _ _ _ _ this ?_
    rintro st ⟨g1, g2, g3, g4, g5, g6⟩
    exact Eventually.done _ ⟨g1, g2, g3, by rw [g4, h6], by rw [g5, h7], g6⟩
