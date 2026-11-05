import Fk.LuReject
import Fk.Contracts
import Fk.Frame

/-!
# ListU64.UnmarshalSSZ reject paths through `fmt.errorf`, on Kraken main

- `lu_reject_toobig_main`: offset 4, len = 4 + 8n with n > 16 → the error from
  `fmt.errorf` (contract `FmtErrorfC`: non-nil, rax ≠ 0).
- `lu_reject_misaligned_main`: offset 4, (len − 4) mod 8 ≠ 0 → same.
Both call `runtime.convT64` (contract `ConvT64C`) to box the count, read the
error global (`ssz.ErrListTooBig` / `ssz.ErrIncorrectListSize`, two words, and
the word at itab + 8 when the itab word is non-zero), store X15 (Go ABI: zero)
into the argument array, and return with rsp + 8 and rbp restored; the
receiver is in the frame `R`, kept by the post (not written).
-/

open Fk Fk.Code
variable [Host]

theorem and7_ne (x : BitVec 64) (h4 : 4 ≤ x.toNat) (h : (x.toNat - 4) % 8 ≠ 0) : (-4 + x) &&& 7 ≠ 0#64 := by
  intro h0
  have := congrArg BitVec.toNat h0
  rw [BitVec.toNat_and, BitVec.add_comm, ← BitVec.sub_eq_add_neg,
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega),
    show (7 : BitVec 64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod] at this
  simp at this; omega

theorem and7_zero' (x : BitVec 64) (n : Nat) (h : x.toNat = 4 + 8 * n) : (-4 + x) &&& 7 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.add_comm, ← BitVec.sub_eq_add_neg,
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega),
    show (7 : BitVec 64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp; omega

theorem shr3_toNat' (x : BitVec 64) (n : Nat) (h : x.toNat = 4 + 8 * n) :
    (BitVec.ushiftRight (-4 + x) 3).toNat = n := by
  rw [show (-4 + x).ushiftRight 3 = (-4 + x) >>> 3 from rfl, BitVec.toNat_ushiftRight, BitVec.add_comm,
    ← BitVec.sub_eq_add_neg, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega), Nat.shiftRight_eq_div_pow]
  simp; omega

/-- `cmp $16, a; jg` is taken when `16 < a < 2^62`. -/
theorem jg16_true (a : BitVec 64) (af : Bool) (h : 16 < a.toNat) (h2 : a.toNat < 2 ^ 62) :
    CondCode.g.interp (StatusFlags.from_result (a - 16)
      { cf := BitVec.unsigned (a - 16) != a.unsigned - BitVec.unsigned (16 : BitVec 64), af := af,
        of := BitVec.toInt (a - 16) != a.toInt - BitVec.toInt (16 : BitVec 64) }) = true := by
  have ta : a.toInt = a.toNat := BitVec.toInt_eq_toNat_of_lt (by omega)
  have t16 : BitVec.toInt (16 : BitVec 64) = 16 := by decide
  have hs : (a - 16).toInt = (a.toNat : Int) - 16 := by
    rw [BitVec.toInt_sub, ta, t16]; apply Int.bmod_eq_of_le <;> omega
  have hz : a - 16 ≠ 0#64 := by
    intro h0; have := congrArg BitVec.toNat h0; simp [BitVec.toNat_sub] at this; omega
  have hm : (a - 16).msb = false := by
    rw [BitVec.msb_eq_decide]; simp [BitVec.toNat_sub]; omega
  simp [CondCode.interp, StatusFlags.from_result, ta, t16, hs]
  refine ⟨by simpa using hz, ?_⟩
  rw [show (a - 16#64) = a - 16 from rfl, hm, Int.bmod_eq_of_le (by omega) (by omega)]; simp

/-- A 16-byte AVX store (`movups`) into a separated chunk. -/
theorem store_avx_step (s : MachineData) (addr : BitVec 64) {w : AvxWidth} (v : w.type) (ret : MachineData → Effects)
    (bs : List UInt8) (F : DataMem → Prop) (post : MachineState → Prop)
    (H : (Eq (bs.At addr) ⋆ F) s.dmem) (hl : bs.length = w.bytes) (hw : w.bytes ≤ 2 ^ 64)
    (k : ∀ m', (Eq ((Int.toBytes w.bytes v.toInt).At addr) ⋆ F) m' → (ret { s with dmem := m' }).All post) :
    (MachineData.storeAvx s addr v ret).All post := by
  unfold MachineData.storeAvx
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rw [Effects.All_require_write_access]
  rw [Mem.loadInt_sep bs addr _ F s.dmem H hl hw]
  exact k _ (Mem.storeInt_sep addr w.bytes bs F s.dmem ⟨H, hl⟩ v.toInt)

theorem lr_a72 (x : BitVec 64) : -128 + (x - 8#64) + 64 = x - 72 := by bv_omega
theorem lr_a56 (x : BitVec 64) : x - 72 + 16 = x - 56 := by bv_omega
theorem lr_split16 (bs : List UInt8) (h : bs.length = 16) (a : BitVec 64) :
    Eq (bs.At a) = Eq ((bs.take 8).At a) ⋆ Eq ((bs.drop 8).At (a + 8)) := by
  conv => lhs; rw [← List.take_append_drop 8 bs]
  rw [Mem.At_append_sep _ _ _ (by simp; omega)]; simp [h]
theorem lr_b144 (x o : BitVec 64) : ({ toBitVec := x - 144 } + 8 : UInt64).toBitVec + o = x - 136 + o := by
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
theorem lr_d72 (x : BitVec 64) : x - 72 + 8 = x - 64 := by bv_omega
theorem lr_d56 (x : BitVec 64) : x - 56 + 8 = x - 48 := by bv_omega
theorem lr_c64 (x : BitVec 64) : x - 136 + 64 = x - 72 := by bv_omega
theorem lr_c72 (x : BitVec 64) : x - 136 + 72 = x - 64 := by bv_omega
theorem lr_c80 (x : BitVec 64) : x - 136 + 80 = x - 56 := by bv_omega
theorem lr_c88 (x : BitVec 64) : x - 136 + 88 = x - 48 := by bv_omega
theorem lr_p128 (x : BitVec 64) : ({ toBitVec := x - 144 } + 8 : UInt64).toBitVec - -128 = x - 8 := by
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
theorem lr_c144 (x : BitVec 64) : ({ toBitVec := x - 144 } + 8 : UInt64).toBitVec - 8#64 = x - 144 := by
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega

/-- Four 8-byte words as one argument array (two `any` values). -/
theorem join4 (a b c d : BitVec 64) (A0 A1 A2 A3 : List UInt8) (h0 : A0.length = 8) (h1 : A1.length = 8)
    (h2 : A2.length = 8) (h3 : A3.length = 8) (hb : b = a + 8) (hc : c = a + 16) (hd : d = a + 24) :
    Eq ((A0 ++ (A1 ++ (A2 ++ A3))).At a) = Eq (A0.At a) ⋆ Eq (A1.At b) ⋆ Eq (A2.At c) ⋆ Eq (A3.At d) := by
  rw [at_app A0 _ (b := b) (by rw [h0, hb]; rfl) (by simp [*]), at_app A1 _ (b := c) (by rw [h1, hb, hc]; bv_omega) (by simp [*]),
    at_app A2 A3 (b := d) (by rw [h2, hc, hd]; bv_omega) (by simp [*])]
  simp only [Std.ExtHashMap.sep_assoc]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem lu_reject_toobig_main (k : Nat) (hk : ListU64UnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListU64UnmarshalSSZ k)
    (n : Nat) (hn : 16 < n)
    (s : MachineData) (ra guard e0 e1 t8 : UInt64) (he0 : e0 ≠ 0)
    (fp s98 a40 a50 rslot : List UInt8) (hfp : fp.length = 8) (h98 : s98.length = 8)
    (ha40 : a40.length = 16) (ha50 : a50.length = 16) (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch spl fs : List UInt8) (hsc : scratch.length = S)
    (hspl : spl.length = 40) (hfs : fs.length = 56)
    (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 8 ≤ avail)
    (h_mem : s.dmem =⋆ Eq (spl.At (s.regs.rsp.toBitVec - 136)) ⋆ Eq (fs.At (label "go_string._" + 40290).toBitVec) ⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s98.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (a40.At (s.regs.rsp.toBitVec - 72)) ⋆ Eq (a50.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 144)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq ([4, 0, 0, 0].At s.regs.rbx.toBitVec)
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrListTooBig").toBitVec)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrListTooBig" + 8).toBitVec)
      ⋆ Eq ((Int.toBytes 8 t8.toBitVec.toInt).At (e0.toBitVec + 8)) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat - 8) (hsp : 144 ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rcx.toNat = 4 + 8 * n)
    (hcv : ConvT64C Heap S) (hfe : FmtErrorfC Heap S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax ≠ 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hlen ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size
  simp only [UInt64.size] at *
  kat hk ListU64UnmarshalSSZ 0
  kat hk ListU64UnmarshalSSZ 1
  kat hk ListU64UnmarshalSSZ 2
  kat hk ListU64UnmarshalSSZ 3
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListU64UnmarshalSSZ 4
  split
  case isTrue h =>
    exfalso
    rw [cmp_be_false _ _ _ _ (by rw [toNat_add_neg8 _ (by simp; omega)]; simpa using hguard)] at h
    exact absurd h (by simp)
  simp only [Effects.All]
  kat hk ListU64UnmarshalSSZ 5
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by kaddr) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk ListU64UnmarshalSSZ 6
  kat hk ListU64UnmarshalSSZ 7
  kat hk ListU64UnmarshalSSZ 8
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s98 _ _ (lu_neg8 _) (by ecancel) (by exact h98)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk ListU64UnmarshalSSZ 9
  kat hk ListU64UnmarshalSSZ 10
  kat hk ListU64UnmarshalSSZ 11
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
  simp only [Effects.All]
  kat hk ListU64UnmarshalSSZ 12
  apply load_step_at _ _ rbx.toBitVec _ _ [4, 0, 0, 0] _ _ (by bv_omega) (by ecancel) (by simp)
  simp only [show Int.ofBytes [4, 0, 0, 0] = 4 by simp [Int.ofBytes]]
  kunfold
  kat hk ListU64UnmarshalSSZ 13
  kat hk ListU64UnmarshalSSZ 14
  kat hk ListU64UnmarshalSSZ 15
  kat hk ListU64UnmarshalSSZ 16
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk ListU64UnmarshalSSZ 17
  kat hk ListU64UnmarshalSSZ 18
  kat hk ListU64UnmarshalSSZ 19
  kat hk ListU64UnmarshalSSZ 20
  kshl64 63
  kat hk ListU64UnmarshalSSZ 21
  intro _
  kat hk ListU64UnmarshalSSZ 22
  kat hk ListU64UnmarshalSSZ 23
  kat hk ListU64UnmarshalSSZ 24
  intro _
  kat hk ListU64UnmarshalSSZ 25
  split
  case isTrue h =>
    exfalso; rw [and7_zero' rcx.toBitVec n (by simpa using hlen)] at h
    simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk ListU64UnmarshalSSZ 26
  kshl64 3
  kat hk ListU64UnmarshalSSZ 27
  kat hk ListU64UnmarshalSSZ 28
  have hnN := shr3_toNat' rcx.toBitVec n (by simpa using hlen)
  generalize BitVec.ushiftRight (-4 + rcx.toBitVec) 3 = nV at hnN ⊢
  rw [jg16_true nV _ (by omega) (by omega)]
  simp only [↓reduceIte, Effects.All]
  klabel hk hf ListU64UnmarshalSSZ 52
  kat hk ListU64UnmarshalSSZ 52
  kat hk ListU64UnmarshalSSZ 53
  kat hk ListU64UnmarshalSSZ 54
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  kunfold
  rw [lr_a72]
  apply store_avx_step _ _ _ _ a40 _ _ (by ecancel) (by exact ha40) (by decide)
  intro m3 H3
  kunfold
  kat hk ListU64UnmarshalSSZ 55
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  kunfold
  rw [lr_a56]
  apply store_avx_step _ _ _ _ a50 _ _ (by ecancel) (by exact ha50) (by decide)
  intro m4 H4
  kunfold
  kat hk ListU64UnmarshalSSZ 56
  kat hk ListU64UnmarshalSSZ 57
  kat hk ListU64UnmarshalSSZ 58
  apply store_step_at _ _ (rsp.toBitVec - 144) _ _ _ rslot _ _ (call_slot _) (by ecancel) (by exact hrs)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  rw [call_slot] at *
  have hA : rsp.toBitVec - 144 + 8 = rsp.toBitVec - 136 := by bv_omega
  rw [← List.take_append_drop 8 spl, at_app (spl.take 8) (spl.drop 8) (a := rsp.toBitVec - 136)
    (b := rsp.toBitVec - 128) (by simp [hspl]; bv_omega) (by simp [hspl])] at H5
  refine eventually_trans _ _ _ _ (hcv _ (Host.addrOf (k + 58 + 1)) avail scratch (spl.take 8) _ hav hsc
    (by simp [hspl]) (by dsimp only; rw [hA]; ecancel)) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hr141, hrax1, stk1, sp1, av1, hstk1, hsp1, hav1, hav1', Hm1⟩
  dsimp only at hpc1 hrsp1 Hm1
  subst hpc1
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩,
    zmms1, flags1, mem1⟩ := d1
  simp only at hrsp1 Hm1
  rw [hA] at Hm1
  subst hrsp1
  rw [lr_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 72), lr_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 56)] at Hm1
  rw [lr_d72, lr_d56] at Hm1
  kat hk ListU64UnmarshalSSZ 59
  kat hk ListU64UnmarshalSSZ 60
  rw [lr_b144, lr_c64]
  apply store_step _ _ _ _ _ ((Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).take 8) _ _ (by ecancel) (by simp [Int.toBytes_length])
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  kat hk ListU64UnmarshalSSZ 61
  rw [lr_b144, lr_c72]
  apply store_step _ _ _ _ _ ((Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8) _ _ (by ecancel) (by simp [Int.toBytes_length])
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  kat hk ListU64UnmarshalSSZ 62
  apply load_step _ _ _ _ (Int.toBytes 8 e0.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListU64UnmarshalSSZ 63
  kat hk ListU64UnmarshalSSZ 64
  intro _
  kat hk ListU64UnmarshalSSZ 65
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    exact he0 (UInt64.toBitVec_inj.mp (by simpa using h))
  simp only [Effects.All]
  kat hk ListU64UnmarshalSSZ 66
  apply load_step _ _ _ _ (Int.toBytes 8 t8.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListU64UnmarshalSSZ 67
  kat hk ListU64UnmarshalSSZ 68
  apply load_step _ _ _ _ (Int.toBytes 8 e1.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListU64UnmarshalSSZ 69
  rw [lr_b144, lr_c80]
  apply store_step _ _ _ _ _ ((Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).take 8) _ _ (by ecancel) (by simp [Int.toBytes_length])
  intro m8 H8
  simp only [Width.bytes, Width.bits] at H8
  kunfold
  kat hk ListU64UnmarshalSSZ 70
  rw [lr_b144, lr_c88]
  apply store_step _ _ _ _ _ ((Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8) _ _ (by ecancel) (by simp [Int.toBytes_length])
  intro m9 H9
  simp only [Width.bytes, Width.bits] at H9
  kunfold
  kat hk ListU64UnmarshalSSZ 71
  kat hk ListU64UnmarshalSSZ 72
  kat hk ListU64UnmarshalSSZ 73
  kat hk ListU64UnmarshalSSZ 74
  kat hk ListU64UnmarshalSSZ 75
  kat hk ListU64UnmarshalSSZ 76
  apply store_step_at _ _ (rsp.toBitVec - 144) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 58 + 1)).toBitVec.toInt) _ _
    (lr_c144 _) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m10 H10
  simp only [Width.bytes, Width.bits] at H10
  kunfold
  rw [lr_c144] at *
  rw [← hA] at H10
  refine eventually_trans _ _ _ _ (hfe _ (Host.addrOf (k + 76 + 1)) av1 fs
    (Int.toBytes 8 (label "type__" + 49184).toBitVec.toInt ++ (Int.toBytes 8 rax1.toBitVec.toInt
      ++ (Int.toBytes 8 t8.toBitVec.toInt ++ Int.toBytes 8 e1.toBitVec.toInt)))
    stk1 (sp1 ++ spl.drop 8) _ (by rw [hfs]; rfl) (by simp only []; decide) rfl (by simp only [List.length_append, Int.toBytes_length]; decide) hstk1 (by simp [hsp1, hspl])
    (by dsimp only
        try simp only [lr_b144, lr_c64]
        rw [at_app sp1 (spl.drop 8) (b := rsp.toBitVec - 128) (by rw [hsp1]; bv_omega) (by simp [hsp1, hspl]),
          join4 (rsp.toBitVec - 72) (rsp.toBitVec - 64) (rsp.toBitVec - 56) (rsp.toBitVec - 48) _ _ _ _ (Int.toBytes_length 8 _)
            (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) (by bv_omega) (by bv_omega) (by bv_omega)]
        ecancel)) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrsp2, hr142, hrax2, stk2, sp2, av2, hstk2, hsp2, hav2, Hm2⟩
  dsimp only at hpc2 hrsp2 hrax2 Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := d2
  simp only at hrsp2 hrax2 Hm2
  subst hrsp2
  kat hk ListU64UnmarshalSSZ 77
  intro _
  kat hk ListU64UnmarshalSSZ 78
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    exact hrax2 (UInt64.toBitVec_inj.mp (by simpa using h))
  simp only [Effects.All]
  klabel hk hf ListU64UnmarshalSSZ 87
  kat hk ListU64UnmarshalSSZ 87
  kat hk ListU64UnmarshalSSZ 88
  kat hk ListU64UnmarshalSSZ 89
  rw [lr_p128]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListU64UnmarshalSSZ 90
  rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨trivial, hrax2, ?_, ?_, ?_⟩
  · apply UInt64.toBitVec_inj.mp; simp
  · first | trivial | rfl
  · have : (R ⋆ fun _ => True) mem2 := sep_true (by ecancel)
    exact this

theorem lr_e40 (x : BitVec 64) : -128 + (x - 8#64) + 96 = x - 40 := by bv_omega
theorem lr_e24 (x : BitVec 64) : x - 40 + 16 = x - 24 := by bv_omega
theorem lr_f40 (x : BitVec 64) : x - 40 + 8 = x - 32 := by bv_omega
theorem lr_f24 (x : BitVec 64) : x - 24 + 8 = x - 16 := by bv_omega
theorem lr_g96 (x : BitVec 64) : x - 136 + 96 = x - 40 := by bv_omega
theorem lr_g104 (x : BitVec 64) : x - 136 + 104 = x - 32 := by bv_omega
theorem lr_g112 (x : BitVec 64) : x - 136 + 112 = x - 24 := by bv_omega
theorem lr_g120 (x : BitVec 64) : x - 136 + 120 = x - 16 := by bv_omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem lu_reject_misaligned_main (k : Nat) (hk : ListU64UnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListU64UnmarshalSSZ k)
    (s : MachineData) (ra guard e0 e1 t8 : UInt64) (he0 : e0 ≠ 0)
    (fp s98 a40 a50 rslot : List UInt8) (hfp : fp.length = 8) (h98 : s98.length = 8)
    (ha40 : a40.length = 16) (ha50 : a50.length = 16) (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch spl fs : List UInt8) (hsc : scratch.length = S)
    (hspl : spl.length = 40) (hfs : fs.length = 68)
    (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 8 ≤ avail)
    (h_mem : s.dmem =⋆ Eq (spl.At (s.regs.rsp.toBitVec - 136)) ⋆ Eq (fs.At (label "go_string._" + 42646).toBitVec) ⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s98.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (a40.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (a50.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 144)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq ([4, 0, 0, 0].At s.regs.rbx.toBitVec)
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrIncorrectListSize").toBitVec)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrIncorrectListSize" + 8).toBitVec)
      ⋆ Eq ((Int.toBytes 8 t8.toBitVec.toInt).At (e0.toBitVec + 8)) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat - 8) (hsp : 144 ≤ s.regs.rsp.toNat)
    (hlen : 4 ≤ s.regs.rcx.toNat) (hmis : (s.regs.rcx.toNat - 4) % 8 ≠ 0)
    (hcv : ConvT64C Heap S) (hfe : FmtErrorfC Heap S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax ≠ 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hlen hmis ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size
  simp only [UInt64.size] at *
  kat hk ListU64UnmarshalSSZ 0
  kat hk ListU64UnmarshalSSZ 1
  kat hk ListU64UnmarshalSSZ 2
  kat hk ListU64UnmarshalSSZ 3
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListU64UnmarshalSSZ 4
  split
  case isTrue h =>
    exfalso
    rw [cmp_be_false _ _ _ _ (by rw [toNat_add_neg8 _ (by simp; omega)]; simpa using hguard)] at h
    exact absurd h (by simp)
  simp only [Effects.All]
  kat hk ListU64UnmarshalSSZ 5
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by kaddr) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk ListU64UnmarshalSSZ 6
  kat hk ListU64UnmarshalSSZ 7
  kat hk ListU64UnmarshalSSZ 8
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s98 _ _ (lu_neg8 _) (by ecancel) (by exact h98)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk ListU64UnmarshalSSZ 9
  kat hk ListU64UnmarshalSSZ 10
  kat hk ListU64UnmarshalSSZ 11
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
  simp only [Effects.All]
  kat hk ListU64UnmarshalSSZ 12
  apply load_step_at _ _ rbx.toBitVec _ _ [4, 0, 0, 0] _ _ (by bv_omega) (by ecancel) (by simp)
  simp only [show Int.ofBytes [4, 0, 0, 0] = 4 by simp [Int.ofBytes]]
  kunfold
  kat hk ListU64UnmarshalSSZ 13
  kat hk ListU64UnmarshalSSZ 14
  kat hk ListU64UnmarshalSSZ 15
  kat hk ListU64UnmarshalSSZ 16
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk ListU64UnmarshalSSZ 17
  kat hk ListU64UnmarshalSSZ 18
  kat hk ListU64UnmarshalSSZ 19
  kat hk ListU64UnmarshalSSZ 20
  kshl64 63
  kat hk ListU64UnmarshalSSZ 21
  intro _
  kat hk ListU64UnmarshalSSZ 22
  kat hk ListU64UnmarshalSSZ 23
  kat hk ListU64UnmarshalSSZ 24
  intro _
  kat hk ListU64UnmarshalSSZ 25
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    exact and7_ne rcx.toBitVec (by simpa using hlen) (by simpa using hmis) h
  simp only [Effects.All]
  klabel hk hf ListU64UnmarshalSSZ 91
  kat hk ListU64UnmarshalSSZ 91
  kat hk ListU64UnmarshalSSZ 92
  kat hk ListU64UnmarshalSSZ 93
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  kunfold
  rw [lr_e40]
  apply store_avx_step _ _ _ _ a40 _ _ (by ecancel) (by exact ha40) (by decide)
  intro m3 H3
  kunfold
  kat hk ListU64UnmarshalSSZ 94
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  kunfold
  rw [lr_e24]
  apply store_avx_step _ _ _ _ a50 _ _ (by ecancel) (by exact ha50) (by decide)
  intro m4 H4
  kunfold
  kat hk ListU64UnmarshalSSZ 95
  kat hk ListU64UnmarshalSSZ 96
  kat hk ListU64UnmarshalSSZ 97
  apply store_step_at _ _ (rsp.toBitVec - 144) _ _ _ rslot _ _ (call_slot _) (by ecancel) (by exact hrs)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  rw [call_slot] at *
  have hA : rsp.toBitVec - 144 + 8 = rsp.toBitVec - 136 := by bv_omega
  rw [← List.take_append_drop 8 spl, at_app (spl.take 8) (spl.drop 8) (a := rsp.toBitVec - 136)
    (b := rsp.toBitVec - 128) (by simp [hspl]; bv_omega) (by simp [hspl])] at H5
  refine eventually_trans _ _ _ _ (hcv _ (Host.addrOf (k + 97 + 1)) avail scratch (spl.take 8) _ hav hsc
    (by simp [hspl]) (by dsimp only; rw [hA]; ecancel)) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hr141, hrax1, stk1, sp1, av1, hstk1, hsp1, hav1, hav1', Hm1⟩
  dsimp only at hpc1 hrsp1 Hm1
  subst hpc1
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩,
    zmms1, flags1, mem1⟩ := d1
  simp only at hrsp1 Hm1
  rw [hA] at Hm1
  subst hrsp1
  rw [lr_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 40), lr_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 24)] at Hm1
  rw [lr_f40, lr_f24] at Hm1
  kat hk ListU64UnmarshalSSZ 98
  kat hk ListU64UnmarshalSSZ 99
  rw [lr_b144, lr_g96]
  apply store_step _ _ _ _ _ ((Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).take 8) _ _ (by ecancel) (by simp [Int.toBytes_length])
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  kat hk ListU64UnmarshalSSZ 100
  rw [lr_b144, lr_g104]
  apply store_step _ _ _ _ _ ((Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8) _ _ (by ecancel) (by simp [Int.toBytes_length])
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  kat hk ListU64UnmarshalSSZ 101
  apply load_step _ _ _ _ (Int.toBytes 8 e0.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListU64UnmarshalSSZ 102
  kat hk ListU64UnmarshalSSZ 103
  intro _
  kat hk ListU64UnmarshalSSZ 104
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    exact he0 (UInt64.toBitVec_inj.mp (by simpa using h))
  simp only [Effects.All]
  kat hk ListU64UnmarshalSSZ 105
  apply load_step _ _ _ _ (Int.toBytes 8 t8.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListU64UnmarshalSSZ 106
  kat hk ListU64UnmarshalSSZ 107
  apply load_step _ _ _ _ (Int.toBytes 8 e1.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListU64UnmarshalSSZ 108
  rw [lr_b144, lr_g112]
  apply store_step _ _ _ _ _ ((Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).take 8) _ _ (by ecancel) (by simp [Int.toBytes_length])
  intro m8 H8
  simp only [Width.bytes, Width.bits] at H8
  kunfold
  kat hk ListU64UnmarshalSSZ 109
  rw [lr_b144, lr_g120]
  apply store_step _ _ _ _ _ ((Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8) _ _ (by ecancel) (by simp [Int.toBytes_length])
  intro m9 H9
  simp only [Width.bytes, Width.bits] at H9
  kunfold
  kat hk ListU64UnmarshalSSZ 110
  kat hk ListU64UnmarshalSSZ 111
  kat hk ListU64UnmarshalSSZ 112
  kat hk ListU64UnmarshalSSZ 113
  kat hk ListU64UnmarshalSSZ 114
  kat hk ListU64UnmarshalSSZ 115
  apply store_step_at _ _ (rsp.toBitVec - 144) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 97 + 1)).toBitVec.toInt) _ _
    (lr_c144 _) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m10 H10
  simp only [Width.bytes, Width.bits] at H10
  kunfold
  rw [lr_c144] at *
  rw [← hA] at H10
  refine eventually_trans _ _ _ _ (hfe _ (Host.addrOf (k + 115 + 1)) av1 fs
    (Int.toBytes 8 (label "type__" + 49184).toBitVec.toInt ++ (Int.toBytes 8 rax1.toBitVec.toInt
      ++ (Int.toBytes 8 t8.toBitVec.toInt ++ Int.toBytes 8 e1.toBitVec.toInt)))
    stk1 (sp1 ++ spl.drop 8) _ (by rw [hfs]; rfl) (by simp only []; decide) rfl (by simp only [List.length_append, Int.toBytes_length]; decide) hstk1 (by simp [hsp1, hspl])
    (by dsimp only
        try simp only [lr_b144, lr_g96]
        rw [at_app sp1 (spl.drop 8) (b := rsp.toBitVec - 128) (by rw [hsp1]; bv_omega) (by simp [hsp1, hspl]),
          join4 (rsp.toBitVec - 40) (rsp.toBitVec - 32) (rsp.toBitVec - 24) (rsp.toBitVec - 16) _ _ _ _ (Int.toBytes_length 8 _)
            (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) (by bv_omega) (by bv_omega) (by bv_omega)]
        ecancel)) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrsp2, hr142, hrax2, stk2, sp2, av2, hstk2, hsp2, hav2, Hm2⟩
  dsimp only at hpc2 hrsp2 hrax2 Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := d2
  simp only at hrsp2 hrax2 Hm2
  subst hrsp2
  kat hk ListU64UnmarshalSSZ 116
  intro _
  kat hk ListU64UnmarshalSSZ 117
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    exact hrax2 (UInt64.toBitVec_inj.mp (by simpa using h))
  simp only [Effects.All]
  klabel hk hf ListU64UnmarshalSSZ 126
  kat hk ListU64UnmarshalSSZ 126
  kat hk ListU64UnmarshalSSZ 127
  kat hk ListU64UnmarshalSSZ 128
  rw [lr_p128]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListU64UnmarshalSSZ 129
  rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨trivial, hrax2, ?_, ?_, ?_⟩
  · apply UInt64.toBitVec_inj.mp; simp
  · first | trivial | rfl
  · have : (R ⋆ fun _ => True) mem2 := sep_true (by ecancel)
    exact this
