import Fk.LcAccept
import Fk.LuRejectCall

/-!
# ListC.UnmarshalSSZ, element offset order reject (fix 3 X5)

In the element loop (iteration `i`, not the last), the next offset `e` (bytes
`4(i+1)..`) is below the current start `s`: directives 276–277 (`cmp %r11,%rsi;
jb`) jump to the reject block, which boxes `e` and `s` with `runtime.convT64`
and returns `fmt.Errorf("offset %d is not greater than start offset %d …",
e, s)` (the format `Fk.Data.lcFmtOrder`, contract `FmtErrorfDDC`). The block
writes the 32-byte argument array at `x - 104` and uses the callee spill area
`x - 224 .. x - 184`: these slots are premises here (not of `lc_accept_main`).
-/

open Fk Fk.Code Fv1 EthLib.Serialization.Ssz
variable [Host]

theorem jb_true (a b : BitVec 64) (af of' : Bool) (h : a.toNat < b.toNat) :
    CondCode.c.interp (StatusFlags.from_result (a - b)
      { cf := BitVec.unsigned (a - b) != a.unsigned - b.unsigned, af := af, of := of' }) = true := by
  have hb := b.isLt
  have hs : (a - b).toNat = 2 ^ 64 - b.toNat + a.toNat := by rw [BitVec.toNat_sub]; omega
  simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, hs]
  simp; omega

theorem lcFmtOrder_len : lcFmtOrder.length = 67 := by rfl

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
theorem lcl_order (k : Nat) (hk : ListCUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListCUnmarshalSSZ k)
    (x base recv A : BitVec 64) (tl ptrs : List UInt8) (T n i s e : Nat)
    (hT : tl.length = T) (hn : n ≤ 4) (hi : i + 1 < n) (hptrs : ptrs.length = 8 * i)
    (hes : e < s) (hs4 : 4 * n ≤ s) (hsT : s ≤ T)
    (hnext : i + 1 < n → (tl.drop (4 * (i + 1))).take 4 = (uintBytes 4 e).toList)
    (hT32 : T < 2 ^ 32) (cap0 : Nat) (hcap : T + 4 ≤ cap0) (hcap63 : cap0 < 2 ^ 63)
    (S : Nat) (hS : S < 2 ^ 60) (blk rslot sp1 sp2 sp3 s200 s192 s136 s152 s160 s184 a0 a1 : List UInt8)
    (hblk : blk.length = 144 + S) (hrs : rslot.length = 8) (hsp1 : sp1.length = 8) (hsp2 : sp2.length = 8)
    (hsp3 : sp3.length = 8) (h200 : s200.length = 8) (h192 : s192.length = 8)
    (h136 : s136.length = 8) (h152 : s152.length = 8) (h160 : s160.length = 8) (h184 : s184.length = 8)
    (ha0 : a0.length = 16) (ha1 : a1.length = 16)
    (ra rbp0 guard : UInt64) (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 24 + 16 + 67 + 40 + 8192 ≤ avail)
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
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
      ⋆ Eq (sp3.At (x - 208)) ⋆ Eq (s200.At (x - 200)) ⋆ Eq (s192.At (x - 192))
      ⋆ Eq (a0.At (x - 104)) ⋆ Eq (a1.At (x - 88)) ⋆ Eq (lcFmtOrder.At lcFmtOrder_addr)
      ⋆ StaticBox (BitVec.ofNat 64 e) ⋆ StaticBox (BitVec.ofNat 64 s) ⋆ O ⋆ R)
    (hno : NewobjectC Heap (label "type__" + 83104).toBitVec 24 (144 + S))
    (hcv : ConvT64C Heap (144 + S)) (hfe : FmtErrorfDDC Heap lcFmtOrder uint64Type_addr (144 + S)) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax ≠ 0
        ∧ st.data.regs.rsp.toBitVec = x + 8 ∧ st.data.regs.rbp = rbp0 ∧ (R ⋆ fun _ => True) st.data.dmem)
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
  have hl : ¬ (i + 1 = n) := by omega
  split
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
  rw [jb_true _ _ _ _ (by simp; omega)]
  simp only [↓reduceIte, Effects.All]
  klabel hk hf ListCUnmarshalSSZ 371
  kat hk ListCUnmarshalSSZ 371
  kat hk ListCUnmarshalSSZ 372
  kat hk ListCUnmarshalSSZ 373
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  kunfold
  rw [lcl_g, show x - 224 + 120 = x - 104 by bv_omega]
  apply store_avx_step _ _ _ _ a0 _ _ (by ecancel) (by exact ha0) (by decide)
  intro m6 H6
  kunfold
  kat hk ListCUnmarshalSSZ 374
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  kunfold
  rw [show x - 104 + 16 = x - 88 by bv_omega]
  apply store_avx_step _ _ _ _ a1 _ _ (by ecancel) (by exact ha1) (by decide)
  intro m7 H7
  kunfold
  kat hk ListCUnmarshalSSZ 375
  kat hk ListCUnmarshalSSZ 376
  kat hk ListCUnmarshalSSZ 377
  apply store_step_at _ _ (x - 232) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 246 + 1)).toBitVec.toInt) _ _
    (lcl_call _) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m8 H8
  simp only [Width.bytes, Width.bits] at H8
  kunfold
  rw [lcl_call] at *
  refine eventually_trans _ _ _ _ (hcv _ (Host.addrOf (k + 377 + 1)) (avail - 24) stk1 sn1 _ (by omega) hstk1 hsn1
    (by dsimp only; rw [lcl_blk, hspA]; ecancel)) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrsp2, hr142, stk2, sn2, hb1, av1, hstk2, hsn2, hbox1, hav1, hav1', Hm2⟩
  dsimp only at hpc2 hrsp2 Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := d2
  simp only at hrsp2 Hm2
  subst hrsp2
  rw [lcl_blk, hspA] at Hm2
  rw [lr_split16 _ (Int.toBytes_length 16 _) (x - 104), lr_split16 _ (Int.toBytes_length 16 _) (x - 88)] at Hm2
  kat hk ListCUnmarshalSSZ 378
  kat hk ListCUnmarshalSSZ 379
  rw [lcl_g, show x - 224 + 120 = x - 104 by bv_omega]
  apply store_step _ _ _ _ _ ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).take 8) _ _ (by ecancel) (by simp [Int.toBytes_length])
  intro m9 H9
  simp only [Width.bytes, Width.bits] at H9
  kunfold
  kat hk ListCUnmarshalSSZ 380
  rw [lcl_g, show x - 224 + 128 = x - 104 + 8 by bv_omega]
  apply store_step _ _ _ _ _ ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8) _ _ (by ecancel) (by simp [Int.toBytes_length])
  intro m10 H10
  simp only [Width.bytes, Width.bits] at H10
  kunfold
  kat hk ListCUnmarshalSSZ 381
  rw [lcl_g, show x - 224 + 40 = x - 184 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rcx.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk ListCUnmarshalSSZ 382
  kat hk ListCUnmarshalSSZ 383
  apply store_step_at _ _ (x - 232) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 377 + 1)).toBitVec.toInt) _ _
    (lcl_call _) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m11 H11
  simp only [Width.bytes, Width.bits] at H11
  kunfold
  rw [lcl_call] at *
  have hrcxs : rcx.toBitVec = BitVec.ofNat 64 s := by apply BitVec.eq_of_toNat_eq; simp; omega
  refine eventually_trans _ _ _ _ (hcv _ (Host.addrOf (k + 383 + 1)) av1 stk2 sn2 _ (by omega) hstk2 hsn2
    (by dsimp only; rw [lcl_blk, hspA, staticBox_congr hrcxs]; ecancel)) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrsp3, hr143, stk3, sn3, hb2, av2, hstk3, hsn3, hbox2, hav2, hav2', Hm3⟩
  dsimp only at hpc3 hrsp3 Hm3
  subst hpc3
  obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,
    zmms3, flags3, mem3⟩ := d3
  simp only at hrsp3 Hm3
  subst hrsp3
  rw [lcl_blk, hspA, staticBox_congr hrcxs] at Hm3
  kat hk ListCUnmarshalSSZ 384
  kat hk ListCUnmarshalSSZ 385
  rw [lcl_g, show x - 224 + 136 = x - 88 by bv_omega]
  apply store_step _ _ _ _ _ ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).take 8) _ _ (by ecancel) (by simp [Int.toBytes_length])
  intro m12 H12
  simp only [Width.bytes, Width.bits] at H12
  kunfold
  kat hk ListCUnmarshalSSZ 386
  rw [lcl_g, show x - 224 + 144 = x - 88 + 8 by bv_omega]
  apply store_step _ _ _ _ _ ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8) _ _ (by ecancel) (by simp [Int.toBytes_length])
  intro m13 H13
  simp only [Width.bytes, Width.bits] at H13
  kunfold
  kat hk ListCUnmarshalSSZ 387
  kat hk ListCUnmarshalSSZ 388
  kat hk ListCUnmarshalSSZ 389
  kat hk ListCUnmarshalSSZ 390
  kat hk ListCUnmarshalSSZ 391
  kat hk ListCUnmarshalSSZ 392
  apply store_step_at _ _ (x - 232) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 383 + 1)).toBitVec.toInt) _ _
    (lcl_call _) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m14 H14
  simp only [Width.bytes, Width.bits] at H14
  kunfold
  rw [lcl_call] at *
  simp only [lcFmtOrder_addr] at H14
  refine eventually_trans _ _ _ _ (hfe _ (Host.addrOf (k + 392 + 1)) av2 hb1 hb2 stk3 (sn3 ++ (sp2 ++ (sp3 ++ (s200 ++ s192))))
    rax2.toBitVec (BitVec.ofNat 64 e) rax3.toBitVec (BitVec.ofNat 64 s) _
    (by rw [lcFmtOrder_len]; rfl) (by first | rfl | decide) (by first | rfl | decide)
    hbox1 (hrcxs ▸ hbox2) hstk3 (by simp [hsn3, hsp2, hsp3, h200, h192]) (by rw [lcFmtOrder_len]; omega)
    (by dsimp only
        simp only [uint64Type_addr, List.append_assoc]
        rw [lcl_g, show x - 224 + 120 = x - 104 by bv_omega,
          at_app sn3 _ (b := x - 216) (by rw [hsn3]; bv_omega) (by simp [hsn3, hsp2, hsp3, h200, h192]),
          join4 (x - 216) (x - 208) (x - 200) (x - 192) _ _ _ _ hsp2 hsp3 h200 h192 (by bv_omega) (by bv_omega) (by bv_omega),
          join4 (x - 104) (x - 104 + 8) (x - 88) (x - 88 + 8) _ _ _ _ (Int.toBytes_length 8 _)
            (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) (by bv_omega) (by bv_omega) (by bv_omega),
          lcl_blk, hspA]
        ecancel)) ?_
  rintro ⟨d4, pc4⟩ ⟨hpc4, hrsp4, hr144, hrax4, stk4, sp4, av4, hstk4, hsp4, hav4, Hm4⟩
  dsimp only at hpc4 hrsp4 hrax4 Hm4
  subst hpc4
  obtain ⟨⟨rax4, rbx4, rcx4, rdx4, rsi4, rdi4, rsp4, rbp4, r84, r94, r104, r114, r124, r134, r144, r154⟩,
    zmms4, flags4, mem4⟩ := d4
  simp only at hrsp4 hrax4 Hm4
  subst hrsp4
  kat hk ListCUnmarshalSSZ 393
  intro _
  kat hk ListCUnmarshalSSZ 394
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    exact hrax4 (UInt64.toBitVec_inj.mp (by simpa using h))
  simp only [Effects.All]
  klabel hk hf ListCUnmarshalSSZ 403
  kat hk ListCUnmarshalSSZ 403
  kat hk ListCUnmarshalSSZ 404
  kat hk ListCUnmarshalSSZ 405
  rw [show (216 : BitVec 64) + ({ toBitVec := x - 232 } + 8 : UInt64).toBitVec = x - 8 by
    simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp0.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListCUnmarshalSSZ 406
  rw [show x - 8 + 8#64 = x by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨trivial, hrax4, ?_, ?_, ?_⟩
  · first | (simp; done) | (simp; bv_omega)
  · first | trivial | rfl | (apply UInt64.toBitVec_inj.mp; simp)
  · exact sep_true (by ecancel)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
/-- **ListC element offset order reject** (fix 3 X5, astra fix 2 required 7).
Input `buf = offset 4 ‖ tl` with `n` elements (2 ≤ n ≤ 4): the first element
offset is `4n` (`hfirst`), the second offset `e` (`hsecond`) is below it. The
decoder allocates the element slice (`makeslice`), enters the element loop,
allocates element 0 (`newobject`) and, at directives 276–277, rejects: two
`convT64` boxes and `fmt.errorf` with `lcFmtOrder`, a non-nil error (rax ≠ 0).
Premises beyond `lc_accept_main`'s frame: the argument array (`rsp − 104`,
32 bytes), the spill slots `rsp − 200`, `rsp − 192`, the format bytes and the
two static boxes. -/
theorem lc_reject_offset_order_main (k : Nat) (hk : ListCUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListCUnmarshalSSZ k)
    (tl : List UInt8) (T n e : Nat) (hT : tl.length = T) (hn2 : 2 ≤ n) (hn : n ≤ 4) (hT32 : T < 2 ^ 32)
    (hle4n : 4 * n ≤ T) (he : e < 4 * n)
    (hfirst : tl.take 4 = (uintBytes 4 (4 * n)).toList)
    (hsecond : (tl.drop 4).take 4 = (uintBytes 4 e).toList)
    (s : MachineData) (ra guard : UInt64) (fp slot s8 s32 l128 l136 l144 l152 l160 l168 l176 l184 l192 l200 l208 l216 l224
      rslot blk cP cL cC a0 a1 : List UInt8)
    (hfp : fp.length = 8) (hsl : slot.length = 8) (h8 : s8.length = 8) (h32 : s32.length = 8)
    (hl128 : l128.length = 8) (hl136 : l136.length = 8) (hl144 : l144.length = 8) (hl152 : l152.length = 8)
    (hl160 : l160.length = 8) (hl168 : l168.length = 8) (hl176 : l176.length = 8) (hl184 : l184.length = 8)
    (hl192 : l192.length = 8) (hl200 : l200.length = 8)
    (hl208 : l208.length = 8) (hl216 : l216.length = 8) (hl224 : l224.length = 8) (hrs : rslot.length = 8)
    (hcP : cP.length = 8) (hcL : cL.length = 8) (hcC : cC.length = 8) (ha0 : a0.length = 16) (ha1 : a1.length = 16)
    (S : Nat) (hS : S < 2 ^ 60) (hblk : blk.length = 144 + S)
    (R : DataMem → Prop) (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 32 + 24 + 16 + 67 + 40 + 8192 ≤ avail)
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
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
      ⋆ Eq (l200.At (s.regs.rsp.toBitVec - 200)) ⋆ Eq (l192.At (s.regs.rsp.toBitVec - 192))
      ⋆ Eq (a0.At (s.regs.rsp.toBitVec - 104)) ⋆ Eq (a1.At (s.regs.rsp.toBitVec - 88))
      ⋆ Eq (lcFmtOrder.At lcFmtOrder_addr)
      ⋆ StaticBox (BitVec.ofNat 64 e) ⋆ StaticBox (BitVec.ofNat 64 (4 * n)) ⋆ R)
    (hguard : guard.toNat + 400 + S < s.regs.rsp.toNat) (hsp : 400 + S ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rcx.toNat = 4 + T) (hcap : s.regs.rcx.toNat ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hms : MakesliceC Heap (label "type__" + 114368).toBitVec 8 (144 + S))
    (hno : NewobjectC Heap (label "type__" + 83104).toBitVec 24 (144 + S))
    (hcv : ConvT64C Heap (144 + S)) (hfe : FmtErrorfDDC Heap lcFmtOrder uint64Type_addr (144 + S)) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax ≠ 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ (R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  have hT4 : 4 ≤ T := by omega
  have ho4 : (tl.take 4).length = 4 := by simp; omega
  have hoff : Int.ofBytes (tl.take 4) = ((4 * n : Nat) : Int) := by
    rw [hfirst, ofBytes_uintBytes4 _ (by omega)]
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
  have ho32 : 4 * n < 2 ^ 32 := by
    omega
  rw [zx_o (4 * n) ho32]
  kat hk ListCUnmarshalSSZ 32
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    have := congrArg BitVec.toNat h; simp at this; omega
  simp only [Effects.All]
  kat hk ListCUnmarshalSSZ 33
  kat hk ListCUnmarshalSSZ 34
  intro _
  rw [and3_zero (4 * n) ho32 (by omega)]
  kat hk ListCUnmarshalSSZ 35
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk ListCUnmarshalSSZ 36
  kat hk ListCUnmarshalSSZ 37
  kshl64 2
  rw [shr2_o (4 * n) ho32]
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
  have hn4 : 4 * n / 4 = n := by omega
  rw [hn4]
  have hsp3 : ∀ (a b c : List UInt8), a.length = 8 → b.length = 8 → c.length = 8 →
      Eq ((a ++ (b ++ c)).At (rsp.toBitVec - 232 + 8)) = Eq (a.At (rsp.toBitVec - 224)) ⋆ Eq (b.At (rsp.toBitVec - 216))
        ⋆ Eq (c.At (rsp.toBitVec - 208)) := by
    intro a b c ha hb hc
    rw [at_app a _ (b := rsp.toBitVec - 216) (by rw [ha]; bv_omega) (by simp [*]),
      at_app b c (b := rsp.toBitVec - 208) (by rw [hb]; bv_omega) (by simp [*]), show rsp.toBitVec - 232 + 8 = rsp.toBitVec - 224 by bv_omega]
    simp only [Std.ExtHashMap.sep_assoc]
  refine eventually_trans _ _ _ _ (hms _ (Host.addrOf (k + 75 + 1)) n avail blk (l224 ++ (l216 ++ l208)) _ rfl
    (by show (BitVec.ofNat 64 n).toNat ≤ _; simp; omega)
    (by show (BitVec.ofNat 64 n).toNat = _; simp; omega) (by omega) (by unfold maxAlloc; omega) (by omega) hblk
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
  apply load_step _ _ _ _ (Int.toBytes 8 (BitVec.ofNat 64 n).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
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
  apply load_step _ _ _ _ (Int.toBytes 8 (BitVec.ofNat 64 (4 * n)).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
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
  have htl : Eq (tl.At (rbx.toBitVec + 4)) = Eq ((tl.take 4).At (rbx.toBitVec + 4))
      ⋆ Eq ((tl.drop 4).At (rbx.toBitVec + 4 + 4)) := by
    conv => lhs; rw [← List.take_append_drop 4 tl]
    exact at_app _ _ (by rw [List.length_take, Nat.min_eq_left (by omega)]; rfl) (by simp; omega)
  refine eventually_trans _ _ _ _ (lcl_order k hk hf rsp.toBitVec (rbx.toBitVec + 4) rax.toBitVec rax1.toBitVec tl []
    T n 0 (4 * n) e hT hn (by omega) rfl he (Nat.le_refl _) hle4n (fun _ => by simpa using hsecond) hT32
    rdi.toBitVec.toNat (by simp; omega) (by simpa using hcap63) S hS stk1
    (Int.toBytes 8 (Host.addrOf (k + 75 + 1)).toBitVec.toInt) (sm1.take 8) ((sm1.drop 8).take 8) ((sm1.drop 8).drop 8)
    l200 l192 l136 (Int.toBytes 8 (BitVec.ofNat 64 (4 * n)).toInt) l160 l184 a0 a1
    hstk1 (Int.toBytes_length 8 _) (by simp [hsm1]) (by simp [hsm1]) (by simp [hsm1]) hl200 hl192 hl136
    (Int.toBytes_length 8 _) hl160 hl184 ha0 ha1 ra rbp guard Heap (avail - 8 * n) (by omega)
    (Eq ((Int.toBytes 8 rbx.toBitVec.toInt).At (rsp.toBitVec + 16)) ⋆ Eq ([4, 0, 0, 0].At rbx.toBitVec)
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 n).toInt).At (rax.toBitVec + 16))) R _
    (by simp) (by show (BitVec.ofNat 64 n).toNat = _; simp; omega)
    (by show (BitVec.ofNat 64 (4 * n)).toNat = _; simp; omega)
    (by simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega) hguard hsp
    (by
      dsimp only
      simp only [List.nil_append, Nat.sub_zero]
      rw [htl]
      ecancel) hno hcv hfe) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrax2, hrsp2, hrbp2, Hm2⟩
  dsimp only at hpc2 hrax2 hrsp2 hrbp2 Hm2
  refine Eventually.done _ ⟨hpc2, hrax2, ?_, hrbp2, Hm2⟩
  apply UInt64.toBitVec_inj.mp; rw [hrsp2]; simp
