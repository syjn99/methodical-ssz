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
