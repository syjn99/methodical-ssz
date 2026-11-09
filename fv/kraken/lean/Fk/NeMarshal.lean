import Fk.NeMarshalLoop
import Fk.NeAccept
import Fk.LcReject
import Fk.CpMarshal

/-!
# Nested.MarshalSSZTo, fast path, on Kraken main

With S and L non-nil, `len(c.L.L) = n ≤ 16`, and `cap(dst) ≥ len(dst) + 32 + 8n`,
the function appends A (8), the five Scalars fields (1, 2, 4, 8, bool), the
offset 28 (`ssz.WriteOffset`), the ListU64 offset 4 and the n elements, and
-/

open Fk Fk.Code
variable [Host]

theorem nem_pop (x : BitVec 64) : 200 + (x - 8#64 - 200) = x - 8 := by bv_omega
theorem toNat_add_neg80 (x : BitVec 64) (h : 80 ≤ x.toNat) : (x + -80).toNat = x.toNat - 80 := by
  rw [← BitVec.sub_eq_add_neg, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simpa using h)]; rfl
theorem add4_neg4 (x y : BitVec 64) : 4 + y + x * 1#64 + -4 = x + y := by
  rw [BitVec.mul_one, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm 4, BitVec.add_assoc, BitVec.add_assoc]
  rw [show (-4 : BitVec 64) + 4 = 0 by decide, Fk.add_lit_zero, BitVec.add_comm]

/-- The 8-byte pointer chunk, split for the 1-byte nil check `test %al,(%r8)`. -/
theorem split1 (a : BitVec 64) (l : List UInt8) (h : l.length = 8) :
    Eq (l.At a) = Eq ((l.take 1).At a) ⋆ Eq ((l.drop 1).At (a + 1)) := by
  conv => lhs; rw [← List.take_append_drop 1 l]
  rw [Mem.At_append_sep _ _ _ (by simp; omega)]; simp [h]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem ne_marshal_tail (k : Nat) (hk : NestedMarshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh NestedMarshalSSZTo k)
    (x : BitVec 64) (recv b pl q : BitVec 64) (L cap : Nat) (bs d o28 o4 : List UInt8) (n : Nat) (hn : n ≤ 16)
    (hbs : bs.length = 8 * n) (hd : d.length = 8 * n) (h28 : o28.length = 4) (h4 : o4.length = 4)
    (hcap : L + 32 + 8 * n ≤ cap) (hcap63 : cap < 2 ^ 63) (hpl : pl ≠ 0)
    (ra rbp0 : UInt64) (l72 l32 : List UInt8) (hl72 : l72.length = 8) (hl32 : l32.length = 8)
    (R : DataMem → Prop) (s : MachineData)
    (hrax : s.regs.rax.toBitVec = recv) (hrbx : s.regs.rbx.toBitVec = b) (hrdx : s.regs.rdx.toNat = L + 24)
    (hrdi : s.regs.rdi.toNat = cap) (hrsp : s.regs.rsp.toBitVec = x - 8#64 - 200) (hrbp : s.regs.rbp.toBitVec = x - 8)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At x) ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (x - 8))
      ⋆ Eq (l72.At (x - 72)) ⋆ Eq (l32.At (x - 32))
      ⋆ Eq ((Int.toBytes 8 pl.toInt).At (recv + 16))
      ⋆ Eq ((Int.toBytes 8 q.toInt).At pl) ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 n).toInt).At (pl + 8))
      ⋆ Eq (bs.At q)
      ⋆ Eq (o28.At (b + BitVec.ofNat 64 (L + 24))) ⋆ Eq (o4.At (b + BitVec.ofNat 64 (L + 28)))
      ⋆ Eq (d.At (b + BitVec.ofNat 64 (L + 32))) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax.toBitVec = b
        ∧ st.data.regs.rbx.toNat = L + 32 + 8 * n ∧ st.data.regs.rcx.toNat = cap
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp.toBitVec = x + 8 ∧ st.data.regs.rbp = rbp0
        ∧ (Eq ([28, 0, 0, 0].At (b + BitVec.ofNat 64 (L + 24))) ⋆ Eq ([4, 0, 0, 0].At (b + BitVec.ofNat 64 (L + 28)))
          ⋆ Eq (bs.At (b + BitVec.ofNat 64 (L + 32))) ⋆ Eq (bs.At q) ⋆ R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf (k + 165)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hrax hrbx hrdx hrdi hrsp hrbp ⊢
  subst hrax hrbx
  have := rdx.toNat_lt_size; have := rdi.toNat_lt_size; simp only [UInt64.size] at *
  kat hk NestedMarshalSSZTo 165
  kat hk NestedMarshalSSZTo 166
  apply load_step_at _ _ (rax.toBitVec + 16) _ _ (Int.toBytes 8 pl.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk NestedMarshalSSZTo 167
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h; exact hpl h
  simp only [Effects.All]
  klabel hk hf NestedMarshalSSZTo 189
  kat hk NestedMarshalSSZTo 189
  kat hk NestedMarshalSSZTo 190
  kat hk NestedMarshalSSZTo 191
  kat hk NestedMarshalSSZTo 192
  kat hk NestedMarshalSSZTo 193
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf NestedMarshalSSZTo 204
  kat hk NestedMarshalSSZTo 204
  kat hk NestedMarshalSSZTo 205
  rw [add4_neg4, show rbx.toBitVec + rdx.toBitVec = rbx.toBitVec + BitVec.ofNat 64 (L + 24) by
    congr 1; apply BitVec.eq_of_toNat_eq; simp; omega]
  apply store_step _ _ _ _ _ o28 _ _ (by ecancel) (by exact h28)
  intro m1 H1
  simp only [Width.bytes, Width.bits, show Int.toBytes 4 (BitVec.truncate 32 (28 : BitVec 64)).toInt = [28, 0, 0, 0] by decide] at H1
  kunfold
  kat hk NestedMarshalSSZTo 206
  apply load_step_at _ _ (rax.toBitVec + 16) _ _ (Int.toBytes 8 pl.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk NestedMarshalSSZTo 207
  rw [split1 pl _ (Int.toBytes_length 8 _)] at H1
  apply load_step _ _ _ _ ((Int.toBytes 8 q.toInt).take 1) _ _ (by ecancel) (by simp [Int.toBytes_length])
  kunfold
  intro _
  rw [← split1 pl _ (Int.toBytes_length 8 _)] at H1
  kat hk NestedMarshalSSZTo 208
  kat hk NestedMarshalSSZTo 209
  kat hk NestedMarshalSSZTo 210
  kat hk NestedMarshalSSZTo 211
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf NestedMarshalSSZTo 223
  kat hk NestedMarshalSSZTo 223
  kat hk NestedMarshalSSZTo 224
  rw [add4_neg4, show rbx.toBitVec + (4 + rdx.toBitVec) = rbx.toBitVec + BitVec.ofNat 64 (L + 28) by
    congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega]
  apply store_step _ _ _ _ _ o4 _ _ (by ecancel) (by exact h4)
  intro m2 H2
  simp only [Width.bytes, Width.bits, show Int.toBytes 4 (BitVec.truncate 32 (4 : BitVec 64)).toInt = [4, 0, 0, 0] by decide] at H2
  kunfold
  kat hk NestedMarshalSSZTo 225
  apply load_step_at _ _ (pl + 8) _ _ (Int.toBytes 8 (BitVec.ofNat 64 n).toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk NestedMarshalSSZTo 226
  kat hk NestedMarshalSSZTo 227
  rw [jg16_false _ _ (by simp; omega)]
  simp only [Bool.false_eq_true, ↓reduceIte, Effects.All]
  kat hk NestedMarshalSSZTo 228
  rw [show rsp.toBitVec + 136 = x - 72 by rw [hrsp]; bv_omega]
  apply store_step _ _ _ _ _ l72 _ _ (by ecancel) (by exact hl72)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk NestedMarshalSSZTo 229
  apply load_step _ _ _ _ (Int.toBytes 8 q.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk NestedMarshalSSZTo 230
  rw [show rsp.toBitVec + 176 = x - 32 by rw [hrsp]; bv_omega]
  apply store_step _ _ _ _ _ l32 _ _ (by ecancel) (by exact hl32)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  kat hk NestedMarshalSSZTo 231
  intro _
  kat hk NestedMarshalSSZTo 232
  klabel hk hf NestedMarshalSSZTo 285
  refine eventually_trans _ _ _ _ (nem_loop k hk hf bs d n hn hbs hd rbx.toBitVec q (L + 28) cap (by omega) hcap63
    (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At x) ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (x - 8))
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 n).toInt).At (x - 72)) ⋆ Eq ((Int.toBytes 8 q.toInt).At (x - 32))
      ⋆ Eq ((Int.toBytes 8 pl.toInt).At (rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 q.toInt).At pl) ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 n).toInt).At (pl + 8))
      ⋆ Eq ([28, 0, 0, 0].At (rbx.toBitVec + BitVec.ofNat 64 (L + 24)))
      ⋆ Eq ([4, 0, 0, 0].At (rbx.toBitVec + BitVec.ofNat 64 (L + 28))) ⋆ R)
    _ _ n 0 _ (by omega) (by simp) rfl (by show (4 + (4 + rdx.toBitVec)).toNat = _; simp [BitVec.toNat_add]; omega)
    hrdi (by show (BitVec.ofNat 64 n).toNat = _; simp; omega) rfl rfl rfl
    (by dsimp only; simp only [Nat.mul_zero, List.take_zero, List.nil_append, List.drop_zero,
      show L + 28 + 4 = L + 32 by omega]; ecancel)) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrbx1, hrdx1, hrdi1, hrsp1, hrbp1, Hm1⟩
  dsimp only at hpc1 hrbx1 hrdx1 hrdi1 hrsp1 hrbp1 Hm1
  subst hpc1
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩,
    zmms1, flags1, mem1⟩ := d1
  simp only at hrbx1 hrdx1 hrdi1 hrsp1 hrbp1 Hm1
  subst hrsp1 hrbp1
  simp only [show L + 28 + 4 = L + 32 by omega] at Hm1 hrdx1
  kat hk NestedMarshalSSZTo 308
  kat hk NestedMarshalSSZTo 309
  intro _
  kat hk NestedMarshalSSZTo 310
  kat hk NestedMarshalSSZTo 311
  kat hk NestedMarshalSSZTo 312
  intro _
  kat hk NestedMarshalSSZTo 313
  klabel hk hf NestedMarshalSSZTo 239
  kat hk NestedMarshalSSZTo 239
  kat hk NestedMarshalSSZTo 240
  intro _
  kat hk NestedMarshalSSZTo 241
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf NestedMarshalSSZTo 273
  kat hk NestedMarshalSSZTo 273
  kat hk NestedMarshalSSZTo 274
  kat hk NestedMarshalSSZTo 275
  kat hk NestedMarshalSSZTo 276
  kat hk NestedMarshalSSZTo 277
  kat hk NestedMarshalSSZTo 278
  kat hk NestedMarshalSSZTo 279
  kat hk NestedMarshalSSZTo 280
  rw [hrsp, nem_pop]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp0.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk NestedMarshalSSZTo 281
  rw [show x - 8 + 8#64 = x by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨trivial, hrbx1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrdx1]
  · exact hrdi1
  · apply UInt64.toBitVec_inj.mp; simp
  · apply UInt64.toBitVec_inj.mp; simp
  · bv_omega
  · first | exact True.intro | (apply UInt64.toBitVec_inj.mp; simp) | (simp)
  · exact sep_true (P := Eq ([28, 0, 0, 0].At (rbx.toBitVec + BitVec.ofNat 64 (L + 24)))
      ⋆ Eq ([4, 0, 0, 0].At (rbx.toBitVec + BitVec.ofNat 64 (L + 28)))
      ⋆ Eq (bs.At (rbx.toBitVec + BitVec.ofNat 64 (L + 32))) ⋆ Eq (bs.At q) ⋆ R) (by ecancel)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
theorem ne_marshal_main (k : Nat) (hk : NestedMarshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh NestedMarshalSSZTo k)
    (a8 cA cB cC cD cE bs pre d0 d1 d2 d3 d4 d5 o28 o4 d : List UInt8) (n : Nat) (hn : n ≤ 16)
    (ha8 : a8.length = 8) (hA : cA.length = 1) (hB : cB.length = 2) (hC : cC.length = 4) (hD : cD.length = 8)
    (hE : cE = [0] ∨ cE = [1]) (hbs : bs.length = 8 * n) (hd : d.length = 8 * n)
    (hd0 : d0.length = 8) (hd1 : d1.length = 1) (hd2 : d2.length = 2) (hd3 : d3.length = 4) (hd4 : d4.length = 8)
    (hd5 : d5.length = 1) (h28 : o28.length = 4) (h4 : o4.length = 4)
    (ps pl q : BitVec 64) (hps : ps ≠ 0) (hpl : pl ≠ 0)
    (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s8 s16 l40 l72 l32 : List UInt8)
    (hfp : fp.length = 8) (hs8 : s8.length = 8) (hs16 : s16.length = 8) (hl40 : l40.length = 8)
    (hl72 : l72.length = 8) (hl32 : l32.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s8.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s16.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (l72.At (s.regs.rsp.toBitVec - 72)) ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (a8.At s.regs.rax.toBitVec) ⋆ Eq ((Int.toBytes 8 ps.toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 pl.toInt).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (cA.At ps) ⋆ Eq (cB.At (ps + 2)) ⋆ Eq (cC.At (ps + 4)) ⋆ Eq (cD.At (ps + 8)) ⋆ Eq (cE.At (ps + 16))
      ⋆ Eq ((Int.toBytes 8 q.toInt).At pl) ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 n).toInt).At (pl + 8))
      ⋆ Eq (bs.At q)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 9))
      ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 11))
      ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 15))
      ⋆ Eq (d5.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 23))
      ⋆ Eq (o28.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 24))
      ⋆ Eq (o4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 28))
      ⋆ Eq (d.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 32)) ⋆ R)
    (hguard : guard.toNat + 80 < s.regs.rsp.toNat) (hsp : 208 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 32 + 8 * n ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 32 + 8 * n ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (a8.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (cA.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (cB.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 9))
          ⋆ Eq (cC.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 11))
          ⋆ Eq (cD.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 15))
          ⋆ Eq (cE.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 23))
          ⋆ Eq ([28, 0, 0, 0].At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 24))
          ⋆ Eq ([4, 0, 0, 0].At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 28))
          ⋆ Eq (bs.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 32)) ⋆ R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hcap hcap63 hpre ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *
  have hb24 : rbx.toBitVec + BitVec.ofNat 64 (rcx.toNat + 24) = rbx.toBitVec + rcx.toBitVec + 24 := by
    rw [BitVec.add_assoc]; congr 1
  have hb28 : rbx.toBitVec + BitVec.ofNat 64 (rcx.toNat + 28) = rbx.toBitVec + rcx.toBitVec + 28 := by
    rw [BitVec.add_assoc]; congr 1
  have hb32 : rbx.toBitVec + BitVec.ofNat 64 (rcx.toNat + 32) = rbx.toBitVec + rcx.toBitVec + 32 := by
    rw [BitVec.add_assoc]; congr 1
  kat hk NestedMarshalSSZTo 0
  kat hk NestedMarshalSSZTo 1
  kat hk NestedMarshalSSZTo 2
  kat hk NestedMarshalSSZTo 3
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk NestedMarshalSSZTo 4
  split
  case isTrue h =>
    exfalso
    rw [cmp_be_false _ _ _ _ (by rw [toNat_add_neg80 _ (by simp; omega)]; simp; omega)] at h
    exact absurd h (by simp)
  simp only [Effects.All]
  kat hk NestedMarshalSSZTo 5
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk NestedMarshalSSZTo 6
  kat hk NestedMarshalSSZTo 7
  kat hk NestedMarshalSSZTo 8
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s16 _ _ (by bv_omega) (by ecancel) (by exact hs16)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk NestedMarshalSSZTo 9
  apply store_step_at _ _ (rsp.toBitVec + 8) _ _ _ s8 _ _ (by bv_omega) (by ecancel) (by exact hs8)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk NestedMarshalSSZTo 10
  kat hk NestedMarshalSSZTo 11
  apply load_step _ _ _ _ a8 _ _ (by ecancel) (by exact ha8)
  kunfold
  kat hk NestedMarshalSSZTo 12
  kat hk NestedMarshalSSZTo 13
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf NestedMarshalSSZTo 26
  kat hk NestedMarshalSSZTo 26
  kat hk NestedMarshalSSZTo 27
  rw [cpm_addr]
  apply store_step _ _ _ _ _ d0 _ _ (by ecancel) (by exact hd0)
  intro m4 H4
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl a8 ha8] at H4
  kunfold
  kat hk NestedMarshalSSZTo 28
  apply load_step_at _ _ (rax.toBitVec + 8) _ _ (Int.toBytes 8 ps.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk NestedMarshalSSZTo 29
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h; exact hps h
  simp only [Effects.All]
  klabel hk hf NestedMarshalSSZTo 51
  kat hk NestedMarshalSSZTo 51
  kat hk NestedMarshalSSZTo 52
  apply load_step_at _ _ (rax.toBitVec + 8) _ _ (Int.toBytes 8 ps.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk NestedMarshalSSZTo 53
  apply store_step_at _ _ (rsp.toBitVec - 40) _ _ _ l40 _ _ (by bv_omega) (by ecancel) (by exact hl40)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  kat hk NestedMarshalSSZTo 54
  kat hk NestedMarshalSSZTo 55
  apply load_step _ _ _ _ cA _ _ (by ecancel) (by exact hA)
  kunfold
  kat hk NestedMarshalSSZTo 56
  kat hk NestedMarshalSSZTo 57
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf NestedMarshalSSZTo 71
  kat hk NestedMarshalSSZTo 71
  kat hk NestedMarshalSSZTo 72
  rw [show rcx.toBitVec + 8 + 1 + rbx.toBitVec * 1#64 + -1 = rbx.toBitVec + rcx.toBitVec + 8 by bv_omega]
  apply store_step _ _ _ _ _ d1 _ _ (by ecancel) (by exact hd1)
  intro m6 H6
  simp only [Width.bytes, Width.bits, zx8, toBytes_ofInt_ofBytes 8 1 rfl cA hA] at H6
  kunfold
  kat hk NestedMarshalSSZTo 73
  kat hk NestedMarshalSSZTo 74
  apply load_step_at _ _ (ps + 2) _ _ cB _ _ (by bv_omega) (by ecancel) (by exact hB)
  kunfold
  kat hk NestedMarshalSSZTo 75
  kat hk NestedMarshalSSZTo 76
  kat hk NestedMarshalSSZTo 77
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf NestedMarshalSSZTo 91
  kat hk NestedMarshalSSZTo 91
  kat hk NestedMarshalSSZTo 92
  rw [show 2 + (rcx.toBitVec + 8 + 1) + rbx.toBitVec * 1#64 + -2 = rbx.toBitVec + rcx.toBitVec + 9 by bv_omega]
  apply store_step _ _ _ _ _ d2 _ _ (by ecancel) (by exact hd2)
  intro m7 H7
  simp only [Width.bytes, Width.bits, zx16, toBytes_ofInt_ofBytes 16 2 rfl cB hB] at H7
  kunfold
  kat hk NestedMarshalSSZTo 93
  kat hk NestedMarshalSSZTo 94
  apply load_step_at _ _ (ps + 4) _ _ cC _ _ (by bv_omega) (by ecancel) (by exact hC)
  kunfold
  kat hk NestedMarshalSSZTo 95
  kat hk NestedMarshalSSZTo 96
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf NestedMarshalSSZTo 110
  kat hk NestedMarshalSSZTo 110
  kat hk NestedMarshalSSZTo 111
  rw [show 4 + (2 + (rcx.toBitVec + 8 + 1)) + rbx.toBitVec * 1#64 + -4 = rbx.toBitVec + rcx.toBitVec + 11 by bv_omega]
  apply store_step _ _ _ _ _ d3 _ _ (by ecancel) (by exact hd3)
  intro m8 H8
  simp only [Width.bytes, Width.bits, zx32, toBytes_ofInt_ofBytes 32 4 rfl cC hC] at H8
  kunfold
  kat hk NestedMarshalSSZTo 112
  kat hk NestedMarshalSSZTo 113
  apply load_step_at _ _ (ps + 8) _ _ cD _ _ (by bv_omega) (by ecancel) (by exact hD)
  kunfold
  kat hk NestedMarshalSSZTo 114
  kat hk NestedMarshalSSZTo 115
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf NestedMarshalSSZTo 129
  kat hk NestedMarshalSSZTo 129
  kat hk NestedMarshalSSZTo 130
  rw [show 8 + (4 + (2 + (rcx.toBitVec + 8 + 1))) + rbx.toBitVec * 1#64 + -8 = rbx.toBitVec + rcx.toBitVec + 15 by bv_omega]
  apply store_step _ _ _ _ _ d4 _ _ (by ecancel) (by exact hd4)
  intro m9' H9'
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl cD hD] at H9'
  kunfold
  kat hk NestedMarshalSSZTo 131
  apply load_step_at _ _ (ps + 16) _ _ cE _ _ (by bv_omega) (by ecancel) (by rcases hE with rfl | rfl <;> rfl)
  kunfold
  rcases hE with rfl | rfl
  · kat hk NestedMarshalSSZTo 132
    split
    case isFalse h => exact absurd h (by decide)
    simp only [Effects.All]
    klabel hk hf NestedMarshalSSZTo 149
    kat hk NestedMarshalSSZTo 149
    kat hk NestedMarshalSSZTo 150
    kat hk NestedMarshalSSZTo 151
    kat hk NestedMarshalSSZTo 152
    split
    case isFalse h =>
      exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
    simp only [Effects.All]
    klabel hk hf NestedMarshalSSZTo 163
    kat hk NestedMarshalSSZTo 163
    kat hk NestedMarshalSSZTo 164
    rw [show 8 + (4 + (2 + (rcx.toBitVec + 8 + 1))) + 1 + rbx.toBitVec * 1#64 + -1
      = rbx.toBitVec + rcx.toBitVec + 23 by bv_omega]
    apply store_step _ _ _ _ _ d5 _ _ (by ecancel) (by exact hd5)
    intro m9 H9
    simp only [Width.bytes, Width.bits, show Int.toBytes 1 (BitVec.truncate 8 (0 : BitVec 64)).toInt = [0] by decide] at H9
    kunfold
    have hrd : (8 + (4 + (2 + (rcx.toBitVec + 8 + 1))) + 1).toNat = rcx.toNat + 24 := by
      simp [BitVec.toNat_add]; omega
    obtain ⟨F, HF0⟩ : ∃ F, (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At rsp.toBitVec)
        ⋆ Eq ((Int.toBytes 8 rbp.toBitVec.toInt).At (rsp.toBitVec - 8))
        ⋆ Eq (l72.At (rsp.toBitVec - 72)) ⋆ Eq (l32.At (rsp.toBitVec - 32))
        ⋆ Eq ((Int.toBytes 8 pl.toInt).At (rax.toBitVec + 16))
        ⋆ Eq ((Int.toBytes 8 q.toInt).At pl) ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 n).toInt).At (pl + 8))
        ⋆ Eq (bs.At q)
        ⋆ Eq (o28.At (rbx.toBitVec + BitVec.ofNat 64 (rcx.toNat + 24)))
        ⋆ Eq (o4.At (rbx.toBitVec + BitVec.ofNat 64 (rcx.toNat + 28)))
        ⋆ Eq (d.At (rbx.toBitVec + BitVec.ofNat 64 (rcx.toNat + 32)))
        ⋆ Eq (pre.At rbx.toBitVec) ⋆ Eq (a8.At (rbx.toBitVec + rcx.toBitVec))
        ⋆ Eq (cA.At (rbx.toBitVec + rcx.toBitVec + 8)) ⋆ Eq (cB.At (rbx.toBitVec + rcx.toBitVec + 9))
        ⋆ Eq (cC.At (rbx.toBitVec + rcx.toBitVec + 11)) ⋆ Eq (cD.At (rbx.toBitVec + rcx.toBitVec + 15))
        ⋆ Eq ([0].At (rbx.toBitVec + rcx.toBitVec + 23)) ⋆ R ⋆ F) m9 := by
      rw [hb24, hb28, hb32] at *
      exact ⟨_, by ecancel⟩
    have HF : (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At rsp.toBitVec)
        ⋆ Eq ((Int.toBytes 8 rbp.toBitVec.toInt).At (rsp.toBitVec - 8))
        ⋆ Eq (l72.At (rsp.toBitVec - 72)) ⋆ Eq (l32.At (rsp.toBitVec - 32))
        ⋆ Eq ((Int.toBytes 8 pl.toInt).At (rax.toBitVec + 16))
        ⋆ Eq ((Int.toBytes 8 q.toInt).At pl) ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 n).toInt).At (pl + 8))
        ⋆ Eq (bs.At q)
        ⋆ Eq (o28.At (rbx.toBitVec + BitVec.ofNat 64 (rcx.toNat + 24)))
        ⋆ Eq (o4.At (rbx.toBitVec + BitVec.ofNat 64 (rcx.toNat + 28)))
        ⋆ Eq (d.At (rbx.toBitVec + BitVec.ofNat 64 (rcx.toNat + 32)))
        ⋆ (Eq (pre.At rbx.toBitVec) ⋆ Eq (a8.At (rbx.toBitVec + rcx.toBitVec))
        ⋆ Eq (cA.At (rbx.toBitVec + rcx.toBitVec + 8)) ⋆ Eq (cB.At (rbx.toBitVec + rcx.toBitVec + 9))
        ⋆ Eq (cC.At (rbx.toBitVec + rcx.toBitVec + 11)) ⋆ Eq (cD.At (rbx.toBitVec + rcx.toBitVec + 15))
        ⋆ Eq ([0].At (rbx.toBitVec + rcx.toBitVec + 23)) ⋆ R ⋆ F)) m9 := by
      simp only [Std.ExtHashMap.sep_assoc] at HF0 ⊢; exact HF0
    refine eventually_trans _ _ _ _ (ne_marshal_tail k hk hf rsp.toBitVec rax.toBitVec rbx.toBitVec pl q rcx.toNat
      rdi.toNat bs d o28 o4 n hn hbs hd h28 h4 (by omega) hcap63 hpl ra rbp l72 l32 hl72 hl32
      (Eq (pre.At rbx.toBitVec) ⋆ Eq (a8.At (rbx.toBitVec + rcx.toBitVec))
        ⋆ Eq (cA.At (rbx.toBitVec + rcx.toBitVec + 8)) ⋆ Eq (cB.At (rbx.toBitVec + rcx.toBitVec + 9))
        ⋆ Eq (cC.At (rbx.toBitVec + rcx.toBitVec + 11)) ⋆ Eq (cD.At (rbx.toBitVec + rcx.toBitVec + 15))
        ⋆ Eq ([0].At (rbx.toBitVec + rcx.toBitVec + 23)) ⋆ R ⋆ F) _ rfl rfl
      hrd (by simp) (by bv_omega) (by bv_omega) HF) ?_
    rintro ⟨d1, pc1⟩ ⟨hpc1, h1, h2, h3, h4', h5, h6, h7, Hm1⟩
    dsimp only at hpc1 h1 h2 h3 h4' h5 h6 h7 Hm1
    apply Eventually.done
    refine ⟨hpc1, ?_, ?_, ?_, h4', h5, ?_, h7, ?_⟩
    · exact UInt64.toBitVec_inj.mp h1
    · rw [h2]
    · apply UInt64.toNat_inj.mp; rw [h3]
    · apply UInt64.toBitVec_inj.mp; rw [h6]; simp
    · rw [hb24, hb28, hb32] at Hm1
      exact sep_true (P := Eq (pre.At rbx.toBitVec) ⋆ Eq (a8.At (rbx.toBitVec + rcx.toBitVec))
        ⋆ Eq (cA.At (rbx.toBitVec + rcx.toBitVec + 8)) ⋆ Eq (cB.At (rbx.toBitVec + rcx.toBitVec + 9))
        ⋆ Eq (cC.At (rbx.toBitVec + rcx.toBitVec + 11)) ⋆ Eq (cD.At (rbx.toBitVec + rcx.toBitVec + 15))
        ⋆ Eq ([0].At (rbx.toBitVec + rcx.toBitVec + 23))
        ⋆ Eq ([28, 0, 0, 0].At (rbx.toBitVec + rcx.toBitVec + 24)) ⋆ Eq ([4, 0, 0, 0].At (rbx.toBitVec + rcx.toBitVec + 28))
        ⋆ Eq (bs.At (rbx.toBitVec + rcx.toBitVec + 32)) ⋆ R) (by ecancel)

  · kat hk NestedMarshalSSZTo 132
    split
    case isTrue h => exact absurd h (by decide)
    simp only [Effects.All]
    kat hk NestedMarshalSSZTo 133
    kat hk NestedMarshalSSZTo 134
    kat hk NestedMarshalSSZTo 135
    split
    case isFalse h =>
      exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
    simp only [Effects.All]
    klabel hk hf NestedMarshalSSZTo 146
    kat hk NestedMarshalSSZTo 146
    kat hk NestedMarshalSSZTo 147
    rw [show 8 + (4 + (2 + (rcx.toBitVec + 8 + 1))) + 1 + rbx.toBitVec * 1#64 + -1
      = rbx.toBitVec + rcx.toBitVec + 23 by bv_omega]
    apply store_step _ _ _ _ _ d5 _ _ (by ecancel) (by exact hd5)
    intro m9 H9
    simp only [Width.bytes, Width.bits, show Int.toBytes 1 (BitVec.truncate 8 (1 : BitVec 64)).toInt = [1] by decide] at H9
    kunfold
    kat hk NestedMarshalSSZTo 148
    klabel hk hf NestedMarshalSSZTo 165
    have hrd : (8 + (4 + (2 + (rcx.toBitVec + 8 + 1))) + 1).toNat = rcx.toNat + 24 := by
      simp [BitVec.toNat_add]; omega
    obtain ⟨F, HF0⟩ : ∃ F, (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At rsp.toBitVec)
        ⋆ Eq ((Int.toBytes 8 rbp.toBitVec.toInt).At (rsp.toBitVec - 8))
        ⋆ Eq (l72.At (rsp.toBitVec - 72)) ⋆ Eq (l32.At (rsp.toBitVec - 32))
        ⋆ Eq ((Int.toBytes 8 pl.toInt).At (rax.toBitVec + 16))
        ⋆ Eq ((Int.toBytes 8 q.toInt).At pl) ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 n).toInt).At (pl + 8))
        ⋆ Eq (bs.At q)
        ⋆ Eq (o28.At (rbx.toBitVec + BitVec.ofNat 64 (rcx.toNat + 24)))
        ⋆ Eq (o4.At (rbx.toBitVec + BitVec.ofNat 64 (rcx.toNat + 28)))
        ⋆ Eq (d.At (rbx.toBitVec + BitVec.ofNat 64 (rcx.toNat + 32)))
        ⋆ Eq (pre.At rbx.toBitVec) ⋆ Eq (a8.At (rbx.toBitVec + rcx.toBitVec))
        ⋆ Eq (cA.At (rbx.toBitVec + rcx.toBitVec + 8)) ⋆ Eq (cB.At (rbx.toBitVec + rcx.toBitVec + 9))
        ⋆ Eq (cC.At (rbx.toBitVec + rcx.toBitVec + 11)) ⋆ Eq (cD.At (rbx.toBitVec + rcx.toBitVec + 15))
        ⋆ Eq ([1].At (rbx.toBitVec + rcx.toBitVec + 23)) ⋆ R ⋆ F) m9 := by
      rw [hb24, hb28, hb32] at *
      exact ⟨_, by ecancel⟩
    have HF : (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At rsp.toBitVec)
        ⋆ Eq ((Int.toBytes 8 rbp.toBitVec.toInt).At (rsp.toBitVec - 8))
        ⋆ Eq (l72.At (rsp.toBitVec - 72)) ⋆ Eq (l32.At (rsp.toBitVec - 32))
        ⋆ Eq ((Int.toBytes 8 pl.toInt).At (rax.toBitVec + 16))
        ⋆ Eq ((Int.toBytes 8 q.toInt).At pl) ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 n).toInt).At (pl + 8))
        ⋆ Eq (bs.At q)
        ⋆ Eq (o28.At (rbx.toBitVec + BitVec.ofNat 64 (rcx.toNat + 24)))
        ⋆ Eq (o4.At (rbx.toBitVec + BitVec.ofNat 64 (rcx.toNat + 28)))
        ⋆ Eq (d.At (rbx.toBitVec + BitVec.ofNat 64 (rcx.toNat + 32)))
        ⋆ (Eq (pre.At rbx.toBitVec) ⋆ Eq (a8.At (rbx.toBitVec + rcx.toBitVec))
        ⋆ Eq (cA.At (rbx.toBitVec + rcx.toBitVec + 8)) ⋆ Eq (cB.At (rbx.toBitVec + rcx.toBitVec + 9))
        ⋆ Eq (cC.At (rbx.toBitVec + rcx.toBitVec + 11)) ⋆ Eq (cD.At (rbx.toBitVec + rcx.toBitVec + 15))
        ⋆ Eq ([1].At (rbx.toBitVec + rcx.toBitVec + 23)) ⋆ R ⋆ F)) m9 := by
      simp only [Std.ExtHashMap.sep_assoc] at HF0 ⊢; exact HF0
    refine eventually_trans _ _ _ _ (ne_marshal_tail k hk hf rsp.toBitVec rax.toBitVec rbx.toBitVec pl q rcx.toNat
      rdi.toNat bs d o28 o4 n hn hbs hd h28 h4 (by omega) hcap63 hpl ra rbp l72 l32 hl72 hl32
      (Eq (pre.At rbx.toBitVec) ⋆ Eq (a8.At (rbx.toBitVec + rcx.toBitVec))
        ⋆ Eq (cA.At (rbx.toBitVec + rcx.toBitVec + 8)) ⋆ Eq (cB.At (rbx.toBitVec + rcx.toBitVec + 9))
        ⋆ Eq (cC.At (rbx.toBitVec + rcx.toBitVec + 11)) ⋆ Eq (cD.At (rbx.toBitVec + rcx.toBitVec + 15))
        ⋆ Eq ([1].At (rbx.toBitVec + rcx.toBitVec + 23)) ⋆ R ⋆ F) _ rfl rfl
      hrd (by simp) (by bv_omega) (by bv_omega) HF) ?_
    rintro ⟨d1, pc1⟩ ⟨hpc1, h1, h2, h3, h4', h5, h6, h7, Hm1⟩
    dsimp only at hpc1 h1 h2 h3 h4' h5 h6 h7 Hm1
    apply Eventually.done
    refine ⟨hpc1, ?_, ?_, ?_, h4', h5, ?_, h7, ?_⟩
    · exact UInt64.toBitVec_inj.mp h1
    · rw [h2]
    · apply UInt64.toNat_inj.mp; rw [h3]
    · apply UInt64.toBitVec_inj.mp; rw [h6]; simp
    · rw [hb24, hb28, hb32] at Hm1
      exact sep_true (P := Eq (pre.At rbx.toBitVec) ⋆ Eq (a8.At (rbx.toBitVec + rcx.toBitVec))
        ⋆ Eq (cA.At (rbx.toBitVec + rcx.toBitVec + 8)) ⋆ Eq (cB.At (rbx.toBitVec + rcx.toBitVec + 9))
        ⋆ Eq (cC.At (rbx.toBitVec + rcx.toBitVec + 11)) ⋆ Eq (cD.At (rbx.toBitVec + rcx.toBitVec + 15))
        ⋆ Eq ([1].At (rbx.toBitVec + rcx.toBitVec + 23))
        ⋆ Eq ([28, 0, 0, 0].At (rbx.toBitVec + rcx.toBitVec + 24)) ⋆ Eq ([4, 0, 0, 0].At (rbx.toBitVec + rcx.toBitVec + 28))
        ⋆ Eq (bs.At (rbx.toBitVec + rcx.toBitVec + 32)) ⋆ R) (by ecancel)

