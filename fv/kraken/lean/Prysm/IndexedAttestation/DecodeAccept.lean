import Prysm.AttestationData.DecodeAccept
import Codec.StackGuard
import Prysm.IndexedAttestation.AddressTactic
import Prysm.IndexedAttestation.Statements
import Prysm.IndexedAttestation.DecodeLoop
import Codec.BitVecShiftLemmas

/-!
# `(*v1alpha1.IndexedAttestation).UnmarshalSSZ`, accept path, Go 1.26.10 machine code

* head 0–56 (hand steps): guard, prologue (`sub $0xa8`), size check, offset check, slice header of `buf[228:]`
  (18–24, the pointer mask), alignment and bound checks, spills, `makeslice` of AttestingIndices
  (`MakesliceC Heap lvU64Type_addr 8 (Sd + 224)`, cnt n), len = cap = n, writeBarrier = 0, ptr, rax = 0, `jmp L_28a`;
* element loop 147–165, 143–146: `Decode.loop` (each iteration proves the three panicBounds branches not taken);
* Data 166–189: `newobject` (`NewobjectC Heap lvAdType_addr 96 (Sd + 224)`), the pointer store, the call of
  `AttestationData.UnmarshalSSZ` on buf[4:132] discharged by `Prysm.AttestationData.Decode.accept` (its entry rsp = x − 184,
  scratch `Sd`), `je L_39c` taken (rax = 0);
* Signature 217–260: `makeslice` (esz 1, cap 96), the header stores, `memmove` of buf[132:228], the epilogue.
Statement: the frozen `Prysm.IndexedAttestation.Decode.accept_statement`.
-/

open Machine Runtime Prysm.IndexedAttestation.Code
variable [Host]

namespace Prysm.IndexedAttestation

omit [Host] in
theorem Decode.mask_ones :
    BitVec.zeroExtend 64 (BitVec.extractLsb' 0 32 (BitVec.allOnes 64) &&& BitVec.truncate 32 (228 : BitVec 64))
      = 228 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.truncate_eq_setWidth, BitVec.toNat_and, BitVec.extractLsb'_toNat,
    BitVec.toNat_allOnes, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_zero, Nat.reducePow,
    Nat.reduceSub, Nat.reduceMod, Nat.reduceAnd]

omit [Host] in
theorem Decode.mask_zero :
    BitVec.zeroExtend 64 (BitVec.extractLsb' 0 32 (BitVec.sshiftRight (-(0 : BitVec 64)) 63)
      &&& BitVec.truncate 32 (228 : BitVec 64)) = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.ofNat_eq_ofNat, BitVec.neg_zero, BitVec.zero_sshiftRight, BitVec.toNat_setWidth,
    BitVec.truncate_eq_setWidth, BitVec.toNat_and, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero,
    Nat.reducePow, Nat.reduceMod, Nat.zero_and]

omit [Host] in
/-- `c − 228` as a natural number (stated without `simp` on the negative literal: `simp [BitVec.toNat_add]` on
`c + -228` makes a proof term the kernel rejects with "deep recursion" after minutes and 16 GiB). -/
theorem Decode.sub228 (c : BitVec 64) (h : 228 ≤ c.toNat) : (c + -228).toNat = c.toNat - 228 := by
  rw [← BitVec.sub_eq_add_neg, BitVec.toNat_sub_of_le]
  · rfl
  · rw [BitVec.le_def]; exact h

omit [Host] in
/-- The `buf[228:]` pointer of directives 18–24 (`rbx + (cap − 228 > 0 ? 228 : 0)`) addresses the element bytes: when
cap = 228 the list is empty. Uses `cap < 2⁶³` (the `sar` sign test). -/
theorem Decode.input_pointer_mask (ib : List UInt8) (n : Nat) (hib : ib.length = 8 * n) (b c : BitVec 64) (hc : 228 + 8 * n ≤ c.toNat)
    (h63 : c.toNat < 2 ^ 63) :
    Eq (ib.At (b + BitVec.zeroExtend 64 (BitVec.extractLsb' 0 32 (BitVec.sshiftRight (-(c + -228)) 63)
      &&& BitVec.truncate 32 (228 : BitVec 64)))) = Eq (ib.At (b + 228)) := by
  by_cases h : c.toNat = 228
  · have hn : n = 0 := by omega
    subst hn
    have : ib = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp only [List.At, List.mapIdx_nil]
  · have hd := Decode.sub228 c (by omega)
    rw [Codec.sshiftRight_neg_63_eq_allOnes _ (by omega) (by omega), Decode.mask_ones]

omit [Host] in
/-- `cmp $0x800, a; jg` is not taken when `a ≤ 2048` (the text of `Machine.jg16_false`). -/
theorem Decode.jg2048_false (a : BitVec 64) (af : Bool) (h : a.toNat ≤ 2048) :
    CondCode.g.interp (StatusFlags.from_result (a - 2048)
      { cf := BitVec.unsigned (a - 2048) != a.unsigned - BitVec.unsigned (2048 : BitVec 64), af := af,
        of := BitVec.toInt (a - 2048) != a.toInt - BitVec.toInt (2048 : BitVec 64) }) = false := by
  have ta : a.toInt = a.toNat := BitVec.toInt_eq_toNat_of_lt (by omega)
  have t16 : BitVec.toInt (2048 : BitVec 64) = 2048 := by decide
  have hs : (a - 2048).toInt = (a.toNat : Int) - 2048 := by
    rw [BitVec.toInt_sub, ta, t16]; apply Int.bmod_eq_of_le <;> omega
  by_cases h16 : a.toNat = 2048
  · have : a - 2048 = 0#64 := by apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega
    simp [CondCode.interp, StatusFlags.from_result]
    intro h1; exact absurd this h1
  · have hm : (a - 2048).msb = true := by
      rw [BitVec.msb_eq_decide]; simp [BitVec.toNat_sub]; omega
    simp [CondCode.interp, StatusFlags.from_result, ta]
    intro _
    rw [show (a - 2048#64).msb = true from hm, Int.bmod_eq_of_le (by omega) (by omega)]; simp

omit [Host] in
/-- A list as a prefix of length `n` and the rest. -/
theorem Decode.bytes_split (l : List UInt8) (n : Nat) (h : n ≤ l.length) :
    ∃ a r : List UInt8, a.length = n ∧ r.length = l.length - n ∧ l = a ++ r :=
  ⟨l.take n, l.drop n, by simp [h], by simp, (List.take_append_drop n l).symm⟩

omit [Host] in
/-- The 40-byte callee spill area at x − 176 as five 8-byte chunks. -/
theorem Decode.j5 (x : BitVec 64) (a b c d e : List UInt8) (ha : a.length = 8) (hb : b.length = 8) (hc : c.length = 8)
    (hd : d.length = 8) (he : e.length = 8) :
    Eq ((a ++ (b ++ (c ++ (d ++ e)))).At (x - 176)) = Eq (a.At (x - 176)) ⋆ Eq (b.At (x - 168)) ⋆ Eq (c.At (x - 160))
      ⋆ Eq (d.At (x - 152)) ⋆ Eq (e.At (x - 144)) := by
  rw [at_app _ _ (b := x - 168) (by rw [ha]; bv_omega) (by simp [ha, hb, hc, hd, he]),
    at_app _ _ (b := x - 160) (by rw [hb]; bv_omega) (by simp [hb, hc, hd, he]),
    at_app _ _ (b := x - 152) (by rw [hc]; bv_omega) (by simp [hc, hd, he]),
    at_app _ _ (b := x - 144) (by rw [hd]; bv_omega) (by simp [hd, he])]
  simp only [Std.ExtHashMap.sep_assoc]

omit [Host] in
/-- The 24-byte `makeslice` spill area at x − 176 as three 8-byte chunks. -/
theorem Decode.j3 (x : BitVec 64) (a b c : List UInt8) (ha : a.length = 8) (hb : b.length = 8) (hc : c.length = 8) :
    Eq ((a ++ (b ++ c)).At (x - 176)) = Eq (a.At (x - 176)) ⋆ Eq (b.At (x - 168)) ⋆ Eq (c.At (x - 160)) := by
  rw [at_app _ _ (b := x - 168) (by rw [ha]; bv_omega) (by simp [ha, hb, hc]),
    at_app _ _ (b := x - 160) (by rw [hb]; bv_omega) (by simp [hb, hc])]
  simp only [Std.ExtHashMap.sep_assoc]

omit [Host] in
/-- Our scratch (`Sd + 224` bytes below the return slot x − 184) as the AttestationData callee's frame (entry rsp
y = x − 184): its scratch (`Sd + 96`), its return slot, its argument area (3 × 8), the untouched gap (80), its Root
pointer save, its saved rbp. -/
theorem Decode.lo8 (x y : BitVec 64) (S : Nat) (hS : S < 2 ^ 60) (hy : y = x - 184)
    (a b c0 c1 c2 d e f : List UInt8) (ha : a.length = S + 96) (hb : b.length = 8) (h0 : c0.length = 8)
    (h1 : c1.length = 8) (h2 : c2.length = 8) (hd : d.length = 80) (he : e.length = 8) (hf : f.length = 8) :
    Eq ((a ++ (b ++ (c0 ++ (c1 ++ (c2 ++ (d ++ (e ++ f))))))).At (x - 184 - BitVec.ofNat 64 (S + 224)))
      = Eq (a.At (y - 224 - BitVec.ofNat 64 S)) ⋆ Eq (b.At (y - 128)) ⋆ Eq (c0.At (y - 120)) ⋆ Eq (c1.At (y - 112))
        ⋆ Eq (c2.At (y - 104)) ⋆ Eq (d.At (y - 96)) ⋆ Eq (e.At (y - 16)) ⋆ Eq (f.At (y - 8)) := by
  subst hy
  have e1 : x - 184 - BitVec.ofNat 64 (S + 224) = x - 184 - 224 - BitVec.ofNat 64 S := by
    have : BitVec.ofNat 64 (S + 224) = BitVec.ofNat 64 S + 224 := by apply BitVec.eq_of_toNat_eq; simp
    rw [this]; bv_omega
  have hl : S + 96 < 2 ^ 64 := by omega
  rw [e1, at_app _ _ (b := x - 184 - 128) (by rw [ha]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega)
      (by simp [ha, hb, h0, h1, h2, hd, he, hf]; omega),
    at_app _ _ (b := x - 184 - 120) (by rw [hb]; bv_omega) (by simp [hb, h0, h1, h2, hd, he, hf]),
    at_app _ _ (b := x - 184 - 112) (by rw [h0]; bv_omega) (by simp [h0, h1, h2, hd, he, hf]),
    at_app _ _ (b := x - 184 - 104) (by rw [h1]; bv_omega) (by simp [h1, h2, hd, he, hf]),
    at_app _ _ (b := x - 184 - 96) (by rw [h2]; bv_omega) (by simp [h2, hd, he, hf]),
    at_app _ _ (b := x - 184 - 16) (by rw [hd]; bv_omega) (by simp [hd, he, hf]),
    at_app _ _ (b := x - 184 - 8) (by rw [he]; bv_omega) (by simp [he, hf])]
  simp only [Std.ExtHashMap.sep_assoc]

omit [Host] in
/-- A fresh 96-byte AttestationData object as the receiver chunks of `ad_e2e_accept_main`. -/
theorem Decode.obj96 (p : BitVec 64) :
    Eq ((List.replicate 96 (0 : UInt8)).At p) = Eq ((List.replicate 8 0).At p) ⋆ Eq ((List.replicate 8 0).At (p + 8))
      ⋆ Eq ((List.replicate 8 0).At (p + 16)) ⋆ Eq ((List.replicate 8 0).At (p + 24))
      ⋆ Eq ((List.replicate 8 0).At (p + 32)) ⋆ Eq ((List.replicate 8 0).At (p + 40))
      ⋆ Eq ((List.replicate 8 0).At (p + 48)) ⋆ Eq ((List.replicate 8 0).At (p + 56))
      ⋆ Eq ((List.replicate 32 0).At (p + 64)) := by
  rw [show List.replicate 96 (0 : UInt8) = List.replicate 8 0 ++ (List.replicate 8 0 ++ (List.replicate 8 0
    ++ (List.replicate 8 0 ++ (List.replicate 8 0 ++ (List.replicate 8 0 ++ (List.replicate 8 0
    ++ (List.replicate 8 0 ++ List.replicate 32 0))))))) by rfl]
  rw [at_app _ _ (b := p + 8) (by simp) (by simp), at_app _ _ (b := p + 16) (by simp; bv_omega) (by simp),
    at_app _ _ (b := p + 24) (by simp; bv_omega) (by simp), at_app _ _ (b := p + 32) (by simp; bv_omega) (by simp),
    at_app _ _ (b := p + 40) (by simp; bv_omega) (by simp), at_app _ _ (b := p + 48) (by simp; bv_omega) (by simp),
    at_app _ _ (b := p + 56) (by simp; bv_omega) (by simp), at_app _ _ (b := p + 64) (by simp; bv_omega) (by simp)]
  simp only [Std.ExtHashMap.sep_assoc]

-- Measured causes:
-- * heartbeats: the whole proof (about 230 `kat` steps, 3 runtime calls, the loop and the AttestationData call) stops
--   with a `whnf` timeout at the default (200000) and at 400000; 800000 passes; the value is twice that;
-- * recursion depth: without the option the first `kat` (directive 0) stops with "maximum recursion depth", as in
--   `Prysm/IndexedAttestation/DecodeRejectSize.lean`; 1024 passes.
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1024 in
/-- **Accept path of the real `(*v1alpha1.IndexedAttestation).UnmarshalSSZ` (Go 1.26.10)**; statement = the frozen
`Decode.accept_statement`. -/
theorem Decode.accept : Decode.accept_statement := by
  intro k hk hf kA hkA hfA kS hkS hfS kI hkI hfI kC hkC hfC kE hkE hfE n hn in0 in1 root se sroot te troot sig ib
    hin0 hin1 hroot hse hsroot hte htroot hsig hib s ra guard
    fp s1 s2 s4 l28 l30 l38 l40 l48 la0 spl rslot lo ast aP1 aL1 aC1 aD aP2 aL2 aC2
    hfp h1 h2 h4 hl28 hl30 hl38 hl40 hl48 hla0 hspl hrs hast haP1 haL1 haC1 haD haP2 haL2 haC2
    R Sd hSd8 hSd hlo Heap avail h_mem hguard hlen hcap hcap63 hav hmsU hms hmm hno hmsD hmmD hmsD' hmmD' hnoD
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen hcap hcap63
  dsimp only
  have hz1 := rsp.toNat_lt_size; have hz2 := guard.toNat_lt_size; have hz3 := rcx.toNat_lt_size
  have hz4 := rdi.toNat_lt_size
  simp only [UInt64.size] at hz1 hz2 hz3 hz4
  -- the spill area as five chunks
  have espl : spl = spl.take 8 ++ ((spl.drop 8).take 8 ++ ((spl.drop 16).take 8 ++ ((spl.drop 24).take 8
      ++ spl.drop 32))) := by
    conv => lhs; rw [← List.take_append_drop 8 spl, ← List.take_append_drop 8 (spl.drop 8),
      ← List.take_append_drop 8 ((spl.drop 8).drop 8), ← List.take_append_drop 8 (((spl.drop 8).drop 8).drop 8)]
    simp only [List.drop_drop]
  rw [espl, Decode.j5 _ _ _ _ _ _ (by simp [hspl]) (by simp [hspl]) (by simp [hspl]) (by simp [hspl])
    (by simp [hspl])] at h_mem
  -- 0–8 guard and prologue
  kat hk unmarshalSSZ 0
  kat hk unmarshalSSZ 1
  kat hk unmarshalSSZ 2
  kat hk unmarshalSSZ 3
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk unmarshalSSZ 4
  split
  case isTrue h =>
    exfalso
    rw [Codec.lea_cmp_be_false rsp.toBitVec _ guard.toBitVec _ _ 48 (by rfl)
      (by rw [UInt64.toNat_toBitVec, UInt64.toNat_toBitVec]; omega)] at h
    exact Bool.noConfusion h
  simp only [Effects.All]
  kat hk unmarshalSSZ 5
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by iaaddr) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk unmarshalSSZ 6
  kat hk unmarshalSSZ 7
  kat hk unmarshalSSZ 8
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by iaaddr) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  -- 9–17 size and offset checks (not taken)
  kat hk unmarshalSSZ 9
  kat hk unmarshalSSZ 10
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
  simp only [Effects.All]
  kat hk unmarshalSSZ 11
  apply load_step _ _ _ _ offsetBytes _ _ (by ecancel) (by rfl)
  kunfold
  kat hk unmarshalSSZ 12
  kat hk unmarshalSSZ 13
  kat hk unmarshalSSZ 14
  kat hk unmarshalSSZ 15
  kat hk unmarshalSSZ 16
  kat hk unmarshalSSZ 17
  split
  case isTrue h => exfalso; revert h; decide
  simp only [Effects.All]
  -- 18–30 slice header, alignment and bound checks
  kat hk unmarshalSSZ 18
  kat hk unmarshalSSZ 19
  kat hk unmarshalSSZ 20
  kat hk unmarshalSSZ 21
  kshl64 63
  kat hk unmarshalSSZ 22
  intro _
  kat hk unmarshalSSZ 23
  kat hk unmarshalSSZ 24
  kat hk unmarshalSSZ 25
  intro _
  have hr8 : (-228 + rcx.toBitVec).toNat = 8 * n := by
    rw [BitVec.add_comm, Decode.sub228 _ (by rw [UInt64.toNat_toBitVec]; omega), UInt64.toNat_toBitVec]; omega
  have hal : (-228 + rcx.toBitVec &&& 7) = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, hr8]
    show 8 * n &&& 7 = 0
    rw [show (7 : Nat) = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega
  kat hk unmarshalSSZ 26
  split
  case isTrue h => exfalso; rw [hal] at h; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk unmarshalSSZ 27
  kshl64 3
  have hq : (BitVec.ushiftRight (-228 + rcx.toBitVec) 3).toNat = n := by
    rw [show (-228 + rcx.toBitVec).ushiftRight 3 = (-228 + rcx.toBitVec) >>> 3 from rfl, BitVec.toNat_ushiftRight, hr8,
      Nat.shiftRight_eq_div_pow]; omega
  kat hk unmarshalSSZ 28
  kat hk unmarshalSSZ 29
  kat hk unmarshalSSZ 30
  split
  case isTrue h => exfalso; rw [Decode.jg2048_false _ _ (by omega)] at h; exact Bool.noConfusion h
  simp only [Effects.All]
  -- name the computed values (AC normalization in `ecancel` does not stop on the raw `sar`/`and` term)
  have hPib := Decode.input_pointer_mask ib n hib rbx.toBitVec rdi.toBitVec (by rw [UInt64.toNat_toBitVec]; omega)
    (by rw [UInt64.toNat_toBitVec]; omega)
  have hC := Decode.sub228 rdi.toBitVec (by rw [UInt64.toNat_toBitVec]; omega)
  generalize rbx.toBitVec + BitVec.zeroExtend 64 (BitVec.extractLsb' 0 32
    (BitVec.sshiftRight (-(rdi.toBitVec + -228)) 63) &&& BitVec.truncate 32 (228 : BitVec 64)) = P at hPib ⊢
  generalize rdi.toBitVec + -228 = C at hC ⊢
  generalize BitVec.ushiftRight (-228 + rcx.toBitVec) 3 = Q at hq ⊢
  -- 31–39 spills and the AttestingIndices `makeslice`
  kat hk unmarshalSSZ 31
  apply store_step_at _ _ (rsp.toBitVec + 8) _ _ _ s1 _ _ (by iaaddr) (by ecancel) (by exact h1)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk unmarshalSSZ 32
  apply store_step_at _ _ (rsp.toBitVec + 32) _ _ _ s4 _ _ (by iaaddr) (by ecancel) (by exact h4)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  kat hk unmarshalSSZ 33
  apply store_step_at _ _ (rsp.toBitVec - 120) _ _ _ l38 _ _ (by iaaddr) (by ecancel) (by exact hl38)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  kat hk unmarshalSSZ 34
  apply store_step_at _ _ (rsp.toBitVec - 112) _ _ _ l40 _ _ (by iaaddr) (by ecancel) (by exact hl40)
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  kat hk unmarshalSSZ 35
  apply store_step_at _ _ (rsp.toBitVec - 136) _ _ _ l28 _ _ (by iaaddr) (by ecancel) (by exact hl28)
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  kat hk unmarshalSSZ 36
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by iaaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m8 H8
  simp only [Width.bytes, Width.bits] at H8
  kunfold
  kat hk unmarshalSSZ 37
  kat hk unmarshalSSZ 38
  kat hk unmarshalSSZ 39
  apply store_step_at _ _ (rsp.toBitVec - 184) _ _ _ rslot _ _ (by iaaddr) (by ecancel) (by exact hrs)
  intro m9 H9
  simp only [Width.bytes, Width.bits] at H9
  kunfold
  rw [show rsp.toBitVec - 8#64 - 168 - 8#64 = rsp.toBitVec - 184 by iaaddr]
  refine eventually_trans _ _ _ _ (hmsU _ (Host.addrOf (k + 39 + 1)) n avail lo
    (spl.take 8 ++ ((spl.drop 8).take 8 ++ (spl.drop 16).take 8)) _
    rfl (by show Q.toNat ≤ n; omega) hq (by omega) (by unfold maxAlloc; omega) (by omega) hlo (by simp [hspl])
    (by
      dsimp only
      rw [show rsp.toBitVec - 184 + 8 = rsp.toBitVec - 176 by iaaddr,
        Decode.j3 _ _ _ _ (by simp [hspl]) (by simp [hspl]) (by simp [hspl])]
      ecancel)) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrsp3, hr143, hrbp3, stk3, spm3, hstk3, hspm3, Hm3⟩
  dsimp only at hpc3 hrsp3 hr143 hrbp3 Hm3
  subst hpc3
  obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,
    zmms3, flags3, mem3⟩ := d3
  simp only at hrsp3 hr143 hrbp3 Hm3
  rw [show ({ toBitVec := rsp.toBitVec - 184 } + 8 : UInt64) = { toBitVec := rsp.toBitVec - 176 } by
    apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; iaaddr] at hrsp3
  subst hrsp3 hr143 hrbp3
  rw [show rsp.toBitVec - 184 + 8 = rsp.toBitVec - 176 by iaaddr] at Hm3
  -- 40–56: len = cap = n, writeBarrier = 0, ptr, rcx = cap − 228, rbx = buf[228:], rax = 0, `jmp L_28a`
  kat hk unmarshalSSZ 40
  apply load_step_at _ _ (rsp.toBitVec - 136) _ _ (Int.toBytes 8 Q.toInt) _ _ (by iaaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk unmarshalSSZ 41
  apply load_step_at _ _ (rsp.toBitVec + 8) _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by iaaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk unmarshalSSZ 42
  apply store_step_at _ _ (rax.toBitVec + 16) _ _ _ aL1 _ _ (by iaaddr) (by ecancel) (by exact haL1)
  intro m10 H10
  simp only [Width.bytes, Width.bits] at H10
  kunfold
  kat hk unmarshalSSZ 43
  apply store_step_at _ _ (rax.toBitVec + 24) _ _ _ aC1 _ _ (by iaaddr) (by ecancel) (by exact haC1)
  intro m11 H11
  simp only [Width.bytes, Width.bits] at H11
  kunfold
  kat hk unmarshalSSZ 44
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk unmarshalSSZ 45
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf unmarshalSSZ 50
  kat hk unmarshalSSZ 50
  kat hk unmarshalSSZ 51
  apply store_step_at _ _ (rax.toBitVec + 8) _ _ _ aP1 _ _ (by iaaddr) (by ecancel) (by exact haP1)
  intro m12 H12
  simp only [Width.bytes, Width.bits] at H12
  kunfold
  kat hk unmarshalSSZ 52
  apply load_step_at _ _ (rsp.toBitVec - 120) _ _ (Int.toBytes 8 C.toInt) _ _ (by iaaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk unmarshalSSZ 53
  apply load_step_at _ _ (rsp.toBitVec - 112) _ _ (Int.toBytes 8 P.toInt) _ _ (by iaaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk unmarshalSSZ 54
  intro _
  kat hk unmarshalSSZ 55
  kat hk unmarshalSSZ 56
  klabel hk hf unmarshalSSZ 147
  -- element loop: L_28a (147) → L_2cc (166)
  refine eventually_trans _ _ _ _ (Decode.loop k hk hf ib n hib hn P rax.toBitVec rax3.toBitVec Q hq _ _ _ _ n 0 _
    (by omega) (by show (BitVec.zeroExtend 64 _).toNat = 0; simp) hq
    (by show 8 * n ≤ C.toNat; rw [hC, UInt64.toNat_toBitVec]; omega) rfl rfl rfl rfl rfl
    (by
      dsimp only
      rw [hPib]
      simp only [Nat.mul_zero, List.take_zero, Nat.sub_zero, List.nil_append]
      ecancel)) ?_
  rintro ⟨d4, pc4⟩ ⟨hpc4, hrsp4, hrbp4, hr144, Hm4⟩
  dsimp only at hpc4 hrsp4 hrbp4 hr144 Hm4
  subst hpc4
  obtain ⟨⟨rax4, rbx4, rcx4, rdx4, rsi4, rdi4, rsp4, rbp4, r84, r94, r104, r114, r124, r134, r144, r154⟩,
    zmms4, flags4, mem4⟩ := d4
  simp only at hrsp4 hrbp4 hr144 Hm4
  subst hrsp4 hrbp4 hr144
  rw [hPib] at Hm4
  -- 166–168: the AttestationData object (`newobject`)
  kat hk unmarshalSSZ 166
  kat hk unmarshalSSZ 167
  kat hk unmarshalSSZ 168
  apply store_step_at _ _ (rsp.toBitVec - 184) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 39 + 1)).toBitVec.toInt) _ _
    (by iaaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m13 H13
  simp only [Width.bytes, Width.bits] at H13
  kunfold
  rw [show rsp.toBitVec - 176 - 8#64 = rsp.toBitVec - 184 by iaaddr]
  obtain ⟨q0, rq, hq0, hrq, rfl⟩ := Decode.bytes_split spm3 8 (by omega)
  obtain ⟨q1, q2, hq1, -, rfl⟩ := Decode.bytes_split rq 8 (by omega)
  have hq2 : q2.length = 8 := by simp only [List.length_append, hq0, hq1] at hspm3; omega
  rw [Decode.j3 _ _ _ _ hq0 hq1 hq2] at H13
  refine eventually_trans _ _ _ _ (hno _ (Host.addrOf (k + 168 + 1)) (avail - 8 * n) stk3 q0 _
    rfl (by omega) hstk3 hq0
    (by dsimp only; rw [show rsp.toBitVec - 184 + 8 = rsp.toBitVec - 176 by iaaddr]; ecancel)) ?_
  rintro ⟨d5, pc5⟩ ⟨hpc5, hrsp5, hr145, hrbp5, stk5, spm5, hstk5, hspm5, Hm5⟩
  dsimp only at hpc5 hrsp5 hr145 hrbp5 Hm5
  subst hpc5
  obtain ⟨⟨rax5, rbx5, rcx5, rdx5, rsi5, rdi5, rsp5, rbp5, r85, r95, r105, r115, r125, r135, r145, r155⟩,
    zmms5, flags5, mem5⟩ := d5
  simp only at hrsp5 hr145 hrbp5 Hm5
  rw [show ({ toBitVec := rsp.toBitVec - 184 } + 8 : UInt64) = { toBitVec := rsp.toBitVec - 176 } by
    apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; iaaddr] at hrsp5
  subst hrsp5 hr145 hrbp5
  rw [show rsp.toBitVec - 184 + 8 = rsp.toBitVec - 176 by iaaddr, Decode.obj96] at Hm5
  -- 169–187: writeBarrier = 0, Data pointer, the arguments buf[4:132] (rbx, rcx = 128, rdi = cap − 4), the call
  kat hk unmarshalSSZ 169
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk unmarshalSSZ 170
  kat hk unmarshalSSZ 171
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk unmarshalSSZ 172
  apply load_step_at _ _ (rsp.toBitVec + 8) _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by iaaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk unmarshalSSZ 173
  klabel hk hf unmarshalSSZ 180
  kat hk unmarshalSSZ 180
  kat hk unmarshalSSZ 181
  apply store_step_at _ _ (rax.toBitVec + 32) _ _ _ aD _ _ (by iaaddr) (by ecancel) (by exact haD)
  intro m14 H14
  simp only [Width.bytes, Width.bits] at H14
  kunfold
  kat hk unmarshalSSZ 182
  apply load_step_at _ _ (rsp.toBitVec + 16) _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by iaaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk unmarshalSSZ 183
  kat hk unmarshalSSZ 184
  apply load_step_at _ _ (rsp.toBitVec + 32) _ _ (Int.toBytes 8 rdi.toBitVec.toInt) _ _ (by iaaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk unmarshalSSZ 185
  kat hk unmarshalSSZ 186
  kat hk unmarshalSSZ 187
  apply store_step_at _ _ (rsp.toBitVec - 184) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 168 + 1)).toBitVec.toInt) _ _
    (by iaaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m15 H15
  simp only [Width.bytes, Width.bits] at H15
  kunfold
  rw [show rsp.toBitVec - 176 - 8#64 = rsp.toBitVec - 184 by iaaddr]
  rw [show label "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ"
    = Host.addrOf (kA + 0) from label_at hkA hfA (j := 0) (by rfl) (by intro i hi; omega)]
  -- our scratch as the callee's frame
  obtain ⟨fa, r1, hfa, hr1, rfl⟩ := Decode.bytes_split stk5 (Sd + 96) (by omega)
  obtain ⟨fb, r2, hfb, hr2, rfl⟩ := Decode.bytes_split r1 8 (by omega)
  obtain ⟨fc0, r3, hfc0, hr3, rfl⟩ := Decode.bytes_split r2 8 (by omega)
  obtain ⟨fc1, r4, hfc1, hr4, rfl⟩ := Decode.bytes_split r3 8 (by omega)
  obtain ⟨fc2, r5, hfc2, hr5, rfl⟩ := Decode.bytes_split r4 8 (by omega)
  obtain ⟨fd, r6, hfd, hr6, rfl⟩ := Decode.bytes_split r5 80 (by omega)
  obtain ⟨fe, ff, hfe, hff, rfl⟩ := Decode.bytes_split r6 8 (by omega)
  simp only [List.length_append] at hstk5 hr1 hr2 hr3 hr4 hr5 hr6 hff
  rw [Decode.lo8 rsp.toBitVec (rsp.toBitVec - 184) Sd hSd rfl fa fb fc0 fc1 fc2 fd fe ff hfa hfb hfc0 hfc1 hfc2 hfd hfe
    (by omega)] at H15
  refine eventually_trans _ _ _ _ (Prysm.AttestationData.Decode.accept kA hkA hfA kS hkS hfS kI hkI hfI kC hkC hfC kE hkE hfE
    in0 in1 root se sroot te troot hin0 hin1 hroot hse hsroot hte htroot _
    (UInt64.ofBitVec (Host.addrOf (k + 187 + 1)).toBitVec) guard
    ff spm5 q1 ((spl.drop 24).take 8) fc0 fc1 fc2 fe fb fa
    (List.replicate 8 0) (List.replicate 8 0) (List.replicate 8 0) (List.replicate 8 0) (List.replicate 8 0)
    (List.replicate 8 0) (List.replicate 8 0) (List.replicate 8 0)
    (by omega) hspm5 hq1 (by simp [hspl]) hfc0 hfc1 hfc2 hfe hfb (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) _ Sd hSd8 hSd hfa Heap (avail - 8 * n - 96)
    (by
      dsimp only
      rw [show rsp.toBitVec - 184 + 8 = rsp.toBitVec - 176 by iaaddr,
        show rsp.toBitVec - 184 + 16 = rsp.toBitVec - 168 by iaaddr,
        show rsp.toBitVec - 184 + 32 = rsp.toBitVec - 152 by iaaddr,
        show 4 + rbx.toBitVec = rbx.toBitVec + 4 by iaaddr,
        show rbx.toBitVec + 4 + 8 = rbx.toBitVec + 12 by iaaddr,
        show rbx.toBitVec + 4 + 16 = rbx.toBitVec + 20 by iaaddr,
        show rbx.toBitVec + 4 + 48 = rbx.toBitVec + 52 by iaaddr,
        show rbx.toBitVec + 4 + 56 = rbx.toBitVec + 60 by iaaddr,
        show rbx.toBitVec + 4 + 88 = rbx.toBitVec + 92 by iaaddr,
        show rbx.toBitVec + 4 + 96 = rbx.toBitVec + 100 by iaaddr]
      ecancel)
    (by
      dsimp only
      show guard.toNat + 224 < (rsp.toBitVec - 184).toNat
      have hg := hguard
      rw [← UInt64.toNat_toBitVec rsp] at hg
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, Nat.reducePow]
      omega)
    (by rfl) (by omega) hmsD hmmD hmsD' hmmD' hnoD) ?_
  rintro ⟨d6, pc6⟩ ⟨hpc6, hrax6, hrbx6, hrsp6, hrbp6, hr146, p, ps, pt, p1, p2, w, lo6, hw, hlo6, Hm6⟩
  dsimp only at hpc6 hrax6 hrbx6 hrsp6 hrbp6 hr146 Hm6
  simp only [Int64.ofBitVec_toBitVec] at hpc6 Hm6
  subst hpc6
  obtain ⟨⟨rax6, rbx6, rcx6, rdx6, rsi6, rdi6, rsp6, rbp6, r86, r96, r106, r116, r126, r136, r146, r156⟩,
    zmms6, flags6, mem6⟩ := d6
  simp only at hrax6 hrbx6 hrsp6 hrbp6 hr146 Hm6
  rw [show ({ toBitVec := rsp.toBitVec - 184 } + 8 : UInt64) = { toBitVec := rsp.toBitVec - 176 } by
    apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; iaaddr] at hrsp6
  subst hrax6 hrbx6 hrsp6 hrbp6 hr146
  rw [show rsp.toBitVec - 184 + 8 = rsp.toBitVec - 176 by iaaddr,
    show rsp.toBitVec - 184 + 16 = rsp.toBitVec - 168 by iaaddr,
    show rsp.toBitVec - 184 + 32 = rsp.toBitVec - 152 by iaaddr,
    show 4 + rbx.toBitVec = rbx.toBitVec + 4 by iaaddr,
    show rbx.toBitVec + 4 + 8 = rbx.toBitVec + 12 by iaaddr,
    show rbx.toBitVec + 4 + 16 = rbx.toBitVec + 20 by iaaddr,
    show rbx.toBitVec + 4 + 48 = rbx.toBitVec + 52 by iaaddr,
    show rbx.toBitVec + 4 + 56 = rbx.toBitVec + 60 by iaaddr,
    show rbx.toBitVec + 4 + 88 = rbx.toBitVec + 92 by iaaddr,
    show rbx.toBitVec + 4 + 96 = rbx.toBitVec + 100 by iaaddr] at Hm6
  -- the callee's saved-rbp word (in our scratch): a name, so that `ecancel` matches it structurally
  have hvb := Int.toBytes_length 8 (BitVec.toInt (rsp.toBitVec - 8#64))
  generalize Int.toBytes 8 (BitVec.toInt (rsp.toBitVec - 8#64)) = vb at Hm6 hvb
  have hv4 := Int.toBytes_length 8 (BitVec.toInt (-4 + rdi.toBitVec))
  generalize Int.toBytes 8 (BitVec.toInt (-4 + rdi.toBitVec)) = v4 at Hm6 hv4
  -- 188–189: err = nil, `je L_39c` taken
  kat hk unmarshalSSZ 188
  try intro _
  kat hk unmarshalSSZ 189
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf unmarshalSSZ 217
  -- 217–223: spill rbx, rax (both 0), the Signature `makeslice` (len 0, cap 96)
  kat hk unmarshalSSZ 217
  kat hk unmarshalSSZ 218
  apply store_step_at _ _ (rsp.toBitVec - 104) _ _ _ l48 _ _ (by iaaddr) (by ecancel) (by exact hl48)
  intro m16 H16
  simp only [Width.bytes, Width.bits] at H16
  kunfold
  kat hk unmarshalSSZ 219
  apply store_step_at _ _ (rsp.toBitVec - 128) _ _ _ l30 _ _ (by iaaddr) (by ecancel) (by exact hl30)
  intro m17 H17
  simp only [Width.bytes, Width.bits] at H17
  kunfold
  kat hk unmarshalSSZ 220
  kat hk unmarshalSSZ 221
  intro _
  kat hk unmarshalSSZ 222
  kat hk unmarshalSSZ 223
  apply store_step_at _ _ (rsp.toBitVec - 184) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 187 + 1)).toBitVec.toInt) _ _
    (by iaaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m18 H18
  simp only [Width.bytes, Width.bits] at H18
  kunfold
  rw [show rsp.toBitVec - 176 - 8#64 = rsp.toBitVec - 184 by iaaddr]
  refine eventually_trans _ _ _ _ (hms _ (Host.addrOf (k + 223 + 1)) 96 (avail - 8 * n - 96 - 240)
    (lo6 ++ (Int.toBytes 8 (Host.addrOf (kA + 193)).toBitVec.toInt ++ (Int.toBytes 8 pt.toInt
      ++ (Int.toBytes 8 (rbx.toBitVec + 92).toInt ++ (w ++ (fd ++ (Int.toBytes 8 p.toInt ++ vb)))))))
    (Int.toBytes 8 rax5.toBitVec.toInt ++ (Int.toBytes 8 (BitVec.toInt (rbx.toBitVec + 4)) ++ q2)) _
    rfl (by show (0 : Nat) ≤ 96; omega) (by rfl) (by omega) (by unfold maxAlloc; omega) (by omega)
    (by simp only [List.length_append, Int.toBytes_length, hlo6, hw, hfd, hvb])
    (by simp only [List.length_append, Int.toBytes_length, hq2])
    (by
      dsimp only
      rw [show rsp.toBitVec - 184 + 8 = rsp.toBitVec - 176 by iaaddr,
        Decode.j3 _ _ _ _ (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) hq2,
        Decode.lo8 rsp.toBitVec (rsp.toBitVec - 184) Sd hSd rfl _ _ _ _ _ _ _ _ hlo6 (Int.toBytes_length 8 _)
          (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) hw hfd (Int.toBytes_length 8 _) hvb]
      ecancel)) ?_
  rintro ⟨d7, pc7⟩ ⟨hpc7, hrsp7, hr147, hrbp7, stk7, spm7, hstk7, hspm7, Hm7⟩
  dsimp only at hpc7 hrsp7 hr147 hrbp7 Hm7
  subst hpc7
  obtain ⟨⟨rax7, rbx7, rcx7, rdx7, rsi7, rdi7, rsp7, rbp7, r87, r97, r107, r117, r127, r137, r147, r157⟩,
    zmms7, flags7, mem7⟩ := d7
  simp only at hrsp7 hr147 hrbp7 Hm7
  rw [show ({ toBitVec := rsp.toBitVec - 184 } + 8 : UInt64) = { toBitVec := rsp.toBitVec - 176 } by
    apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; iaaddr] at hrsp7
  subst hrsp7 hr147 hrbp7
  rw [show rsp.toBitVec - 184 + 8 = rsp.toBitVec - 176 by iaaddr] at Hm7
  simp only [Nat.one_mul] at Hm7
  -- 224–240: Signature len 0, cap 96, writeBarrier = 0, ptr (also at rsp − 16), `memmove(psig, buf + 132, 96)`
  kat hk unmarshalSSZ 224
  apply load_step_at _ _ (rsp.toBitVec + 8) _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by iaaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  have e0 : Int.toBytes 8 (BitVec.toInt (0 : BitVec 64)) = Int.toBytes 8 0 := by decide
  have e96 : Int.toBytes 8 (BitVec.toInt (96 : BitVec 64)) = Int.toBytes 8 96 := by decide
  kat hk unmarshalSSZ 225
  apply store_step_at _ _ (rax.toBitVec + 48) _ _ _ aL2 _ _ (by iaaddr) (by ecancel) (by exact haL2)
  intro m19 H19
  simp only [Width.bytes, Width.bits, e0] at H19
  kunfold
  kat hk unmarshalSSZ 226
  apply store_step_at _ _ (rax.toBitVec + 56) _ _ _ aC2 _ _ (by iaaddr) (by ecancel) (by exact haC2)
  intro m20 H20
  simp only [Width.bytes, Width.bits, e96] at H20
  kunfold
  kat hk unmarshalSSZ 227
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk unmarshalSSZ 228
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf unmarshalSSZ 234
  kat hk unmarshalSSZ 234
  kat hk unmarshalSSZ 235
  apply store_step_at _ _ (rsp.toBitVec - 16) _ _ _ la0 _ _ (by iaaddr) (by ecancel) (by exact hla0)
  intro m21 H21
  simp only [Width.bytes, Width.bits] at H21
  kunfold
  kat hk unmarshalSSZ 236
  apply store_step_at _ _ (rax.toBitVec + 40) _ _ _ aP2 _ _ (by iaaddr) (by ecancel) (by exact haP2)
  intro m22 H22
  simp only [Width.bytes, Width.bits] at H22
  kunfold
  kat hk unmarshalSSZ 237
  apply load_step_at _ _ (rsp.toBitVec + 16) _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by iaaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk unmarshalSSZ 238
  kat hk unmarshalSSZ 239
  kat hk unmarshalSSZ 240
  apply store_step_at _ _ (rsp.toBitVec - 184) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 223 + 1)).toBitVec.toInt) _ _
    (by iaaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m23 H23
  simp only [Width.bytes, Width.bits] at H23
  kunfold
  rw [show rsp.toBitVec - 176 - 8#64 = rsp.toBitVec - 184 by iaaddr]
  refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (k + 240 + 1)) sig (List.replicate 96 0) stk7 _
    (by rw [hsig]; rfl) (by simp [hsig]) hstk7
    (by
      dsimp only
      try rw [show 132 + rbx.toBitVec = rbx.toBitVec + 132 by iaaddr]
      ecancel)) ?_
  rintro ⟨d8, pc8⟩ ⟨hpc8, hrsp8, hr148, hrbp8, stk8, hstk8, Hm8⟩
  dsimp only at hpc8 hrsp8 hr148 hrbp8 Hm8
  subst hpc8
  obtain ⟨⟨rax8, rbx8, rcx8, rdx8, rsi8, rdi8, rsp8, rbp8, r88, r98, r108, r118, r128, r138, r148, r158⟩,
    zmms8, flags8, mem8⟩ := d8
  simp only at hrsp8 hr148 hrbp8 Hm8
  rw [show ({ toBitVec := rsp.toBitVec - 184 } + 8 : UInt64) = { toBitVec := rsp.toBitVec - 176 } by
    apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; iaaddr] at hrsp8
  subst hrsp8 hr148 hrbp8
  rw [show 132 + rbx.toBitVec = rbx.toBitVec + 132 by iaaddr] at Hm8
  -- 241–260: len = cap = 96, writeBarrier = 0, ptr, rax = rbx = 0 (the spilled nil error), epilogue
  kat hk unmarshalSSZ 241
  apply load_step_at _ _ (rsp.toBitVec + 8) _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by iaaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk unmarshalSSZ 242
  apply store_step_at _ _ (rax.toBitVec + 48) _ _ _ (Int.toBytes 8 0) _ _ (by iaaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m24 H24
  simp only [Width.bytes, Width.bits, e96] at H24
  kunfold
  kat hk unmarshalSSZ 243
  apply store_step_at _ _ (rax.toBitVec + 56) _ _ _ (Int.toBytes 8 96) _ _ (by iaaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m25 H25
  simp only [Width.bytes, Width.bits, e96] at H25
  kunfold
  kat hk unmarshalSSZ 244
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk unmarshalSSZ 245
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk unmarshalSSZ 246
  apply load_step_at _ _ (rsp.toBitVec - 16) _ _ (Int.toBytes 8 rax7.toBitVec.toInt) _ _ (by iaaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk unmarshalSSZ 247
  klabel hk hf unmarshalSSZ 254
  kat hk unmarshalSSZ 254
  kat hk unmarshalSSZ 255
  apply store_step_at _ _ (rax.toBitVec + 40) _ _ _ (Int.toBytes 8 rax7.toBitVec.toInt) _ _ (by iaaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m26 H26
  simp only [Width.bytes, Width.bits] at H26
  kunfold
  kat hk unmarshalSSZ 256
  apply load_step_at _ _ (rsp.toBitVec - 128) _ _ (Int.toBytes 8 (0#64).toInt) _ _ (by iaaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk unmarshalSSZ 257
  apply load_step_at _ _ (rsp.toBitVec - 104) _ _ (Int.toBytes 8 (0#64).toInt) _ _ (by iaaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk unmarshalSSZ 258
  try intro _
  kat hk unmarshalSSZ 259
  apply load_step_at _ _ (rsp.toBitVec - 8) _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by iaaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk unmarshalSSZ 260
  apply load_step_at _ _ rsp.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by iaaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  have hQi : Q.toInt = (n : Int) := by rw [BitVec.toInt_eq_toNat_of_lt (by omega), hq]
  rw [hQi, show k + 240 + 1 = k + 241 from rfl, show avail - 8 * n - 96 - 240 - 96 = avail - (8 * n + 432) by omega]
    at H26
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rax3.toBitVec, rax5.toBitVec, p, ps, pt, p1, p2, rax7.toBitVec,
    Int.toBytes 8 (n : Int), Int.toBytes 8 (0#64).toInt, Int.toBytes 8 C.toInt, Int.toBytes 8 P.toInt,
    Int.toBytes 8 (0#64).toInt, spm7 ++ (v4 ++ spl.drop 32), stk8, Int.toBytes_length 8 _, Int.toBytes_length 8 _,
    Int.toBytes_length 8 _, Int.toBytes_length 8 _, Int.toBytes_length 8 _,
    by simp only [List.length_append, List.length_drop, hspm7, hv4, hspl], hstk8, ?_⟩
  rotate_right
  · rw [at_app spm7 (v4 ++ spl.drop 32) (b := rsp.toBitVec - 152) (by rw [hspm7]; iaaddr)
        (by simp only [List.length_append, List.length_drop, hspm7, hv4, hspl]; omega),
      at_app v4 (spl.drop 32) (b := rsp.toBitVec - 144) (by rw [hv4]; iaaddr)
        (by simp only [List.length_drop, hv4, hspl]; omega)]
    ecancel
  all_goals first
    | exact trivial
    | with_reducible rfl
    | (apply UInt64.toBitVec_inj.mp
       simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, Width.bits]
       done)
    | (apply UInt64.toBitVec_inj.mp; iaaddr)

end Prysm.IndexedAttestation
