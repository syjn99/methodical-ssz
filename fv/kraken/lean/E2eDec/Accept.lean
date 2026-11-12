import Codec.StackGuard
import E2eList.IaAccept
import E2eEnc.Tail
import E2eDec.Reject
import E2eDec.Loop

/-!
# Decoder `(*v1alpha1.DataColumnsByRootIdentifier).UnmarshalSSZ`, accept path (Go 1.26.10 machine code)

The order of `E2eList/IaAccept.lean` (IndexedAttestation accept path): guard and prologue 0–8, size and offset checks 9–15, spills 16–19,
BlockRoot `makeslice` 20–23 (`MakesliceC Heap e2eU8Type_addr 1 S`, len 0, cap 32), header stores 24–26, the
`buf[36:]` pointer 27–35 (the mask of `IaAccept.lean` 18–24 with 36), `writeBarrier = 0` (36–37 `je` taken), 43–47 the pointer store
and `memmove(pb, buf, 32)`, 48–63 len/cap 32 and the barrier branch, 64–71 alignment and bound checks, 72–75 Columns
`makeslice` (`MakesliceC Heap lvU64Type_addr 8 S`, len = cap = n), 76–93 the header and pointer stores, `jmp L_320`,
the element loop `dcd_loop` (185 → 204), 204–209 nil and the epilogue. Statement: the frozen `dcd_accept_stmt`.
-/

open Machine Runtime TestTarget E2eDec.Code
variable [Host]

namespace E2eDec

omit [Host] in
theorem dcd_mask_ones :
    BitVec.zeroExtend 64 (BitVec.extractLsb' 0 32 (BitVec.allOnes 64) &&& BitVec.truncate 32 (36 : BitVec 64))
      = 36 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.truncate_eq_setWidth, BitVec.toNat_and, BitVec.extractLsb'_toNat,
    BitVec.toNat_allOnes, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_zero, Nat.reducePow,
    Nat.reduceSub, Nat.reduceMod, Nat.reduceAnd]

omit [Host] in
/-- `c − 36` as a natural number (the form of `E2eList.ia_sub228`: no `simp` on the negative literal). -/
theorem dcd_sub36 (c : BitVec 64) (h : 36 ≤ c.toNat) : (-36 + c).toNat = c.toNat - 36 := by
  rw [BitVec.add_comm, ← BitVec.sub_eq_add_neg, BitVec.toNat_sub_of_le]
  · rfl
  · rw [BitVec.le_def]; exact h

omit [Host] in
/-- The `buf[36:]` pointer of directives 27–34 (`rbx + (cap − 36 > 0 ? 36 : 0)`) addresses the element bytes: when
cap = 36 the list is empty. Uses `cap < 2⁶³` (the `sar` sign test). The text of `E2eList.ia_p0`. -/
theorem dcd_p0 (ib : List UInt8) (n : Nat) (hib : ib.length = 8 * n) (b c : BitVec 64) (hc : 36 + 8 * n ≤ c.toNat)
    (h63 : c.toNat < 2 ^ 63) :
    Eq (ib.At (b + BitVec.zeroExtend 64 (BitVec.extractLsb' 0 32 (BitVec.sshiftRight (-(-36 + c)) 63)
      &&& BitVec.truncate 32 (36 : BitVec 64)))) = Eq (ib.At (b + 36)) := by
  by_cases h : c.toNat = 36
  · have hn : n = 0 := by omega
    subst hn
    have : ib = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp only [List.At, List.mapIdx_nil]
  · have hd := dcd_sub36 c (by omega)
    rw [E2eList.ia_sar63 _ (by omega) (by omega), dcd_mask_ones]

-- Measured: heartbeats: the default 200000 fails (`whnf` timeout at the loop call), 400000 passes;
-- recursion depth: the default fails at `klabel` (directive 185, the `simp` that unfolds the program literal), 1024 passes.
set_option maxHeartbeats 400000 in
set_option maxRecDepth 1024 in
theorem dcd_e2e_accept_main : dcd_accept_stmt := by
  intro k hk hf n hn root ib hroot hib s ra guard fp s1 s2 s3 s4 l28 l30 l38 l40 spl rslot lo aP1 aL1 aC1 aP2 aL2 aC2
    hfp h1 h2 h3 h4 hl28 hl30 hl38 hl40 hspl hrs haP1 haL1 haC1 haP2 haL2 haC2 S hlo R Heap avail h_mem
    hguard hlen hcap hcap63 hav hms hmsU hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen hcap hcap63
  dsimp only
  have hz1 := rsp.toNat_lt_size; have hz2 := guard.toNat_lt_size; have hz3 := rcx.toNat_lt_size
  have hz4 := rdi.toNat_lt_size
  simp only [UInt64.size] at hz1 hz2 hz3 hz4
  -- the spill area: the 24 makeslice spill bytes and the rest
  rw [show spl = spl.take 24 ++ spl.drop 24 from (List.take_append_drop 24 spl).symm,
    at_app (spl.take 24) (spl.drop 24) (b := rsp.toBitVec - 120) (by simp [hspl]; dcaddr) (by simp [hspl])] at h_mem
  -- 0–8 guard and prologue
  kat hk DcUnmarshal 0
  kat hk DcUnmarshal 1
  kat hk DcUnmarshal 2
  kat hk DcUnmarshal 3
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk DcUnmarshal 4
  split
  case isTrue h =>
    exfalso
    rw [Codec.lea_cmp_be_false rsp.toBitVec _ guard.toBitVec _ _ 16 (by rfl)
      (by rw [UInt64.toNat_toBitVec, UInt64.toNat_toBitVec]; omega)] at h
    exact Bool.noConfusion h
  simp only [Effects.All]
  kat hk DcUnmarshal 5
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by dcaddr) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk DcUnmarshal 6
  kat hk DcUnmarshal 7
  kat hk DcUnmarshal 8
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by dcaddr) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  -- 9–15 size and offset checks (not taken)
  kat hk DcUnmarshal 9
  kat hk DcUnmarshal 10
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
  simp only [Effects.All]
  kat hk DcUnmarshal 11
  apply load_step_at _ _ (rbx.toBitVec + 32) _ _ E2eEnc.dcOff _ _ (by dcaddr) (by ecancel) (by rfl)
  kunfold
  kat hk DcUnmarshal 12
  kat hk DcUnmarshal 13
  kat hk DcUnmarshal 14
  kat hk DcUnmarshal 15
  split
  case isTrue h => exfalso; revert h; decide
  simp only [Effects.All]
  -- 16–19 spills
  kat hk DcUnmarshal 16
  apply store_step_at _ _ (rsp.toBitVec + 8) _ _ _ s1 _ _ (by dcaddr) (by ecancel) (by exact h1)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk DcUnmarshal 17
  apply store_step_at _ _ (rsp.toBitVec + 32) _ _ _ s4 _ _ (by dcaddr) (by ecancel) (by exact h4)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  kat hk DcUnmarshal 18
  apply store_step_at _ _ (rsp.toBitVec + 24) _ _ _ s3 _ _ (by dcaddr) (by ecancel) (by exact h3)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  kat hk DcUnmarshal 19
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by dcaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  -- 20–23 the BlockRoot makeslice (len 0, cap 32)
  kat hk DcUnmarshal 20
  kat hk DcUnmarshal 21
  intro _
  kat hk DcUnmarshal 22
  kat hk DcUnmarshal 23
  apply store_step_at _ _ (rsp.toBitVec - 152) _ _ _ rslot _ _ (by dcaddr) (by ecancel) (by exact hrs)
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  rw [show rsp.toBitVec - 8#64 - 136 - 8#64 = rsp.toBitVec - 152 by dcaddr]
  refine eventually_trans _ _ _ _ (hms _ (Host.addrOf (k + 23 + 1)) 32 avail lo (spl.take 24) _
    rfl (by simp) (by rfl) (by omega) (by unfold maxAlloc; omega) (by decide) hlo (by simp [hspl])
    (by
      dsimp only
      rw [show rsp.toBitVec - 152 + 8 = rsp.toBitVec - 144 by dcaddr]
      ecancel)) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrsp3, hr143, hrbp3, stk3, spm3, hstk3, hspm3, Hm3⟩
  dsimp only at hpc3 hrsp3 hr143 hrbp3 Hm3
  subst hpc3
  obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,
    zmms3, flags3, mem3⟩ := d3
  simp only at hrsp3 hr143 hrbp3 Hm3
  rw [show ({ toBitVec := rsp.toBitVec - 152 } + 8 : UInt64) = { toBitVec := rsp.toBitVec - 144 } by
    apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; dcaddr] at hrsp3
  subst hrsp3 hr143 hrbp3
  rw [show rsp.toBitVec - 152 + 8 = rsp.toBitVec - 144 by dcaddr] at Hm3
  simp only [Nat.one_mul] at Hm3
  -- 24–26 the BlockRoot header: len 0, cap 32
  kat hk DcUnmarshal 24
  apply load_step_at _ _ (rsp.toBitVec + 8) _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by dcaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk DcUnmarshal 25
  apply store_step_at _ _ (rax.toBitVec + 16) _ _ _ aL1 _ _ (by dcaddr) (by ecancel) (by exact haL1)
  intro m8 H8
  simp only [Width.bytes, Width.bits] at H8
  kunfold
  kat hk DcUnmarshal 26
  apply store_step_at _ _ (rax.toBitVec + 24) _ _ _ aC1 _ _ (by dcaddr) (by ecancel) (by exact haC1)
  intro m9 H9
  simp only [Width.bytes, Width.bits] at H9
  kunfold
  -- 27–35 the buf[36:] pointer
  kat hk DcUnmarshal 27
  apply load_step_at _ _ (rsp.toBitVec + 32) _ _ (Int.toBytes 8 rdi.toBitVec.toInt) _ _ (by dcaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk DcUnmarshal 28
  generalize hCdef : -36 + rdi.toBitVec = C
  kat hk DcUnmarshal 29
  apply store_step_at _ _ (rsp.toBitVec - 104) _ _ _ l28 _ _ (by dcaddr) (by ecancel) (by exact hl28)
  intro m10 H10
  simp only [Width.bytes, Width.bits] at H10
  kunfold
  kat hk DcUnmarshal 30
  kat hk DcUnmarshal 31
  kshl64 63
  kat hk DcUnmarshal 32
  intro _
  kat hk DcUnmarshal 33
  apply load_step_at _ _ (rsp.toBitVec + 16) _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by dcaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk DcUnmarshal 34
  -- name the computed values (as in `E2eList/IaAccept.lean`)
  have hPib := dcd_p0 ib n hib rbx.toBitVec rdi.toBitVec (by rw [UInt64.toNat_toBitVec]; omega)
    (by rw [UInt64.toNat_toBitVec]; omega)
  have hC := dcd_sub36 rdi.toBitVec (by rw [UInt64.toNat_toBitVec]; omega)
  rw [hCdef] at hPib hC
  generalize rbx.toBitVec + BitVec.zeroExtend 64 (BitVec.extractLsb' 0 32
    (BitVec.sshiftRight (-C) 63) &&& BitVec.truncate 32 (36 : BitVec 64)) = P at hPib ⊢
  kat hk DcUnmarshal 35
  apply store_step_at _ _ (rsp.toBitVec - 88) _ _ _ l38 _ _ (by dcaddr) (by ecancel) (by exact hl38)
  intro m11 H11
  simp only [Width.bytes, Width.bits] at H11
  kunfold
  -- 36–37 writeBarrier = 0: `je L_cc` taken
  kat hk DcUnmarshal 36
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk DcUnmarshal 37
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf DcUnmarshal 43
  -- 43–47 pointer stores and `memmove(pb, buf, 32)`
  kat hk DcUnmarshal 43
  kat hk DcUnmarshal 44
  apply store_step_at _ _ (rsp.toBitVec - 80) _ _ _ l40 _ _ (by dcaddr) (by ecancel) (by exact hl40)
  intro m12 H12
  simp only [Width.bytes, Width.bits] at H12
  kunfold
  kat hk DcUnmarshal 45
  apply store_step_at _ _ (rax.toBitVec + 8) _ _ _ aP1 _ _ (by dcaddr) (by ecancel) (by exact haP1)
  intro m13 H13
  simp only [Width.bytes, Width.bits] at H13
  kunfold
  kat hk DcUnmarshal 46
  kat hk DcUnmarshal 47
  apply store_step_at _ _ (rsp.toBitVec - 152) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 23 + 1)).toBitVec.toInt) _ _
    (by dcaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m14 H14
  simp only [Width.bytes, Width.bits] at H14
  kunfold
  rw [show rsp.toBitVec - 144 - 8#64 = rsp.toBitVec - 152 by dcaddr]
  refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (k + 47 + 1)) root (List.replicate 32 0) stk3 _
    (by rw [hroot]; rfl) (by simp [hroot]) hstk3 (by dsimp only; ecancel)) ?_
  rintro ⟨d4, pc4⟩ ⟨hpc4, hrsp4, hr144, hrbp4, stk4, hstk4, Hm4⟩
  dsimp only at hpc4 hrsp4 hr144 hrbp4 Hm4
  subst hpc4
  obtain ⟨⟨rax4, rbx4, rcx4, rdx4, rsi4, rdi4, rsp4, rbp4, r84, r94, r104, r114, r124, r134, r144, r154⟩,
    zmms4, flags4, mem4⟩ := d4
  simp only at hrsp4 hr144 hrbp4 Hm4
  rw [show ({ toBitVec := rsp.toBitVec - 152 } + 8 : UInt64) = { toBitVec := rsp.toBitVec - 144 } by
    apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; dcaddr] at hrsp4
  subst hrsp4 hr144 hrbp4
  -- 48–63 len = cap = 32, the barrier branch (not taken), the pointer store again
  kat hk DcUnmarshal 48
  apply load_step_at _ _ (rsp.toBitVec + 8) _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by dcaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk DcUnmarshal 49
  apply store_step_at _ _ (rax.toBitVec + 16) _ _ _ (Int.toBytes 8 (BitVec.toInt (0 : BitVec 64))) _ _ (by dcaddr)
    (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m15 H15
  simp only [Width.bytes, Width.bits] at H15
  kunfold
  kat hk DcUnmarshal 50
  apply store_step_at _ _ (rax.toBitVec + 24) _ _ _ (Int.toBytes 8 (BitVec.toInt (32 : BitVec 64))) _ _ (by dcaddr)
    (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m16 H16
  simp only [Width.bytes, Width.bits] at H16
  kunfold
  kat hk DcUnmarshal 51
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk DcUnmarshal 52
  kat hk DcUnmarshal 53
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk DcUnmarshal 54
  apply load_step_at _ _ (rsp.toBitVec - 80) _ _ (Int.toBytes 8 rax3.toBitVec.toInt) _ _ (by dcaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk DcUnmarshal 55
  klabel hk hf DcUnmarshal 62
  kat hk DcUnmarshal 62
  kat hk DcUnmarshal 63
  apply store_step_at _ _ (rax.toBitVec + 8) _ _ _ (Int.toBytes 8 rax3.toBitVec.toInt) _ _ (by dcaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m17 H17
  simp only [Width.bytes, Width.bits] at H17
  kunfold
  -- 64–71 alignment and bound checks (not taken)
  kat hk DcUnmarshal 64
  apply load_step_at _ _ (rsp.toBitVec + 24) _ _ (Int.toBytes 8 rcx.toBitVec.toInt) _ _ (by dcaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk DcUnmarshal 65
  have hr8 : (-36 + rcx.toBitVec).toNat = 8 * n := by
    rw [dcd_sub36 _ (by rw [UInt64.toNat_toBitVec]; omega), UInt64.toNat_toBitVec]; omega
  have hal : (-36 + rcx.toBitVec &&& 7) = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, hr8]
    show 8 * n &&& 7 = 0
    rw [show (7 : Nat) = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega
  kat hk DcUnmarshal 66
  intro _
  kat hk DcUnmarshal 67
  split
  case isTrue h => exfalso; rw [hal] at h; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk DcUnmarshal 68
  kshl64 3
  have hq : (BitVec.ushiftRight (-36 + rcx.toBitVec) 3).toNat = n := by
    rw [show (-36 + rcx.toBitVec).ushiftRight 3 = (-36 + rcx.toBitVec) >>> 3 from rfl, BitVec.toNat_ushiftRight, hr8,
      Nat.shiftRight_eq_div_pow]; omega
  kat hk DcUnmarshal 69
  kat hk DcUnmarshal 70
  kat hk DcUnmarshal 71
  split
  case isTrue h => exfalso; rw [E2eEnc.dc_jg128_false _ _ (by omega)] at h; exact Bool.noConfusion h
  simp only [Effects.All]
  generalize BitVec.ushiftRight (-36 + rcx.toBitVec) 3 = Q at hq ⊢
  -- 72–75 the Columns makeslice (len = cap = n)
  kat hk DcUnmarshal 72
  apply store_step_at _ _ (rsp.toBitVec - 96) _ _ _ l30 _ _ (by dcaddr) (by ecancel) (by exact hl30)
  intro m18 H18
  simp only [Width.bytes, Width.bits] at H18
  kunfold
  kat hk DcUnmarshal 73
  kat hk DcUnmarshal 74
  kat hk DcUnmarshal 75
  apply store_step_at _ _ (rsp.toBitVec - 152) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 47 + 1)).toBitVec.toInt) _ _
    (by dcaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m19 H19
  simp only [Width.bytes, Width.bits] at H19
  kunfold
  rw [show rsp.toBitVec - 144 - 8#64 = rsp.toBitVec - 152 by dcaddr]
  refine eventually_trans _ _ _ _ (hmsU _ (Host.addrOf (k + 75 + 1)) n (avail - 32) stk4 spm3 _
    rfl (by show Q.toNat ≤ n; omega) hq (by omega) (by unfold maxAlloc; omega) (by omega) hstk4 hspm3
    (by
      dsimp only
      rw [show rsp.toBitVec - 152 + 8 = rsp.toBitVec - 144 by dcaddr]
      ecancel)) ?_
  rintro ⟨d5, pc5⟩ ⟨hpc5, hrsp5, hr145, hrbp5, stk5, spm5, hstk5, hspm5, Hm5⟩
  dsimp only at hpc5 hrsp5 hr145 hrbp5 Hm5
  subst hpc5
  obtain ⟨⟨rax5, rbx5, rcx5, rdx5, rsi5, rdi5, rsp5, rbp5, r85, r95, r105, r115, r125, r135, r145, r155⟩,
    zmms5, flags5, mem5⟩ := d5
  simp only at hrsp5 hr145 hrbp5 Hm5
  rw [show ({ toBitVec := rsp.toBitVec - 152 } + 8 : UInt64) = { toBitVec := rsp.toBitVec - 144 } by
    apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; dcaddr] at hrsp5
  subst hrsp5 hr145 hrbp5
  rw [show rsp.toBitVec - 152 + 8 = rsp.toBitVec - 144 by dcaddr] at Hm5
  -- 76–93 the Columns header and pointer, rcx = cap − 36, rdi = buf[36:], rax = 0, `jmp L_320`
  kat hk DcUnmarshal 76
  apply load_step_at _ _ (rsp.toBitVec - 96) _ _ (Int.toBytes 8 Q.toInt) _ _ (by dcaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk DcUnmarshal 77
  apply load_step_at _ _ (rsp.toBitVec + 8) _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by dcaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk DcUnmarshal 78
  apply store_step_at _ _ (rax.toBitVec + 40) _ _ _ aL2 _ _ (by dcaddr) (by ecancel) (by exact haL2)
  intro m20 H20
  simp only [Width.bytes, Width.bits] at H20
  kunfold
  kat hk DcUnmarshal 79
  apply store_step_at _ _ (rax.toBitVec + 48) _ _ _ aC2 _ _ (by dcaddr) (by ecancel) (by exact haC2)
  intro m21 H21
  simp only [Width.bytes, Width.bits] at H21
  kunfold
  kat hk DcUnmarshal 80
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk DcUnmarshal 81
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf DcUnmarshal 87
  kat hk DcUnmarshal 87
  kat hk DcUnmarshal 88
  apply store_step_at _ _ (rax.toBitVec + 32) _ _ _ aP2 _ _ (by dcaddr) (by ecancel) (by exact haP2)
  intro m22 H22
  simp only [Width.bytes, Width.bits] at H22
  kunfold
  kat hk DcUnmarshal 89
  apply load_step_at _ _ (rsp.toBitVec - 104) _ _ (Int.toBytes 8 C.toInt) _ _ (by dcaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk DcUnmarshal 90
  apply load_step_at _ _ (rsp.toBitVec - 88) _ _ (Int.toBytes 8 P.toInt) _ _ (by dcaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk DcUnmarshal 91
  intro _
  kat hk DcUnmarshal 92
  kat hk DcUnmarshal 93
  klabel hk hf DcUnmarshal 185
  -- the element loop: L_320 (185) → L_355 (204)
  refine eventually_trans _ _ _ _ (dcd_loop k hk hf ib n hib hn P rax.toBitVec rax5.toBitVec Q hq _ _ _ _ n 0 _
    (by omega) (by show (BitVec.zeroExtend 64 _).toNat = 0; simp) hq
    (by show 8 * n ≤ C.toNat; rw [hC, UInt64.toNat_toBitVec]; omega) rfl rfl rfl rfl rfl
    (by
      dsimp only
      rw [hPib]
      simp only [Nat.mul_zero, List.take_zero, Nat.sub_zero, List.nil_append]
      ecancel)) ?_
  rintro ⟨d6, pc6⟩ ⟨hpc6, hrsp6, hrbp6, hr146, Hm6⟩
  dsimp only at hpc6 hrsp6 hrbp6 hr146 Hm6
  subst hpc6
  obtain ⟨⟨rax6, rbx6, rcx6, rdx6, rsi6, rdi6, rsp6, rbp6, r86, r96, r106, r116, r126, r136, r146, r156⟩,
    zmms6, flags6, mem6⟩ := d6
  simp only at hrsp6 hrbp6 hr146 Hm6
  subst hrsp6 hrbp6 hr146
  rw [hPib] at Hm6
  -- 204–209 nil, epilogue
  kat hk DcUnmarshal 204
  kat hk DcUnmarshal 205
  intro _
  kat hk DcUnmarshal 206
  intro _
  kat hk DcUnmarshal 207
  kat hk DcUnmarshal 208
  apply load_step_at _ _ (rsp.toBitVec - 8) _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by dcaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk DcUnmarshal 209
  apply load_step_at _ _ rsp.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by dcaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  have hQ : Q = BitVec.ofNat 64 n := by apply BitVec.eq_of_toNat_eq; rw [hq]; simp; omega
  subst hQ
  have e32 : BitVec.toInt (32 : BitVec 64) = 32 := by decide
  simp only [e32] at Hm6
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rax3.toBitVec, rax5.toBitVec, Int.toBytes 8 C.toInt,
    Int.toBytes 8 (BitVec.ofNat 64 n).toInt, Int.toBytes 8 P.toInt, Int.toBytes 8 rax3.toBitVec.toInt,
    spm5 ++ spl.drop 24, stk5, Int.toBytes_length 8 _, Int.toBytes_length 8 _, Int.toBytes_length 8 _,
    Int.toBytes_length 8 _, by simp [hspm5, hspl], hstk5, ?mem⟩
  case mem =>
    rw [at_app spm5 (spl.drop 24) (b := rsp.toBitVec - 120) (by rw [hspm5]; dcaddr) (by simp [hspm5, hspl])]
    rw [Nat.sub_sub, show k + 75 + 1 = k + 76 from rfl] at Hm6
    ecancel
  all_goals first
    | exact trivial
    | rfl
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (apply UInt64.toBitVec_inj.mp; dcaddr)

end E2eDec
