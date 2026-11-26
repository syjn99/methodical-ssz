import Codec.SegmentAddress
import Machine.StoreLemmas
import Runtime.StaticBoxLemmas
import Prysm.DataColumnsByRootIdentifier.StatementsDecodeErrorWordNonzero
import Prysm.DataColumnsByRootIdentifier.DecodeAccept
import Prysm.DataColumnsByRootIdentifier.Code

/-!
# `(*v1alpha1.DataColumnsByRootIdentifier).UnmarshalSSZ`: alignment reject

Statement: `Decode.reject_alignment_error_word_nonzero_statement`
(`Prysm/DataColumnsByRootIdentifier/StatementsDecodeErrorWordNonzero.lean`, with the premise `e0 ≠ 0`).
The directives 0–65 are those of `Decode.accept` (`Prysm/DataColumnsByRootIdentifier/DecodeAccept.lean`).
These are the guard, the size and offset checks, the BlockRoot `makeslice` and the `buf[36:]` pointer.
Then `writeBarrier = 0`, the `memmove` of the root and the header stores.
Alignment reject: `jne L_242` taken (67), the 32-byte argument array at rsp − 40 (two `movups`), `convT64(len − 36)` (`ConvT64Contract`).
Then the itab word (140–143, `e0 ≠ 0`), `fmt.errorf` (`FmtErrorfDecimalWrapContract`), `jne L_2d9` taken (rax ≠ 0), epilogue 165–167.
-/

open Machine Runtime Prysm.DataColumnsByRootIdentifier.Code
variable [Host]

namespace Prysm.DataColumnsByRootIdentifier

omit [Host] in
theorem formatColumnsMisaligned_length : ElfData.PrysmTarget.formatColumnsMisaligned.length = 74 := by rfl

/-- The address of the alignment reject format string in the label form of the code (`lea go_string._+164835(%rip)`). -/
theorem formatColumnsMisaligned_addr_eq :
    ElfData.PrysmTarget.formatColumnsMisaligned_addr = (label "go_string._" + 164835).toBitVec := rfl

-- Measured: heartbeats: the default 200000 fails (`whnf` timeout, reported at the theorem line), 400000 passes;
-- recursion depth: the default fails at `label_address` (directive 164, the `simp` that unfolds the program literal), 1024 passes.
set_option maxHeartbeats 400000 in
set_option maxRecDepth 1024 in
theorem Decode.reject_alignment_error_word_nonzero : Decode.reject_alignment_error_word_nonzero_statement := by
  intro k hk hf root hroot s ra guard e0 e1 esp msg ity he0 he0nz hity fp s1 s2 s3 s4 l28 l38 l40 aw spl rslot lo aP1 aL1 aC1
    hfp h1 h2 h3 h4 hl28 hl38 hl40 haw hspl hrs haP1 haL1 haC1 S hlo Heap avail R h_mem hguard hlen hmis hav hms hmm hcv hfe
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen hmis hav
  dsimp only
  have hz1 := rsp.toNat_lt_size; have hz2 := guard.toNat_lt_size; have hz3 := rcx.toNat_lt_size
  simp only [UInt64.size] at hz1 hz2 hz3
  generalize hSB : StaticBox (rcx.toBitVec - 36) = SB at h_mem
  rw [ElfData.PrysmTarget.sszErrIncorrectListSize_addr_eq, formatColumnsMisaligned_addr_eq] at h_mem
  -- the argument array as two 16-byte chunks
  rw [← List.take_append_drop 16 aw, at_app (aw.take 16) (aw.drop 16) (b := rsp.toBitVec - 24)
    (by simp only [List.length_take, haw]; segment_addr) (by simp [haw])] at h_mem
  -- the spill area: the 24 makeslice spill bytes and the rest
  rw [show spl = spl.take 24 ++ spl.drop 24 from (List.take_append_drop 24 spl).symm,
    at_app (spl.take 24) (spl.drop 24) (b := rsp.toBitVec - 120) (by simp [hspl]; segment_addr) (by simp [hspl])] at h_mem
  -- 0–8 guard and prologue
  step_directive hk unmarshalSSZ 0
  step_directive hk unmarshalSSZ 1
  step_directive hk unmarshalSSZ 2
  step_directive hk unmarshalSSZ 3
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk unmarshalSSZ 4
  split
  case isTrue h =>
    exfalso
    rw [Codec.lea_cmp_be_false rsp.toBitVec _ guard.toBitVec _ _ 16 (by rfl)
      (by rw [UInt64.toNat_toBitVec, UInt64.toNat_toBitVec]; omega)] at h
    exact Bool.noConfusion h
  simp only [Effects.All]
  step_directive hk unmarshalSSZ 5
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by segment_addr) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  unfold_step
  step_directive hk unmarshalSSZ 6
  step_directive hk unmarshalSSZ 7
  step_directive hk unmarshalSSZ 8
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by segment_addr) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  unfold_step
  -- 9–15 size and offset checks (not taken)
  step_directive hk unmarshalSSZ 9
  step_directive hk unmarshalSSZ 10
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
  simp only [Effects.All]
  step_directive hk unmarshalSSZ 11
  apply load_step_at _ _ (rbx.toBitVec + 32) _ _ Prysm.DataColumnsByRootIdentifier.offsetBytes _ _ (by segment_addr) (by ecancel) (by rfl)
  unfold_step
  step_directive hk unmarshalSSZ 12
  step_directive hk unmarshalSSZ 13
  step_directive hk unmarshalSSZ 14
  step_directive hk unmarshalSSZ 15
  split
  case isTrue h => exfalso; revert h; decide
  simp only [Effects.All]
  -- 16–19 spills
  step_directive hk unmarshalSSZ 16
  apply store_step_at _ _ (rsp.toBitVec + 8) _ _ _ s1 _ _ (by segment_addr) (by ecancel) (by exact h1)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  unfold_step
  step_directive hk unmarshalSSZ 17
  apply store_step_at _ _ (rsp.toBitVec + 32) _ _ _ s4 _ _ (by segment_addr) (by ecancel) (by exact h4)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  unfold_step
  step_directive hk unmarshalSSZ 18
  apply store_step_at _ _ (rsp.toBitVec + 24) _ _ _ s3 _ _ (by segment_addr) (by ecancel) (by exact h3)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  unfold_step
  step_directive hk unmarshalSSZ 19
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  unfold_step
  -- 20–23 the BlockRoot makeslice (len 0, cap 32)
  step_directive hk unmarshalSSZ 20
  step_directive hk unmarshalSSZ 21
  intro _
  step_directive hk unmarshalSSZ 22
  step_directive hk unmarshalSSZ 23
  apply store_step_at _ _ (rsp.toBitVec - 152) _ _ _ rslot _ _ (by segment_addr) (by ecancel) (by exact hrs)
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  unfold_step
  rw [show rsp.toBitVec - 8#64 - 136 - 8#64 = rsp.toBitVec - 152 by segment_addr]
  refine eventually_trans _ _ _ _ (hms _ (Host.addrOf (k + 23 + 1)) 32 avail lo (spl.take 24) _
    rfl (by simp) (by rfl) (by omega) (by unfold maxAlloc; omega) (by decide) hlo (by simp [hspl])
    (by
      dsimp only
      rw [show rsp.toBitVec - 152 + 8 = rsp.toBitVec - 144 by segment_addr]
      ecancel)) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrsp3, hr143, hrbp3, stk3, spm3, hstk3, hspm3, Hm3⟩
  dsimp only at hpc3 hrsp3 hr143 hrbp3 Hm3
  subst hpc3
  obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,
    zmms3, flags3, mem3⟩ := d3
  simp only at hrsp3 hr143 hrbp3 Hm3
  rw [show ({ toBitVec := rsp.toBitVec - 152 } + 8 : UInt64) = { toBitVec := rsp.toBitVec - 144 } by
    apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; segment_addr] at hrsp3
  subst hrsp3 hr143 hrbp3
  rw [show rsp.toBitVec - 152 + 8 = rsp.toBitVec - 144 by segment_addr] at Hm3
  simp only [Nat.one_mul] at Hm3
  -- the makeslice spill bytes as the convT64 spill slot and the rest
  rw [← List.take_append_drop 8 spm3, at_app (spm3.take 8) (spm3.drop 8) (b := rsp.toBitVec - 136)
    (by simp only [List.length_take, hspm3]; segment_addr) (by simp [hspm3])] at Hm3
  -- 24–26 the BlockRoot header: len 0, cap 32
  step_directive hk unmarshalSSZ 24
  apply load_step_at _ _ (rsp.toBitVec + 8) _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  try simp only [ofInt_ofBytes_toBytes64]
  step_directive hk unmarshalSSZ 25
  apply store_step_at _ _ (rax.toBitVec + 16) _ _ _ aL1 _ _ (by segment_addr) (by ecancel) (by exact haL1)
  intro m8 H8
  simp only [Width.bytes, Width.bits] at H8
  unfold_step
  step_directive hk unmarshalSSZ 26
  apply store_step_at _ _ (rax.toBitVec + 24) _ _ _ aC1 _ _ (by segment_addr) (by ecancel) (by exact haC1)
  intro m9 H9
  simp only [Width.bytes, Width.bits] at H9
  unfold_step
  -- 27–35 the buf[36:] pointer (its value is not used on this path)
  step_directive hk unmarshalSSZ 27
  apply load_step_at _ _ (rsp.toBitVec + 32) _ _ (Int.toBytes 8 rdi.toBitVec.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  try simp only [ofInt_ofBytes_toBytes64]
  step_directive hk unmarshalSSZ 28
  generalize -36 + rdi.toBitVec = C
  step_directive hk unmarshalSSZ 29
  apply store_step_at _ _ (rsp.toBitVec - 104) _ _ _ l28 _ _ (by segment_addr) (by ecancel) (by exact hl28)
  intro m10 H10
  simp only [Width.bytes, Width.bits] at H10
  unfold_step
  step_directive hk unmarshalSSZ 30
  step_directive hk unmarshalSSZ 31
  shift_left64 63
  step_directive hk unmarshalSSZ 32
  intro _
  step_directive hk unmarshalSSZ 33
  apply load_step_at _ _ (rsp.toBitVec + 16) _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  try simp only [ofInt_ofBytes_toBytes64]
  step_directive hk unmarshalSSZ 34
  generalize rbx.toBitVec + BitVec.zeroExtend 64 (BitVec.extractLsb' 0 32
    (BitVec.sshiftRight (-C) 63) &&& BitVec.truncate 32 (36 : BitVec 64)) = P
  step_directive hk unmarshalSSZ 35
  apply store_step_at _ _ (rsp.toBitVec - 88) _ _ _ l38 _ _ (by segment_addr) (by ecancel) (by exact hl38)
  intro m11 H11
  simp only [Width.bytes, Width.bits] at H11
  unfold_step
  -- 36–37 writeBarrier = 0: `je L_cc` taken
  step_directive hk unmarshalSSZ 36
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  unfold_step
  step_directive hk unmarshalSSZ 37
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  label_address hk hf unmarshalSSZ 43
  -- 43–47 pointer stores and `memmove(pb, buf, 32)`
  step_directive hk unmarshalSSZ 43
  step_directive hk unmarshalSSZ 44
  apply store_step_at _ _ (rsp.toBitVec - 80) _ _ _ l40 _ _ (by segment_addr) (by ecancel) (by exact hl40)
  intro m12 H12
  simp only [Width.bytes, Width.bits] at H12
  unfold_step
  step_directive hk unmarshalSSZ 45
  apply store_step_at _ _ (rax.toBitVec + 8) _ _ _ aP1 _ _ (by segment_addr) (by ecancel) (by exact haP1)
  intro m13 H13
  simp only [Width.bytes, Width.bits] at H13
  unfold_step
  step_directive hk unmarshalSSZ 46
  step_directive hk unmarshalSSZ 47
  apply store_step_at _ _ (rsp.toBitVec - 152) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 23 + 1)).toBitVec.toInt) _ _
    (by segment_addr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m14 H14
  simp only [Width.bytes, Width.bits] at H14
  unfold_step
  rw [show rsp.toBitVec - 144 - 8#64 = rsp.toBitVec - 152 by segment_addr]
  refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (k + 47 + 1)) root (List.replicate 32 0) stk3 _
    (by rw [hroot]; rfl) (by simp [hroot]) hstk3 (by dsimp only; ecancel)) ?_
  rintro ⟨d4, pc4⟩ ⟨hpc4, hrsp4, hr144, hrbp4, stk4, hstk4, Hm4⟩
  dsimp only at hpc4 hrsp4 hr144 hrbp4 Hm4
  subst hpc4
  obtain ⟨⟨rax4, rbx4, rcx4, rdx4, rsi4, rdi4, rsp4, rbp4, r84, r94, r104, r114, r124, r134, r144, r154⟩,
    zmms4, flags4, mem4⟩ := d4
  simp only at hrsp4 hr144 hrbp4 Hm4
  rw [show ({ toBitVec := rsp.toBitVec - 152 } + 8 : UInt64) = { toBitVec := rsp.toBitVec - 144 } by
    apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; segment_addr] at hrsp4
  subst hrsp4 hr144 hrbp4
  -- 48–63 len = cap = 32, the barrier branch (not taken), the pointer store again
  step_directive hk unmarshalSSZ 48
  apply load_step_at _ _ (rsp.toBitVec + 8) _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  try simp only [ofInt_ofBytes_toBytes64]
  step_directive hk unmarshalSSZ 49
  apply store_step_at _ _ (rax.toBitVec + 16) _ _ _ (Int.toBytes 8 (BitVec.toInt (0 : BitVec 64))) _ _ (by segment_addr)
    (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m15 H15
  simp only [Width.bytes, Width.bits] at H15
  unfold_step
  step_directive hk unmarshalSSZ 50
  apply store_step_at _ _ (rax.toBitVec + 24) _ _ _ (Int.toBytes 8 (BitVec.toInt (32 : BitVec 64))) _ _ (by segment_addr)
    (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m16 H16
  simp only [Width.bytes, Width.bits] at H16
  unfold_step
  step_directive hk unmarshalSSZ 51
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  unfold_step
  step_directive hk unmarshalSSZ 52
  step_directive hk unmarshalSSZ 53
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  step_directive hk unmarshalSSZ 54
  apply load_step_at _ _ (rsp.toBitVec - 80) _ _ (Int.toBytes 8 rax3.toBitVec.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  try simp only [ofInt_ofBytes_toBytes64]
  step_directive hk unmarshalSSZ 55
  label_address hk hf unmarshalSSZ 62
  step_directive hk unmarshalSSZ 62
  step_directive hk unmarshalSSZ 63
  apply store_step_at _ _ (rax.toBitVec + 8) _ _ _ (Int.toBytes 8 rax3.toBitVec.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m17 H17
  simp only [Width.bytes, Width.bits] at H17
  unfold_step
  -- 64–67 the alignment check: `jne L_242` taken
  step_directive hk unmarshalSSZ 64
  apply load_step_at _ _ (rsp.toBitVec + 24) _ _ (Int.toBytes 8 rcx.toBitVec.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  try simp only [ofInt_ofBytes_toBytes64]
  step_directive hk unmarshalSSZ 65
  have hDn : (-36 + rcx.toBitVec).toNat = rcx.toNat - 36 := by
    rw [Decode.sub36 _ (by rw [UInt64.toNat_toBitVec]; omega), UInt64.toNat_toBitVec]
  have hDv : -36 + rcx.toBitVec = rcx.toBitVec - 36 := by rw [BitVec.add_comm, ← BitVec.sub_eq_add_neg]
  have hal : (-36 + rcx.toBitVec &&& 7) ≠ 0 := by
    intro h0
    have h1 := congrArg BitVec.toNat h0
    rw [BitVec.toNat_and, hDn] at h1
    have h7 : (7 : BitVec 64).toNat = 2 ^ 3 - 1 := rfl
    rw [h7, Nat.and_two_pow_sub_one_eq_mod] at h1
    exact hmis (by simpa using h1)
  generalize -36 + rcx.toBitVec = D at hDn hDv hal ⊢
  step_directive hk unmarshalSSZ 66
  intro _
  step_directive hk unmarshalSSZ 67
  split
  case isFalse h => exfalso; apply h; simp only [CondCode.interp, StatusFlags.from_result]; simp; exact hal
  simp only [Effects.All]
  label_address hk hf unmarshalSSZ 131
  -- 131–136 the argument array at rsp − 40 (two `movups`), `convT64(len − 36)`
  step_directive hk unmarshalSSZ 131
  step_directive hk unmarshalSSZ 132
  step_directive hk unmarshalSSZ 133
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  unfold_step
  rw [show rsp.toBitVec - 144 + 104 = rsp.toBitVec - 40 by segment_addr]
  apply Machine.store_avx_step _ _ _ _ (aw.take 16) _ _ (by ecancel) (by simp [haw]) (by decide)
  intro m18 H18
  unfold_step
  step_directive hk unmarshalSSZ 134
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  unfold_step
  rw [show rsp.toBitVec - 40 + 16 = rsp.toBitVec - 24 by segment_addr]
  apply Machine.store_avx_step _ _ _ _ (aw.drop 16) _ _ (by ecancel) (by simp [haw]) (by decide)
  intro m19 H19
  unfold_step
  step_directive hk unmarshalSSZ 135
  step_directive hk unmarshalSSZ 136
  apply store_step_at _ _ (rsp.toBitVec - 152) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 47 + 1)).toBitVec.toInt) _ _
    (by segment_addr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m20 H20
  simp only [Width.bytes, Width.bits] at H20
  unfold_step
  rw [show rsp.toBitVec - 144 - 8#64 = rsp.toBitVec - 152 by segment_addr]
  refine eventually_trans _ _ _ _ (hcv _ (Host.addrOf (k + 136 + 1)) (avail - 32) stk4 (spm3.take 8) _ (by omega) hstk4
    (by simp [hspm3]) (by
      dsimp only
      rw [show rsp.toBitVec - 152 + 8 = rsp.toBitVec - 144 by segment_addr, Runtime.staticBox_congr hDv, hSB]
      ecancel)) ?_
  rintro ⟨d5, pc5⟩ ⟨hpc5, hrsp5, hr145, stk5, sp5, hb5, av5, hstk5, hsp5, hbox5, hav5, hav5', Hm5⟩
  dsimp only at hpc5 hrsp5 hr145 Hm5
  subst hpc5
  rw [Runtime.staticBox_congr hDv, hSB] at Hm5
  obtain ⟨⟨rax5, rbx5, rcx5, rdx5, rsi5, rdi5, rsp5, rbp5, r85, r95, r105, r115, r125, r135, r145, r155⟩,
    zmms5, flags5, mem5⟩ := d5
  simp only at hrsp5 hr145 Hm5 hbox5
  rw [show ({ toBitVec := rsp.toBitVec - 152 } + 8 : UInt64) = { toBitVec := rsp.toBitVec - 144 } by
    apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; segment_addr] at hrsp5
  subst hrsp5 hr145
  rw [show rsp.toBitVec - 152 + 8 = rsp.toBitVec - 144 by segment_addr,
    Machine.at_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 40), Machine.at_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 24),
    show rsp.toBitVec - 40 + 8 = rsp.toBitVec - 32 by segment_addr, show rsp.toBitVec - 24 + 8 = rsp.toBitVec - 16 by segment_addr]
    at Hm5
  -- 137–147: the argument array (type:int, box, itab type word, error data word)
  step_directive hk unmarshalSSZ 137
  step_directive hk unmarshalSSZ 138
  apply store_step_at _ _ (rsp.toBitVec - 40) _ _ _ ((Int.toBytes 16 (zmms4.get (AvxReg.xmm RegMm.mm15)).toInt).take 8)
    _ _ (by segment_addr) (by ecancel) (by simp [Int.toBytes_length])
  intro m21 H21
  simp only [Width.bytes, Width.bits] at H21
  unfold_step
  step_directive hk unmarshalSSZ 139
  apply store_step_at _ _ (rsp.toBitVec - 32) _ _ _ ((Int.toBytes 16 (zmms4.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8)
    _ _ (by segment_addr) (by ecancel) (by simp [Int.toBytes_length])
  intro m22 H22
  simp only [Width.bytes, Width.bits] at H22
  unfold_step
  step_directive hk unmarshalSSZ 140
  apply load_step _ _ _ _ (Int.toBytes 8 e0.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk unmarshalSSZ 141
  intro _
  step_directive hk unmarshalSSZ 142
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    exact he0nz (UInt64.toBitVec_inj.mp (by simpa using h))
  simp only [Effects.All]
  step_directive hk unmarshalSSZ 143
  apply load_step_at _ _ ((label "go_itab._errors.errorString_error").toBitVec + 8) _ _ ity _ _ (by rw [he0])
    (by ecancel) (by exact hity)
  unfold_step
  step_directive hk unmarshalSSZ 144
  step_directive hk unmarshalSSZ 145
  apply load_step _ _ _ _ (Int.toBytes 8 e1.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk unmarshalSSZ 146
  apply store_step_at _ _ (rsp.toBitVec - 24) _ _ _ ((Int.toBytes 16 (zmms4.get (AvxReg.xmm RegMm.mm15)).toInt).take 8)
    _ _ (by segment_addr) (by ecancel) (by simp [Int.toBytes_length])
  intro m23 H23
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl ity hity] at H23
  unfold_step
  step_directive hk unmarshalSSZ 147
  apply store_step_at _ _ (rsp.toBitVec - 16) _ _ _ ((Int.toBytes 16 (zmms4.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8)
    _ _ (by segment_addr) (by ecancel) (by simp [Int.toBytes_length])
  intro m24 H24
  simp only [Width.bytes, Width.bits] at H24
  unfold_step
  -- 148–153: `fmt.errorf(fmt, 74, &args, 2, 2)`
  step_directive hk unmarshalSSZ 148
  step_directive hk unmarshalSSZ 149
  step_directive hk unmarshalSSZ 150
  step_directive hk unmarshalSSZ 151
  step_directive hk unmarshalSSZ 152
  step_directive hk unmarshalSSZ 153
  apply store_step_at _ _ (rsp.toBitVec - 152) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 136 + 1)).toBitVec.toInt) _ _
    (by segment_addr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m25 H25
  simp only [Width.bytes, Width.bits] at H25
  unfold_step
  rw [show rsp.toBitVec - 144 - 8#64 = rsp.toBitVec - 152 by segment_addr]
  refine eventually_trans _ _ _ _ (hfe _ (Host.addrOf (k + 153 + 1)) av5 ity msg hb5 stk5 (sp5 ++ (spm3.drop 8 ++ spl.drop 24))
    rax5.toBitVec D e1.toBitVec esp _
    (by rw [formatColumnsMisaligned_length]; rfl) (by first | rfl | decide) (by first | rfl | decide)
    hity hbox5 hstk5 (by simp [hsp5, hspm3, hspl]) (by rw [formatColumnsMisaligned_length] at hav ⊢; omega)
    (by
      dsimp only
      rw [show rsp.toBitVec - 144 + 104 = rsp.toBitVec - 40 by segment_addr]
      rw [show rsp.toBitVec - 152 + 8 = rsp.toBitVec - 144 by segment_addr, ElfData.PrysmTarget.typeInt_addr_eq,
        Runtime.staticBox_congr hDv, hSB,
        at_app (Int.toBytes 8 (label "type__" + 387520).toBitVec.toInt ++ Int.toBytes 8 rax5.toBitVec.toInt ++ ity)
          (Int.toBytes 8 e1.toBitVec.toInt) (a := rsp.toBitVec - 40) (b := rsp.toBitVec - 16) (by simp only [List.length_append, Int.toBytes_length, hity]; segment_addr) (by simp only [List.length_append, Int.toBytes_length, hity]; omega),
        at_app (Int.toBytes 8 (label "type__" + 387520).toBitVec.toInt ++ Int.toBytes 8 rax5.toBitVec.toInt) ity
          (a := rsp.toBitVec - 40) (b := rsp.toBitVec - 24) (by simp only [List.length_append, Int.toBytes_length]; segment_addr) (by simp only [List.length_append, Int.toBytes_length, hity]; omega),
        at_app (Int.toBytes 8 (label "type__" + 387520).toBitVec.toInt) (Int.toBytes 8 rax5.toBitVec.toInt)
          (a := rsp.toBitVec - 40) (b := rsp.toBitVec - 32) (by simp only [Int.toBytes_length]; segment_addr) (by simp only [Int.toBytes_length]; omega),
        at_app sp5 (spm3.drop 8 ++ spl.drop 24) (a := rsp.toBitVec - 144) (b := rsp.toBitVec - 136) (by rw [hsp5]; segment_addr) (by simp [hsp5, hspm3, hspl]),
        at_app (spm3.drop 8) (spl.drop 24) (a := rsp.toBitVec - 136) (b := rsp.toBitVec - 120) (by simp only [List.length_drop, hspm3]; segment_addr) (by simp [hspm3, hspl])]
      ecancel)) ?_
  rintro ⟨d6, pc6⟩ ⟨hpc6, hrsp6, hr146, hrax6, stk6, sp6, av6, hstk6, hsp6, hav6, Hm6⟩
  dsimp only at hpc6 hrsp6 hr146 hrax6 Hm6
  subst hpc6
  obtain ⟨⟨rax6, rbx6, rcx6, rdx6, rsi6, rdi6, rsp6, rbp6, r86, r96, r106, r116, r126, r136, r146, r156⟩,
    zmms6, flags6, mem6⟩ := d6
  simp only at hrsp6 hr146 hrax6 Hm6
  rw [show ({ toBitVec := rsp.toBitVec - 152 } + 8 : UInt64) = { toBitVec := rsp.toBitVec - 144 } by
    apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; segment_addr] at hrsp6
  subst hrsp6 hr146
  -- 154–167: err ≠ nil, `jne L_2d9` taken, epilogue
  step_directive hk unmarshalSSZ 154
  try intro _
  step_directive hk unmarshalSSZ 155
  split
  case isFalse h =>
    exfalso; apply h; simp only [CondCode.interp, StatusFlags.from_result]; simp
    intro h0; exact hrax6 (UInt64.toBitVec_inj.mp (by simpa using h0))
  simp only [Effects.All]
  label_address hk hf unmarshalSSZ 164
  step_directive hk unmarshalSSZ 164
  step_directive hk unmarshalSSZ 165
  try intro _
  step_directive hk unmarshalSSZ 166
  apply load_step_at _ _ (rsp.toBitVec - 8) _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk unmarshalSSZ 167
  apply load_step_at _ _ rsp.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  apply Eventually.done
  rw [hDv] at hbox5
  have e32 : BitVec.toInt (32 : BitVec 64) = 32 := by decide
  simp only [e32] at Hm6
  refine ⟨?_, hrax6, ?_, ?_, ?_, rax3.toBitVec, rax5.toBitVec, hb5, Int.toBytes 8 C.toInt, Int.toBytes 8 P.toInt,
    Int.toBytes 8 rax3.toBitVec.toInt, sp6, stk6, av6, Int.toBytes_length 8 _, Int.toBytes_length 8 _,
    Int.toBytes_length 8 _, hsp6, hstk6, hbox5, by omega, ?_⟩
  rotate_right
  · rw [ElfData.PrysmTarget.sszErrIncorrectListSize_addr_eq, formatColumnsMisaligned_addr_eq, ElfData.PrysmTarget.typeInt_addr_eq]
    rw [show k + 153 + 1 = k + 154 from rfl] at Hm6
    rw [show rsp.toBitVec - 144 + 104 = rsp.toBitVec - 40 by segment_addr] at Hm6
    rw [show rsp.toBitVec - 152 + 8 = rsp.toBitVec - 144 by segment_addr, Runtime.staticBox_congr hDv, hSB] at Hm6
    ecancel
  all_goals first
    | exact trivial
    | with_reducible rfl
    | (apply UInt64.toBitVec_inj.mp
       simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, Width.bits]
       done)
    | (apply UInt64.toBitVec_inj.mp; segment_addr)

end Prysm.DataColumnsByRootIdentifier
