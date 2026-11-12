import TestTarget.ListU64DecodeRejectCall
import Prysm.IndexedAttestation.StatementsErrorWordNonzero
import Prysm.IndexedAttestation.DecodeAccept

/-!
# `(*v1alpha1.IndexedAttestation).UnmarshalSSZ`: alignment reject and overflow reject

Statements: the corrected `Decode.reject_alignment_error_word_nonzero_statement` and `Decode.reject_overflow_error_word_nonzero_statement` (`Prysm/IndexedAttestation/StatementsErrorWordNonzero.lean`, the frozen
texts plus `e0 ≠ 0`). The text of `Fk.lu_reject_misaligned_main` (`TestTarget/ListU64DecodeRejectCall.lean`, Go 1.26.3) with the IndexedAttestation
directive indices: the head 0–26 of `Prysm/IndexedAttestation/DecodeAccept.lean`; alignment reject: `jne L_1a2` taken (94), the 32-byte argument array at
rsp − 48 (two `movups`), `convT64(len − 228)` (`ConvT64C`), the itab word (103–106, `e0 ≠ 0`), `fmt.errorf`
(`FmtErrorfDWC`), `jne L_248` taken (rax ≠ 0), epilogue 128–130. Overflow reject: `jg L_105` taken (57), the array at rsp − 80,
`convT64(numElem)`, 66–69, `fmt.errorf`, `jne L_199`, epilogue 91–93.
-/

open Machine Runtime TestTarget Prysm.IndexedAttestation.Code
variable [Host]

namespace Prysm.IndexedAttestation

theorem errIncorrectListSize_addr_eq : ElfData.IndexedAttestation.lvErrIncorrectListSize_addr = (label "ssz.ErrIncorrectListSize").toBitVec := rfl
theorem errListTooBig_addr_eq : ElfData.IndexedAttestation.lvErrListTooBig_addr = (label "ssz.ErrListTooBig").toBitVec := rfl
theorem fmtMisaligned_addr_eq : ElfData.IndexedAttestation.lvFmtMis_addr = (label "go_string._" + 171319).toBitVec := rfl
theorem fmtTooBig_addr_eq : ElfData.IndexedAttestation.lvFmtTooBig_addr = (label "go_string._" + 163839).toBitVec := rfl
theorem intType_addr_eq : ElfData.CheckpointAndEpoch.e2eIntType_addr = (label "type__" + 387520).toBitVec := rfl
omit [Host] in
theorem fmtMisaligned_length : ElfData.IndexedAttestation.lvFmtMis.length = 83 := by rfl
omit [Host] in
theorem fmtTooBig_length : ElfData.IndexedAttestation.lvFmtTooBig.length = 73 := by rfl

omit [Host] in
/-- `cmp $0x800, a; jg` is taken when `2048 < a < 2⁶²`. -/
theorem Decode.jg2048_true (a : BitVec 64) (af : Bool) (h : 2048 < a.toNat) (h62 : a.toNat < 2 ^ 62) :
    CondCode.g.interp (StatusFlags.from_result (a - 2048)
      { cf := BitVec.unsigned (a - 2048) != a.unsigned - BitVec.unsigned (2048 : BitVec 64), af := af,
        of := BitVec.toInt (a - 2048) != a.toInt - BitVec.toInt (2048 : BitVec 64) }) = true := by
  have ta : a.toInt = a.toNat := BitVec.toInt_eq_toNat_of_lt (by omega)
  have t16 : BitVec.toInt (2048 : BitVec 64) = 2048 := by decide
  have hs : (a - 2048).toInt = (a.toNat : Int) - 2048 := by
    rw [BitVec.toInt_sub, ta, t16]; apply Int.bmod_eq_of_le <;> omega
  have hz : a - 2048 ≠ 0#64 := by
    intro h0; have := congrArg BitVec.toNat h0; simp [BitVec.toNat_sub] at this; omega
  have hm : (a - 2048).msb = false := by
    rw [BitVec.msb_eq_decide]; simp [BitVec.toNat_sub]; omega
  simp [CondCode.interp, StatusFlags.from_result, ta]
  refine ⟨hz, ?_⟩
  rw [show (a - 2048#64) = a - 2048 from rfl, hm, Int.bmod_eq_of_le (by omega) (by omega)]; simp

-- Measured cause: without this option the first `kat` (directive 0) stops with "maximum recursion depth", as in
-- `Prysm/IndexedAttestation/DecodeRejectSize.lean`; 1024 passes.
set_option maxRecDepth 1024 in
theorem Decode.reject_alignment_error_word_nonzero : Decode.reject_alignment_error_word_nonzero_statement := by
  intro k hk hf s ra guard e0 e1 esp msg ity he0 he0nz hity fp s2 aw spl rslot lo hfp h2 haw hspl hrs S hlo
    Heap avail R h_mem hguard hlen hmis hav hcv hfe
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen hmis hav
  dsimp only
  have hz1 := rsp.toNat_lt_size; have hz2 := guard.toNat_lt_size; have hz3 := rcx.toNat_lt_size
  simp only [UInt64.size] at hz1 hz2 hz3
  generalize hSB : StaticBox (rcx.toBitVec - 228) = SB at h_mem
  rw [errIncorrectListSize_addr_eq, fmtMisaligned_addr_eq] at h_mem
  -- the argument array as two 16-byte chunks
  rw [← List.take_append_drop 16 aw, at_app (aw.take 16) (aw.drop 16) (b := rsp.toBitVec - 32)
    (by simp only [List.length_take, haw]; iaaddr) (by simp [haw])] at h_mem
  -- the spill area as the convT64 spill slot and the rest
  rw [← List.take_append_drop 8 spl, at_app (spl.take 8) (spl.drop 8) (b := rsp.toBitVec - 168)
    (by simp only [List.length_take, hspl]; iaaddr) (by simp [hspl])] at h_mem
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
  have hCn : (-228 + rcx.toBitVec).toNat = rcx.toNat - 228 := by
    rw [BitVec.add_comm, Decode.sub228 _ (by rw [UInt64.toNat_toBitVec]; omega), UInt64.toNat_toBitVec]
  have hCv : -228 + rcx.toBitVec = rcx.toBitVec - 228 := by rw [BitVec.add_comm, ← BitVec.sub_eq_add_neg]
  have hal : (-228 + rcx.toBitVec &&& 7) ≠ 0 := by
    intro h0
    have h1 := congrArg BitVec.toNat h0
    rw [BitVec.toNat_and, hCn] at h1
    have h7 : (7 : BitVec 64).toNat = 2 ^ 3 - 1 := rfl
    rw [h7, Nat.and_two_pow_sub_one_eq_mod] at h1
    exact hmis (by simpa using h1)
  generalize -228 + rcx.toBitVec = C at hCn hCv hal ⊢
  kat hk unmarshalSSZ 26
  split
  case isFalse h => exfalso; apply h; simp only [CondCode.interp, StatusFlags.from_result]; simp; exact hal
  simp only [Effects.All]
  klabel hk hf unmarshalSSZ 94
  kat hk unmarshalSSZ 94
  kat hk unmarshalSSZ 95
  kat hk unmarshalSSZ 96
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  kunfold
  rw [show rsp.toBitVec - 8#64 - 168 + 128 = rsp.toBitVec - 48 by iaaddr]
  apply store_avx_step _ _ _ _ (aw.take 16) _ _ (by ecancel) (by simp [haw]) (by decide)
  intro m3 H3
  kunfold
  kat hk unmarshalSSZ 97
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  kunfold
  rw [show rsp.toBitVec - 48 + 16 = rsp.toBitVec - 32 by iaaddr]
  apply store_avx_step _ _ _ _ (aw.drop 16) _ _ (by ecancel) (by simp [haw]) (by decide)
  intro m4 H4
  kunfold
  kat hk unmarshalSSZ 98
  kat hk unmarshalSSZ 99
  apply store_step_at _ _ (rsp.toBitVec - 184) _ _ _ rslot _ _ (by iaaddr) (by ecancel) (by exact hrs)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  rw [show rsp.toBitVec - 8#64 - 168 - 8#64 = rsp.toBitVec - 184 by iaaddr]
  refine eventually_trans _ _ _ _ (hcv _ (Host.addrOf (k + 99 + 1)) avail lo (spl.take 8) _ (by omega) hlo
    (by simp [hspl]) (by
      dsimp only
      rw [show rsp.toBitVec - 184 + 8 = rsp.toBitVec - 176 by iaaddr, staticBox_congr hCv, hSB]
      ecancel)) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hr141, stk1, sp1, hb1, av1, hstk1, hsp1, hbox1, hav1, hav1', Hm1⟩
  dsimp only at hpc1 hrsp1 hr141 Hm1
  subst hpc1
  rw [staticBox_congr hCv, hSB] at Hm1
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩,
    zmms1, flags1, mem1⟩ := d1
  simp only at hrsp1 hr141 Hm1 hbox1
  rw [show ({ toBitVec := rsp.toBitVec - 184 } + 8 : UInt64) = { toBitVec := rsp.toBitVec - 176 } by
    apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; iaaddr] at hrsp1
  subst hrsp1 hr141
  rw [show rsp.toBitVec - 184 + 8 = rsp.toBitVec - 176 by iaaddr,
    lr_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 48), lr_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 32),
    show rsp.toBitVec - 48 + 8 = rsp.toBitVec - 40 by iaaddr, show rsp.toBitVec - 32 + 8 = rsp.toBitVec - 24 by iaaddr]
    at Hm1
  -- 100–110: the argument array (type:int, box, itab type word, error data word)
  kat hk unmarshalSSZ 100
  kat hk unmarshalSSZ 101
  apply store_step_at _ _ (rsp.toBitVec - 48) _ _ _ ((Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).take 8)
    _ _ (by iaaddr) (by ecancel) (by simp [Int.toBytes_length])
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  kat hk unmarshalSSZ 102
  apply store_step_at _ _ (rsp.toBitVec - 40) _ _ _ ((Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8)
    _ _ (by iaaddr) (by ecancel) (by simp [Int.toBytes_length])
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  kat hk unmarshalSSZ 103
  apply load_step _ _ _ _ (Int.toBytes 8 e0.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk unmarshalSSZ 104
  intro _
  kat hk unmarshalSSZ 105
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    exact he0nz (UInt64.toBitVec_inj.mp (by simpa using h))
  simp only [Effects.All]
  kat hk unmarshalSSZ 106
  apply load_step_at _ _ ((label "go_itab._errors.errorString_error").toBitVec + 8) _ _ ity _ _ (by rw [he0])
    (by ecancel) (by exact hity)
  kunfold
  kat hk unmarshalSSZ 107
  kat hk unmarshalSSZ 108
  apply load_step _ _ _ _ (Int.toBytes 8 e1.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk unmarshalSSZ 109
  apply store_step_at _ _ (rsp.toBitVec - 32) _ _ _ ((Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).take 8)
    _ _ (by iaaddr) (by ecancel) (by simp [Int.toBytes_length])
  intro m8 H8
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl ity hity] at H8
  kunfold
  kat hk unmarshalSSZ 110
  apply store_step_at _ _ (rsp.toBitVec - 24) _ _ _ ((Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8)
    _ _ (by iaaddr) (by ecancel) (by simp [Int.toBytes_length])
  intro m9 H9
  simp only [Width.bytes, Width.bits] at H9
  kunfold
  -- 111–116: `fmt.errorf(fmt, 83, &args, 2, 2)`
  kat hk unmarshalSSZ 111
  kat hk unmarshalSSZ 112
  kat hk unmarshalSSZ 113
  kat hk unmarshalSSZ 114
  kat hk unmarshalSSZ 115
  kat hk unmarshalSSZ 116
  apply store_step_at _ _ (rsp.toBitVec - 184) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 99 + 1)).toBitVec.toInt) _ _
    (by iaaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m10 H10
  simp only [Width.bytes, Width.bits] at H10
  kunfold
  rw [show rsp.toBitVec - 176 - 8#64 = rsp.toBitVec - 184 by iaaddr]
  refine eventually_trans _ _ _ _ (hfe _ (Host.addrOf (k + 116 + 1)) av1 ity msg hb1 stk1 (sp1 ++ spl.drop 8)
    rax1.toBitVec C e1.toBitVec esp _
    (by rw [fmtMisaligned_length]; rfl) (by first | rfl | decide) (by first | rfl | decide)
    hity hbox1 hstk1 (by simp [hsp1, hspl]) (by rw [fmtMisaligned_length] at hav ⊢; omega)
    (by
      dsimp only
      rw [show rsp.toBitVec - 176 + 128 = rsp.toBitVec - 48 by iaaddr]
      rw [show rsp.toBitVec - 184 + 8 = rsp.toBitVec - 176 by iaaddr, intType_addr_eq,
        staticBox_congr hCv, hSB,
        at_app (Int.toBytes 8 (label "type__" + 387520).toBitVec.toInt ++ Int.toBytes 8 rax1.toBitVec.toInt ++ ity)
          (Int.toBytes 8 e1.toBitVec.toInt) (a := rsp.toBitVec - 48) (b := rsp.toBitVec - 24) (by simp only [List.length_append, Int.toBytes_length, hity]; iaaddr) (by simp only [List.length_append, Int.toBytes_length, hity]; omega),
        at_app (Int.toBytes 8 (label "type__" + 387520).toBitVec.toInt ++ Int.toBytes 8 rax1.toBitVec.toInt) ity
          (a := rsp.toBitVec - 48) (b := rsp.toBitVec - 32) (by simp only [List.length_append, Int.toBytes_length]; iaaddr) (by simp only [List.length_append, Int.toBytes_length, hity]; omega),
        at_app (Int.toBytes 8 (label "type__" + 387520).toBitVec.toInt) (Int.toBytes 8 rax1.toBitVec.toInt)
          (a := rsp.toBitVec - 48) (b := rsp.toBitVec - 40) (by simp only [Int.toBytes_length]; iaaddr) (by simp only [Int.toBytes_length]; omega),
        at_app sp1 (spl.drop 8) (a := rsp.toBitVec - 176) (b := rsp.toBitVec - 168) (by rw [hsp1]; iaaddr) (by simp [hsp1, hspl])]
      ecancel)) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrsp2, hr142, hrax2, stk2, sp2, av2, hstk2, hsp2, hav2, Hm2⟩
  dsimp only at hpc2 hrsp2 hr142 hrax2 Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := d2
  simp only at hrsp2 hr142 hrax2 Hm2
  rw [show ({ toBitVec := rsp.toBitVec - 184 } + 8 : UInt64) = { toBitVec := rsp.toBitVec - 176 } by
    apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; iaaddr] at hrsp2
  subst hrsp2 hr142
  -- 117–130: err ≠ nil, `jne L_248` taken, epilogue
  kat hk unmarshalSSZ 117
  try intro _
  kat hk unmarshalSSZ 118
  split
  case isFalse h =>
    exfalso; apply h; simp only [CondCode.interp, StatusFlags.from_result]; simp
    intro h0; exact hrax2 (UInt64.toBitVec_inj.mp (by simpa using h0))
  simp only [Effects.All]
  klabel hk hf unmarshalSSZ 127
  kat hk unmarshalSSZ 127
  kat hk unmarshalSSZ 128
  try intro _
  kat hk unmarshalSSZ 129
  apply load_step_at _ _ (rsp.toBitVec - 8) _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by iaaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk unmarshalSSZ 130
  apply load_step_at _ _ rsp.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by iaaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  rw [hCv] at hbox1
  refine ⟨?_, hrax2, ?_, ?_, ?_, rax1.toBitVec, hb1, sp2, stk2, av2, hsp2, hstk2, hbox1, by omega, ?_⟩
  rotate_right
  · rw [errIncorrectListSize_addr_eq, fmtMisaligned_addr_eq, intType_addr_eq]
    rw [show k + 116 + 1 = k + 117 from rfl] at Hm2
    rw [show rsp.toBitVec - 176 + 128 = rsp.toBitVec - 48 by iaaddr] at Hm2
    rw [show rsp.toBitVec - 184 + 8 = rsp.toBitVec - 176 by iaaddr, staticBox_congr hCv, hSB] at Hm2
    ecancel
  all_goals first
    | exact trivial
    | with_reducible rfl
    | (apply UInt64.toBitVec_inj.mp
       simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, Width.bits]
       done)
    | (apply UInt64.toBitVec_inj.mp; iaaddr)

-- Measured cause: without this option the first `kat` (directive 0) stops with "maximum recursion depth", as in
-- `Prysm/IndexedAttestation/DecodeRejectSize.lean`; 1024 passes.
set_option maxRecDepth 1024 in
theorem Decode.reject_overflow_error_word_nonzero : Decode.reject_overflow_error_word_nonzero_statement := by
  intro k hk hf s ra guard e0 e1 esp msg ity he0 he0nz hity fp s2 aw spl rslot lo hfp h2 haw hspl hrs S hlo
    Heap avail R h_mem hguard hlen hal0 hbig hav hcv hfe
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen hal0 hbig hav
  dsimp only
  have hz1 := rsp.toNat_lt_size; have hz2 := guard.toNat_lt_size; have hz3 := rcx.toNat_lt_size
  simp only [UInt64.size] at hz1 hz2 hz3
  generalize hSB : StaticBox (BitVec.ofNat 64 ((rcx.toNat - 228) / 8)) = SB at h_mem
  rw [errListTooBig_addr_eq, fmtTooBig_addr_eq] at h_mem
  -- the argument array as two 16-byte chunks
  rw [← List.take_append_drop 16 aw, at_app (aw.take 16) (aw.drop 16) (b := rsp.toBitVec - 64)
    (by simp only [List.length_take, haw]; iaaddr) (by simp [haw])] at h_mem
  -- the spill area as the convT64 spill slot and the rest
  rw [← List.take_append_drop 8 spl, at_app (spl.take 8) (spl.drop 8) (b := rsp.toBitVec - 168)
    (by simp only [List.length_take, hspl]; iaaddr) (by simp [hspl])] at h_mem
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
  have hCn : (-228 + rcx.toBitVec).toNat = rcx.toNat - 228 := by
    rw [BitVec.add_comm, Decode.sub228 _ (by rw [UInt64.toNat_toBitVec]; omega), UInt64.toNat_toBitVec]
  have hal : (-228 + rcx.toBitVec &&& 7) = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, hCn]
    show (rcx.toNat - 228) &&& 7 = 0
    rw [show (7 : Nat) = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; exact hal0
  generalize -228 + rcx.toBitVec = C at hCn hal ⊢
  kat hk unmarshalSSZ 26
  split
  case isTrue h => exfalso; rw [hal] at h; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk unmarshalSSZ 27
  kshl64 3
  have hQn : (BitVec.ushiftRight C 3).toNat = (rcx.toNat - 228) / 8 := by
    rw [show C.ushiftRight 3 = C >>> 3 from rfl, BitVec.toNat_ushiftRight, hCn, Nat.shiftRight_eq_div_pow]
  have hQv : BitVec.ushiftRight C 3 = BitVec.ofNat 64 ((rcx.toNat - 228) / 8) := by
    apply BitVec.eq_of_toNat_eq; rw [hQn, BitVec.toNat_ofNat]; omega
  generalize BitVec.ushiftRight C 3 = Q at hQn hQv ⊢
  kat hk unmarshalSSZ 28
  kat hk unmarshalSSZ 29
  kat hk unmarshalSSZ 30
  split
  case isFalse h =>
    exfalso; apply h; exact Decode.jg2048_true _ _ (by omega) (by omega)
  simp only [Effects.All]
  klabel hk hf unmarshalSSZ 57
  kat hk unmarshalSSZ 57
  kat hk unmarshalSSZ 58
  kat hk unmarshalSSZ 59
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  kunfold
  rw [show rsp.toBitVec - 8#64 - 168 + 96 = rsp.toBitVec - 80 by iaaddr]
  apply store_avx_step _ _ _ _ (aw.take 16) _ _ (by ecancel) (by simp [haw]) (by decide)
  intro m3 H3
  kunfold
  kat hk unmarshalSSZ 60
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  kunfold
  rw [show rsp.toBitVec - 80 + 16 = rsp.toBitVec - 64 by iaaddr]
  apply store_avx_step _ _ _ _ (aw.drop 16) _ _ (by ecancel) (by simp [haw]) (by decide)
  intro m4 H4
  kunfold
  kat hk unmarshalSSZ 61
  kat hk unmarshalSSZ 62
  apply store_step_at _ _ (rsp.toBitVec - 184) _ _ _ rslot _ _ (by iaaddr) (by ecancel) (by exact hrs)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  rw [show rsp.toBitVec - 8#64 - 168 - 8#64 = rsp.toBitVec - 184 by iaaddr]
  refine eventually_trans _ _ _ _ (hcv _ (Host.addrOf (k + 62 + 1)) avail lo (spl.take 8) _ (by omega) hlo
    (by simp [hspl]) (by
      dsimp only
      rw [show rsp.toBitVec - 184 + 8 = rsp.toBitVec - 176 by iaaddr, staticBox_congr hQv, hSB]
      ecancel)) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hr141, stk1, sp1, hb1, av1, hstk1, hsp1, hbox1, hav1, hav1', Hm1⟩
  dsimp only at hpc1 hrsp1 hr141 Hm1
  subst hpc1
  rw [staticBox_congr hQv, hSB] at Hm1
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩,
    zmms1, flags1, mem1⟩ := d1
  simp only at hrsp1 hr141 Hm1 hbox1
  rw [show ({ toBitVec := rsp.toBitVec - 184 } + 8 : UInt64) = { toBitVec := rsp.toBitVec - 176 } by
    apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; iaaddr] at hrsp1
  subst hrsp1 hr141
  rw [show rsp.toBitVec - 184 + 8 = rsp.toBitVec - 176 by iaaddr,
    lr_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 80), lr_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 64),
    show rsp.toBitVec - 80 + 8 = rsp.toBitVec - 72 by iaaddr, show rsp.toBitVec - 64 + 8 = rsp.toBitVec - 56 by iaaddr]
    at Hm1
  -- 63–73: the argument array (type:int, box, itab type word, error data word)
  kat hk unmarshalSSZ 63
  kat hk unmarshalSSZ 64
  apply store_step_at _ _ (rsp.toBitVec - 80) _ _ _ ((Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).take 8)
    _ _ (by iaaddr) (by ecancel) (by simp [Int.toBytes_length])
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  kat hk unmarshalSSZ 65
  apply store_step_at _ _ (rsp.toBitVec - 72) _ _ _ ((Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8)
    _ _ (by iaaddr) (by ecancel) (by simp [Int.toBytes_length])
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  kat hk unmarshalSSZ 66
  apply load_step _ _ _ _ (Int.toBytes 8 e0.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk unmarshalSSZ 67
  intro _
  kat hk unmarshalSSZ 68
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    exact he0nz (UInt64.toBitVec_inj.mp (by simpa using h))
  simp only [Effects.All]
  kat hk unmarshalSSZ 69
  apply load_step_at _ _ ((label "go_itab._errors.errorString_error").toBitVec + 8) _ _ ity _ _ (by rw [he0])
    (by ecancel) (by exact hity)
  kunfold
  kat hk unmarshalSSZ 70
  kat hk unmarshalSSZ 71
  apply load_step _ _ _ _ (Int.toBytes 8 e1.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk unmarshalSSZ 72
  apply store_step_at _ _ (rsp.toBitVec - 64) _ _ _ ((Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).take 8)
    _ _ (by iaaddr) (by ecancel) (by simp [Int.toBytes_length])
  intro m8 H8
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl ity hity] at H8
  kunfold
  kat hk unmarshalSSZ 73
  apply store_step_at _ _ (rsp.toBitVec - 56) _ _ _ ((Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8)
    _ _ (by iaaddr) (by ecancel) (by simp [Int.toBytes_length])
  intro m9 H9
  simp only [Width.bytes, Width.bits] at H9
  kunfold
  -- 74–79: `fmt.errorf(fmt, 73, &args, 2, 2)`
  kat hk unmarshalSSZ 74
  kat hk unmarshalSSZ 75
  kat hk unmarshalSSZ 76
  kat hk unmarshalSSZ 77
  kat hk unmarshalSSZ 78
  kat hk unmarshalSSZ 79
  apply store_step_at _ _ (rsp.toBitVec - 184) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 62 + 1)).toBitVec.toInt) _ _
    (by iaaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m10 H10
  simp only [Width.bytes, Width.bits] at H10
  kunfold
  rw [show rsp.toBitVec - 176 - 8#64 = rsp.toBitVec - 184 by iaaddr]
  refine eventually_trans _ _ _ _ (hfe _ (Host.addrOf (k + 79 + 1)) av1 ity msg hb1 stk1 (sp1 ++ spl.drop 8)
    rax1.toBitVec Q e1.toBitVec esp _
    (by rw [fmtTooBig_length]; rfl) (by first | rfl | decide) (by first | rfl | decide)
    hity hbox1 hstk1 (by simp [hsp1, hspl]) (by rw [fmtTooBig_length] at hav ⊢; omega)
    (by
      dsimp only
      rw [show rsp.toBitVec - 176 + 96 = rsp.toBitVec - 80 by iaaddr]
      rw [show rsp.toBitVec - 184 + 8 = rsp.toBitVec - 176 by iaaddr, intType_addr_eq,
        staticBox_congr hQv, hSB,
        at_app (Int.toBytes 8 (label "type__" + 387520).toBitVec.toInt ++ Int.toBytes 8 rax1.toBitVec.toInt ++ ity)
          (Int.toBytes 8 e1.toBitVec.toInt) (a := rsp.toBitVec - 80) (b := rsp.toBitVec - 56) (by simp only [List.length_append, Int.toBytes_length, hity]; iaaddr) (by simp only [List.length_append, Int.toBytes_length, hity]; omega),
        at_app (Int.toBytes 8 (label "type__" + 387520).toBitVec.toInt ++ Int.toBytes 8 rax1.toBitVec.toInt) ity
          (a := rsp.toBitVec - 80) (b := rsp.toBitVec - 64) (by simp only [List.length_append, Int.toBytes_length]; iaaddr) (by simp only [List.length_append, Int.toBytes_length, hity]; omega),
        at_app (Int.toBytes 8 (label "type__" + 387520).toBitVec.toInt) (Int.toBytes 8 rax1.toBitVec.toInt)
          (a := rsp.toBitVec - 80) (b := rsp.toBitVec - 72) (by simp only [Int.toBytes_length]; iaaddr) (by simp only [Int.toBytes_length]; omega),
        at_app sp1 (spl.drop 8) (a := rsp.toBitVec - 176) (b := rsp.toBitVec - 168) (by rw [hsp1]; iaaddr) (by simp [hsp1, hspl])]
      ecancel)) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrsp2, hr142, hrax2, stk2, sp2, av2, hstk2, hsp2, hav2, Hm2⟩
  dsimp only at hpc2 hrsp2 hr142 hrax2 Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := d2
  simp only at hrsp2 hr142 hrax2 Hm2
  rw [show ({ toBitVec := rsp.toBitVec - 184 } + 8 : UInt64) = { toBitVec := rsp.toBitVec - 176 } by
    apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; iaaddr] at hrsp2
  subst hrsp2 hr142
  -- 80–93: err ≠ nil, `jne L_199` taken, epilogue
  kat hk unmarshalSSZ 80
  try intro _
  kat hk unmarshalSSZ 81
  split
  case isFalse h =>
    exfalso; apply h; simp only [CondCode.interp, StatusFlags.from_result]; simp
    intro h0; exact hrax2 (UInt64.toBitVec_inj.mp (by simpa using h0))
  simp only [Effects.All]
  klabel hk hf unmarshalSSZ 90
  kat hk unmarshalSSZ 90
  kat hk unmarshalSSZ 91
  try intro _
  kat hk unmarshalSSZ 92
  apply load_step_at _ _ (rsp.toBitVec - 8) _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by iaaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk unmarshalSSZ 93
  apply load_step_at _ _ rsp.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by iaaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  rw [hQv] at hbox1
  refine ⟨?_, hrax2, ?_, ?_, ?_, rax1.toBitVec, hb1, sp2, stk2, av2, hsp2, hstk2, hbox1, by omega, ?_⟩
  rotate_right
  · rw [errListTooBig_addr_eq, fmtTooBig_addr_eq, intType_addr_eq]
    rw [show k + 79 + 1 = k + 80 from rfl] at Hm2
    rw [show rsp.toBitVec - 176 + 96 = rsp.toBitVec - 80 by iaaddr] at Hm2
    rw [show rsp.toBitVec - 184 + 8 = rsp.toBitVec - 176 by iaaddr, staticBox_congr hQv, hSB] at Hm2
    ecancel
  all_goals first
    | exact trivial
    | with_reducible rfl
    | (apply UInt64.toBitVec_inj.mp
       simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, Width.bits]
       done)
    | (apply UInt64.toBitVec_inj.mp; iaaddr)

end Prysm.IndexedAttestation
