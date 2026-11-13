import Runtime.Contracts
import Machine.Step
import Machine.Labels
import Codec.StackGuard
import Prysm.DataColumnsByRootIdentifier.StatementsEncode
import Prysm.DataColumnsByRootIdentifier.EncodeTail

/-!
# `(*v1alpha1.DataColumnsByRootIdentifier).MarshalSSZTo`: the two rejects

- `Encode.reject_length : Encode.reject_length_statement`: directives 2–9 as the fast path, 10–11
  `cmpq $0x20,0x10(%rax); jne L_117` taken (`len(BlockRoot) ≠ 32`), 70–78 the two words of `ssz.ErrBytesLength`,
  rax = rbx = rcx = 0, epilogue.
- `Encode.reject_too_big : Encode.reject_too_big_statement`: directives 2–15 and 29–54 as the fast path (the text of
  `Encode.tail_fit` with this frame), 55 `jg L_fc` taken (`128 < n < 2^63`), 61–69 the two words of `ssz.ErrListTooBig`.
-/

open Machine Runtime Prysm.DataColumnsByRootIdentifier.Code
variable [Host]

namespace Prysm.DataColumnsByRootIdentifier

omit [Host] in
/-- `cmp $0x80, a; jg` is taken when `128 < a < 2^63`. -/
theorem Encode.jg128_true (a : BitVec 64) (af : Bool) (h1 : 128 < a.toNat) (h2 : a.toNat < 2 ^ 63) :
    CondCode.g.interp (StatusFlags.from_result (a - 128)
      { cf := BitVec.unsigned (a - 128) != a.unsigned - BitVec.unsigned (128 : BitVec 64), af := af,
        of := BitVec.toInt (a - 128) != a.toInt - BitVec.toInt (128 : BitVec 64) }) = true := by
  have ta : a.toInt = a.toNat := BitVec.toInt_eq_toNat_of_lt (by omega)
  have t16 : BitVec.toInt (128 : BitVec 64) = 128 := by decide
  have hnz : a - 128 ≠ 0#64 := by
    intro h; have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  have hm : (a - 128).msb = false := by
    rw [BitVec.msb_eq_decide]; simp [BitVec.toNat_sub]; omega
  simp [CondCode.interp, StatusFlags.from_result, ta, hnz]
  rw [show (a - 128#64).msb = false from hm, Int.bmod_eq_of_le (by omega) (by omega)]; simp
  all_goals exact hnz

omit [Host] in
theorem Encode.reject_split36 (d : List UInt8) (hd : d.length = 36) (a : BitVec 64) :
    Eq (d.At a) = Eq ((d.take 32).At a) ⋆ Eq ((d.drop 32).At (a + 32)) := by
  conv => lhs; rw [← List.take_append_drop 32 d]
  rw [Mem.At_append_sep _ _ _ (by simp; omega)]
  have l1 : (d.take 32).length = 32 := by simp; omega
  rw [l1]; rfl

omit [Host] in
theorem Encode.reject_join (pre root : List UInt8) (hroot : root.length = 32) (a l : BitVec 64) (hpre : pre.length = l.toNat)
    (hb : pre.length + 36 ≤ 2 ^ 64) :
    Eq (pre.At a) ⋆ Eq (root.At (a + l)) ⋆ Eq (offsetBytes.At (a + l + 32)) = Eq ((pre ++ root ++ offsetBytes).At a) := by
  rw [List.append_assoc, at_app pre _ (b := a + l) (by rw [hpre, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (by simp [hroot, offsetBytes]; omega), at_app root offsetBytes (b := a + l + 32) (by rw [hroot]; rfl)
    (by simp [hroot, offsetBytes]), ← Std.ExtHashMap.sep_assoc]

theorem Encode.reject_length : Encode.reject_length_statement := by
  intro k hk hf s ra guard e0 e1 pr bl hbl fp s2 hfp h2 R h_mem hguard
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard ⊢
  have hz1 := rsp.toNat_lt_size; have hz2 := guard.toNat_lt_size; have hz3 := rcx.toNat_lt_size
  simp only [UInt64.size] at hz1 hz2 hz3
  kat hk marshalSSZTo 0
  kat hk marshalSSZTo 1
  kat hk marshalSSZTo 2
  kat hk marshalSSZTo 3
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 4
  split
  case isTrue h =>
    exfalso
    rw [Codec.lea_cmp_be_false rsp.toBitVec _ guard.toBitVec _ _ 8 (by rfl) hguard] at h
    exact Bool.noConfusion h
  simp only [Effects.All]
  kat hk marshalSSZTo 5
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by daddr) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk marshalSSZTo 6
  kat hk marshalSSZTo 7
  kat hk marshalSSZTo 8
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by daddr) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk marshalSSZTo 9
  apply load_step_at _ _ (rax.toBitVec + 8) _ _ (Int.toBytes 8 pr.toInt) _ _ (by daddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 10
  apply load_step_at _ _ (rax.toBitVec + 16) _ _ (Int.toBytes 8 bl.toInt) _ _ (by daddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 11
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    exact hbl (by rw [← BitVec.sub_add_cancel bl 32#64, h]; decide)
  simp only [Effects.All]
  klabel hk hf marshalSSZTo 70
  kat hk marshalSSZTo 70
  kat hk marshalSSZTo 71
  apply load_step _ _ _ _ (Int.toBytes 8 e0.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 72
  apply load_step _ _ _ _ (Int.toBytes 8 e1.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 73
  intro _
  kat hk marshalSSZTo 74
  intro _
  kat hk marshalSSZTo 75
  kat hk marshalSSZTo 76
  kat hk marshalSSZTo 77
  apply load_step_at _ _ (rsp.toBitVec - 8) _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by daddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 78
  apply load_step_at _ _ rsp.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by daddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_right
  · ecancel
  all_goals first
    | exact trivial
    | rfl
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (apply UInt64.toBitVec_inj.mp; daddr)

theorem Encode.reject_too_big : Encode.reject_too_big_statement := by
  intro k hk hf s ra guard e0 e1 pr nb hn1 hn2 root pre d hroot hpre hd fp s1 s2 l32 l56 l64 rslot hfp h1 h2 hl32 hl56
    hl64 hrs S scratch hsc R h_mem hguard hcap hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hcap hpre ⊢
  rw [Encode.reject_split36 d hd] at h_mem
  have hz1 := rsp.toNat_lt_size; have hz2 := guard.toNat_lt_size; have hz3 := rcx.toNat_lt_size
  have hz4 := rdi.toNat_lt_size
  simp only [UInt64.size] at hz1 hz2 hz3 hz4
  kat hk marshalSSZTo 0
  kat hk marshalSSZTo 1
  kat hk marshalSSZTo 2
  kat hk marshalSSZTo 3
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by dsimp only; ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 4
  split
  case isTrue h =>
    exfalso
    rw [Codec.lea_cmp_be_false rsp.toBitVec _ guard.toBitVec _ _ 8 (by rfl) hguard] at h
    exact Bool.noConfusion h
  simp only [Effects.All]
  kat hk marshalSSZTo 5
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by daddr) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk marshalSSZTo 6
  kat hk marshalSSZTo 7
  kat hk marshalSSZTo 8
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by daddr) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk marshalSSZTo 9
  apply load_step_at _ _ (rax.toBitVec + 8) _ _ (Int.toBytes 8 pr.toInt) _ _ (by daddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 10
  apply load_step_at _ _ (rax.toBitVec + 16) _ _ (Int.toBytes 8 32) _ _ (by daddr) (by ecancel) (by rfl)
  simp only [show Int.ofBytes (Int.toBytes 8 32) = 32 by decide]
  kunfold
  kat hk marshalSSZTo 11
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk marshalSSZTo 12
  apply store_step_at _ _ (rsp.toBitVec + 8) _ _ _ s1 _ _ (by daddr) (by ecancel) (by exact h1)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk marshalSSZTo 13
  kat hk marshalSSZTo 14
  kat hk marshalSSZTo 15
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf marshalSSZTo 29
  kat hk marshalSSZTo 29
  kat hk marshalSSZTo 30
  apply store_step_at _ _ (rsp.toBitVec - 64) _ _ _ l64 _ _ (by daddr) (by ecancel) (by exact hl64)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk marshalSSZTo 31
  apply store_step_at _ _ (rsp.toBitVec - 32) _ _ _ l32 _ _ (by daddr) (by ecancel) (by exact hl32)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk marshalSSZTo 32
  apply store_step_at _ _ (rsp.toBitVec - 56) _ _ _ l56 _ _ (by daddr) (by ecancel) (by exact hl56)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk marshalSSZTo 33
  kat hk marshalSSZTo 34
  kat hk marshalSSZTo 35
  kat hk marshalSSZTo 36
  apply store_step_at _ _ (rsp.toBitVec - 144) _ _ _ rslot _ _ (by daddr) (by ecancel) (by exact hrs)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  rw [BitVec.mul_one, show -128 + (rsp.toBitVec - 8#64) - 8#64 = rsp.toBitVec - 144 by bv_omega]
  refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (k + 36 + 1)) root (d.take 32) scratch _
    (by rw [hroot]; rfl) (by simp [hd, hroot]) hsc (by dsimp only; ecancel)) ?_
  rintro ⟨e1, pc1⟩ ⟨hpc1, hrsp1, hr141, hrbp1, stk1, hstk1, Hm1⟩
  dsimp only at hpc1 hrsp1 hr141 hrbp1 Hm1
  subst hpc1
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩,
    zmms1, flags1, mem1⟩ := e1
  simp only at hrsp1 hr141 hrbp1 Hm1
  have hrsp1' : rsp1 = { toBitVec := -128 + (rsp.toBitVec - 8#64) } := by
    rw [hrsp1]; apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
  subst hrsp1' hr141 hrbp1
  kat hk marshalSSZTo 37
  apply load_step_at _ _ (rsp.toBitVec - 64) _ _ (Int.toBytes 8 (rcx.toBitVec + 32).toInt) _ _ (by daddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 38
  kat hk marshalSSZTo 39
  kat hk marshalSSZTo 40
  apply load_step_at _ _ (rsp.toBitVec - 56) _ _ (Int.toBytes 8 rdi.toBitVec.toInt) _ _ (by daddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 41
  kat hk marshalSSZTo 42
  split
  case isTrue h =>
    exfalso; simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    have := Encode.tail_room (rcx.toBitVec + 32) rcx.toBitVec rdi.toBitVec rdi.toNat rfl rfl hcap (by omega)
    simp [BitVec.toNat_add] at this h; omega
  simp only [Effects.All]
  kat hk marshalSSZTo 43
  apply load_step_at _ _ (rsp.toBitVec - 32) _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by daddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 44
  klabel hk hf marshalSSZTo 50
  kat hk marshalSSZTo 50
  kat hk marshalSSZTo 51
  rw [Encode.tail_offset_addr _ _ _ rfl]
  apply store_step _ _ _ _ _ (d.drop 32) _ _ (by ecancel) (by simp [hd])

  intro m5 H5
  simp only [Width.bytes, Encode.offset_bytes_eq] at H5
  kunfold
  kat hk marshalSSZTo 52
  apply load_step_at _ _ (rsp.toBitVec + 8) _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by daddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 53
  apply load_step_at _ _ (rax.toBitVec + 40) _ _ (Int.toBytes 8 nb.toInt) _ _ (by daddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 54
  kat hk marshalSSZTo 55
  split
  case isFalse h => exfalso; rw [Encode.jg128_true _ _ hn1 hn2] at h; exact h rfl
  simp only [Effects.All]
  klabel hk hf marshalSSZTo 61
  kat hk marshalSSZTo 61
  kat hk marshalSSZTo 62
  apply load_step_at _ _ (label "ssz.ErrListTooBig").toBitVec _ _ (Int.toBytes 8 e0.toBitVec.toInt) _ _ rfl
    (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 63
  apply load_step_at _ _ (label "ssz.ErrListTooBig" + 8).toBitVec _ _ (Int.toBytes 8 e1.toBitVec.toInt) _ _ rfl
    (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 64
  intro _
  kat hk marshalSSZTo 65
  intro _
  kat hk marshalSSZTo 66
  kat hk marshalSSZTo 67
  kat hk marshalSSZTo 68
  apply load_step_at _ _ (rsp.toBitVec - 8) _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by daddr) (by dsimp only; ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 69
  apply load_step_at _ _ rsp.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by daddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Int.toBytes 8 rbx.toBitVec.toInt, Int.toBytes 8 rdi.toBitVec.toInt,
    Int.toBytes 8 (rcx.toBitVec + 32).toInt, Int.toBytes 8 (Host.addrOf (k + 36 + 1)).toBitVec.toInt, stk1,
    Int.toBytes_length 8 _, Int.toBytes_length 8 _, Int.toBytes_length 8 _, Int.toBytes_length 8 _, hstk1, ?mem⟩
  case mem =>
    rw [← Encode.reject_join pre root hroot _ _ hpre (by omega)]
    ecancel
  all_goals first
    | exact trivial
    | rfl
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (apply UInt64.toBitVec_inj.mp; daddr)

end Prysm.DataColumnsByRootIdentifier
