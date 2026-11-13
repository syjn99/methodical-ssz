import Runtime.Contracts
import Machine.Step
import Machine.Labels
import Codec.StackGuard
import Prysm.DataColumnsByRootIdentifier.StatementsEncode
import Prysm.DataColumnsByRootIdentifier.EncodeTail

/-!
# `(*v1alpha1.DataColumnsByRootIdentifier).MarshalSSZTo`: first-site grow path (one grow at site 1 only)

`Encode.grow_first_site : Encode.grow_first_site_statement`. Directives 2–14 as the fast path; 15 `jae L_7c` not taken
(cap < len + 32); 16–17 rcx to x + 24, rdx (BlockRoot pointer) to x − 16; 18–23
`growslice(dst.ptr, len + 32, cap, 32, uint8)` under `GrowsliceC Heap typeUint8_addr 1 S` (spill area x − 136, return
slot x − 144); 24–28 restore rdx, rdi = newCap, r8 = len + 32, rcx = len, rbx = new pointer; then `Encode.tail_fit` with the
new block (premise `hfit`: sites 2 and 3 do not grow).
-/

open Machine Runtime Prysm.DataColumnsByRootIdentifier.Code
variable [Host]

namespace Prysm.DataColumnsByRootIdentifier

omit [Host] in
theorem Encode.grow_first_site_split (np len : BitVec 64) (pre tail : List UInt8) (m : Nat) (hpre : pre.length = len.toNat)
    (ht : m ≤ tail.length) (hb : pre.length + tail.length < 2 ^ 64) :
    Eq ((pre ++ tail).At np) = Eq (pre.At np) ⋆ Eq ((tail.take m).At (np + len))
      ⋆ Eq ((tail.drop m).At (np + len + BitVec.ofNat 64 m)) := by
  rw [at_app pre tail (b := np + len) (by rw [hpre, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega)]
  conv => lhs; rhs; rw [← List.take_append_drop m tail]
  rw [at_app _ _ (b := np + len + BitVec.ofNat 64 m) (by rw [List.length_take, Nat.min_eq_left ht])
    (by simp; omega), ← Std.ExtHashMap.sep_assoc]

omit [Host] in
theorem Encode.grow_first_site_join (np len : BitVec 64) (pre body rest : List UInt8) (hpre : pre.length = len.toNat)
    (hb : pre.length + body.length + rest.length < 2 ^ 64) :
    Eq (pre.At np) ⋆ Eq (body.At (np + len)) ⋆ Eq (rest.At (np + len + BitVec.ofNat 64 body.length))
      = Eq ((pre ++ body ++ rest).At np) := by
  rw [List.append_assoc, at_app pre _ (b := np + len) (by rw [hpre, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (by simp; omega), at_app body rest (b := np + len + BitVec.ofNat 64 body.length) rfl (by omega),
    ← Std.ExtHashMap.sep_assoc]

theorem Encode.grow_first_site : Encode.grow_first_site_statement := by
  intro k hk hf s ra guard pr pc nb n hnb hn root cb pre hroot hcb hpre fp s1 s2 s3 l16 l24 l32 l40 l56 l64 spl rslot
    hfp h1 h2 h3 hl16 hl24 hl32 hl40 hl56 hl64 hspl hrs S scratch hsc Heap avail R h_mem hguard hlc hgrow hfit hbud
    hmax hgs hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlc hgrow hfit hbud hpre ⊢
  have hz1 := rsp.toNat_lt_size; have hz2 := guard.toNat_lt_size; have hz3 := rcx.toNat_lt_size
  have hz4 := rdi.toNat_lt_size
  simp only [UInt64.size] at hz1 hz2 hz3 hz4
  have hnsc := nextSliceCap_le (rcx.toNat + 32) rdi.toNat (by omega)
  have hb48 : rcx.toNat + 36 + 8 * n ≤ 2 ^ 48 := by unfold maxAlloc at hmax; omega
  have e32 : ({ toBitVec := BitVec.zeroExtend 64 (BitVec.truncate 32 (32 : BitVec 64)) } : UInt64).toNat = 32 := by
    decide
  have enl : ({ toBitVec := rcx.toBitVec + 32 } : UInt64).toNat = rcx.toNat + 32 := by
    show (rcx.toBitVec + 32).toNat = _; simp [BitVec.toNat_add]; omega
  have erd : ({ toBitVec := rdi.toBitVec } : UInt64).toNat = rdi.toNat := rfl
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
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by data_columns_by_root_identifier_encode_addr) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk marshalSSZTo 6
  kat hk marshalSSZTo 7
  kat hk marshalSSZTo 8
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by data_columns_by_root_identifier_encode_addr) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk marshalSSZTo 9
  apply load_step_at _ _ (rax.toBitVec + 8) _ _ (Int.toBytes 8 pr.toInt) _ _ (by data_columns_by_root_identifier_encode_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 10
  apply load_step_at _ _ (rax.toBitVec + 16) _ _ (Int.toBytes 8 32) _ _ (by data_columns_by_root_identifier_encode_addr) (by ecancel) (by rfl)
  simp only [show Int.ofBytes (Int.toBytes 8 32) = 32 by decide]
  kunfold
  kat hk marshalSSZTo 11
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk marshalSSZTo 12
  apply store_step_at _ _ (rsp.toBitVec + 8) _ _ _ s1 _ _ (by data_columns_by_root_identifier_encode_addr) (by ecancel) (by exact h1)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk marshalSSZTo 13
  kat hk marshalSSZTo 14
  kat hk marshalSSZTo 15
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  kat hk marshalSSZTo 16
  apply store_step_at _ _ (rsp.toBitVec + 24) _ _ _ s3 _ _ (by data_columns_by_root_identifier_encode_addr) (by ecancel) (by exact h3)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  kat hk marshalSSZTo 17
  apply store_step_at _ _ (rsp.toBitVec - 16) _ _ _ l16 _ _ (by data_columns_by_root_identifier_encode_addr) (by ecancel) (by exact hl16)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  kat hk marshalSSZTo 18
  kat hk marshalSSZTo 19
  kat hk marshalSSZTo 20
  kat hk marshalSSZTo 21
  kat hk marshalSSZTo 22
  kat hk marshalSSZTo 23
  apply store_step_at _ _ (rsp.toBitVec - 144) _ _ _ rslot _ _ (by data_columns_by_root_identifier_encode_addr) (by ecancel) (by exact hrs)
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  rw [show -128 + (rsp.toBitVec - 8#64) - 8#64 = rsp.toBitVec - 144 by bv_omega]
  refine eventually_trans _ _ _ _ (hgs _ (Host.addrOf (k + 23 + 1)) pre scratch spl avail _ (by decide) rfl
    ?gnum ?gold ?gcap ?gbud hmax ?glen hsc hspl
    (by dsimp only; rw [show rsp.toBitVec - 144 + 8 = rsp.toBitVec - 136 by bv_omega]; ecancel)) ?_
  all_goals try (dsimp only; simp only [e32, enl, erd, Nat.one_mul]; omega)
  rintro ⟨e1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, hrbx1, hnc1, hub1, stk1, spl1, tail, av1, hstk1, hspl1, htail, hav1,
    Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 hrbx1 hnc1 hub1 htail hav1 Hm1
  subst hpc1
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩,
    zmms1, flags1, mem1⟩ := e1
  simp only at hrsp1 hrbp1 hr141 hrbx1 hnc1 hub1 htail hav1 Hm1
  simp only [enl, erd, Nat.one_mul] at hnc1 hub1 htail hav1
  have hrsp1' : rsp1 = { toBitVec := -128 + (rsp.toBitVec - 8#64) } := by
    rw [hrsp1]; apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
  subst hrsp1' hrbp1 hr141 hrbx1
  have htl : 36 + 8 * n ≤ tail.length := by omega
  rw [Encode.grow_first_site_split rax1.toBitVec rcx.toBitVec pre tail (36 + 8 * n) hpre htl (by omega),
    show rsp.toBitVec - 144 + 8 = rsp.toBitVec - 136 by bv_omega] at Hm1
  kat hk marshalSSZTo 24
  apply load_step_at _ _ (rsp.toBitVec - 16) _ _ (Int.toBytes 8 pr.toInt) _ _ (by data_columns_by_root_identifier_encode_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 25
  kat hk marshalSSZTo 26
  kat hk marshalSSZTo 27
  apply load_step_at _ _ (rsp.toBitVec + 24) _ _ (Int.toBytes 8 rcx.toBitVec.toInt) _ _ (by data_columns_by_root_identifier_encode_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 28
  refine eventually_mono (Encode.tail_fit k hk hf rsp.toBitVec rax.toBitVec pr pc nb rax1.toBitVec ra rbp n rcx1.toNat hnb hn
    root cb (tail.take (36 + 8 * n)) hroot hcb (by rw [List.length_take, Nat.min_eq_left htl]) l24 l32 l40 l56 l64
    (Int.toBytes 8 (Host.addrOf (k + 23 + 1)).toBitVec.toInt) hl24 hl32 hl40 hl56 hl64 (Int.toBytes_length 8 _)
    S stk1 hstk1 _ _
    (by show -128 + (rsp.toBitVec - 8#64) = rsp.toBitVec - 136; bv_omega) rfl rfl rfl rfl
    (by show rcx.toNat + 36 + 8 * n ≤ rcx1.toNat; omega)
    (by dsimp only; ecancel) hmm) ?_
  rintro t ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, hrsp, hrbp, hr14, l24', l32', l40', l56', l64', rslot', scr,
    h24, h32, h40, h56, h64, hrs', hscr, hm⟩
  simp only at hrbx hr14 hm
  have hbody : (root ++ offsetBytes ++ cb).length = 36 + 8 * n := by simp [hroot, hcb, offsetBytes]; omega
  refine ⟨hpc, hrbx, hrcx ▸ hnc1, hrdi, hrsi, UInt64.toBitVec_inj.mp (by rw [hrsp]; simp), hrbp, hr14,
    Int.toBytes 8 pr.toInt, l24', l32', l40', l56', l64', spl1, rslot', scr, tail.drop (36 + 8 * n), av1,
    Int.toBytes_length 8 _, h24, h32, h40, h56, h64, hspl1, hrs', hscr, ?_, ?_, ?_⟩
  · rw [hrcx, List.length_drop]; omega
  · rw [hrcx]; omega
  · rw [hrax, show pre ++ root ++ offsetBytes ++ cb ++ tail.drop (36 + 8 * n)
        = pre ++ (root ++ offsetBytes ++ cb) ++ tail.drop (36 + 8 * n) by simp,
      ← Encode.grow_first_site_join rax1.toBitVec rcx.toBitVec pre (root ++ offsetBytes ++ cb) _ hpre (by simp only [hbody, List.length_drop]; omega),
      hbody]
    ecancel

end Prysm.DataColumnsByRootIdentifier
