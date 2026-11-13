import Prysm.DataColumnsByRootIdentifier.StatementsEncodeGrowOneSite
import Prysm.DataColumnsByRootIdentifier.EncodeFastPath
import Prysm.DataColumnsByRootIdentifier.EncodeGrowFirstSite
import Prysm.DataColumnsByRootIdentifier.EncodeTailGrow

/-!
# One-growth path, main theorem: growth at any one site (`Encode.grow_one_site_statement`)

Directives 2–14 as the fast path; 15 `jae L_7c`: taken (site 1 fits: `Encode.grow_tail` on the old block `pre ‖ spare`,
garbage empty) or not taken (16–28 as the first-site grow path, `growslice` of site 1; the new capacity holds the output by
`hone`; the old block joins the garbage frame), then `Encode.grow_tail` (sites 2 and 3 fit or grow, `Prysm/DataColumnsByRootIdentifier/EncodeTailGrow.lean`).
-/

open Machine Runtime TestTarget Prysm.DataColumnsByRootIdentifier.Code
variable [Host]

namespace Prysm.DataColumnsByRootIdentifier

theorem Encode.grow_one_site : Encode.grow_one_site_statement := by
  intro k hk hf s ra guard pr pc nb n hnb hn root cb pre spare hroot hcb hpre hspare fp s1 s2 s3 l16 l24 l32 l40 l48
    l56 l64 l72 spl rslot hfp h1 h2 h3 hl16 hl24 hl32 hl40 hl48 hl56 hl64 hl72 hspl hrs S scratch hsc Heap avail R
    h_mem hguard hbud hmax hone hgs hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hpre hspare hbud hone ⊢
  have hz1 := rsp.toNat_lt_size; have hz2 := guard.toNat_lt_size; have hz3 := rcx.toNat_lt_size
  have hz4 := rdi.toNat_lt_size
  simp only [UInt64.size] at hz1 hz2 hz3 hz4
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
  have hLm : rcx.toNat + 36 + 8 * n < 2 ^ 47 := by unfold maxAlloc at hmax; omega
  kat hk marshalSSZTo 15
  split
  · -- site 1 fits: `jae L_7c` taken
    rename_i h
    have hf32 : rcx.toNat + 32 ≤ rdi.toNat := by
      simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
    simp only [Effects.All]
    klabel hk hf marshalSSZTo 29
    refine eventually_mono (Encode.grow_tail k hk hf rsp.toBitVec rax.toBitVec pr pc nb ra rbp n rdi.toNat rdi.toNat hnb hn
      root cb pre spare hroot hcb S Heap _ hgs hmm avail Std.ExtHashMap.emp l24 l32 l40 l48 l56 l64 l72 spl rslot
      scratch hl24 hl32 hl40 hl48 hl56 hl64 hl72 hspl hrs hsc _ rbx.toBitVec hpre (by omega) hf32
      (by by_cases hb : rcx.toNat + 36 + 8 * n ≤ rdi.toNat
          · exact Or.inl hb
          · exact Or.inr ⟨rfl, by omega⟩) hmax hLm hone
      (by show -128 + (rsp.toBitVec - 8#64) = rsp.toBitVec - 136; bv_omega) rfl rfl rfl rfl
      (by dsimp only; simp only [Std.ExtHashMap.sep_emp]; ecancel)) ?_
    rintro st ⟨hpc, hrbx, hrdi, hrsi, hrsp, hrbp, hr14, a24, a32, a40, a48, a56, a64, a72, aspl, ars, ascr, rest, av',
      G', h24, h32, h40, h48, h56, h64, h72, hsp, hrs', hsc', hlen, hav', hm⟩
    refine ⟨hpc, hrbx, by simp only [UInt64.toNat] at hlen ⊢; omega, hrdi, hrsi, UInt64.toBitVec_inj.mp (by rw [hrsp]; simp), hrbp, hr14,
      s3, l16, a24, a32, a40, a48, a56, a64, a72, aspl, ars, ascr, rest, av', G', h3, hl16, h24, h32, h40, h48, h56, h64,
      h72, hsp, hrs', hsc', hlen, hav', ?_⟩
    ecancel
  · -- site 1 grows: 16–28
    rename_i h
    have hg32 : rdi.toNat < rcx.toNat + 32 := by
      simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
    have hnsc := nextSliceCap_le (rcx.toNat + 32) rdi.toNat (by omega)
    have e32 : ({ toBitVec := BitVec.zeroExtend 64 (BitVec.truncate 32 (32 : BitVec 64)) } : UInt64).toNat = 32 := by
      decide
    have enl : ({ toBitVec := rcx.toBitVec + 32 } : UInt64).toNat = rcx.toNat + 32 := by
      show (rcx.toBitVec + 32).toNat = _; simp [BitVec.toNat_add]; omega
    have erd : ({ toBitVec := rdi.toBitVec } : UInt64).toNat = rdi.toNat := rfl
    have epre : Eq ((pre ++ spare).At rbx.toBitVec) = Eq (pre.At rbx.toBitVec)
        ⋆ Eq (spare.At (rbx.toBitVec + rcx.toBitVec)) := by
      rw [at_app pre spare (b := rbx.toBitVec + rcx.toBitVec) (by rw [hpre]; simp) (by omega)]
    rw [epre] at H3
    simp only [Effects.All]
    kat hk marshalSSZTo 16
    apply store_step_at _ _ (rsp.toBitVec + 24) _ _ _ s3 _ _ (by daddr) (by ecancel) (by exact h3)
    intro m4 H4
    simp only [Width.bytes, Width.bits] at H4
    kunfold
    kat hk marshalSSZTo 17
    apply store_step_at _ _ (rsp.toBitVec - 16) _ _ _ l16 _ _ (by daddr) (by ecancel) (by exact hl16)
    intro m5 H5
    simp only [Width.bytes, Width.bits] at H5
    kunfold
    kat hk marshalSSZTo 18
    kat hk marshalSSZTo 19
    kat hk marshalSSZTo 20
    kat hk marshalSSZTo 21
    kat hk marshalSSZTo 22
    kat hk marshalSSZTo 23
    apply store_step_at _ _ (rsp.toBitVec - 144) _ _ _ rslot _ _ (by daddr) (by ecancel) (by exact hrs)
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
    rw [show rsp.toBitVec - 144 + 8 = rsp.toBitVec - 136 by bv_omega] at Hm1
    kat hk marshalSSZTo 24
    apply load_step_at _ _ (rsp.toBitVec - 16) _ _ (Int.toBytes 8 pr.toInt) _ _ (by daddr) (by ecancel)
      (by exact Int.toBytes_length 8 _)
    kunfold
    kat hk marshalSSZTo 25
    kat hk marshalSSZTo 26
    kat hk marshalSSZTo 27
    apply load_step_at _ _ (rsp.toBitVec + 24) _ _ (Int.toBytes 8 rcx.toBitVec.toInt) _ _ (by daddr) (by ecancel)
      (by exact Int.toBytes_length 8 _)
    kunfold
    kat hk marshalSSZTo 28
    have hbig := hone (rcx.toNat + 32) (by omega) hg32
    refine eventually_mono (Encode.grow_tail k hk hf rsp.toBitVec rax.toBitVec pr pc nb ra rbp n rcx1.toNat rdi.toNat hnb hn
      root cb pre tail hroot hcb S Heap _ hgs hmm av1 (Eq (pre.At rbx.toBitVec) ⋆ Eq (spare.At (rbx.toBitVec + rcx.toBitVec)))
      l24 l32 l40 l48 l56 l64 l72 spl1 (Int.toBytes 8 (Host.addrOf (k + 23 + 1)).toBitVec.toInt) stk1 hl24 hl32 hl40
      hl48 hl56 hl64 hl72 hspl1 (Int.toBytes_length 8 _) hstk1 _ rax1.toBitVec hpre (by simp only [UInt64.toNat] at htail ⊢; omega)
      (by dsimp only; simp only [UInt64.toNat] at hnc1 hbig ⊢; omega)
      (Or.inl (by dsimp only; simp only [UInt64.toNat] at hnc1 hbig ⊢; omega)) (by omega) hLm hone
      (by show -128 + (rsp.toBitVec - 8#64) = rsp.toBitVec - 136; bv_omega) rfl rfl rfl rfl
      (by dsimp only; ecancel)) ?_
    rintro st ⟨hpc, hrbx, hrdi, hrsi, hrsp, hrbp, hr14, a24, a32, a40, a48, a56, a64, a72, aspl, ars, ascr, rest, av',
      G', h24, h32, h40, h48, h56, h64, h72, hsp, hrs', hsc', hlen, hav', hm⟩
    refine ⟨hpc, hrbx, by simp only [UInt64.toNat] at hlen ⊢; omega, hrdi, hrsi, UInt64.toBitVec_inj.mp (by rw [hrsp]; simp), hrbp, hr14,
      Int.toBytes 8 rcx.toBitVec.toInt, Int.toBytes 8 pr.toInt, a24, a32, a40, a48, a56, a64, a72, aspl, ars, ascr, rest,
      av', G', Int.toBytes_length 8 _, Int.toBytes_length 8 _, h24, h32, h40, h48, h56, h64, h72, hsp, hrs', hsc', hlen,
      by omega, ?_⟩
    ecancel

end Prysm.DataColumnsByRootIdentifier
