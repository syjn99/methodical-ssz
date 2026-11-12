import E2eScal.BhAcceptG3
import E2eScal.SmSeg
import E2eScal.Gen3SmDecPartial
import E2eScal.Gen4Examples
import E2eScal.H5Stmt

/-!
# `(*v1alpha1.SyncCommitteeMessage).UnmarshalSSZ`, accept path, re-derived with the window and step mechanisms

`sm_e2e_accept_g4 : H5.sm_accept_stmt` (the pre-committed hand statement, `H5Stmt.lean`, unchanged). The text of
`SmAccept.lean` with the two fields that the hold-out run missed taken from the window and step mechanisms:

* BlockRoot 47–81: `Gen4Ex.sm_g4_BlockRoot_field` (byte segment over windows with the receiver register
  `rY = rax`, then the tail as four steps) instead of the hand lemma `bytes32dec_seg_rax` and hand steps;
* ValidatorIndex 82–117: `Gen4Ex.sm_g4_ValidatorIndex_field` (six step theorems and the call-block window)
  instead of the hand lemma `sm_vi_arg` and a hand-applied `calldec_seg`;
* Signature 120–145: `Gen4Ex.sm_g4_Signature_seg` (window; the padding `nop` before `callq runtime.makeslice` is inside it) instead of the `p2dec --gen3`
  `pad` instance.
Unchanged: `sm_head0` and `sm_spill2` (hand, `SmSeg.lean`), the generated Slot theorems (`Gen3SmDecPartial.lean`),
the hand steps 146–160. `SmSeg.lean` is imported for `sm_head0` / `sm_spill2` only; `G4DepCheck.lean` checks by
program that this proof does not reach `bytes32dec_seg_rax`, `sm_vi_arg` or `calldec_nop_seg`.
In-sample (the type is development data since its hold-out evaluation); no transfer claim.
-/

open Fk E2e E2eAd E2eAd.Code E2eScal.H5Code E2eScal.BhCode E2eScal E2eScal.Bh
variable [Host]

namespace E2eScal.H5

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- **Accept path of the real `(*v1alpha1.SyncCommitteeMessage).UnmarshalSSZ` (Go 1.26.10), re-derived with the
window and step mechanisms**; statement = the hand statement `sm_accept_stmt` (unchanged). -/
theorem sm_e2e_accept_g4 : sm_accept_stmt := by
  intro k hk hf kS hkS hfS kV hkV hfV in0 rt in1 sig hin0 hrt hin1 hsig s ra guard
    fp s1 s2 s4 sp0 sp1 sp2 s28 s30 l38 rslot lo ast a8 aP1 aL1 aC1 a40 aP2 aL2 aC2
    hfp h1 h2 h4 hsp0 hsp1 hsp2 hs28 hs30 hl38 hrs hast ha8 haP1 haL1 haC1 ha40 haP2 haL2 haC2
    R S hS hlo Heap avail h_mem hguard hlen hav hms hmm
  have hsl : U64CalleeAcc slLabel := sl_uacc_holds kS hkS hfS
  have hvi : U64CalleeAcc viLabel := vi_uacc_holds kV hkV hfV
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  have hrsp_lt : rsp.toNat < 2 ^ 64 := rsp.toNat_lt_size
  have hg : guard.toNat < (rsp.toBitVec - 112).toNat := bhg_guard _ _ hguard
  have hlS : (lo.take S).length = S := by simp [hlo]
  have hl8 : (lo.drop S).length = 8 := by simp [hlo]
  have hlos : Eq (lo.At (rsp.toBitVec - 120 - BitVec.ofNat 64 S)) =
      Eq ((lo.take S).At (rsp.toBitVec - 120 - BitVec.ofNat 64 S)) ⋆ Eq ((lo.drop S).At (rsp.toBitVec - 120)) := by
    conv => lhs; rw [← List.take_append_drop S lo]
    exact bh_lo8 _ S hS _ _ hlS hl8
  rw [hlos] at h_mem
  -- head: entry → directive 15
  refine eventually_trans _ _ _ _ (sm_head0 k hk _ ra guard fp s1 s2 s4 ast hfp h1 h2 h4 hast _
    (by dsimp only; ecancel) (Nat.lt_of_le_of_lt (Nat.le_add_right _ 112) hguard) hlen) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, hrax1, hrbx1, Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 hrax1 hrbx1 Hm1
  subst hpc1
  -- Slot: set-up 15–16 (generated)
  refine eventually_trans _ _ _ _ (Gen.sm_g3dec_Slot_arg k hk hf rax.toBitVec (rax.toBitVec + 8)
    (by simp only [Int64.toBitVec_ofNat]) d1 (by rw [hrax1])) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrsp2, hrbp2, hr142, hrbx2, hrax2, hrcx2, hmem2⟩
  dsimp only at hpc2 hrsp2 hrbp2 hr142 hrbx2 hrax2 hrcx2 hmem2
  subst hpc2
  -- Slot: call block 17–19, label 46 (generated; hC discharged by sl_uacc_holds)
  refine eventually_trans _ _ _ _ (Gen.sm_g3dec_Slot_call k hk hf hsl
    (rsp.toBitVec - 104) (rax.toBitVec + 8) rbx.toBitVec (rsp.toBitVec - 112) (rsp.toBitVec - 120) (rsp.toBitVec - 96)
    (by bv_omega) (by bv_omega) (by bv_omega)
    { toBitVec := rsp.toBitVec - 8#64 } r14 guard in0 rslot (lo.drop S) sp1 a8 hin0 hrs hl8 hsp1 ha8 hg _ d2
    (hrsp2.trans hrsp1) (hrbp2.trans hrbp1) (hr142.trans hr141) hrax2 (by rw [hrbx2, hrbx1]) hrcx2
    (by rw [hmem2]; ecancel)) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrax3, hrbx3, hrsp3, hrbp3, hr143, Hm3⟩
  dsimp only at hpc3 hrax3 hrbx3 hrsp3 hrbp3 hr143 Hm3
  subst hpc3
  -- BlockRoot: 47 → 82 (worked byte field: window segment with rY = rax, then the tail as steps)
  refine eventually_trans _ _ _ _ (E2eScal.Gen4Ex.sm_g4_BlockRoot_field k hk hf
    (rsp.toBitVec - 104) rax.toBitVec rbx.toBitVec
    (rsp.toBitVec + 8) (rsp.toBitVec + 16) (rsp.toBitVec - 48) (rsp.toBitVec - 112)
    (rsp.toBitVec - 120 - BitVec.ofNat 64 S) (rax.toBitVec + 16) (rax.toBitVec + 24) (rax.toBitVec + 32)
    (rbx.toBitVec + 8) (S + 8)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by bv_omega) (bh_lo _ _)
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    { toBitVec := rsp.toBitVec - 8#64 } r14 rt hrt
    (sp0 ++ (Int.toBytes 8 rbx.toBitVec.toInt ++ sp2)) (Int.toBytes 8 (Host.addrOf (k + 17 + 1)).toBitVec.toInt)
    (lo.take S ++ Int.toBytes 8 (rsp.toBitVec - 8#64).toInt) l38 aP1 aL1 aC1
    (by simp only [List.length_append, hsp0, hsp2, Int.toBytes_length]) (Int.toBytes_length 8 _)
    (by simp only [List.length_append, hlS, Int.toBytes_length]) hl38 haP1 haL1 haC1
    _ Heap avail (by omega) d3 hrsp3 hrbp3 hr143
    (by rw [bh_j3 _ _ _ _ hsp0 (Int.toBytes_length 8 _) hsp2, bh_lo8 _ S hS _ _ hlS (Int.toBytes_length 8 _)]
        ecancel) hms hmm) ?_
  rintro ⟨d4, pc4⟩ ⟨hpc4, hrsp4, hrbp4, hr144, p1, spl1, lo1, hspl1, hlo1, hrax4, Hm4⟩
  dsimp only at hpc4 hrsp4 hrbp4 hr144 hrax4 Hm4
  subst hpc4
  -- split the spill area and the low stack for the ValidatorIndex callee
  have hq0 : (spl1.take 8).length = 8 := by simp [hspl1]
  have hq1 : ((spl1.drop 8).take 8).length = 8 := by simp [hspl1]
  have hq2 : ((spl1.drop 8).drop 8).length = 8 := by simp [hspl1]
  have hlS1 : (lo1.take S).length = S := by simp [hlo1]
  have hl81 : (lo1.drop S).length = 8 := by simp [hlo1]
  have hsp3 : spl1 = spl1.take 8 ++ ((spl1.drop 8).take 8 ++ (spl1.drop 8).drop 8) := by
    rw [List.take_append_drop, List.take_append_drop]
  have hlo3 : lo1 = lo1.take S ++ lo1.drop S := (List.take_append_drop S lo1).symm
  rw [hsp3, hlo3, bh_j3 _ _ _ _ hq0 hq1 hq2, bh_lo8 _ S hS _ _ hlS1 hl81] at Hm4
  -- ValidatorIndex: 82 → 118 (worked call field: six steps and the call block; hC = vi_uacc_holds)
  refine eventually_trans _ _ _ _ (E2eScal.Gen4Ex.sm_g4_ValidatorIndex_field k hk hf hvi
    (rsp.toBitVec - 104) rax.toBitVec rbx.toBitVec (rsp.toBitVec - 112) (rsp.toBitVec - 120) (rsp.toBitVec - 96)
    (rsp.toBitVec + 16) (rsp.toBitVec + 32) (by bv_omega) (by bv_omega) (by bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    { toBitVec := rsp.toBitVec - 8#64 } r14 guard in1
    (Int.toBytes 8 (Host.addrOf (k + 66 + 1)).toBitVec.toInt) (lo1.drop S) ((spl1.drop 8).take 8) a40
    (Int.toBytes 8 rdi.toBitVec.toInt)
    hin1 (Int.toBytes_length 8 _) hl81 hq1 ha40 (Int.toBytes_length 8 _) hg _ d4 hrsp4 hrbp4 hr144
    (by exact hrax4) (by ecancel)) ?_
  rintro ⟨d6, pc6⟩ ⟨hpc6, hrax6, hrbx6, hrsp6, hrbp6, hr146, Hm6⟩
  dsimp only at hpc6 hrax6 hrbx6 hrsp6 hrbp6 hr146 Hm6
  subst hpc6
  -- nil-error spills 118–119
  refine eventually_trans _ _ _ _ (sm_spill2 k hk (rsp.toBitVec - 104) (rsp.toBitVec - 64) (rsp.toBitVec - 56)
    (by bv_omega) (by bv_omega) s28 s30 hs28 hs30 _ d6 hrsp6 (by ecancel)) ?_
  rintro ⟨d7, pc7⟩ ⟨hpc7, hrsp7, hrbp7, hr147, Hm7⟩
  dsimp only at hpc7 hrsp7 hrbp7 hr147 Hm7
  subst hpc7
  rw [hrax6, hrbx6] at Hm7
  -- Signature: 120 → 146 (window segment: the nop before makeslice is inside the first window)
  refine eventually_trans _ _ _ _ (E2eScal.Gen4Ex.sm_g4_Signature_seg k hk hf (rsp.toBitVec - 104) rax.toBitVec rbx.toBitVec
    (rsp.toBitVec + 8) (rsp.toBitVec + 16) (rsp.toBitVec - 48) (rsp.toBitVec - 112)
    (rsp.toBitVec - 120 - BitVec.ofNat 64 S) (rax.toBitVec + 48) (rax.toBitVec + 56) (rax.toBitVec + 64)
    (rbx.toBitVec + 48) (S + 8)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by bv_omega) (bh_lo _ _)
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    _ _ sig hsig
    (spl1.take 8 ++ (Int.toBytes 8 (rbx.toBitVec + 40).toInt ++ (spl1.drop 8).drop 8))
    (Int.toBytes 8 (Host.addrOf (k + 88 + 1)).toBitVec.toInt)
    (lo1.take S ++ Int.toBytes 8 (rsp.toBitVec - 8#64).toInt) (Int.toBytes 8 p1.toInt) aP2 aL2 aC2
    (by simp only [List.length_append, hq0, hq2, Int.toBytes_length]) (Int.toBytes_length 8 _)
    (by simp only [List.length_append, hlS1, Int.toBytes_length]) (Int.toBytes_length 8 _) haP2 haL2 haC2
    _ Heap (avail - 32) (by omega) d7 (hrsp7.trans hrsp6) (hrbp7.trans hrbp6) (hr147.trans hr146)
    (by rw [bh_j3 _ _ _ _ hq0 (Int.toBytes_length 8 _) hq2, bh_lo8 _ S hS _ _ hlS1 (Int.toBytes_length 8 _)]
        ecancel) hms hmm) ?_
  rintro ⟨d8, pc8⟩ ⟨hpc8, hrsp8, hrbp8, hr148, p2, spl2, lo2, hspl2, hlo2, hrdx8, Hm8⟩
  dsimp only at hpc8 hrsp8 hrbp8 hr148 hrdx8 Hm8
  subst hpc8
  obtain ⟨⟨rax8, rbx8, rcx8, rdx8, rsi8, rdi8, rsp8, rbp8, r88, r98, r108, r118, r128, r138, r148, r158⟩,
    zmms8, flags8, mem8⟩ := d8
  simp only at hrsp8 hrbp8 hr148 hrdx8 Hm8
  replace hrdx8 : rdx8.toBitVec = rax.toBitVec := hrdx8
  subst hrsp8 hrbp8 hr148
  -- instance directives 146–147, L_289 (154), 155, epilogue 156–160
  kat hk SmUnmarshal 146
  apply load_step_at _ _ (rsp.toBitVec - 48) _ _ (Int.toBytes 8 p2.toInt) _ _ (by bhaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk SmUnmarshal 147
  klabel hk hf SmUnmarshal 154
  kat hk SmUnmarshal 154
  kat hk SmUnmarshal 155
  apply store_step_at _ _ (rax.toBitVec + 48) _ _ _ (Int.toBytes 8 p2.toInt) _ _ (by rw [hrdx8]; try bhaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m5' H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  kat hk SmUnmarshal 156
  apply load_step_at _ _ (rsp.toBitVec - 64) _ _ (Int.toBytes 8 (UInt64.toBitVec 0).toInt) _ _ (by bhaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk SmUnmarshal 157
  apply load_step_at _ _ (rsp.toBitVec - 56) _ _ (Int.toBytes 8 (UInt64.toBitVec 0).toInt) _ _ (by bhaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk SmUnmarshal 158
  kat hk SmUnmarshal 159
  apply load_step_at _ _ (rsp.toBitVec - 8) _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by bhaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk SmUnmarshal 160
  apply load_step_at _ _ rsp.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by bhaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  rw [show UInt64.toBitVec 0 = 0#64 from rfl] at H5
  rw [show k + 140 + 1 = k + 141 from rfl] at H5
  rw [show avail - 32 - 96 = avail - 128 by omega] at H5
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, p1, p2, spl2, lo2, hspl2, hlo2, ?_⟩
  rotate_right
  · ecancel
  all_goals first
    | exact trivial
    | with_reducible rfl
    | (apply UInt64.toBitVec_inj.mp
       simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, Width.bits]
       done)
    | (apply UInt64.toBitVec_inj.mp; bhaddr)

end E2eScal.H5
