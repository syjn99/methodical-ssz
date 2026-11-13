import Prysm.BeaconBlockHeader.DecodeAcceptFromGeneratedCallSegments
import Prysm.SyncCommitteeMessage.DecodeSegments
import Prysm.SyncCommitteeMessage.GeneratedDecodeCallSegmentsPartial
import Prysm.SyncCommitteeMessage.Statements

/-!
# Real Prysm `(*v1alpha1.SyncCommitteeMessage).UnmarshalSSZ`, accept path, Go 1.26.10 (hold-out, class C)

Hand composition, written AFTER the raw generator output was committed. The
statement is the independent hand statement `Prysm.SyncCommitteeMessage.Decode.accept_statement` (`Prysm/SyncCommitteeMessage/Statements.lean`, unchanged). Chain of
`eventually_trans` over

* `Decode.head0` (hand, 0–14),
* `Decode.generated_call_Slot_arg` (15–16) and `Decode.generated_call_Slot_call` (17–19, label 46): GENERATED
  (`Prysm/SyncCommitteeMessage/GeneratedDecodeCallSegmentsPartial.lean`, raw); `hC` discharged by the proved `Prysm.Slot.Decode.accept_function_spec_holds`,
* `bytes32dec_seg_rax` (hand lemma, BlockRoot 47–71) and hand steps 72–73, label 80, 81,
* `Decode.validator_index_arg` (hand lemma, 82–87) and `Codec.calldec_seg` (existing lemma applied by hand, 88–90,
  label 117; callee ValidatorIndex, `Prysm.ValidatorIndex.Decode.accept_function_spec_holds`),
* `Decode.spill2` (hand, 118–119),
* `Decode.generated_call_Signature_seg` (120–145): GENERATED,
* hand steps 146–147, label 154, 155 and the epilogue 156–160 (the text of the BeaconBlockHeader tail).

Stack (rsp = entry rsp): frame `sub $0x60` as BeaconBlockHeader; the helper lemmas `Prysm.BeaconBlockHeader.Decode.stack_low_eq`, `Prysm.BeaconBlockHeader.Decode.lo8`,
`Prysm.BeaconBlockHeader.Decode.j3`, `Prysm.BeaconBlockHeader.Decode.accept_guard` and the tactic `bhaddr` are reused. No contract, no new hypothesis form.
-/

open Machine Runtime Prysm.AttestationData.Code Prysm.SyncCommitteeMessage.Code Codec
variable [Host]

namespace Prysm.SyncCommitteeMessage

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- **Accept path of the real `(*v1alpha1.SyncCommitteeMessage).UnmarshalSSZ` (Go 1.26.10)**; statement = the
hand statement `Decode.accept_statement` (unchanged), from the generated Slot / Signature theorems and hand steps. -/
theorem Decode.accept : Decode.accept_statement := by
  intro k hk hf kS hkS hfS kV hkV hfV in0 rt in1 sig hin0 hrt hin1 hsig s ra guard
    fp s1 s2 s4 sp0 sp1 sp2 s28 s30 l38 rslot lo ast a8 aP1 aL1 aC1 a40 aP2 aL2 aC2
    hfp h1 h2 h4 hsp0 hsp1 hsp2 hs28 hs30 hl38 hrs hast ha8 haP1 haL1 haC1 ha40 haP2 haL2 haC2
    R S hS hlo Heap avail h_mem hguard hlen hav hms hmm
  have hsl : U64CalleeAcc Prysm.Slot.Code.unmarshalSSZLabel := Prysm.Slot.Decode.accept_function_spec_holds kS hkS hfS
  have hvi : U64CalleeAcc Prysm.ValidatorIndex.Code.unmarshalLabel := Prysm.ValidatorIndex.Decode.accept_function_spec_holds kV hkV hfV
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  have hrsp_lt : rsp.toNat < 2 ^ 64 := rsp.toNat_lt_size
  have hg : guard.toNat < (rsp.toBitVec - 112).toNat := Prysm.BeaconBlockHeader.Decode.accept_guard _ _ hguard
  have hlS : (lo.take S).length = S := by simp [hlo]
  have hl8 : (lo.drop S).length = 8 := by simp [hlo]
  have hlos : Eq (lo.At (rsp.toBitVec - 120 - BitVec.ofNat 64 S)) =
      Eq ((lo.take S).At (rsp.toBitVec - 120 - BitVec.ofNat 64 S)) ⋆ Eq ((lo.drop S).At (rsp.toBitVec - 120)) := by
    conv => lhs; rw [← List.take_append_drop S lo]
    exact Prysm.BeaconBlockHeader.Decode.lo8 _ S hS _ _ hlS hl8
  rw [hlos] at h_mem
  -- code facts of the hand-applied blocks
  have hRA := Codec.infix_sub (q := Codec.bytesDecHead 32 "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_fd" 112 24 32) 47 hk
    (by simp only [Code.unmarshalSSZ, Codec.bytesDecHead, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hRB := Codec.infix_sub (q := bytesDecMidA 32 "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_fd" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_13e" 112 120 56 16 24 32 8) 60 hk
    (by simp only [Code.unmarshalSSZ, bytesDecMidA, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hRl := Machine.label_at' hk hf (j := 60)
    (by simp only [Code.unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [Code.unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  have hC2 := Codec.infix_sub (q := Codec.callDec "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_1e7") 88 hk
    (by simp only [Code.unmarshalSSZ, Codec.callDec, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hL2 := Codec.infix_sub (q := Codec.callDecL "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_1e7") 117 hk
    (by simp only [Code.unmarshalSSZ, Codec.callDecL, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hl2 := Machine.label_at' hk hf (j := 117)
    (by simp only [Code.unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [Code.unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  -- head: entry → directive 15
  refine eventually_trans _ _ _ _ (Decode.head0 k hk _ ra guard fp s1 s2 s4 ast hfp h1 h2 h4 hast _
    (by dsimp only; ecancel) (Nat.lt_of_le_of_lt (Nat.le_add_right _ 112) hguard) hlen) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, hrax1, hrbx1, Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 hrax1 hrbx1 Hm1
  subst hpc1
  -- Slot: set-up 15–16 (generated)
  refine eventually_trans _ _ _ _ (Decode.generated_call_Slot_arg k hk hf rax.toBitVec (rax.toBitVec + 8)
    (by simp only [Int64.toBitVec_ofNat]) d1 (by rw [hrax1])) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrsp2, hrbp2, hr142, hrbx2, hrax2, hrcx2, hmem2⟩
  dsimp only at hpc2 hrsp2 hrbp2 hr142 hrbx2 hrax2 hrcx2 hmem2
  subst hpc2
  -- Slot: call block 17–19, label 46 (generated; hC discharged by Prysm.Slot.Decode.accept_function_spec_holds)
  refine eventually_trans _ _ _ _ (Decode.generated_call_Slot_call k hk hf hsl
    (rsp.toBitVec - 104) (rax.toBitVec + 8) rbx.toBitVec (rsp.toBitVec - 112) (rsp.toBitVec - 120) (rsp.toBitVec - 96)
    (by bv_omega) (by bv_omega) (by bv_omega)
    { toBitVec := rsp.toBitVec - 8#64 } r14 guard in0 rslot (lo.drop S) sp1 a8 hin0 hrs hl8 hsp1 ha8 hg _ d2
    (hrsp2.trans hrsp1) (hrbp2.trans hrbp1) (hr142.trans hr141) hrax2 (by rw [hrbx2, hrbx1]) hrcx2
    (by rw [hmem2]; ecancel)) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrax3, hrbx3, hrsp3, hrbp3, hr143, Hm3⟩
  dsimp only at hpc3 hrax3 hrbx3 hrsp3 hrbp3 hr143 Hm3
  subst hpc3
  -- BlockRoot: 47 → 72 (hand lemma, receiver in rax)
  refine eventually_trans _ _ _ _ (bytes32dec_seg_rax _ _ 112 120 56 16 24 32 8 (k + 47) (k + 60) hRA hRB hRl
    (rsp.toBitVec - 104) rax.toBitVec rbx.toBitVec
    (rsp.toBitVec + 8) (rsp.toBitVec + 16) (rsp.toBitVec - 48) (rsp.toBitVec - 112)
    (rsp.toBitVec - 120 - BitVec.ofNat 64 S) (rax.toBitVec + 16) (rax.toBitVec + 24) (rax.toBitVec + 32)
    (rbx.toBitVec + 8) (S + 8)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by bv_omega) (Prysm.BeaconBlockHeader.Decode.stack_low_eq _ _)
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    { toBitVec := rsp.toBitVec - 8#64 } r14 rt hrt
    (sp0 ++ (Int.toBytes 8 rbx.toBitVec.toInt ++ sp2)) (Int.toBytes 8 (Host.addrOf (k + 17 + 1)).toBitVec.toInt)
    (lo.take S ++ Int.toBytes 8 (rsp.toBitVec - 8#64).toInt) l38 aP1 aL1 aC1
    (by simp only [List.length_append, hsp0, hsp2, Int.toBytes_length]) (Int.toBytes_length 8 _)
    (by simp only [List.length_append, hlS, Int.toBytes_length]) hl38 haP1 haL1 haC1
    _ Heap avail (by omega) d3 hrsp3 hrbp3 hr143
    (by rw [Prysm.BeaconBlockHeader.Decode.j3 _ _ _ _ hsp0 (Int.toBytes_length 8 _) hsp2, Prysm.BeaconBlockHeader.Decode.lo8 _ S hS _ _ hlS (Int.toBytes_length 8 _)]
        ecancel) hms hmm) ?_
  rintro ⟨d4, pc4⟩ ⟨hpc4, hrsp4, hrbp4, hr144, p1, spl1, lo1, hspl1, hlo1, hrax4, Hm4⟩
  dsimp only at hpc4 hrsp4 hrbp4 hr144 hrax4 Hm4
  subst hpc4
  obtain ⟨⟨rax4, rbx4, rcx4, rdx4, rsi4, rdi4, rsp4, rbp4, r84, r94, r104, r114, r124, r134, r144, r154⟩,
    zmms4, flags4, mem4⟩ := d4
  simp only at hrsp4 hrbp4 hr144 hrax4 Hm4
  subst hrsp4 hrbp4 hr144
  -- instance directives 72–73, L_153 (80), 81
  kat hk Code.unmarshalSSZ 72
  apply load_step_at _ _ (rsp.toBitVec - 48) _ _ (Int.toBytes 8 p1.toInt) _ _ (by bhaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk Code.unmarshalSSZ 73
  klabel hk hf Code.unmarshalSSZ 80
  kat hk Code.unmarshalSSZ 80
  kat hk Code.unmarshalSSZ 81
  apply store_step_at _ _ (rax.toBitVec + 16) _ _ _ (Int.toBytes 8 p1.toInt) _ _ (by rw [hrax4]; try bhaddr)
    (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m3' H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  -- split the spill area and the low stack for the ValidatorIndex callee
  have hq0 : (spl1.take 8).length = 8 := by simp [hspl1]
  have hq1 : ((spl1.drop 8).take 8).length = 8 := by simp [hspl1]
  have hq2 : ((spl1.drop 8).drop 8).length = 8 := by simp [hspl1]
  have hlS1 : (lo1.take S).length = S := by simp [hlo1]
  have hl81 : (lo1.drop S).length = 8 := by simp [hlo1]
  have hsp3 : spl1 = spl1.take 8 ++ ((spl1.drop 8).take 8 ++ (spl1.drop 8).drop 8) := by
    rw [List.take_append_drop, List.take_append_drop]
  have hlo3 : lo1 = lo1.take S ++ lo1.drop S := (List.take_append_drop S lo1).symm
  rw [hsp3, hlo3, Prysm.BeaconBlockHeader.Decode.j3 _ _ _ _ hq0 hq1 hq2, Prysm.BeaconBlockHeader.Decode.lo8 _ S hS _ _ hlS1 hl81] at H3
  -- ValidatorIndex: set-up 82–87 (hand lemma)
  refine eventually_trans _ _ _ _ (Decode.validator_index_arg k hk (rsp.toBitVec - 104) rax.toBitVec rbx.toBitVec
    (rsp.toBitVec + 16) (rsp.toBitVec + 32) (rbx.toBitVec + 40) (rax.toBitVec + 40)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    (Int.toBytes 8 rdi.toBitVec.toInt) (Int.toBytes_length 8 _) _ _ rfl hrax4 (by ecancel)) ?_
  rintro ⟨d5, pc5⟩ ⟨hpc5, hrsp5, hrbp5, hr145, hrbx5, hrax5, hrcx5, hmem5⟩
  dsimp only at hpc5 hrsp5 hrbp5 hr145 hrbx5 hrax5 hrcx5 hmem5
  subst hpc5
  -- ValidatorIndex: call block 88–90, label 117 (existing lemma; hC = Prysm.ValidatorIndex.Decode.accept_function_spec_holds)
  refine eventually_trans _ _ _ _ (Codec.calldec_seg _ _ (k + 88) (k + 117) hC2 hL2 hl2 hvi
    (rsp.toBitVec - 104) (rax.toBitVec + 40) (rbx.toBitVec + 40) (rsp.toBitVec - 112) (rsp.toBitVec - 120)
    (rsp.toBitVec - 96) (by bv_omega) (by bv_omega) (by bv_omega)
    { toBitVec := rsp.toBitVec - 8#64 } _ guard in1
    (Int.toBytes 8 (Host.addrOf (k + 60 + 6 + 1)).toBitVec.toInt) (lo1.drop S) ((spl1.drop 8).take 8) a40
    hin1 (Int.toBytes_length 8 _) hl81 hq1 ha40 hg _ d5 hrsp5 hrbp5 hr145 hrax5 hrbx5 hrcx5
    (by rw [hmem5]; ecancel)) ?_
  rintro ⟨d6, pc6⟩ ⟨hpc6, hrax6, hrbx6, hrsp6, hrbp6, hr146, Hm6⟩
  dsimp only at hpc6 hrax6 hrbx6 hrsp6 hrbp6 hr146 Hm6
  subst hpc6
  -- nil-error spills 118–119
  refine eventually_trans _ _ _ _ (Decode.spill2 k hk (rsp.toBitVec - 104) (rsp.toBitVec - 64) (rsp.toBitVec - 56)
    (by bv_omega) (by bv_omega) s28 s30 hs28 hs30 _ d6 hrsp6 (by ecancel)) ?_
  rintro ⟨d7, pc7⟩ ⟨hpc7, hrsp7, hrbp7, hr147, Hm7⟩
  dsimp only at hpc7 hrsp7 hrbp7 hr147 Hm7
  subst hpc7
  rw [hrax6, hrbx6] at Hm7
  -- Signature: 120 → 146 (generated)
  refine eventually_trans _ _ _ _ (Decode.generated_call_Signature_seg k hk hf (rsp.toBitVec - 104) rax.toBitVec rbx.toBitVec
    (rsp.toBitVec + 8) (rsp.toBitVec + 16) (rsp.toBitVec - 48) (rsp.toBitVec - 112)
    (rsp.toBitVec - 120 - BitVec.ofNat 64 S) (rax.toBitVec + 48) (rax.toBitVec + 56) (rax.toBitVec + 64)
    (rbx.toBitVec + 48) (S + 8)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by bv_omega) (Prysm.BeaconBlockHeader.Decode.stack_low_eq _ _)
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    _ _ sig hsig
    (spl1.take 8 ++ (Int.toBytes 8 (rbx.toBitVec + 40).toInt ++ (spl1.drop 8).drop 8))
    (Int.toBytes 8 (Host.addrOf (k + 88 + 1)).toBitVec.toInt)
    (lo1.take S ++ Int.toBytes 8 (rsp.toBitVec - 8#64).toInt) (Int.toBytes 8 p1.toInt) aP2 aL2 aC2
    (by simp only [List.length_append, hq0, hq2, Int.toBytes_length]) (Int.toBytes_length 8 _)
    (by simp only [List.length_append, hlS1, Int.toBytes_length]) (Int.toBytes_length 8 _) haP2 haL2 haC2
    _ Heap (avail - 32) (by omega) d7 (hrsp7.trans hrsp6) (hrbp7.trans hrbp6) (hr147.trans hr146)
    (by rw [Prysm.BeaconBlockHeader.Decode.j3 _ _ _ _ hq0 (Int.toBytes_length 8 _) hq2, Prysm.BeaconBlockHeader.Decode.lo8 _ S hS _ _ hlS1 (Int.toBytes_length 8 _)]
        ecancel) hms hmm) ?_
  rintro ⟨d8, pc8⟩ ⟨hpc8, hrsp8, hrbp8, hr148, p2, spl2, lo2, hspl2, hlo2, hrdx8, Hm8⟩
  dsimp only at hpc8 hrsp8 hrbp8 hr148 hrdx8 Hm8
  subst hpc8
  obtain ⟨⟨rax8, rbx8, rcx8, rdx8, rsi8, rdi8, rsp8, rbp8, r88, r98, r108, r118, r128, r138, r148, r158⟩,
    zmms8, flags8, mem8⟩ := d8
  simp only at hrsp8 hrbp8 hr148 hrdx8 Hm8
  subst hrsp8 hrbp8 hr148
  -- instance directives 146–147, L_289 (154), 155, epilogue 156–160
  kat hk Code.unmarshalSSZ 146
  apply load_step_at _ _ (rsp.toBitVec - 48) _ _ (Int.toBytes 8 p2.toInt) _ _ (by bhaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk Code.unmarshalSSZ 147
  klabel hk hf Code.unmarshalSSZ 154
  kat hk Code.unmarshalSSZ 154
  kat hk Code.unmarshalSSZ 155
  apply store_step_at _ _ (rax.toBitVec + 48) _ _ _ (Int.toBytes 8 p2.toInt) _ _ (by rw [hrdx8]; try bhaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m5' H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  kat hk Code.unmarshalSSZ 156
  apply load_step_at _ _ (rsp.toBitVec - 64) _ _ (Int.toBytes 8 (UInt64.toBitVec 0).toInt) _ _ (by bhaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk Code.unmarshalSSZ 157
  apply load_step_at _ _ (rsp.toBitVec - 56) _ _ (Int.toBytes 8 (UInt64.toBitVec 0).toInt) _ _ (by bhaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk Code.unmarshalSSZ 158
  kat hk Code.unmarshalSSZ 159
  apply load_step_at _ _ (rsp.toBitVec - 8) _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by bhaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk Code.unmarshalSSZ 160
  apply load_step_at _ _ rsp.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by bhaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  rw [show UInt64.toBitVec 0 = 0#64 from rfl] at H5
  rw [show k + 134 + 6 + 1 = k + 141 from rfl] at H5
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

end Prysm.SyncCommitteeMessage
