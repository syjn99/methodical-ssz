import Codec.DecoderHeadEpilogue
import Prysm.Deposit_Data.GeneratedDecodeFieldSegmentsPartial
import Prysm.Deposit_Data.DecodeFieldSegmentPadding
import Prysm.Eth1Data.DecodeAccept
import Prysm.Deposit_Data.Statements

/-!
# Real Prysm `(*v1alpha1.Deposit_Data).UnmarshalSSZ`, accept path, Go 1.26.10 machine code (hold-out, type A)

Hand-written AFTER the raw generator outputs were committed (results (S), (C)).
Result (C) was "refused" (`--compose needs every field covered (3 of 4)`), so the accept theorem is this hand
composition. Its statement is the independent hand statement `Prysm.Deposit_Data.Decode.accept_statement` (`H4Stmt.lean`,
committed before the generator ran). Proof text: the composition text of `Gen2DmAccept.lean` (generated for
the in-sample DepositMessage) with the Deposit_Data indices, offsets and one more field.

* head 0–12: `dechead_seg` (size 184);
* PublicKey 13–36: GENERATED `Decode.generated_field_PublicKey_seg` (raw `Gen2DdDecPartial.lean`); pointer tail 37–38, 45–46;
* WithdrawalCredentials 47–72: HAND `bytes32dec_seg_nop` (`DdSegNop.lean`; the generator did not match the
  `nop` at 50); pointer tail 73–74, 81–82;
* Amount 83–85: GENERATED `Decode.generated_field_Amount_seg`;
* Signature 86–110: GENERATED `Decode.generated_field_Signature_seg`; pointer tail 111–112, 119–120;
* epilogue 121–125: `decepi_seg`.
-/

open Machine Runtime TestTarget Prysm.Deposit_Data.Code
variable [Host]

open Codec
namespace Prysm.Deposit_Data

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Accept path of the real `(*v1alpha1.Deposit_Data).UnmarshalSSZ` (Go 1.26.10)**; statement =
the hand statement `Decode.accept_statement`. -/
theorem Decode.accept : Decode.accept_statement := by
  intro k hk hf pk wc amt sig hpk hwc hamt hsig s ra guard
    fp s1 s2 spl l18 rslot lo ast aP1 aL1 aC1 aP2 aL2 aC2 aN aP3 aL3 aC3
    hfp h1 h2 hspl hl18 hrs hast haP1 haL1 haC1 haP2 haL2 haC2 haN haP3 haL3 haC3
    R S hlo Heap avail h_mem hguard hlen hav hms hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  have hrsp_lt : rsp.toNat < 2 ^ 64 := rsp.toNat_lt_size
  -- code facts
  have hH := Codec.infix_sub (q := Codec.decHead "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_0" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_233" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_21f" 184) 0 hk
    (by simp only [unmarshalSSZ, Codec.decHead, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hTa0 := Codec.infix_sub (q := Codec.bytesDecTailA Reg64.rdi "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_ca" 24) 37 hk
    (by simp only [unmarshalSSZ, Codec.bytesDecTailA, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hTb0 := Codec.infix_sub (q := Codec.bytesDecTailB Reg64.rdi "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_ca" 8) 45 hk
    (by simp only [unmarshalSSZ, Codec.bytesDecTailB, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hlT0 := Machine.label_at' hk hf (j := 45)
    (by simp only [unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  have hYdi : Codec.U64InlineReg Reg64.rdi := by decide
  have hWa := Codec.infix_sub (q := Prysm.Deposit_Data.bytesDecHeadNop "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_113" 48 40 48) 47 hk
    (by simp only [unmarshalSSZ, Prysm.Deposit_Data.bytesDecHeadNop, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hWb := Codec.infix_sub (q := Codec.bytesDecMid 32 "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_113" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_154" 48 56 24 32 40 48 48) 61 hk
    (by simp only [unmarshalSSZ, Codec.bytesDecMid, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hlW := Machine.label_at' hk hf (j := 61)
    (by simp only [unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  have hTa1 := Codec.infix_sub (q := Codec.bytesDecTailA Reg64.rdi "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_169" 24) 73 hk
    (by simp only [unmarshalSSZ, Codec.bytesDecTailA, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hTb1 := Codec.infix_sub (q := Codec.bytesDecTailB Reg64.rdi "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_169" 32) 81 hk
    (by simp only [unmarshalSSZ, Codec.bytesDecTailB, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hlT1 := Machine.label_at' hk hf (j := 81)
    (by simp only [unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  have hTa2 := Codec.infix_sub (q := Codec.bytesDecTailA Reg64.rsi "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_211" 24) 111 hk
    (by simp only [unmarshalSSZ, Codec.bytesDecTailA, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hTb2 := Codec.infix_sub (q := Codec.bytesDecTailB Reg64.rsi "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_211" 64) 119 hk
    (by simp only [unmarshalSSZ, Codec.bytesDecTailB, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hlT2 := Machine.label_at' hk hf (j := 119)
    (by simp only [unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  have hYsi : Codec.U64InlineReg Reg64.rsi := by decide
  have hE := Codec.infix_sub (q := Codec.decEpi) 121 hk
    (by simp only [unmarshalSSZ, Codec.decEpi, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  -- head: entry → directive 13
  refine eventually_trans _ _ _ _ (Codec.dechead_seg _ _ _ _ 184 (k + 0) hH _ ra guard fp s1 s2 hfp h1 h2 _
    (by dsimp only; ecancel) hguard (by rw [hlen]; rfl)) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, hrax1, hrbx1, Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 hrax1 hrbx1 Hm1
  subst hpc1
  -- PublicKey: generated segment (48 bytes, zero form), 13 → 37
  refine eventually_trans _ _ _ _ (Prysm.Deposit_Data.Decode.generated_field_PublicKey_seg k hk hf
    (rsp.toBitVec - 40) rax.toBitVec rbx.toBitVec
    (rsp.toBitVec + 8) (rsp.toBitVec + 16) (rsp.toBitVec - 16) (rsp.toBitVec - 48)
    (rsp.toBitVec - 48 - BitVec.ofNat 64 S) (rax.toBitVec + 8) (rax.toBitVec + 16) (rax.toBitVec + 24) S
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by bv_omega) (Prysm.Eth1Data.Decode.stack_low_eq _ _)
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    (by simp only [Int64.toBitVec_ofNat])
    (rsp - 8) r14 pk hpk spl rslot lo l18 aP1 aL1 aC1 hspl hrs hlo hl18 haP1 haL1 haC1
    _ Heap avail (by omega) d1
    (by rw [hrsp1]; first | rfl | (apply UInt64.toBitVec_inj.mp; simp))
    (by rw [hrbp1]) hr141
    (by ecancel) hms hmm) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrsp2, hrbp2, hr142, p1, spl1, lo1, hspl1, hlo1, hrdx2, Hm2⟩
  dsimp only at hpc2 hrsp2 hrbp2 hr142 hrdx2 Hm2
  subst hpc2
  -- pointer tail of PublicKey (rdi), 37–38 and 45–46
  refine eventually_trans _ _ _ _ (Codec.bytesdec_tail_seg Reg64.rdi hYdi _ _ _ (k + 37) (k + 45) hTa0 hTb0 hlT0
    (rsp.toBitVec - 40) rax.toBitVec p1 (rsp.toBitVec - 16) (rax.toBitVec + 8)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat])
    (rsp - 8) r14 (Int.toBytes 8 p1.toInt) (Int.toBytes_length 8 _) _ d2 hrsp2 hrbp2 hr142 hrdx2
    (by ecancel)) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrsp3, hrbp3, hr143, hrdx3, Hm3⟩
  dsimp only at hpc3 hrsp3 hrbp3 hr143 hrdx3 Hm3
  subst hpc3
  -- WithdrawalCredentials: HAND segment with the nop head (32 bytes, add form), 47 → 73
  refine eventually_trans _ _ _ _ (Prysm.Deposit_Data.bytes32dec_seg_nop _ _ _ _ _ _ _ _ _ (k + 47) (k + 61) hWa hWb hlW
    (rsp.toBitVec - 40) rax.toBitVec rbx.toBitVec
    (rsp.toBitVec + 8) (rsp.toBitVec + 16) (rsp.toBitVec - 16) (rsp.toBitVec - 48)
    (rsp.toBitVec - 48 - BitVec.ofNat 64 S) (rax.toBitVec + 32) (rax.toBitVec + 40) (rax.toBitVec + 48) (rbx.toBitVec + 48) S
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by bv_omega) (Prysm.Eth1Data.Decode.stack_low_eq _ _)
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    (rsp - 8) r14 wc hwc spl1 (Int.toBytes 8 (Host.addrOf (k + 26 + 5 + 1)).toBitVec.toInt) lo1 (Int.toBytes 8 p1.toInt) aP2 aL2 aC2 hspl1 (Int.toBytes_length 8 _) hlo1 (Int.toBytes_length 8 _) haP2 haL2 haC2
    _ Heap (avail - 48) (by omega) d3
    hrsp3
    hrbp3 hr143
    (by ecancel) hms hmm) ?_
  rintro ⟨d4, pc4⟩ ⟨hpc4, hrsp4, hrbp4, hr144, p2, spl2, lo2, hspl2, hlo2, hrdx4, Hm4⟩
  dsimp only at hpc4 hrsp4 hrbp4 hr144 hrdx4 Hm4
  subst hpc4
  -- pointer tail of WithdrawalCredentials (rdi), 73–74 and 81–82
  refine eventually_trans _ _ _ _ (Codec.bytesdec_tail_seg Reg64.rdi hYdi _ _ _ (k + 73) (k + 81) hTa1 hTb1 hlT1
    (rsp.toBitVec - 40) rax.toBitVec p2 (rsp.toBitVec - 16) (rax.toBitVec + 32)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat])
    (rsp - 8) r14 (Int.toBytes 8 p2.toInt) (Int.toBytes_length 8 _) _ d4 hrsp4 hrbp4 hr144 hrdx4
    (by ecancel)) ?_
  rintro ⟨d5, pc5⟩ ⟨hpc5, hrsp5, hrbp5, hr145, hrdx5, Hm5⟩
  dsimp only at hpc5 hrsp5 hrbp5 hr145 hrdx5 Hm5
  subst hpc5
  -- Amount: generated segment (inline uint64, rsi), 83–85
  refine eventually_trans _ _ _ _ (Prysm.Deposit_Data.Decode.generated_field_Amount_seg k hk hf
    (rsp.toBitVec - 40) rax.toBitVec rbx.toBitVec (rsp.toBitVec + 16) (rbx.toBitVec + 80) (rax.toBitVec + 56)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat])
    (by simp only [Int64.toBitVec_ofNat])
    (rsp - 8) r14 amt aN hamt haN _ d5 hrsp5 hrbp5 hr145 hrdx5 (by ecancel)) ?_
  rintro ⟨d6, pc6⟩ ⟨hpc6, hrsp6, hrbp6, hr146, hrdx6, Hm6⟩
  dsimp only at hpc6 hrsp6 hrbp6 hr146 hrdx6 Hm6
  subst hpc6
  -- Signature: generated segment (96 bytes, add form), 86 → 111
  refine eventually_trans _ _ _ _ (Prysm.Deposit_Data.Decode.generated_field_Signature_seg k hk hf
    (rsp.toBitVec - 40) rax.toBitVec rbx.toBitVec
    (rsp.toBitVec + 8) (rsp.toBitVec + 16) (rsp.toBitVec - 16) (rsp.toBitVec - 48)
    (rsp.toBitVec - 48 - BitVec.ofNat 64 S) (rax.toBitVec + 64) (rax.toBitVec + 72) (rax.toBitVec + 80) (rbx.toBitVec + 88) S
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by bv_omega) (Prysm.Eth1Data.Decode.stack_low_eq _ _)
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    (rsp - 8) r14 sig hsig spl2 (Int.toBytes 8 (Host.addrOf (k + 61 + 6 + 1)).toBitVec.toInt) lo2 (Int.toBytes 8 p2.toInt) aP3 aL3 aC3 hspl2 (Int.toBytes_length 8 _) hlo2 (Int.toBytes_length 8 _) haP3 haL3 haC3
    _ Heap (avail - 48 - 32) (by omega) d6
    hrsp6
    hrbp6 hr146
    (by ecancel) hms hmm) ?_
  rintro ⟨d7, pc7⟩ ⟨hpc7, hrsp7, hrbp7, hr147, p3, spl3, lo3, hspl3, hlo3, hrdx7, Hm7⟩
  dsimp only at hpc7 hrsp7 hrbp7 hr147 hrdx7 Hm7
  subst hpc7
  -- pointer tail of Signature (rsi), 111–112 and 119–120
  refine eventually_trans _ _ _ _ (Codec.bytesdec_tail_seg Reg64.rsi hYsi _ _ _ (k + 111) (k + 119) hTa2 hTb2 hlT2
    (rsp.toBitVec - 40) rax.toBitVec p3 (rsp.toBitVec - 16) (rax.toBitVec + 64)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat])
    (rsp - 8) r14 (Int.toBytes 8 p3.toInt) (Int.toBytes_length 8 _) _ d7 hrsp7 hrbp7 hr147 hrdx7
    (by ecancel)) ?_
  rintro ⟨d8, pc8⟩ ⟨hpc8, hrsp8, hrbp8, hr148, hrdx8, Hm8⟩
  dsimp only at hpc8 hrsp8 hrbp8 hr148 hrdx8 Hm8
  subst hpc8
  -- epilogue, 121–125
  refine eventually_trans _ _ _ _ (Codec.decepi_seg (k + 121) hE (rsp.toBitVec - 40) (rsp.toBitVec - 8) rsp.toBitVec
    (by bv_omega) (by bv_omega) rbp ra r14 _ d8 hrsp8 hr148 (by ecancel)) ?_
  rintro ⟨d9, pc9⟩ ⟨hpc9, hrax9, hrbx9, hrsp9, hrbp9, hr149, Hm9⟩
  dsimp only at hpc9 hrax9 hrbx9 hrsp9 hrbp9 hr149 Hm9
  apply Eventually.done
  rw [show k + 99 + 6 + 1 = k + 106 from rfl, show avail - 48 - 32 - 96 = avail - 176 by omega] at Hm9
  refine ⟨hpc9, hrax9, hrbx9, ?_, hrbp9, hr149, p1, p2, p3, spl3, lo3, hspl3, hlo3, ?_⟩
  · dsimp only; rw [hrsp9]; apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
  · dsimp only; ecancel

end Prysm.Deposit_Data
