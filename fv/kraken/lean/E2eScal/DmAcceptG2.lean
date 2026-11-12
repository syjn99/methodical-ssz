import Codec.DecoderHeadEpilogue
import E2eScal.Gen2DmDec
import E2eScal.DmAccept

/-!
# Reuse demonstration: the DepositMessage accept path from the GENERATED segment theorems

`dm_e2e_accept_main_g2` has the statement text of `E2eScal.Dm.dm_e2e_accept_main`; `dm_e2e_accept_main_g2_type`
proves that the two declared types are equal (`with_reducible rfl`). The proof is a chain of
`eventually_trans` over `dechead_seg`, the generated segments of `Gen2DmDec.lean` (raw `scalgen.py p2dec --gen2`
output: PublicKey 48 bytes offset-0 form, WithdrawalCredentials 32 bytes add form, Amount inline uint64),
two `bytesdec_tail_seg` steps (rdi, then rsi) and `decepi_seg`. No directive is stepped by hand and neither
`DmSeg0.lean` nor `dm_e2e_head` is used. By hand here: the statement copy, the code facts of the head /
tail / epilogue templates and the frame instance of each step.
-/

open Machine Runtime TestTarget E2eScal Codec E2eScal.H3Code E2eScal.E1
variable [Host]

namespace E2eScal.G2

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- The accept path of `(*v1alpha1.DepositMessage).UnmarshalSSZ`, composed from generated segment theorems. -/
theorem dm_e2e_accept_main_g2 (k : Nat) (hk : DmUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh DmUnmarshal k)
    (pk wc amt : List UInt8) (hpk : pk.length = 48) (hwc : wc.length = 32) (hamt : amt.length = 8)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 spl l18 rslot lo aP1 aL1 aC1 aP2 aL2 aC2 aN : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8)
    (hspl : spl.length = 24) (hl18 : l18.length = 8) (hrs : rslot.length = 8)
    (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8)
    (haP2 : aP2.length = 8) (haL2 : aL2.length = 8) (haC2 : aC2.length = 8) (haN : aN.length = 8)
    (R : DataMem → Prop) (S : Nat) (hlo : lo.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (l18.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 48 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (pk.At s.regs.rbx.toBitVec) ⋆ Eq (wc.At (s.regs.rbx.toBitVec + 48))
      ⋆ Eq (amt.At (s.regs.rbx.toBitVec + 80))
      ⋆ Eq (aP1.At s.regs.rax.toBitVec) ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 16)) ⋆ Eq (aP2.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (aL2.At (s.regs.rax.toBitVec + 32)) ⋆ Eq (aC2.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (aN.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx = 88) (hav : 80 ≤ avail)
    (hms : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 S) (hmm : MemmoveC S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (p1 p2 : BitVec 64) (spl' lo' : List UInt8), spl'.length = 24 ∧ lo'.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 68)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 48 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 80)
          ⋆ Eq (pk.At s.regs.rbx.toBitVec) ⋆ Eq (wc.At (s.regs.rbx.toBitVec + 48))
          ⋆ Eq (amt.At (s.regs.rbx.toBitVec + 80))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 8)) ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (amt.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (pk.At p1) ⋆ Eq (wc.At p2)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  have hrsp_lt : rsp.toNat < 2 ^ 64 := rsp.toNat_lt_size
  -- code facts of the composition templates
  have hH := Codec.infix_sub (q := Codec.decHead "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ_0" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ_191" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ_17d" 88) 0 hk
    (by simp only [DmUnmarshal, Codec.decHead, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hT1 := Codec.infix_sub (q := Codec.bytesDecTailA Reg64.rdi "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ_c4" 24) 37 hk
    (by simp only [DmUnmarshal, Codec.bytesDecTailA, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hT2 := Codec.infix_sub (q := Codec.bytesDecTailB Reg64.rdi "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ_c4" 0) 45 hk
    (by simp only [DmUnmarshal, Codec.bytesDecTailB, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hlT := Machine.label_at' hk hf (j := 45)
    (by simp only [DmUnmarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [DmUnmarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  have hT3 := Codec.infix_sub (q := Codec.bytesDecTailA Reg64.rsi "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ_162" 24) 73 hk
    (by simp only [DmUnmarshal, Codec.bytesDecTailA, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hT4 := Codec.infix_sub (q := Codec.bytesDecTailB Reg64.rsi "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ_162" 24) 81 hk
    (by simp only [DmUnmarshal, Codec.bytesDecTailB, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hlT2 := Machine.label_at' hk hf (j := 81)
    (by simp only [DmUnmarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [DmUnmarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  have hE := Codec.infix_sub (q := Codec.decEpi) 86 hk
    (by simp only [DmUnmarshal, Codec.decEpi, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hY1 : Codec.U64InlineReg Reg64.rdi := by decide
  have hY2 : Codec.U64InlineReg Reg64.rsi := by decide
  -- head: entry → directive 13
  refine eventually_trans _ _ _ _ (Codec.dechead_seg _ _ _ _ 88 (k + 0) hH _ ra guard fp s1 s2 hfp h1 h2 _
    (by dsimp only; ecancel) hguard (by rw [hlen]; rfl)) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, hrax1, hrbx1, Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 hrax1 hrbx1 Hm1
  subst hpc1
  -- PublicKey: generated segment (48 bytes, offset-0 form), 13 → 37
  refine eventually_trans _ _ _ _ (E2eScal.Gen.dm_g2dec_PublicKey_seg k hk hf
    (rsp.toBitVec - 40) rax.toBitVec rbx.toBitVec
    (rsp.toBitVec + 8) (rsp.toBitVec + 16) (rsp.toBitVec - 16) (rsp.toBitVec - 48)
    (rsp.toBitVec - 48 - BitVec.ofNat 64 S) rax.toBitVec (rax.toBitVec + 8) (rax.toBitVec + 16) S
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by bv_omega) (e1_lo _ _)
    (by simp) (by simp only [Int64.toBitVec_ofNat])
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
  refine eventually_trans _ _ _ _ (Codec.bytesdec_tail_seg Reg64.rdi hY1 _ _ _ (k + 37) (k + 45) hT1 hT2 hlT
    (rsp.toBitVec - 40) rax.toBitVec p1 (rsp.toBitVec - 16) rax.toBitVec
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp)
    (rsp - 8) r14 (Int.toBytes 8 p1.toInt) (Int.toBytes_length 8 _) _ d2 hrsp2 hrbp2 hr142 hrdx2
    (by ecancel)) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrsp3, hrbp3, hr143, hrdx3, Hm3⟩
  dsimp only at hpc3 hrsp3 hrbp3 hr143 hrdx3 Hm3
  subst hpc3
  -- WithdrawalCredentials: generated segment (32 bytes, add form), 47 → 73
  refine eventually_trans _ _ _ _ (E2eScal.Gen.dm_g2dec_WithdrawalCredentials_seg k hk hf
    (rsp.toBitVec - 40) rax.toBitVec rbx.toBitVec
    (rsp.toBitVec + 8) (rsp.toBitVec + 16) (rsp.toBitVec - 16) (rsp.toBitVec - 48)
    (rsp.toBitVec - 48 - BitVec.ofNat 64 S) (rax.toBitVec + 24) (rax.toBitVec + 32) (rax.toBitVec + 40)
    (rbx.toBitVec + 48) S
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by bv_omega) (e1_lo _ _)
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    (rsp - 8) r14 wc hwc spl1 (Int.toBytes 8 (Host.addrOf (k + 26 + 5 + 1)).toBitVec.toInt) lo1 (Int.toBytes 8 p1.toInt)
    aP2 aL2 aC2 hspl1 (Int.toBytes_length 8 _) hlo1 (Int.toBytes_length 8 _) haP2 haL2 haC2
    _ Heap (avail - 48) (by omega) d3 hrsp3 hrbp3 hr143 (by ecancel) hms hmm) ?_
  rintro ⟨d4, pc4⟩ ⟨hpc4, hrsp4, hrbp4, hr144, p2, spl2, lo2, hspl2, hlo2, hrdx4, Hm4⟩
  dsimp only at hpc4 hrsp4 hrbp4 hr144 hrdx4 Hm4
  subst hpc4
  -- pointer tail of WithdrawalCredentials (rsi), 73–74 and 81–82
  refine eventually_trans _ _ _ _ (Codec.bytesdec_tail_seg Reg64.rsi hY2 _ _ _ (k + 73) (k + 81) hT3 hT4 hlT2
    (rsp.toBitVec - 40) rax.toBitVec p2 (rsp.toBitVec - 16) (rax.toBitVec + 24)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat])
    (rsp - 8) r14 (Int.toBytes 8 p2.toInt) (Int.toBytes_length 8 _) _ d4 hrsp4 hrbp4 hr144 hrdx4
    (by ecancel)) ?_
  rintro ⟨d5, pc5⟩ ⟨hpc5, hrsp5, hrbp5, hr145, hrdx5, Hm5⟩
  dsimp only at hpc5 hrsp5 hrbp5 hr145 hrdx5 Hm5
  subst hpc5
  -- Amount: generated segment (inline uint64), 83–85
  refine eventually_trans _ _ _ _ (E2eScal.Gen.dm_g2dec_Amount_seg k hk hf
    (rsp.toBitVec - 40) rax.toBitVec rbx.toBitVec (rsp.toBitVec + 16) (rbx.toBitVec + 80) (rax.toBitVec + 48)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat])
    (by simp only [Int64.toBitVec_ofNat])
    (rsp - 8) r14 amt aN hamt haN _ d5 hrsp5 hrbp5 hr145 hrdx5 (by ecancel)) ?_
  rintro ⟨d6, pc6⟩ ⟨hpc6, hrsp6, hrbp6, hr146, hrdx6, Hm6⟩
  dsimp only at hpc6 hrsp6 hrbp6 hr146 hrdx6 Hm6
  subst hpc6
  -- epilogue, 86–90
  refine eventually_trans _ _ _ _ (Codec.decepi_seg (k + 86) hE (rsp.toBitVec - 40) (rsp.toBitVec - 8) rsp.toBitVec
    (by bv_omega) (by bv_omega) rbp ra r14 _ d6 hrsp6 hr146 (by ecancel)) ?_
  rintro ⟨d7, pc7⟩ ⟨hpc7, hrax7, hrbx7, hrsp7, hrbp7, hr147, Hm7⟩
  dsimp only at hpc7 hrax7 hrbx7 hrsp7 hrbp7 hr147 Hm7
  apply Eventually.done
  rw [show k + 61 + 6 + 1 = k + 68 from rfl, show avail - 48 - 32 = avail - 80 by omega] at Hm7
  refine ⟨hpc7, hrax7, hrbx7, ?_, hrbp7, hr147, p1, p2, spl2, lo2, hspl2, hlo2, ?_⟩
  · dsimp only; rw [hrsp7]; apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
  · dsimp only; ecancel

/-- The `_g2` theorem has the declared type of the existing hand theorem (definitional identity). -/
theorem dm_e2e_accept_main_g2_type : ∀ (h : Host),
    type_of% (@dm_e2e_accept_main_g2 h) = type_of% (@E2eScal.Dm.dm_e2e_accept_main h) := by
  intro h; with_reducible rfl

end E2eScal.G2
