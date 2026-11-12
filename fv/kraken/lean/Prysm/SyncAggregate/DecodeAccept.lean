import Codec.DecoderHeadEpilogue
import E2eScal.E1Accept
import Prysm.SyncAggregate.DecodeFieldSegments
import Prysm.SyncAggregate.Statements

/-!
# `(*v1alpha1.SyncAggregate).UnmarshalSSZ`, accept path, Go 1.26.10 machine code

Hand composition with the text of `E2eScal.H4.dd_e2e_accept_main` (`DdAccept.lean`):

* head 0–12: `Codec.dechead_seg` (size 160);
* SyncCommitteeBits 13–36: `Prysm.SyncAggregate.bytesdec_seg_z64` (64 bytes, offset 0); pointer tail 37–38, 45–46 (rdi);
* SyncCommitteeSignature 47–72: `Prysm.SyncAggregate.bytes96dec_seg_nop` (96 bytes, src 64, `nop` at 50); pointer tail 73–74,
  81–82 (rsi);
* epilogue 83–87: `Codec.decepi_seg`.

The write-barrier blocks (22–25, 39–44, 57–60, 75–80) are skipped under the premise `writeBarrier = 0`
(inside the segment lemmas). Statement: the frozen `Prysm.SyncAggregate.Decode.accept_statement`.
-/

open Machine Runtime TestTarget Prysm.SyncAggregate.Code
variable [Host]

namespace Prysm.SyncAggregate

/-- SyncCommitteeBits (64 bytes, SSZ offset 0, Go offset 8): decode segment, directives 13–36 (literal-size
statement of `bytesdec_seg_z64`, as the generated `Gen.dd_g2dec_PublicKey_seg` is of `bytesdec_seg_z 48`). -/
theorem Decode.bits_seg (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k) :
    ∀ (sp rcv bf aR aB aS aRet aLo aP aL aC : BitVec 64) (St : Nat)
    (hR : sp + (48 : Int64).toBitVec = aR) (hB' : sp + (56 : Int64).toBitVec = aB)
    (hS : sp + (24 : Int64).toBitVec = aS)
    (hRet : sp - 8 = aRet) (hLo : sp - 8 - BitVec.ofNat 64 St = aLo)
    (hP : rcv + (8 : Int64).toBitVec = aP) (hL : rcv + (16 : Int64).toBitVec = aL)
    (hC : rcv + (24 : Int64).toBitVec = aC)
    (rbp0 r140 : UInt64) (root : List UInt8) (hroot : root.length = 64)
    (spl rslot lo lS vP vL vC : List UInt8)
    (hspl : spl.length = 24) (hrs : rslot.length = 8) (hlo : lo.length = St) (hlS : lS.length = 8)
    (hvP : vP.length = 8) (hvL : vL.length = 8) (hvC : vC.length = 8)
    (R : DataMem → Prop) (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 64 ≤ avail)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
      ⋆ Eq (spl.At sp) ⋆ Eq (rslot.At aRet) ⋆ Eq (lo.At aLo) ⋆ Eq (lS.At aS)
      ⋆ Heap avail
      ⋆ Eq (vP.At aP) ⋆ Eq (vL.At aL) ⋆ Eq (vC.At aC)
      ⋆ Eq (root.At bf)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hms : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 St) (hmm : MemmoveC St),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 26 + 11) ∧ st.data.regs.rsp = { toBitVec := sp }
        ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        ∃ (p : BitVec 64) (spl' lo' : List UInt8), spl'.length = 24 ∧ lo'.length = St
          ∧ st.data.regs.rdx.toBitVec = rcv ∧
        (Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
          ⋆ Eq (spl'.At sp)
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 26 + 5 + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq (lo'.At aLo)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aS)
          ⋆ Heap (avail - 64)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aP) ⋆ Eq ((Int.toBytes 8 64).At aL)
          ⋆ Eq ((Int.toBytes 8 64).At aC) ⋆ Eq (root.At p)
          ⋆ Eq (root.At bf)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 13)⟩ := by
  have hA := Codec.infix_sub (q := Codec.bytesDecHead 64 "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_78" 48 16 24) 13 hk
    (by simp only [unmarshalSSZ, Codec.bytesDecHead, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hB := Codec.infix_sub (q := Codec.bytesDecMidZ 64 "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_78" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_b5" 48 56 24 8 16 24) 26 hk
    (by simp only [unmarshalSSZ, Codec.bytesDecMidZ, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hl := Machine.label_at' hk hf (j := 26)
    (by simp only [unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  with_reducible exact Prysm.SyncAggregate.bytesdec_seg_z64 64 rfl _ _ _ _ _ _ _ _ (k + 13) (k + 26) hA hB hl
/-- **Accept path of the real `(*v1alpha1.SyncAggregate).UnmarshalSSZ` (Go 1.26.10)**; statement = the frozen
`Decode.accept_statement`. -/
theorem Decode.accept : Decode.accept_statement := by
  intro k hk hf bits sig hbits hsig s ra guard
    fp s1 s2 spl l18 rslot lo ast aP1 aL1 aC1 aP2 aL2 aC2
    hfp h1 h2 hspl hl18 hrs hast haP1 haL1 haC1 haP2 haL2 haC2
    R S hlo Heap avail h_mem hguard hlen hav hms hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  have hrsp_lt : rsp.toNat < 2 ^ 64 := rsp.toNat_lt_size
  -- code facts
  have hH := Codec.infix_sub (q := Codec.decHead "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_0" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_18b" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_177" 160) 0 hk
    (by simp only [unmarshalSSZ, Codec.decHead, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hTa0 := Codec.infix_sub (q := Codec.bytesDecTailA Reg64.rdi "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_ca" 24) 37 hk
    (by simp only [unmarshalSSZ, Codec.bytesDecTailA, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hTb0 := Codec.infix_sub (q := Codec.bytesDecTailB Reg64.rdi "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_ca" 8) 45 hk
    (by simp only [unmarshalSSZ, Codec.bytesDecTailB, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hlT0 := Machine.label_at' hk hf (j := 45)
    (by simp only [unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  have hYdi : Codec.U64InlineReg Reg64.rdi := by decide
  have hWa := Codec.infix_sub (q := Prysm.SyncAggregate.bytesDecHeadNop96 "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_113" 48 40 48) 47 hk
    (by simp only [unmarshalSSZ, Prysm.SyncAggregate.bytesDecHeadNop96, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hWb := Codec.infix_sub (q := Codec.bytesDecMid 96 "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_113" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_154" 48 56 24 32 40 48 64) 61 hk
    (by simp only [unmarshalSSZ, Codec.bytesDecMid, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hlW := Machine.label_at' hk hf (j := 61)
    (by simp only [unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  have hTa1 := Codec.infix_sub (q := Codec.bytesDecTailA Reg64.rsi "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_169" 24) 73 hk
    (by simp only [unmarshalSSZ, Codec.bytesDecTailA, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hTb1 := Codec.infix_sub (q := Codec.bytesDecTailB Reg64.rsi "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_169" 32) 81 hk
    (by simp only [unmarshalSSZ, Codec.bytesDecTailB, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hlT1 := Machine.label_at' hk hf (j := 81)
    (by simp only [unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  have hYsi : Codec.U64InlineReg Reg64.rsi := by decide
  have hE := Codec.infix_sub (q := Codec.decEpi) 83 hk
    (by simp only [unmarshalSSZ, Codec.decEpi, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  -- head: entry → directive 13
  refine eventually_trans _ _ _ _ (Codec.dechead_seg _ _ _ _ 160 (k + 0) hH _ ra guard fp s1 s2 hfp h1 h2 _
    (by dsimp only; ecancel) hguard (by rw [hlen]; rfl)) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, hrax1, hrbx1, Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 hrax1 hrbx1 Hm1
  subst hpc1
  -- SyncCommitteeBits (64 bytes, zero form), 13 → 37
  refine eventually_trans _ _ _ _ (Decode.bits_seg k hk hf
    (rsp.toBitVec - 40) rax.toBitVec rbx.toBitVec
    (rsp.toBitVec + 8) (rsp.toBitVec + 16) (rsp.toBitVec - 16) (rsp.toBitVec - 48)
    (rsp.toBitVec - 48 - BitVec.ofNat 64 S) (rax.toBitVec + 8) (rax.toBitVec + 16) (rax.toBitVec + 24) S
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by bv_omega) (E2eScal.E1.e1_lo _ _)
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    (by simp only [Int64.toBitVec_ofNat])
    (rsp - 8) r14 bits hbits spl rslot lo l18 aP1 aL1 aC1 hspl hrs hlo hl18 haP1 haL1 haC1
    _ Heap avail (by omega) d1
    (by rw [hrsp1]; first | rfl | (apply UInt64.toBitVec_inj.mp; simp))
    (by rw [hrbp1]) hr141
    (by ecancel) hms hmm) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrsp2, hrbp2, hr142, p1, spl1, lo1, hspl1, hlo1, hrdx2, Hm2⟩
  dsimp only at hpc2 hrsp2 hrbp2 hr142 hrdx2 Hm2
  subst hpc2
  -- pointer tail of SyncCommitteeBits (rdi), 37–38 and 45–46
  refine eventually_trans _ _ _ _ (Codec.bytesdec_tail_seg Reg64.rdi hYdi _ _ _ (k + 37) (k + 45) hTa0 hTb0 hlT0
    (rsp.toBitVec - 40) rax.toBitVec p1 (rsp.toBitVec - 16) (rax.toBitVec + 8)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat])
    (rsp - 8) r14 (Int.toBytes 8 p1.toInt) (Int.toBytes_length 8 _) _ d2 hrsp2 hrbp2 hr142 hrdx2
    (by ecancel)) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrsp3, hrbp3, hr143, hrdx3, Hm3⟩
  dsimp only at hpc3 hrsp3 hrbp3 hr143 hrdx3 Hm3
  subst hpc3
  -- SyncCommitteeSignature (96 bytes, add form, nop head), 47 → 73
  refine eventually_trans _ _ _ _ (Prysm.SyncAggregate.bytes96dec_seg_nop _ _ _ _ _ _ _ _ _ (k + 47) (k + 61) hWa hWb hlW
    (rsp.toBitVec - 40) rax.toBitVec rbx.toBitVec
    (rsp.toBitVec + 8) (rsp.toBitVec + 16) (rsp.toBitVec - 16) (rsp.toBitVec - 48)
    (rsp.toBitVec - 48 - BitVec.ofNat 64 S) (rax.toBitVec + 32) (rax.toBitVec + 40) (rax.toBitVec + 48) (rbx.toBitVec + 64) S
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by bv_omega) (E2eScal.E1.e1_lo _ _)
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    (rsp - 8) r14 sig hsig spl1 (Int.toBytes 8 (Host.addrOf (k + 26 + 5 + 1)).toBitVec.toInt) lo1 (Int.toBytes 8 p1.toInt) aP2 aL2 aC2 hspl1 (Int.toBytes_length 8 _) hlo1 (Int.toBytes_length 8 _) haP2 haL2 haC2
    _ Heap (avail - 64) (by omega) d3
    hrsp3
    hrbp3 hr143
    (by ecancel) hms hmm) ?_
  rintro ⟨d4, pc4⟩ ⟨hpc4, hrsp4, hrbp4, hr144, p2, spl2, lo2, hspl2, hlo2, hrdx4, Hm4⟩
  dsimp only at hpc4 hrsp4 hrbp4 hr144 hrdx4 Hm4
  subst hpc4
  -- pointer tail of SyncCommitteeSignature (rsi), 73–74 and 81–82
  refine eventually_trans _ _ _ _ (Codec.bytesdec_tail_seg Reg64.rsi hYsi _ _ _ (k + 73) (k + 81) hTa1 hTb1 hlT1
    (rsp.toBitVec - 40) rax.toBitVec p2 (rsp.toBitVec - 16) (rax.toBitVec + 32)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat])
    (rsp - 8) r14 (Int.toBytes 8 p2.toInt) (Int.toBytes_length 8 _) _ d4 hrsp4 hrbp4 hr144 hrdx4
    (by ecancel)) ?_
  rintro ⟨d5, pc5⟩ ⟨hpc5, hrsp5, hrbp5, hr145, hrdx5, Hm5⟩
  dsimp only at hpc5 hrsp5 hrbp5 hr145 hrdx5 Hm5
  subst hpc5
  -- epilogue, 83–87
  refine eventually_trans _ _ _ _ (Codec.decepi_seg (k + 83) hE (rsp.toBitVec - 40) (rsp.toBitVec - 8) rsp.toBitVec
    (by bv_omega) (by bv_omega) rbp ra r14 _ d5 hrsp5 hr145 (by ecancel)) ?_
  rintro ⟨d9, pc9⟩ ⟨hpc9, hrax9, hrbx9, hrsp9, hrbp9, hr149, Hm9⟩
  dsimp only at hpc9 hrax9 hrbx9 hrsp9 hrbp9 hr149 Hm9
  apply Eventually.done
  rw [show k + 61 + 6 + 1 = k + 68 from rfl, show avail - 64 - 96 = avail - 160 by omega] at Hm9
  refine ⟨hpc9, hrax9, hrbx9, ?_, hrbp9, hr149, p1, p2, spl2, lo2, hspl2, hlo2, ?_⟩
  · dsimp only; rw [hrsp9]; apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
  · dsimp only; ecancel

end Prysm.SyncAggregate
