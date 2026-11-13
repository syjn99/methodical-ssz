import Codec.DecoderHeadEpilogue
import Prysm.DepositMessage.DecodeFieldSegmentExamples
import Prysm.BlobIdentifier.DecodeAccept

/-!
# Example: the BlobIdentifier accept path composed from segment theorems only

`Decode.accept_composed_example` has the statement text of `Prysm.BlobIdentifier.Decode.accept`
(`Decode.accept_composed_example_type`: the two declared types are equal by `rfl`). Its proof steps no
directive by hand: it is a chain of `eventually_trans` over `dechead_seg`, the BlockRoot segment
(`Decode.example_field_BlockRoot_seg`, an instance of `bytesdec_seg_offset_zero 32`), `bytesdec_tail_seg`, the Index segment
(`Decode.example_field_Index_seg`, an instance of `u64dec_inline_seg`) and `decepi_seg`. What stays per type is
the frame instance of each step (addresses relative to the entry rsp, rax, rbx) and the code facts
(`infix_sub`, `label_at'`). Hand-written example for the generator; the existing theorem is unchanged.
-/

open Machine Runtime Codec Prysm.BlobIdentifier.Code
variable [Host]

namespace Prysm.BlobIdentifier

theorem Decode.example_lo (x : BitVec 64) (S : Nat) : x - 40 - 8 - BitVec.ofNat 64 S = x - 48 - BitVec.ofNat 64 S := by
  bv_omega

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- The accept path of `(*v1alpha1.BlobIdentifier).UnmarshalSSZ`, composed from segment theorems. -/
theorem Decode.accept_composed_example (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (r1 idx : List UInt8) (hr1 : r1.length = 32) (hidx : idx.length = 8)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 spl l18 rslot lo ast aP1 aL1 aC1 aN : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8)
    (hspl : spl.length = 24) (hl18 : l18.length = 8) (hrs : rslot.length = 8)
    (hast : ast.length = 8)
    (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8) (haN : aN.length = 8)
    (R : DataMem → Prop) (S : Nat) (hlo : lo.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (l18.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 48 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (r1.At s.regs.rbx.toBitVec) ⋆ Eq (idx.At (s.regs.rbx.toBitVec + 32))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 24)) ⋆ Eq (aN.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx = 40) (hav : 32 ≤ avail)
    (hms : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 S) (hmm : MemmoveContract S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (p1 : BitVec 64) (spl' lo' : List UInt8), spl'.length = 24 ∧ lo'.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 32)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 48 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 32)
          ⋆ Eq (r1.At s.regs.rbx.toBitVec) ⋆ Eq (idx.At (s.regs.rbx.toBitVec + 32))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (idx.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (r1.At p1)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  have hrsp_lt : rsp.toNat < 2 ^ 64 := rsp.toNat_lt_size
  -- code facts
  have hH := Codec.infix_sub (q := Codec.decHead "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.UnmarshalSSZ_0" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.UnmarshalSSZ_f6" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.UnmarshalSSZ_e2" 40) 0 hk
    (by simp only [unmarshalSSZ, Codec.decHead, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hT1 := Codec.infix_sub (q := Codec.bytesDecTailA Reg64.rsi "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.UnmarshalSSZ_c7" 24) 37 hk
    (by simp only [unmarshalSSZ, Codec.bytesDecTailA, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hT2 := Codec.infix_sub (q := Codec.bytesDecTailPointerStore Reg64.rsi "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.UnmarshalSSZ_c7" 8) 45 hk
    (by simp only [unmarshalSSZ, Codec.bytesDecTailPointerStore, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hlT := Machine.label_at' hk hf (j := 45)
    (by simp only [unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  have hE := Codec.infix_sub (q := Codec.decEpilogue) 50 hk
    (by simp only [unmarshalSSZ, Codec.decEpilogue, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hY : Codec.U64InlineReg Reg64.rsi := by decide
  -- head: entry → directive 13
  refine eventually_trans _ _ _ _ (Codec.dechead_seg _ _ _ _ 40 (k + 0) hH _ ra guard fp s1 s2 hfp h1 h2 _
    (by dsimp only; ecancel) hguard (by rw [hlen]; rfl)) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, hrax1, hrbx1, Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 hrax1 hrbx1 Hm1
  subst hpc1
  -- BlockRoot segment, 13 → 37
  refine eventually_trans _ _ _ _ (Decode.example_field_BlockRoot_seg k hk hf
    (rsp.toBitVec - 40) rax.toBitVec rbx.toBitVec
    (rsp.toBitVec + 8) (rsp.toBitVec + 16) (rsp.toBitVec - 16) (rsp.toBitVec - 48)
    (rsp.toBitVec - 48 - BitVec.ofNat 64 S) (rax.toBitVec + 8) (rax.toBitVec + 16) (rax.toBitVec + 24) S
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by bv_omega) (Decode.example_lo _ _)
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    (by simp only [Int64.toBitVec_ofNat])
    (rsp - 8) r14 r1 hr1 spl rslot lo l18 aP1 aL1 aC1 hspl hrs hlo hl18 haP1 haL1 haC1
    _ Heap avail (by omega) d1
    (by rw [hrsp1]; first | rfl | (apply UInt64.toBitVec_inj.mp; simp))
    (by rw [hrbp1]) hr141
    (by ecancel) hms hmm) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrsp2, hrbp2, hr142, p1, spl1, lo1, hspl1, hlo1, hrdx2, Hm2⟩
  dsimp only at hpc2 hrsp2 hrbp2 hr142 hrdx2 Hm2
  subst hpc2
  -- pointer tail, 37–38 and 45–46
  refine eventually_trans _ _ _ _ (Codec.bytesdec_tail_seg Reg64.rsi hY _ _ _ (k + 37) (k + 45) hT1 hT2 hlT
    (rsp.toBitVec - 40) rax.toBitVec p1 (rsp.toBitVec - 16) (rax.toBitVec + 8)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat])
    (rsp - 8) r14 (Int.toBytes 8 p1.toInt) (Int.toBytes_length 8 _) _ d2 hrsp2 hrbp2 hr142 hrdx2
    (by ecancel)) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrsp3, hrbp3, hr143, hrdx3, Hm3⟩
  dsimp only at hpc3 hrsp3 hrbp3 hr143 hrdx3 Hm3
  subst hpc3
  -- Index segment, 47–49
  refine eventually_trans _ _ _ _ (Decode.example_field_Index_seg k hk hf
    (rsp.toBitVec - 40) rax.toBitVec rbx.toBitVec (rsp.toBitVec + 16) (rbx.toBitVec + 32) (rax.toBitVec + 32)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat])
    (by simp only [Int64.toBitVec_ofNat])
    (rsp - 8) r14 idx aN hidx haN _ d3 hrsp3 hrbp3 hr143 hrdx3 (by ecancel)) ?_
  rintro ⟨d4, pc4⟩ ⟨hpc4, hrsp4, hrbp4, hr144, hrdx4, Hm4⟩
  dsimp only at hpc4 hrsp4 hrbp4 hr144 hrdx4 Hm4
  subst hpc4
  -- epilogue, 50–54
  refine eventually_trans _ _ _ _ (Codec.decepi_seg (k + 50) hE (rsp.toBitVec - 40) (rsp.toBitVec - 8) rsp.toBitVec
    (by bv_omega) (by bv_omega) rbp ra r14 _ d4 hrsp4 hr144 (by ecancel)) ?_
  rintro ⟨d5, pc5⟩ ⟨hpc5, hrax5, hrbx5, hrsp5, hrbp5, hr145, Hm5⟩
  dsimp only at hpc5 hrax5 hrbx5 hrsp5 hrbp5 hr145 Hm5
  apply Eventually.done
  rw [show k + 26 + 5 + 1 = k + 32 from rfl] at Hm5
  refine ⟨hpc5, hrax5, hrbx5, ?_, hrbp5, hr145, p1, spl1, lo1, hspl1, hlo1, ?_⟩
  · dsimp only; rw [hrsp5]; apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
  · dsimp only; ecancel

/-- The composed theorem has the declared type of the existing hand theorem (definitional identity). -/
theorem Decode.accept_composed_example_type : ∀ (h : Host),
    type_of% (@Decode.accept_composed_example h) = type_of% (@Prysm.BlobIdentifier.Decode.accept h) := by
  intro h; with_reducible rfl

end Prysm.BlobIdentifier
