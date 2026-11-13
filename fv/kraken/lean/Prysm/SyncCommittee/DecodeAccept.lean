import Codec.DecoderHeadEpilogue
import Codec.FixedBytesDecode
import Prysm.SyncCommittee.DecodeLoop
import Prysm.SyncCommittee.Statements

/-!
# `(*v1alpha1.SyncCommittee).UnmarshalSSZ`, accept path, Go 1.26.10 machine code

* head 0–29 (hand steps): guard, prologue (`sub $0x30`), size check, spills, `makeslice` of the `[][]byte` backing
  array (`MakesliceC Heap lvSliceType_addr 24 S`, cnt 512), Pubkeys len = cap = 512, writeBarrier = 0, Pubkeys ptr,
  rax = 0, `jmp L_a0`;
* element loop 40–79, 36–39: `Prysm.SyncCommittee.Decode.loop` (512 iterations; each proves the `panicBounds` branch not taken);
* AggregatePubkey 81–105: `Decode.aggregate_pubkey_seg` (the literal-size statement of `Codec.bytesdec_seg 48`, src 24576);
  pointer tail 106–107, 115–116 (rsi);
* epilogue 117–121 (hand steps, `add $0x30`).
Statement: the frozen `Prysm.SyncCommittee.Decode.accept_statement`.
-/

open Machine Runtime Prysm.SyncCommittee.Code
variable [Host]

namespace Prysm.SyncCommittee

/-- AggregatePubkey (48 bytes, SSZ offset 24576, Go offset 32): decode segment, directives 81–105. -/
theorem Decode.aggregate_pubkey_seg (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k) :
    ∀ (sp rcv bf aR aB aS aRet aLo aP aL aC aSrc : BitVec 64) (St : Nat)
    (hR : sp + (64 : Int64).toBitVec = aR) (hB' : sp + (72 : Int64).toBitVec = aB)
    (hS : sp + (40 : Int64).toBitVec = aS)
    (hRet : sp - 8 = aRet) (hLo : sp - 8 - BitVec.ofNat 64 St = aLo)
    (hP : rcv + (32 : Int64).toBitVec = aP) (hL : rcv + (40 : Int64).toBitVec = aL)
    (hC : rcv + (48 : Int64).toBitVec = aC)
    (hSrc : bf + (24576 : Int64).toBitVec = aSrc)
    (rbp0 r140 : UInt64) (root : List UInt8) (hroot : root.length = 48)
    (spl rslot lo lS vP vL vC : List UInt8)
    (hspl : spl.length = 24) (hrs : rslot.length = 8) (hlo : lo.length = St) (hlS : lS.length = 8)
    (hvP : vP.length = 8) (hvL : vL.length = 8) (hvC : vC.length = 8)
    (R : DataMem → Prop) (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 48 ≤ avail)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
      ⋆ Eq (spl.At sp) ⋆ Eq (rslot.At aRet) ⋆ Eq (lo.At aLo) ⋆ Eq (lS.At aS)
      ⋆ Heap avail
      ⋆ Eq (vP.At aP) ⋆ Eq (vL.At aL) ⋆ Eq (vC.At aC)
      ⋆ Eq (root.At aSrc)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hms : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 St) (hmm : MemmoveC St),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 94 + 12) ∧ st.data.regs.rsp = { toBitVec := sp }
        ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        ∃ (p : BitVec 64) (spl' lo' : List UInt8), spl'.length = 24 ∧ lo'.length = St
          ∧ st.data.regs.rdx.toBitVec = rcv ∧
        (Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
          ⋆ Eq (spl'.At sp)
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 94 + 6 + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq (lo'.At aLo)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aS)
          ⋆ Heap (avail - 48)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aP) ⋆ Eq ((Int.toBytes 8 48).At aL)
          ⋆ Eq ((Int.toBytes 8 48).At aC) ⋆ Eq (root.At p)
          ⋆ Eq (root.At aSrc)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 81)⟩ := by
  have hA := Codec.infix_sub (q := Codec.bytesDecHead 48 "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_197" 64 40 48) 81 hk
    (by simp only [unmarshalSSZ, Codec.bytesDecHead, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hB := Codec.infix_sub (q := Codec.bytesDecMid 48 "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_197" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_1db" 64 72 40 32 40 48 24576) 94 hk
    (by simp only [unmarshalSSZ, Codec.bytesDecMid, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hl := Machine.label_at' hk hf (j := 94)
    (by simp only [unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  with_reducible exact Codec.bytesdec_seg 48 (Or.inr (Or.inl rfl)) _ _ _ _ _ _ _ _ _ (k + 81) (k + 94) hA hB hl

/-- **Accept path of the real `(*v1alpha1.SyncCommittee).UnmarshalSSZ` (Go 1.26.10)**; statement = the frozen
`Decode.accept_statement`. -/
theorem Decode.accept : Decode.accept_statement := by
  intro k hk hf pks agg hpks hpk hagg s ra guard
    fp s1 s2 l18 l20 l28 spl rslot lo ast aP1 aL1 aC1 aP2 aL2 aC2
    hfp h1 h2 hl18 hl20 hl28 hspl hrs hast haP1 haL1 haC1 haP2 haL2 haC2
    R S hlo Heap avail h_mem hguard hlen hav hms hmsA hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  subst hlen
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; simp only [UInt64.size] at *
  kat hk unmarshalSSZ 0
  kat hk unmarshalSSZ 1
  kat hk unmarshalSSZ 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk unmarshalSSZ 3
  split
  · rename_i h; exfalso
    simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk unmarshalSSZ 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk unmarshalSSZ 5
  kat hk unmarshalSSZ 6
  kat hk unmarshalSSZ 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by bv_omega) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk unmarshalSSZ 8
  kat hk unmarshalSSZ 9
  kat hk unmarshalSSZ 10
  split
  case isTrue h => exact absurd h (by decide)
  simp only [Effects.All]
  kat hk unmarshalSSZ 11
  apply store_step_at _ _ (rsp.toBitVec + 8) _ _ _ s1 _ _ (by bv_omega) (by ecancel) (by exact h1)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk unmarshalSSZ 12
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by bv_omega) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  kat hk unmarshalSSZ 13
  kat hk unmarshalSSZ 14
  kat hk unmarshalSSZ 15
  kat hk unmarshalSSZ 16
  apply store_step_at _ _ (rsp.toBitVec - 64) _ _ _ rslot _ _ (by laddr) (by ecancel) (by exact hrs)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  rw [show rsp.toBitVec - 8#64 - 48 - 8#64 = rsp.toBitVec - 64 by bv_omega]
  refine eventually_trans _ _ _ _ (hmsA _ (Host.addrOf (k + 16 + 1)) 512 avail lo spl _
    rfl (Nat.le_refl _) (by rfl) (by omega) (by unfold maxAlloc; omega) (by omega) hlo hspl
    (by dsimp only; rw [show rsp.toBitVec - 64 + 8 = rsp.toBitVec - 56 by bv_omega]; ecancel)) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrsp3, hr143, hrbp3, stk3, spm3, hstk3, hspm3, Hm3⟩
  dsimp only at hpc3 hrsp3 hr143 hrbp3 Hm3
  subst hpc3
  obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,
    zmms3, flags3, mem3⟩ := d3
  simp only at hrsp3 hr143 hrbp3 Hm3
  rw [show ({ toBitVec := rsp.toBitVec - 64 } + 8 : UInt64) = { toBitVec := rsp.toBitVec - 56 } by
    apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega] at hrsp3
  subst hrsp3 hr143 hrbp3
  rw [show rsp.toBitVec - 64 + 8 = rsp.toBitVec - 56 by bv_omega] at Hm3
  -- 17 load recv; 18–19 Pubkeys len = cap = 512; 20–21 writeBarrier; 26–27 Pubkeys ptr; 28 rax = 0; 29 jmp L_a0
  kat hk unmarshalSSZ 17
  apply load_step_at _ _ (rsp.toBitVec + 8) _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by kaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk unmarshalSSZ 18
  apply store_step_at _ _ (rax.toBitVec + 16) _ _ _ aL1 _ _ (by kaddr) (by ecancel) (by exact haL1)
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  kat hk unmarshalSSZ 19
  apply store_step_at _ _ (rax.toBitVec + 24) _ _ _ aC1 _ _ (by kaddr) (by ecancel) (by exact haC1)
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  kat hk unmarshalSSZ 20
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk unmarshalSSZ 21
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf unmarshalSSZ 26
  kat hk unmarshalSSZ 26
  kat hk unmarshalSSZ 27
  apply store_step_at _ _ (rax.toBitVec + 8) _ _ _ aP1 _ _ (by kaddr) (by ecancel) (by exact haP1)
  intro m8 H8
  simp only [Width.bytes, Width.bits] at H8
  kunfold
  kat hk unmarshalSSZ 28
  intro _
  kat hk unmarshalSSZ 29
  klabel hk hf unmarshalSSZ 40
  have e512 : Int.toBytes 8 (BitVec.toInt (512 : BitVec 64)) = Int.toBytes 8 512 := by decide
  simp only [e512] at H8
  -- element loop: L_a0 (40) → directive 81
  refine eventually_trans _ _ _ _ (Decode.loop k hk hf (rsp.toBitVec - 56) rax.toBitVec rbx.toBitVec rax3.toBitVec pks
    hpks hpk _ _ S Heap _ hms hmm 512 0 [] l18 l20 l28 spm3 (Int.toBytes 8 (Host.addrOf (k + 16 + 1)).toBitVec.toInt)
    stk3 (avail - 24 * 512) _ (by omega) rfl hl18 hl20 hl28 hspm3 (Int.toBytes_length 8 _) hstk3 (by omega)
    (by simp) rfl rfl rfl
    (by
      dsimp only
      rw [show rsp.toBitVec - 56 + 64 = rsp.toBitVec + 8 by laddr, show rsp.toBitVec - 56 + 72 = rsp.toBitVec + 16 by laddr,
        show rsp.toBitVec - 56 + 24 = rsp.toBitVec - 32 by laddr, show rsp.toBitVec - 56 + 32 = rsp.toBitVec - 24 by laddr,
        show rsp.toBitVec - 56 + 40 = rsp.toBitVec - 16 by laddr, show rsp.toBitVec - 56 - 8 = rsp.toBitVec - 64 by laddr]
      simp only [show Codec.sliceHeaders 48 [] ++ Codec.zeroBytes (24 * (512 - 0)) = List.replicate (24 * 512) 0 from rfl, List.take_zero,
        show Codec.elementBlocks [] ([] : List (List UInt8)) = Std.ExtHashMap.emp from rfl, Std.ExtHashMap.sep_emp]
      ecancel)) ?_
  rintro ⟨d4, pc4⟩ ⟨hpc4, hrsp4, hrbp4, hr144, ps', l18', l20', l28', spl', rslot', lo', hps', g18, g20, g28, gspl,
    grs, glo, Hm4⟩
  dsimp only at hpc4 hrsp4 hrbp4 hr144 Hm4
  subst hpc4
  -- AggregatePubkey, 81 → 106
  refine eventually_trans _ _ _ _ (Decode.aggregate_pubkey_seg k hk hf (rsp.toBitVec - 56) rax.toBitVec rbx.toBitVec
    (rsp.toBitVec - 56 + 64) (rsp.toBitVec - 56 + 72) (rsp.toBitVec - 56 + 40) (rsp.toBitVec - 56 - 8)
    (rsp.toBitVec - 56 - 8 - BitVec.ofNat 64 S) (rax.toBitVec + 32) (rax.toBitVec + 40) (rax.toBitVec + 48)
    (rbx.toBitVec + 24576) S
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    (by simp only [Int64.toBitVec_ofNat]) rfl rfl
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    _ _ agg hagg spl' rslot' lo' l28' aP2 aL2 aC2 gspl grs glo g28 haP2 haL2 haC2
    _ Heap (avail - 24 * 512 - 48 * 512) (by omega) d4 hrsp4 hrbp4 hr144 (by ecancel) hms hmm) ?_
  rintro ⟨d5, pc5⟩ ⟨hpc5, hrsp5, hrbp5, hr145, pA, spl5, lo5, hspl5, hlo5, hrdx5, Hm5⟩
  dsimp only at hpc5 hrsp5 hrbp5 hr145 hrdx5 Hm5
  subst hpc5
  -- pointer tail of AggregatePubkey (rsi), 106–107 and 115–116
  have hTa := Codec.infix_sub (q := Codec.bytesDecTailA Reg64.rsi "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_1f1" 40) 106 hk
    (by simp only [unmarshalSSZ, Codec.bytesDecTailA, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hTb := Codec.infix_sub (q := Codec.bytesDecTailB Reg64.rsi "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_1f1" 32) 115 hk
    (by simp only [unmarshalSSZ, Codec.bytesDecTailB, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hlT := Machine.label_at' hk hf (j := 115)
    (by simp only [unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  have hYsi : Codec.U64InlineReg Reg64.rsi := by decide
  refine eventually_trans _ _ _ _ (Codec.bytesdec_tail_seg Reg64.rsi hYsi _ _ _ (k + 106) (k + 115) hTa hTb hlT
    (rsp.toBitVec - 56) rax.toBitVec pA (rsp.toBitVec - 56 + 40) (rax.toBitVec + 32)
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    _ _ (Int.toBytes 8 pA.toInt) (Int.toBytes_length 8 _) _ d5 hrsp5 hrbp5 hr145 hrdx5
    (by ecancel)) ?_
  rintro ⟨d6, pc6⟩ ⟨hpc6, hrsp6, hrbp6, hr146, hrdx6, Hm6⟩
  dsimp only at hpc6 hrsp6 hrbp6 hr146 hrdx6 Hm6
  subst hpc6
  obtain ⟨⟨rax6, rbx6, rcx6, rdx6, rsi6, rdi6, rsp6, rbp6, r86, r96, r106, r116, r126, r136, r146', r156⟩,
    zmms6, flags6, mem6⟩ := d6
  simp only at hrsp6 hrbp6 hr146 Hm6
  subst hrsp6 hrbp6 hr146
  -- epilogue 117–121
  kat hk unmarshalSSZ 117
  intro _
  kat hk unmarshalSSZ 118
  intro _
  kat hk unmarshalSSZ 119
  kat hk unmarshalSSZ 120
  apply load_step_at _ _ (rsp.toBitVec - 8) _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by laddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk unmarshalSSZ 121
  apply load_step_at _ _ rsp.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by laddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  rw [show rsp.toBitVec - 56 + 40 = rsp.toBitVec - 16 by laddr, show rsp.toBitVec - 56 + 64 = rsp.toBitVec + 8 by laddr,
    show rsp.toBitVec - 56 + 72 = rsp.toBitVec + 16 by laddr, show rsp.toBitVec - 56 + 24 = rsp.toBitVec - 32 by laddr,
    show rsp.toBitVec - 56 + 32 = rsp.toBitVec - 24 by laddr, show rsp.toBitVec - 56 - 8 = rsp.toBitVec - 64 by laddr,
    show k + 94 + 6 + 1 = k + 101 from rfl, show avail - 24 * 512 - 48 * 512 - 48 = avail - 36912 by omega,
    show Codec.zeroBytes (24 * (512 - 512)) = [] from rfl, List.append_nil, List.take_of_length_le (by omega : pks.length ≤ 512)]
    at Hm6
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rax3.toBitVec, pA, ps', l18', l20', spl5, lo5, hps', g18, g20, hspl5, hlo5, ?_⟩
  rotate_right
  · ecancel
  all_goals first
    | exact trivial
    | with_reducible rfl
    | (apply UInt64.toBitVec_inj.mp
       simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, Width.bits]
       done)
    | (apply UInt64.toBitVec_inj.mp; laddr)
    | (apply UInt64.toBitVec_inj.mp; simp)

end Prysm.SyncCommittee
