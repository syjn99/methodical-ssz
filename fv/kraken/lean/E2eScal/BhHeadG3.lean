import E2eScal.BhHead
import E2eScal.CallDec

/-!
# Second instance of the call-site lemmas: `bh_e2e_head` re-derived with the call-site lemmas

`bh_e2e_head_g3` has the statement text of `E2eScal.Bh.bh_e2e_head` (`BhHead.lean`, unchanged);
`bh_e2e_head_g3_type`: the two declared types are equal by `rfl`. Proof: `bh_head0` (hand steps, directives
0–14, frame `sub $0x60`), then for `Slot` `callarg_first_seg` (15–16) + `calldec_seg` (17–19, label 46), for
`ProposerIndex` `callarg_reload_seg` with the padding `nop` (47–54) + `calldec_seg` (55–57, label 85), then
`bh_spill2` (hand steps, 86–87: the two nil-error spills). The existing hypotheses `SlUAccC` / `ViUAccC` are
used as `U64CalleeAcc` (the same propositions, `CallDecRel.lean`). Hand-written example; the existing theorem
is unchanged.
-/

open Machine Runtime TestTarget E2eAd E2eAd.Code E2eScal.BhCode E2eScal Codec
variable [Host]

namespace E2eScal.Bh

theorem bhh_sp (x : BitVec 64) : x - 8#64 - 96 = x - 104 := by bv_omega

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- Head, directives 0–14: entry to the first argument set-up. -/
theorem bh_head0 (k : Nat) (hk : BhUnmarshal.IsInfixAt Host.prog k)
    (s : MachineData) (ra guard : UInt64) (fp s1 s2 s4 ast : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h4 : s4.length = 8) (hast : ast.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx = 112) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 15) ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 104 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 } ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.rax = s.regs.rax ∧ st.data.regs.rbx = s.regs.rbx ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  subst hlen
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; simp only [UInt64.size] at *
  have hcs : Eq (ast.At rax.toBitVec) = Eq ((ast.take 1).At rax.toBitVec) ⋆ Eq ((ast.drop 1).At (rax.toBitVec + 1)) := by
    conv => lhs; rw [← List.take_append_drop 1 ast]
    exact at_app _ _ (by rw [List.length_take, hast]; rfl) (by simp [hast])
  rw [hcs] at h_mem
  kat hk BhUnmarshal 0
  kat hk BhUnmarshal 1
  kat hk BhUnmarshal 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BhUnmarshal 3
  split
  · rename_i h; exfalso
    simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk BhUnmarshal 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1' H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk BhUnmarshal 5
  kat hk BhUnmarshal 6
  kat hk BhUnmarshal 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by bv_omega) (by ecancel) (by exact h2)
  intro m2' H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk BhUnmarshal 8
  kat hk BhUnmarshal 9
  kat hk BhUnmarshal 10
  split
  case isTrue h => exact absurd h (by decide)
  simp only [Effects.All]
  kat hk BhUnmarshal 11
  apply store_step_at _ _ (rsp.toBitVec + 8) _ _ _ s1 _ _ (by bv_omega) (by ecancel) (by exact h1)
  intro m3' H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk BhUnmarshal 12
  apply store_step_at _ _ (rsp.toBitVec + 32) _ _ _ s4 _ _ (by bv_omega) (by ecancel) (by exact h4)
  intro m4' H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  kat hk BhUnmarshal 13
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by bv_omega) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m5' H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  kat hk BhUnmarshal 14
  apply load_step _ _ _ _ (ast.take 1) _ _ (by ecancel) (by simp [hast])
  kunfold
  intro _
  apply Eventually.done
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_right
  · rw [hcs]; simp only [Std.ExtHashMap.sep_assoc]; ecancel
  all_goals first
    | rfl
    | exact congrArg UInt64.ofBitVec (bhh_sp _)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Directives 86–87: `mov %rbx,0x30(%rsp); mov %rax,0x28(%rsp)`. -/
theorem bh_spill2 (k : Nat) (hk : BhUnmarshal.IsInfixAt Host.prog k)
    (sp a28 a30 : BitVec 64) (h28 : sp + 40 = a28) (h30 : sp + 48 = a30)
    (s28 s30 : List UInt8) (hs28 : s28.length = 8) (hs30 : s30.length = 8) (R : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp })
    (h_mem : s.dmem =⋆ Eq (s28.At a28) ⋆ Eq (s30.At a30) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 88) ∧ st.data.regs.rsp = s.regs.rsp
        ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        (Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At a28)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At a30) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 86)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp h_mem ⊢
  subst rsp h28 h30
  kat hk BhUnmarshal 86
  apply store_step_at _ _ (sp + 48) _ _ _ s30 _ _ (by saddr) (by ecancel) (by exact hs30)
  intro m1' H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk BhUnmarshal 87
  apply store_step_at _ _ (sp + 40) _ _ _ s28 _ _ (by saddr) (by ecancel) (by exact hs28)
  intro m2' H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  apply Eventually.done
  exact ⟨rfl, rfl, rfl, rfl, by ecancel⟩

theorem bhg_guard (x : BitVec 64) (g : Nat) (h : g + 112 < x.toNat) : g < (x - 112).toNat := by bv_omega

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- Segment 1 of the BeaconBlockHeader decoder accept path, re-derived with the call-site lemmas
(statement text of `bh_e2e_head`). -/
theorem bh_e2e_head_g3 (k : Nat) (hk : BhUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh BhUnmarshal k)
    (hsl : SlUAccC) (hvi : ViUAccC)
    (in0 in1 : List UInt8) (hin0 : in0.length = 8) (hin1 : in1.length = 8)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 sp1 rslot lf ast a8 a16 s28 s30 : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h4 : s4.length = 8)
    (hsp1 : sp1.length = 8) (hrs : rslot.length = 8) (hlf : lf.length = 8)
    (hast : ast.length = 8) (ha8 : a8.length = 8) (ha16 : a16.length = 8)
    (hs28 : s28.length = 8) (hs30 : s30.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq (sp1.At (s.regs.rsp.toBitVec - 96)) ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 112))
      ⋆ Eq (lf.At (s.regs.rsp.toBitVec - 120))
      ⋆ Eq (s28.At (s.regs.rsp.toBitVec - 64)) ⋆ Eq (s30.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (in0.At s.regs.rbx.toBitVec) ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 8))
      ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (a8.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (a16.At (s.regs.rax.toBitVec + 16)) ⋆ R)
    (hguard : guard.toNat + 112 < s.regs.rsp.toNat) (hlen : s.regs.rcx = 112) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 88) ∧ st.data.regs.rsp = s.regs.rsp - 104
        ∧ st.data.regs.rbp = s.regs.rsp - 8 ∧ st.data.regs.r14 = s.regs.r14 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rbx.toBitVec + 8).toInt).At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 56)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rsp.toBitVec - 8#64).toInt).At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (in0.At s.regs.rbx.toBitVec) ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (in0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (in1.At (s.regs.rax.toBitVec + 16)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  have hsl' : U64CalleeAcc slLabel := hsl
  have hvi' : U64CalleeAcc viLabel := hvi
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  have hg : guard.toNat < (rsp.toBitVec - 112).toNat := bhg_guard _ _ hguard
  -- code facts
  have hF1 := Codec.infix_sub (q := E2eScal.callArgFirst false 8) 15 hk
    (by simp only [BhUnmarshal, E2eScal.callArgFirst, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hC1 := Codec.infix_sub (q := E2eScal.callDec "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_b9") 17 hk
    (by simp only [BhUnmarshal, E2eScal.callDec, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hL1 := Codec.infix_sub (q := E2eScal.callDecL "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_b9") 46 hk
    (by simp only [BhUnmarshal, E2eScal.callDecL, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hl1 := Machine.label_at' hk hf (j := 46)
    (by simp only [BhUnmarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [BhUnmarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  have hRl := Codec.infix_sub (q := E2eScal.callArgReload true 120 8 136 (-8) 112 16) 47 hk
    (by simp only [BhUnmarshal, E2eScal.callArgReload, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hC2 := Codec.infix_sub (q := E2eScal.callDec "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_154") 55 hk
    (by simp only [BhUnmarshal, E2eScal.callDec, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hL2 := Codec.infix_sub (q := E2eScal.callDecL "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_154") 85 hk
    (by simp only [BhUnmarshal, E2eScal.callDecL, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hl2 := Machine.label_at' hk hf (j := 85)
    (by simp only [BhUnmarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [BhUnmarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  -- head: entry → directive 15
  refine eventually_trans _ _ _ _ (bh_head0 k hk _ ra guard fp s1 s2 s4 ast hfp h1 h2 h4 hast _
    (by dsimp only; ecancel) (Nat.lt_of_le_of_lt (Nat.le_add_right _ 112) hguard) hlen) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, hrax1, hrbx1, Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 hrax1 hrbx1 Hm1
  subst hpc1
  -- Slot: set-up 15–16
  refine eventually_trans _ _ _ _ (E2eScal.callarg_first_seg false 8 (k + 15) hF1 rax.toBitVec (rax.toBitVec + 8)
    (by simp only [Int64.toBitVec_ofNat]) d1 (by rw [hrax1])) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrsp2, hrbp2, hr142, hrbx2, hrax2, hrcx2, hmem2⟩
  dsimp only at hpc2 hrsp2 hrbp2 hr142 hrbx2 hrax2 hrcx2 hmem2
  subst hpc2
  -- Slot: call block 17–19, label 46
  refine eventually_trans _ _ _ _ (E2eScal.calldec_seg _ _ (k + 17) (k + 46) hC1 hL1 hl1 hsl'
    (rsp.toBitVec - 104) (rax.toBitVec + 8) rbx.toBitVec (rsp.toBitVec - 112) (rsp.toBitVec - 120) (rsp.toBitVec - 96)
    (by bv_omega) (by bv_omega) (by bv_omega)
    { toBitVec := rsp.toBitVec - 8#64 } r14 guard in0 rslot lf sp1 a8 hin0 hrs hlf hsp1 ha8 hg _ d2
    (hrsp2.trans hrsp1) (hrbp2.trans hrbp1) (hr142.trans hr141) hrax2 (by rw [hrbx2, hrbx1]) hrcx2
    (by rw [hmem2]; ecancel)) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrax3, hrbx3, hrsp3, hrbp3, hr143, Hm3⟩
  dsimp only at hpc3 hrax3 hrbx3 hrsp3 hrbp3 hr143 Hm3
  subst hpc3
  -- ProposerIndex: set-up by reload 47–54 (with the padding nop)
  refine eventually_trans _ _ _ _ (E2eScal.callarg_reload_seg true 120 8 136 (-8) 112 16 (k + 47) hRl
    (rsp.toBitVec - 104) rax.toBitVec rbx.toBitVec (rsp.toBitVec + 16) (rsp.toBitVec + 32) (rsp.toBitVec + 8)
    (rbx.toBitVec + 8) (rax.toBitVec + 16)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat])
    (by simp only [Int64.toBitVec_ofNat])
    (Int.toBytes 8 rdi.toBitVec.toInt) (Int.toBytes_length 8 _) _ d3 hrsp3 (by ecancel)) ?_
  rintro ⟨d4, pc4⟩ ⟨hpc4, hrsp4, hrbp4, hr144, hrbx4, hrax4, hrcx4, hmem4⟩
  dsimp only at hpc4 hrsp4 hrbp4 hr144 hrbx4 hrax4 hrcx4 hmem4
  subst hpc4
  -- ProposerIndex: call block 55–57, label 85
  refine eventually_trans _ _ _ _ (E2eScal.calldec_seg _ _ (k + 55) (k + 85) hC2 hL2 hl2 hvi'
    (rsp.toBitVec - 104) (rax.toBitVec + 16) (rbx.toBitVec + 8) (rsp.toBitVec - 112) (rsp.toBitVec - 120)
    (rsp.toBitVec - 96) (by bv_omega) (by bv_omega) (by bv_omega)
    { toBitVec := rsp.toBitVec - 8#64 } r14 guard in1
    (Int.toBytes 8 (Host.addrOf (k + 17 + 1)).toBitVec.toInt) (Int.toBytes 8 (rsp.toBitVec - 8#64).toInt)
    (Int.toBytes 8 rbx.toBitVec.toInt) a16
    hin1 (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) ha16 hg _ d4
    (hrsp4.trans hrsp3) (hrbp4.trans hrbp3) (hr144.trans hr143) hrax4 hrbx4 hrcx4
    (by rw [hmem4]; ecancel)) ?_
  rintro ⟨d5, pc5⟩ ⟨hpc5, hrax5, hrbx5, hrsp5, hrbp5, hr145, Hm5⟩
  dsimp only at hpc5 hrax5 hrbx5 hrsp5 hrbp5 hr145 Hm5
  subst hpc5
  -- nil-error spills 86–87
  refine eventually_trans _ _ _ _ (bh_spill2 k hk (rsp.toBitVec - 104) (rsp.toBitVec - 64) (rsp.toBitVec - 56)
    (by bv_omega) (by bv_omega) s28 s30 hs28 hs30 _ d5 hrsp5 (by ecancel)) ?_
  rintro ⟨d6, pc6⟩ ⟨hpc6, hrsp6, hrbp6, hr146, Hm6⟩
  dsimp only at hpc6 hrsp6 hrbp6 hr146 Hm6
  apply Eventually.done
  rw [hrax5, hrbx5] at Hm6
  rw [show k + 55 + 1 = k + 56 from rfl] at Hm6
  refine ⟨hpc6, ?_, ?_, hr146.trans hr145, ?_⟩
  · dsimp only; rw [hrsp6, hrsp5]; apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_sub, UInt64.toBitVec_ofNat]; rfl
  · dsimp only; rw [hrbp6, hrbp5]; apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_sub, UInt64.toBitVec_ofNat]
  · dsimp only; ecancel

/-- The re-derived theorem has the declared type of the existing hand theorem (definitional identity). -/
theorem bh_e2e_head_g3_type : ∀ (h : Host),
    type_of% (@bh_e2e_head_g3 h) = type_of% (@bh_e2e_head h) := by
  intro h; with_reducible rfl

end E2eScal.Bh
