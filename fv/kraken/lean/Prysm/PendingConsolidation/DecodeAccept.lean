import Prysm.PendingPartialWithdrawal.DecodeAccept
import Prysm.PendingConsolidation.GeneratedDecodeCallSegmentsPartial
import Prysm.SyncCommitteeMessage.Statements

/-!
# Real Prysm `(*v1alpha1.PendingConsolidation).UnmarshalSSZ`, accept path, Go 1.26.10 (hold-out, class D)

Hand composition, written AFTER the raw generator output was committed. The
statement is the independent hand statement `Prysm.PendingConsolidation.Decode.accept_statement` (`Prysm/SyncCommitteeMessage/Statements.lean`, unchanged). Chain of
`eventually_trans` over

* `Decode.head` (hand steps, directives 0–14; the text of `pw_head` with the two spills at 12 / 13 in the PendingConsolidation order),
* `Decode.generated_call_SourceIndex_arg` (15–16) and `Decode.generated_call_SourceIndex_call` (17–19, label 47): GENERATED
  (`Prysm/PendingConsolidation/GeneratedDecodeCallSegmentsPartial.lean`, raw); the `_call` theorem is conditional on `hC : U64CalleeAccept`, discharged here by
  the proved `Prysm.ValidatorIndex.Decode.accept_function_spec_holds`,
* `Codec.callarg_reload_seg false 96 8 112 (-8) 88 16` (48–54; existing lemma, applied by hand: the
  generator did not emit TargetIndex),
* `calldec_nop_seg` (hand lemma below, 55–58 + label 85: the call block with a `nop` between `callq` and
  `test`, the reason the generator gave for TargetIndex),
* `Decode.epilogue` (hand steps, 86–88).

The callee is used only through `U64CalleeAccept` (= the existing `Prysm.ValidatorIndex.Decode.accept_function_spec`, proved by `Prysm.ValidatorIndex.Decode.accept_function_spec_holds`). No
contract, no new hypothesis form.
-/

open Machine Runtime Prysm.PendingConsolidation.Code Codec
variable [Host]

namespace Prysm.PendingConsolidation

/-- The call block with one padding `nop`: `callq fn; nop; test %rax,%rax; je lok`. -/
def callDecNop (fn lok : String) : Program :=
  [Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.call (RelRegOrMem.rel ((ConstExpr.label fn).sub ConstExpr.after_current_instruction)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64 (Operation.nop 1)),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.test (RegOrMem.reg (Reg.low Reg64.rax Width.W64))
       (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rax Width.W64))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64 (Operation.jcc CondCode.z lok))]

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `calldec_seg` (`Codec/CalleeDecode.lean`) for the block `callDecNop`: the same pre / post, one more step. -/
theorem calldec_nop_seg (fn lok : String) (j j2 : Nat)
    (hA : (callDecNop fn lok).IsInfixAt Host.prog j) (hB : (callDecContinuationLabel lok).IsInfixAt Host.prog j2)
    (hl : label lok = Host.addrOf j2) (hC : U64CalleeAccept fn)
    (sp dst src aRet aFp aS2 : BitVec 64)
    (hRet : sp - 8 = aRet) (hFp : sp - 16 = aFp) (hS2 : sp + 8 = aS2)
    (rbp0 r140 guard : UInt64) (e8 rslot fp s2 c0 : List UInt8)
    (he8 : e8.length = 8) (hrs : rslot.length = 8) (hfp : fp.length = 8) (hs2 : s2.length = 8)
    (hc0 : c0.length = 8) (hguard : guard.toNat < aRet.toNat)
    (F : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140) (hrax : s.regs.rax.toBitVec = dst) (hrbx : s.regs.rbx.toBitVec = src)
    (hrcx : s.regs.rcx = 8)
    (h_mem : s.dmem =⋆ Eq (rslot.At aRet) ⋆ Eq (fp.At aFp) ⋆ Eq (s2.At aS2)
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
      ⋆ Eq (e8.At src) ⋆ Eq (c0.At dst) ⋆ F) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (j2 + 1) ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = { toBitVec := sp } ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        (Eq ((Int.toBytes 8 (Host.addrOf (j + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At aFp) ⋆ Eq ((Int.toBytes 8 src.toInt).At aS2)
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
          ⋆ Eq (e8.At src) ⋆ Eq (e8.At dst) ⋆ F) st.data.dmem)
      ⟨s, Host.addrOf j⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp hrbp hr14 hrax hrbx hrcx h_mem ⊢
  subst rsp rbp r14 rcx hRet hFp hS2 hrax hrbx
  step_directive hA callDecNop 0
  apply store_step_at _ _ (sp - 8) _ _ _ rslot _ _ (by segment_addr) (by ecancel) (by exact hrs)
  intro m1' H1
  simp only [Width.bytes, Width.bits] at H1
  unfold_step
  try rw [show sp - 8#64 = sp - 8 from rfl] at *
  refine eventually_trans _ _ _ _ (hC _ (Host.addrOf (j + 0 + 1)) e8 fp s2 c0 guard _
    he8 hfp hs2 hc0 rfl hguard
    (by dsimp only; rw [show sp - 8 - 8 = sp - 16 by bv_omega, show sp - 8 + 16 = sp + 8 by bv_omega]; ecancel)) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrax2, hrbx2, hrsp2, hrbp2, hr142, Hm2⟩
  dsimp only at hpc2 hrax2 hrbx2 hrsp2 hrbp2 hr142 Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := d2
  simp only at hrax2 hrbx2 hrsp2 hrbp2 hr142 Hm2
  rw [show ({ toBitVec := sp - 8 } + 8 : UInt64) = { toBitVec := sp } by
    apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega] at hrsp2
  subst rax2 rbx2 rsp2 rbp2 r142
  rw [show sp - 8 - 8 = sp - 16 by bv_omega, show sp - 8 + 16 = sp + 8 by bv_omega] at Hm2
  rw [show j + 0 + 1 = j + 1 from rfl] at Hm2
  step_directive hA callDecNop 1
  step_directive hA callDecNop 2
  intro _
  step_directive hA callDecNop 3
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  rw [hl]
  step_directive hB callDecContinuationLabel 0
  apply Eventually.done
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, by ecancel⟩

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- Head, directives 0–14: entry to the first argument set-up. -/
theorem Decode.head (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k)
    (s : MachineData) (ra guard : UInt64) (fp s1 s2 s4 ast : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h4 : s4.length = 8) (hast : ast.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx = 16) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 15) ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 80 }
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
  step_directive hk unmarshalSSZ 0
  step_directive hk unmarshalSSZ 1
  step_directive hk unmarshalSSZ 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk unmarshalSSZ 3
  split
  · rename_i h; exfalso
    simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  step_directive hk unmarshalSSZ 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1' H1
  simp only [Width.bytes, Width.bits] at H1
  unfold_step
  step_directive hk unmarshalSSZ 5
  step_directive hk unmarshalSSZ 6
  step_directive hk unmarshalSSZ 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by bv_omega) (by ecancel) (by exact h2)
  intro m2' H2
  simp only [Width.bytes, Width.bits] at H2
  unfold_step
  step_directive hk unmarshalSSZ 8
  step_directive hk unmarshalSSZ 9
  step_directive hk unmarshalSSZ 10
  split
  case isTrue h => exact absurd h (by decide)
  simp only [Effects.All]
  step_directive hk unmarshalSSZ 11
  apply store_step_at _ _ (rsp.toBitVec + 8) _ _ _ s1 _ _ (by bv_omega) (by ecancel) (by exact h1)
  intro m3' H3
  simp only [Width.bytes, Width.bits] at H3
  unfold_step
  step_directive hk unmarshalSSZ 12
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by bv_omega) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m5' H5
  simp only [Width.bytes, Width.bits] at H5
  unfold_step
  step_directive hk unmarshalSSZ 13
  apply store_step_at _ _ (rsp.toBitVec + 32) _ _ _ s4 _ _ (by bv_omega) (by ecancel) (by exact h4)
  intro m4' H4
  simp only [Width.bytes, Width.bits] at H4
  unfold_step
  step_directive hk unmarshalSSZ 14
  apply load_step _ _ _ _ (ast.take 1) _ _ (by ecancel) (by simp [hast])
  unfold_step
  intro _
  apply Eventually.done
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_right
  · rw [hcs]; simp only [Std.ExtHashMap.sep_assoc]; ecancel
  all_goals first
    | rfl
    | exact congrArg UInt64.ofBitVec (Prysm.PendingPartialWithdrawal.Decode.head_stack_pointer _)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Epilogue, directives 86–88: `add $0x48,%rsp; pop %rbp; retq`. -/
theorem Decode.epilogue (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k)
    (sp aFp aRa : BitVec 64) (hFp : sp + 72 = aFp) (hRa : sp + 80 = aRa)
    (fp0 ra : UInt64) (R : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp })
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 fp0.toBitVec.toInt).At aFp)
      ⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At aRa) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rax
        ∧ st.data.regs.rbx = s.regs.rbx ∧ st.data.regs.rsp = { toBitVec := sp + 88 }
        ∧ st.data.regs.rbp = fp0 ∧ st.data.regs.r14 = s.regs.r14 ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf (k + 86)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp h_mem ⊢
  subst rsp hFp hRa
  step_directive hk unmarshalSSZ 86
  step_directive hk unmarshalSSZ 87
  apply load_step_at _ _ (sp + 72) _ _ (Int.toBytes 8 fp0.toBitVec.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk unmarshalSSZ 88
  apply load_step_at _ _ (sp + 80) _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  apply Eventually.done
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | exact trivial
    | with_reducible rfl
    | rfl
    | (apply UInt64.toBitVec_inj.mp
       simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, Width.bits]
       done)
    | (apply UInt64.toBitVec_inj.mp; segment_addr)
set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- **Accept path of the real `(*v1alpha1.PendingConsolidation).UnmarshalSSZ` (Go 1.26.10)**; statement = the
hand statement `Decode.accept_statement` (unchanged), from the generated SourceIndex segments and hand steps. -/
theorem Decode.accept : Decode.accept_statement := by
  intro k hk hf kV hkV hfV in0 in1 hin0 hin1 s ra guard
    fp s1 s2 s4 sp1 rslot lo ast a8 a16 hfp h1 h2 h4 hsp1 hrs hlo hast ha8 ha16 R h_mem hguard hlen
  have hvi : U64CalleeAccept Prysm.ValidatorIndex.Code.unmarshalLabel := Prysm.ValidatorIndex.Decode.accept_function_spec_holds kV hkV hfV
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  have hg : guard.toNat < (rsp.toBitVec - 88).toNat := Prysm.PendingPartialWithdrawal.Decode.accept_guard _ _ hguard
  -- code facts of the hand-applied blocks
  have hRl := Codec.infix_sub (q := Codec.callArgReload false 96 8 112 (-8) 88 16) 48 hk
    (by simp only [unmarshalSSZ, Codec.callArgReload, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hC2 := Codec.infix_sub (q := callDecNop "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.UnmarshalSSZ_14d") 55 hk
    (by simp only [unmarshalSSZ, callDecNop, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hL2 := Codec.infix_sub (q := Codec.callDecContinuationLabel "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.UnmarshalSSZ_14d") 85 hk
    (by simp only [unmarshalSSZ, Codec.callDecContinuationLabel, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hl2 := Machine.label_at' hk hf (j := 85)
    (by simp only [unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  -- head: entry → directive 15
  refine eventually_trans _ _ _ _ (Decode.head k hk _ ra guard fp s1 s2 s4 ast hfp h1 h2 h4 hast _
    (by dsimp only; ecancel) (Nat.lt_of_le_of_lt (Nat.le_add_right _ 88) hguard) hlen) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, hrax1, hrbx1, Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 hrax1 hrbx1 Hm1
  subst hpc1
  -- SourceIndex: set-up 15–16 (generated)
  refine eventually_trans _ _ _ _ (Decode.generated_call_SourceIndex_arg k hk hf rax.toBitVec (rax.toBitVec + 8)
    (by simp only [Int64.toBitVec_ofNat]) d1 (by rw [hrax1])) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrsp2, hrbp2, hr142, hrbx2, hrax2, hrcx2, hmem2⟩
  dsimp only at hpc2 hrsp2 hrbp2 hr142 hrbx2 hrax2 hrcx2 hmem2
  subst hpc2
  -- SourceIndex: call block 17–19, label 47 (generated, hC discharged by Prysm.ValidatorIndex.Decode.accept_function_spec_holds)
  refine eventually_trans _ _ _ _ (Decode.generated_call_SourceIndex_call k hk hf hvi
    (rsp.toBitVec - 80) (rax.toBitVec + 8) rbx.toBitVec (rsp.toBitVec - 88) (rsp.toBitVec - 96) (rsp.toBitVec - 72)
    (by bv_omega) (by bv_omega) (by bv_omega)
    { toBitVec := rsp.toBitVec - 8 } r14 guard in0 rslot lo sp1 a8 hin0 hrs hlo hsp1 ha8 hg _ d2
    (hrsp2.trans hrsp1) (hrbp2.trans hrbp1) (hr142.trans hr141) hrax2 (by rw [hrbx2, hrbx1]) hrcx2
    (by rw [hmem2]; ecancel)) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrax3, hrbx3, hrsp3, hrbp3, hr143, Hm3⟩
  dsimp only at hpc3 hrax3 hrbx3 hrsp3 hrbp3 hr143 Hm3
  subst hpc3
  -- TargetIndex: set-up by reload 48–54 (existing lemma, by hand)
  refine eventually_trans _ _ _ _ (Codec.callarg_reload_seg false 96 8 112 (-8) 88 16 (k + 48) hRl
    (rsp.toBitVec - 80) rax.toBitVec rbx.toBitVec (rsp.toBitVec + 16) (rsp.toBitVec + 32) (rsp.toBitVec + 8)
    (rbx.toBitVec + 8) (rax.toBitVec + 16)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat])
    (by simp only [Int64.toBitVec_ofNat])
    (Int.toBytes 8 rdi.toBitVec.toInt) (Int.toBytes_length 8 _) _ d3 hrsp3 (by ecancel)) ?_
  rintro ⟨d4, pc4⟩ ⟨hpc4, hrsp4, hrbp4, hr144, hrbx4, hrax4, hrcx4, hmem4⟩
  dsimp only at hpc4 hrsp4 hrbp4 hr144 hrbx4 hrax4 hrcx4 hmem4
  subst hpc4
  -- TargetIndex: call block with nop 55–58, label 85 (hand lemma)
  refine eventually_trans _ _ _ _ (calldec_nop_seg _ _ (k + 55) (k + 85) hC2 hL2 hl2 hvi
    (rsp.toBitVec - 80) (rax.toBitVec + 16) (rbx.toBitVec + 8) (rsp.toBitVec - 88) (rsp.toBitVec - 96)
    (rsp.toBitVec - 72) (by bv_omega) (by bv_omega) (by bv_omega)
    { toBitVec := rsp.toBitVec - 8 } r14 guard in1
    (Int.toBytes 8 (Host.addrOf (k + 17 + 1)).toBitVec.toInt) (Int.toBytes 8 (rsp.toBitVec - 8).toInt)
    (Int.toBytes 8 rbx.toBitVec.toInt) a16
    hin1 (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) ha16 hg _ d4
    (hrsp4.trans hrsp3) (hrbp4.trans hrbp3) (hr144.trans hr143)
    hrax4 hrbx4 hrcx4
    (by rw [hmem4]; ecancel)) ?_
  rintro ⟨d5, pc5⟩ ⟨hpc5, hrax5, hrbx5, hrsp5, hrbp5, hr145, Hm5⟩
  dsimp only at hpc5 hrax5 hrbx5 hrsp5 hrbp5 hr145 Hm5
  subst hpc5
  -- epilogue 86–88
  refine eventually_trans _ _ _ _ (Decode.epilogue k hk (rsp.toBitVec - 80) (rsp.toBitVec - 8) rsp.toBitVec
    (by bv_omega) (by bv_omega) rbp ra _ d5 hrsp5 (by ecancel)) ?_
  rintro ⟨d6, pc6⟩ ⟨hpc6, hrax6, hrbx6, hrsp6, hrbp6, hr146, hmem6⟩
  dsimp only at hpc6 hrax6 hrbx6 hrsp6 hrbp6 hr146 hmem6
  apply Eventually.done
  rw [show k + 55 + 1 = k + 56 from rfl] at Hm5
  refine ⟨hpc6, hrax6.trans hrax5, hrbx6.trans hrbx5, ?_, hrbp6, hr146.trans hr145,
    Int.toBytes 8 (rbx.toBitVec + 8).toInt, Int.toBytes 8 (rsp.toBitVec - 8).toInt,
    Int.toBytes_length 8 _, Int.toBytes_length 8 _, ?_⟩
  · dsimp only; rw [hrsp6]; apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
  · dsimp only; rw [hmem6]; ecancel

end Prysm.PendingConsolidation
