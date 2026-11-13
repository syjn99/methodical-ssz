import Runtime.Contracts
import Machine.Frame
import Prysm.Epoch.DecodeAccept
import Prysm.ValidatorIndex.DecodeAcceptFunctionSpec
import Prysm.Deposit_Data.Statements
import Codec.CalleeDecode
import Codec.InlineUint64RegisterBase

/-!
# Real Prysm `(*v1alpha1.PendingPartialWithdrawal).UnmarshalSSZ`, accept path, Go 1.26.10 (first instance of the call-site lemmas)

Hand-written (after the hold-out; the type is development data now). The statement is
the independent hand statement `Prysm.PendingPartialWithdrawal.Decode.accept_statement` (`Prysm/Deposit_Data/Statements.lean`), unchanged. The hold-out evaluation did
not prove it (three attempts). Proof: a chain of `eventually_trans` over

* `Decode.head` (hand steps, directives 0–14: stack guard, prologue `sub $0x48`, length check, three spills, nil check),
* `callarg_first_seg` (15–16) and `calldec_seg` (17–19, label 47) for `Index` — callee `ValidatorIndex`,
* `callarg_lea_seg` (48–53), `u64dec_rr_seg` (54–55, `Amount`), `callarg_mov_seg` (56–58) and `calldec_seg`
  (59–61, label 88) for `WithdrawableEpoch` — callee `Epoch`,
* `Decode.epi` (hand steps, 89–91: `add $0x48,%rsp; pop %rbp; retq`).

The callees are used only through `U64CalleeAcc` (= the existing `Prysm.ValidatorIndex.Decode.accept_function_spec` / `Prysm.Epoch.Decode.accept_function_spec`, proved by
`Prysm.ValidatorIndex.Decode.accept_function_spec_holds` / `Prysm.Epoch.Decode.accept_function_spec_holds` from their machine code). No contract, no new hypothesis form.
Stack (rsp = entry rsp): callee return slot rsp − 88, callee saved rbp rsp − 96, callee rbx spill rsp − 72.
-/

open Machine Runtime Prysm.PendingPartialWithdrawal.Code Codec
variable [Host]

namespace Prysm.PendingPartialWithdrawal

theorem Decode.head_sp (x : BitVec 64) : x - 8#64 - 72 = x - 80 := by bv_omega

theorem Decode.accept_guard (x : BitVec 64) (g : Nat) (h : g + 88 < x.toNat) : g < (x - 88).toNat := by bv_omega

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
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx = 24) :
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
  intro m1' H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk unmarshalSSZ 5
  kat hk unmarshalSSZ 6
  kat hk unmarshalSSZ 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by bv_omega) (by ecancel) (by exact h2)
  intro m2' H2
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
  intro m3' H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk unmarshalSSZ 12
  apply store_step_at _ _ (rsp.toBitVec + 32) _ _ _ s4 _ _ (by bv_omega) (by ecancel) (by exact h4)
  intro m4' H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  kat hk unmarshalSSZ 13
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by bv_omega) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m5' H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  kat hk unmarshalSSZ 14
  apply load_step _ _ _ _ (ast.take 1) _ _ (by ecancel) (by simp [hast])
  kunfold
  intro _
  apply Eventually.done
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_right
  · rw [hcs]; simp only [Std.ExtHashMap.sep_assoc]; ecancel
  all_goals first
    | rfl
    | exact congrArg UInt64.ofBitVec (Decode.head_sp _)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Epilogue, directives 89–91: `add $0x48,%rsp; pop %rbp; retq`. -/
theorem Decode.epi (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k)
    (sp aFp aRa : BitVec 64) (hFp : sp + 72 = aFp) (hRa : sp + 80 = aRa)
    (fp0 ra : UInt64) (R : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp })
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 fp0.toBitVec.toInt).At aFp)
      ⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At aRa) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rax
        ∧ st.data.regs.rbx = s.regs.rbx ∧ st.data.regs.rsp = { toBitVec := sp + 88 }
        ∧ st.data.regs.rbp = fp0 ∧ st.data.regs.r14 = s.regs.r14 ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf (k + 89)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp h_mem ⊢
  subst rsp hFp hRa
  kat hk unmarshalSSZ 89
  kat hk unmarshalSSZ 90
  apply load_step_at _ _ (sp + 72) _ _ (Int.toBytes 8 fp0.toBitVec.toInt) _ _ (by saddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk unmarshalSSZ 91
  apply load_step_at _ _ (sp + 80) _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by saddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | exact trivial
    | with_reducible rfl
    | rfl
    | (apply UInt64.toBitVec_inj.mp
       simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, Width.bits]
       done)
    | (apply UInt64.toBitVec_inj.mp; saddr)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- **Accept path of the real `(*v1alpha1.PendingPartialWithdrawal).UnmarshalSSZ` (Go 1.26.10)**; statement =
the hand statement `Decode.accept_statement` (unchanged). -/
theorem Decode.accept : Decode.accept_statement := by
  intro k hk hf kV hkV hfV kE hkE hfE in0 in1 in2 hin0 hin1 hin2 s ra guard
    fp s1 s2 s4 sp1 rslot lo ast a8 a16 a24 hfp h1 h2 h4 hsp1 hrs hlo hast ha8 ha16 ha24 R h_mem hguard hlen
  have hvi : U64CalleeAcc Prysm.ValidatorIndex.Code.unmarshalLabel := Prysm.ValidatorIndex.Decode.accept_function_spec_holds kV hkV hfV
  have hep : U64CalleeAcc Prysm.Epoch.Code.unmarshalSSZLabel := Prysm.Epoch.Decode.accept_function_spec_holds kE hkE hfE
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  have hg : guard.toNat < (rsp.toBitVec - 88).toNat := Decode.accept_guard _ _ hguard
  -- code facts
  have hF1 := Codec.infix_sub (q := Codec.callArgFirst false 8) 15 hk
    (by simp only [unmarshalSSZ, Codec.callArgFirst, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hC1 := Codec.infix_sub (q := Codec.callDec "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ_b9") 17 hk
    (by simp only [unmarshalSSZ, Codec.callDec, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hL1 := Codec.infix_sub (q := Codec.callDecL "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ_b9") 47 hk
    (by simp only [unmarshalSSZ, Codec.callDecL, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hl1 := Machine.label_at' hk hf (j := 47)
    (by simp only [unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  have hLea := Codec.infix_sub (q := Codec.callArgLea 96 16 112 (-16) 88 24) 48 hk
    (by simp only [unmarshalSSZ, Codec.callArgLea, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hRR := Codec.infix_sub (q := Codec.u64DecRR Reg64.r8 8 16) 54 hk
    (by simp only [unmarshalSSZ, Codec.u64DecRR, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hX : Codec.U64RRReg Reg64.r8 := by decide
  have hMov := Codec.infix_sub (q := Codec.callArgMov) 56 hk
    (by simp only [unmarshalSSZ, Codec.callArgMov, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hC2 := Codec.infix_sub (q := Codec.callDec "github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ_159") 59 hk
    (by simp only [unmarshalSSZ, Codec.callDec, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hL2 := Codec.infix_sub (q := Codec.callDecL "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ_159") 88 hk
    (by simp only [unmarshalSSZ, Codec.callDecL, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero])
  have hl2 := Machine.label_at' hk hf (j := 88)
    (by simp only [unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  -- head: entry → directive 15
  refine eventually_trans _ _ _ _ (Decode.head k hk _ ra guard fp s1 s2 s4 ast hfp h1 h2 h4 hast _
    (by dsimp only; ecancel) (Nat.lt_of_le_of_lt (Nat.le_add_right _ 88) hguard) hlen) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, hrax1, hrbx1, Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 hrax1 hrbx1 Hm1
  subst hpc1
  -- Index: set-up 15–16
  refine eventually_trans _ _ _ _ (Codec.callarg_first_seg false 8 (k + 15) hF1 rax.toBitVec (rax.toBitVec + 8)
    (by simp only [Int64.toBitVec_ofNat]) d1 (by rw [hrax1])) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrsp2, hrbp2, hr142, hrbx2, hrax2, hrcx2, hmem2⟩
  dsimp only at hpc2 hrsp2 hrbp2 hr142 hrbx2 hrax2 hrcx2 hmem2
  subst hpc2
  -- Index: call block 17–19, label 47
  refine eventually_trans _ _ _ _ (Codec.calldec_seg _ _ (k + 17) (k + 47) hC1 hL1 hl1 hvi
    (rsp.toBitVec - 80) (rax.toBitVec + 8) rbx.toBitVec (rsp.toBitVec - 88) (rsp.toBitVec - 96) (rsp.toBitVec - 72)
    (by bv_omega) (by bv_omega) (by bv_omega)
    { toBitVec := rsp.toBitVec - 8 } r14 guard in0 rslot lo sp1 a8 hin0 hrs hlo hsp1 ha8 hg _ d2
    (hrsp2.trans hrsp1) (hrbp2.trans hrbp1) (hr142.trans hr141) hrax2 (by rw [hrbx2, hrbx1]) hrcx2
    (by rw [hmem2]; ecancel)) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrax3, hrbx3, hrsp3, hrbp3, hr143, Hm3⟩
  dsimp only at hpc3 hrax3 hrbx3 hrsp3 hrbp3 hr143 Hm3
  subst hpc3
  -- WithdrawableEpoch: set-up, first part 48–53
  refine eventually_trans _ _ _ _ (Codec.callarg_lea_seg 96 16 112 (-16) 88 24 (k + 48) hLea
    (rsp.toBitVec - 80) rax.toBitVec rbx.toBitVec (rsp.toBitVec + 16) (rsp.toBitVec + 32) (rsp.toBitVec + 8)
    (rbx.toBitVec + 16) (rax.toBitVec + 24)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat])
    (by simp only [Int64.toBitVec_ofNat])
    (Int.toBytes 8 rdi.toBitVec.toInt) (Int.toBytes_length 8 _) _ d3 hrsp3 (by ecancel)) ?_
  rintro ⟨d4, pc4⟩ ⟨hpc4, hrsp4, hrbp4, hr144, hrbx4, hrdx4, hrax4, hrsi4, hmem4⟩
  dsimp only at hpc4 hrsp4 hrbp4 hr144 hrbx4 hrdx4 hrax4 hrsi4 hmem4
  subst hpc4
  -- Amount: 54–55
  refine eventually_trans _ _ _ _ (Codec.u64dec_rr_seg Reg64.r8 hX 8 16 (k + 54) hRR
    rbx.toBitVec rax.toBitVec (rbx.toBitVec + 8) (rax.toBitVec + 16)
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    in1 a16 hin1 ha16 _ d4 hrbx4 hrax4 (by rw [hmem4]; ecancel)) ?_
  rintro ⟨d5, pc5⟩ ⟨hpc5, hrsp5, hrbp5, hr145, hrax5, hrbx5, hreg5, Hm5⟩
  dsimp only at hpc5 hrsp5 hrbp5 hr145 hrax5 hrbx5 hreg5 Hm5
  subst hpc5
  have hrsi5 : d5.regs.rsi.toBitVec = rax.toBitVec + 24 := (hreg5 Reg64.rsi (by decide)).trans hrsi4
  have hrdx5 : d5.regs.rdx.toBitVec = rbx.toBitVec + 16 := (hreg5 Reg64.rdx (by decide)).trans hrdx4
  -- WithdrawableEpoch: set-up, second part 56–58
  refine eventually_trans _ _ _ _ (Codec.callarg_mov_seg (k + 56) hMov d5) ?_
  rintro ⟨d6, pc6⟩ ⟨hpc6, hrsp6, hrbp6, hr146, hrax6, hrbx6, hrcx6, hmem6⟩
  dsimp only at hpc6 hrsp6 hrbp6 hr146 hrax6 hrbx6 hrcx6 hmem6
  subst hpc6
  -- WithdrawableEpoch: call block 59–61, label 88
  refine eventually_trans _ _ _ _ (Codec.calldec_seg _ _ (k + 59) (k + 88) hC2 hL2 hl2 hep
    (rsp.toBitVec - 80) (rax.toBitVec + 24) (rbx.toBitVec + 16) (rsp.toBitVec - 88) (rsp.toBitVec - 96)
    (rsp.toBitVec - 72) (by bv_omega) (by bv_omega) (by bv_omega)
    { toBitVec := rsp.toBitVec - 8 } r14 guard in2
    (Int.toBytes 8 (Host.addrOf (k + 17 + 1)).toBitVec.toInt) (Int.toBytes 8 (rsp.toBitVec - 8).toInt)
    (Int.toBytes 8 rbx.toBitVec.toInt) a24
    hin2 (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) ha24 hg _ d6
    (hrsp6.trans (hrsp5.trans (hrsp4.trans hrsp3))) (hrbp6.trans (hrbp5.trans (hrbp4.trans hrbp3)))
    (hr146.trans (hr145.trans (hr144.trans hr143)))
    (by rw [hrax6]; exact hrsi5) (by rw [hrbx6]; exact hrdx5) hrcx6
    (by rw [hmem6]; ecancel)) ?_
  rintro ⟨d7, pc7⟩ ⟨hpc7, hrax7, hrbx7, hrsp7, hrbp7, hr147, Hm7⟩
  dsimp only at hpc7 hrax7 hrbx7 hrsp7 hrbp7 hr147 Hm7
  subst hpc7
  -- epilogue 89–91
  refine eventually_trans _ _ _ _ (Decode.epi k hk (rsp.toBitVec - 80) (rsp.toBitVec - 8) rsp.toBitVec
    (by bv_omega) (by bv_omega) rbp ra _ d7 hrsp7 (by ecancel)) ?_
  rintro ⟨d8, pc8⟩ ⟨hpc8, hrax8, hrbx8, hrsp8, hrbp8, hr148, hmem8⟩
  dsimp only at hpc8 hrax8 hrbx8 hrsp8 hrbp8 hr148 hmem8
  apply Eventually.done
  rw [show k + 59 + 1 = k + 60 from rfl] at Hm7
  refine ⟨hpc8, hrax8.trans hrax7, hrbx8.trans hrbx7, ?_, hrbp8, hr148.trans hr147,
    Int.toBytes 8 (rbx.toBitVec + 16).toInt, Int.toBytes 8 (rsp.toBitVec - 8).toInt,
    Int.toBytes_length 8 _, Int.toBytes_length 8 _, ?_⟩
  · dsimp only; rw [hrsp8]; apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
  · dsimp only; rw [hmem8]; ecancel

end Prysm.PendingPartialWithdrawal
