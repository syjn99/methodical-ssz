import Prysm.AttestationData.DecodeAcceptSource

/-!
# `(*v1alpha1.AttestationData).UnmarshalSSZ`, accept path, segment 4

    a.Target = new(Checkpoint)                      // always: the old pointer is overwritten
    if err = a.Target.UnmarshalSSZ(buf[88:128]); err != nil { return fmt.Errorf("Target: %w", err) }
    return err

Directive indices of `Prysm.AttestationData.Code.unmarshalSSZ`: 172 `L_2d9`, 173–174 `lea type:Checkpoint;
callq runtime.newobject`, 175–176 writeBarrier test (`jne`, not taken), 177–178 reload the
receiver, `jmp L_310`, 185 `L_310`, 186 store `Target`, 187–192 arguments (rbx = buf + 88,
rdi = cap − 88, rcx = 40) and `callq Checkpoint.UnmarshalSSZ`, 193–194 `test %rax,%rax;
je L_3a7`, 222 `L_3a7`, 223–225 epilogue and `retq` with the callee's nil error (rax = rbx = 0).
The text is segment 3's with the Target offsets and the epilogue.
-/

open Machine Runtime Prysm.AttestationData.Code
variable [Host]

namespace Prysm.AttestationData

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- Segment 4: from `L_2d9` (directive 172) to the return: a new Target object
(`NewobjectContract`), the Target decoder through `Prysm.Checkpoint.Decode.accept_function_spec`, and the epilogue. -/
theorem Decode.target (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (rsp0 r140 guard ra rbp0 : UInt64) (rcv bf : BitVec 64) (se sroot : List UInt8) (hse : se.length = 8)
    (hsroot : sroot.length = 32)
    (s4 q0 q1 rslot lo aT : List UInt8)
    (h4 : s4.length = 8) (hq0 : q0.length = 8) (hq1 : q1.length = 8) (hrs : rslot.length = 8)
    (haT : aT.length = 8)
    (R : DataMem → Prop) (S : Nat) (hS8 : 8 ≤ S) (hS : S < 2 ^ 60) (hlo : lo.length = S + 96)
    (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 104 ≤ avail)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := rsp0.toBitVec - 120 })
    (hrbp : s.regs.rbp = { toBitVec := rsp0.toBitVec - 8#64 }) (hr14 : s.regs.r14 = r140)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At rsp0.toBitVec)
      ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (rsp0.toBitVec - 8))
      ⋆ Eq ((Int.toBytes 8 rcv.toInt).At (rsp0.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 bf.toInt).At (rsp0.toBitVec + 16)) ⋆ Eq (s4.At (rsp0.toBitVec + 32))
      ⋆ Eq (q0.At (rsp0.toBitVec - 120)) ⋆ Eq (q1.At (rsp0.toBitVec - 112))
      ⋆ Eq (rslot.At (rsp0.toBitVec - 128)) ⋆ Eq (lo.At (rsp0.toBitVec - 224 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (aT.At (rcv + 56))
      ⋆ Eq (se.At (bf + 88)) ⋆ Eq (sroot.At (bf + 96))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat + 224 < rsp0.toNat)
    (hno : NewobjectContract Heap ElfData.PrysmTarget.typeCheckpoint_addr 72 (S + 96)) (hcp : Prysm.Checkpoint.Decode.accept_function_spec Heap S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = rsp0 + 8 ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        ∃ (ps p1 : BitVec 64) (lo' : List UInt8), lo'.length = S + 96 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At rsp0.toBitVec)
          ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (rsp0.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 rcv.toInt).At (rsp0.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 bf.toInt).At (rsp0.toBitVec + 16)) ⋆ Eq (s4.At (rsp0.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 ps.toInt).At (rsp0.toBitVec - 120))
          ⋆ Eq ((Int.toBytes 8 (bf + 88).toInt).At (rsp0.toBitVec - 112))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 193)).toBitVec.toInt).At (rsp0.toBitVec - 128))
          ⋆ Eq (lo'.At (rsp0.toBitVec - 224 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
          ⋆ Heap (avail - 72 - 32)
          ⋆ Eq ((Int.toBytes 8 ps.toInt).At (rcv + 56))
          ⋆ Eq ((List.replicate 8 0).At ps) ⋆ Eq (se.At (ps + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (ps + 16)) ⋆ Eq ((Int.toBytes 8 32).At (ps + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (ps + 32)) ⋆ Eq ((List.replicate 32 0).At (ps + 40))
          ⋆ Eq (sroot.At p1)
          ⋆ Eq (se.At (bf + 88)) ⋆ Eq (sroot.At (bf + 96))
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 172)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp hrbp hr14 h_mem ⊢
  subst rsp rbp r14
  have := rsp0.toNat_lt_size; have := guard.toNat_lt_size; simp only [UInt64.size] at *
  step_directive hk unmarshalSSZ 172
  step_directive hk unmarshalSSZ 173
  step_directive hk unmarshalSSZ 174
  apply store_step_at _ _ (rsp0.toBitVec - 128) _ _ _ rslot _ _ (Decode.accept_call _) (by ecancel) (by exact hrs)
  intro m2' H2
  simp only [Width.bytes, Width.bits] at H2
  unfold_step
  rw [Decode.accept_call] at *
  refine eventually_trans _ _ _ _ (hno _ (Host.addrOf (k + 174 + 1)) avail lo q0 _ rfl (by omega) hlo hq0
    (by dsimp only; rw [Decode.accept_low_address _ _ hS, show rsp0.toBitVec - 128 + 8 = rsp0.toBitVec - 120 by bv_omega]; ecancel)) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrsp3, hr143, hrbp3, stk3, sp3, hstk3, hsp3, Hm3⟩
  dsimp only at hpc3 hrsp3 hr143 hrbp3 Hm3
  subst hpc3
  obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,
    zmms3, flags3, mem3⟩ := d3
  simp only at hrsp3 hr143 hrbp3 Hm3
  rw [Decode.accept_ret] at hrsp3
  subst hrsp3 hr143 hrbp3
  rw [Decode.accept_low_address _ _ hS, show rsp0.toBitVec - 128 + 8 = rsp0.toBitVec - 120 by bv_omega, Decode.accept_fresh_object72] at Hm3
  step_directive hk unmarshalSSZ 175
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  unfold_step
  step_directive hk unmarshalSSZ 176
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  step_directive hk unmarshalSSZ 177
  apply load_step_at _ _ (rsp0.toBitVec + 8) _ _ (Int.toBytes 8 rcv.toInt) _ _ (by attestation_data_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk unmarshalSSZ 178
  label_address hk hf unmarshalSSZ 185
  step_directive hk unmarshalSSZ 185
  step_directive hk unmarshalSSZ 186
  apply store_step_at _ _ (rcv + 56) _ _ _ aT _ _ (by attestation_data_addr) (by ecancel) (by exact haT)
  intro m3' H3
  simp only [Width.bytes, Width.bits] at H3
  unfold_step
  step_directive hk unmarshalSSZ 187
  apply load_step_at _ _ (rsp0.toBitVec + 16) _ _ (Int.toBytes 8 bf.toInt) _ _ (by attestation_data_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk unmarshalSSZ 188
  step_directive hk unmarshalSSZ 189
  apply load_step_at _ _ (rsp0.toBitVec + 32) _ _ s4 _ _ (by attestation_data_addr) (by ecancel) (by exact h4)
  unfold_step
  step_directive hk unmarshalSSZ 190
  step_directive hk unmarshalSSZ 191
  step_directive hk unmarshalSSZ 192
  apply store_step_at _ _ (rsp0.toBitVec - 128) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 174 + 1)).toBitVec.toInt) _ _
    (Decode.accept_call _) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m4' H4
  simp only [Width.bytes, Width.bits] at H4
  unfold_step
  rw [Decode.accept_call] at *
  -- the callee frame in the S + 96 stack bytes
  obtain ⟨l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := Decode.frame_lengths stk3 S hstk3
  rw [Decode.frame_slices stk3 S] at H4
  try dsimp only at H4
  rw [Decode.frame_sep _ S hS _ _ _ _ _ _ _ _ _ l0 l1 l2 l3 l4 l5 l6 l7 l8, Decode.accept_split_argument_words _ _ l2] at H4
  rw [show (88 : BitVec 64) + bf = bf + 88 from BitVec.add_comm _ _]
  rw [show bf + 96 = bf + 88 + 8 by bv_omega] at H4
  refine eventually_trans _ _ _ _ (hcp _ (Host.addrOf (k + 192 + 1)) guard (avail - 72) se sroot _ sp3 q1 _ _ _
    ((((stk3.drop S).drop 8).take 24).take 8) (((((stk3.drop S).drop 8).take 24).drop 8).take 8)
    ((((stk3.drop S).drop 8).take 24).drop 16) _
    (List.replicate 8 0) (List.replicate 8 0) (List.replicate 8 0) (List.replicate 8 0) (List.replicate 8 0)
    (List.replicate 32 0) _ _
    hse hsroot l8 hsp3 hq1 l6 l5 l4 (by simp [hstk3]) (by simp [hstk3]) (by simp [hstk3]) l1
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) hS8 hS l0
    (Decode.accept_guard96 _ _ hguard) rfl (by omega)
    (by dsimp only
        rw [show rsp0.toBitVec - 128 - 8 = rsp0.toBitVec - 136 by bv_omega,
          show rsp0.toBitVec - 128 + 8 = rsp0.toBitVec - 120 by bv_omega,
          show rsp0.toBitVec - 128 + 16 = rsp0.toBitVec - 112 by bv_omega,
          show rsp0.toBitVec - 128 - 32 = rsp0.toBitVec - 160 by bv_omega,
          show rsp0.toBitVec - 128 - 40 = rsp0.toBitVec - 168 by bv_omega,
          show rsp0.toBitVec - 128 - 48 = rsp0.toBitVec - 176 by bv_omega,
          show rsp0.toBitVec - 128 - 72 = rsp0.toBitVec - 200 by bv_omega,
          show rsp0.toBitVec - 128 - 80 = rsp0.toBitVec - 208 by bv_omega,
          show rsp0.toBitVec - 128 - 88 = rsp0.toBitVec - 216 by bv_omega,
          show rsp0.toBitVec - 128 - 96 = rsp0.toBitVec - 224 by bv_omega]
        ecancel)) ?_
  rintro ⟨d5, pc5⟩ ⟨hpc5, hrax5, hrbx5, hrsp5, hrbp5, hr145, p1, scr, mm, rs', hscr, hmm, hrs', Hm5⟩
  dsimp only at hpc5 hrax5 hrbx5 hrsp5 hrbp5 hr145 Hm5
  subst hpc5
  obtain ⟨⟨rax5, rbx5, rcx5, rdx5, rsi5, rdi5, rsp5, rbp5, r85, r95, r105, r115, r125, r135, r145, r155⟩,
    zmms5, flags5, mem5⟩ := d5
  simp only at hrax5 hrbx5 hrsp5 hrbp5 hr145 Hm5
  rw [Decode.accept_ret] at hrsp5
  subst rax5 rbx5 rsp5 rbp5 r145
  try dsimp only at Hm5
  rw [show rsp0.toBitVec - 128 - 8 = rsp0.toBitVec - 136 by bv_omega,
    show rsp0.toBitVec - 128 + 8 = rsp0.toBitVec - 120 by bv_omega,
    show rsp0.toBitVec - 128 + 16 = rsp0.toBitVec - 112 by bv_omega,
    show rsp0.toBitVec - 128 - 32 = rsp0.toBitVec - 160 by bv_omega,
    show rsp0.toBitVec - 128 - 40 = rsp0.toBitVec - 168 by bv_omega,
    show rsp0.toBitVec - 128 - 48 = rsp0.toBitVec - 176 by bv_omega,
    show rsp0.toBitVec - 128 - 88 = rsp0.toBitVec - 216 by bv_omega,
    show rsp0.toBitVec - 128 - 96 = rsp0.toBitVec - 224 by bv_omega,
    show bf + 88 + 8 = bf + 96 by bv_omega] at Hm5
  step_directive hk unmarshalSSZ 193
  intro _
  step_directive hk unmarshalSSZ 194
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  label_address hk hf unmarshalSSZ 222
  step_directive hk unmarshalSSZ 222
  step_directive hk unmarshalSSZ 223
  step_directive hk unmarshalSSZ 224
  apply load_step_at _ _ (rsp0.toBitVec - 8) _ _ (Int.toBytes 8 rbp0.toBitVec.toInt) _ _ (by attestation_data_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk unmarshalSSZ 225
  apply load_step_at _ _ rsp0.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by attestation_data_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  rw [show k + 192 + 1 = k + 193 from rfl] at Hm5
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rax3.toBitVec, p1,
    Decode.frame scr rs' mm _ (Int.toBytes 8 0) (Int.toBytes 8 0) (Int.toBytes 8 p1.toInt) _ (Int.toBytes 8 (rsp0.toBitVec - 8#64).toInt),
    Decode.frame_length _ _ _ _ _ _ _ _ _ S hscr hrs' hmm l3 (Int.toBytes_length 8 _) (Int.toBytes_length 8 _)
      (Int.toBytes_length 8 _) l7 (Int.toBytes_length 8 _), ?_⟩
  rotate_right
  · rw [Decode.frame_sep _ S hS _ _ _ _ _ _ _ _ _ hscr hrs' hmm l3 (Int.toBytes_length 8 _) (Int.toBytes_length 8 _)
        (Int.toBytes_length 8 _) l7 (Int.toBytes_length 8 _)]
    ecancel
  all_goals first
    | exact trivial
    | with_reducible rfl
    | (apply UInt64.toBitVec_inj.mp
       simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, Width.bits]
       done)
    | (apply UInt64.toBitVec_inj.mp; attestation_data_addr)

end Prysm.AttestationData
