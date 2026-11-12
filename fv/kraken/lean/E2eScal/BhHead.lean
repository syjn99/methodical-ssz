import Runtime.Contracts
import Machine.Frame
import Prysm.Slot.DecodeAccept
import E2eScal.ViSpec

/-!
# Real Prysm `(*v1alpha1.BeaconBlockHeader).UnmarshalSSZ`, accept path, segment 1 (hold-out)

Hand-written: the text of `Prysm/AttestationData/DecodeAcceptHead.lean` with the Go 1.26.10
BeaconBlockHeader indices and stack offsets (frame `sub $0x60`, so every frame address is 16 bytes higher
than in AttestationData). Not generator output.

    func (b *BeaconBlockHeader) UnmarshalSSZ(buf []byte) error {
        if uint64(len(buf)) != 112 { return ssz.ErrSize }
        if err = b.Slot.UnmarshalSSZ(buf[0:8]); err != nil { return fmt.Errorf("Slot: %w", err) }
        if err = b.ProposerIndex.UnmarshalSSZ(buf[8:16]); err != nil { ... }
        ...

Directive indices of `E2eScal.BhCode.BhUnmarshal` (index = line − 1 of the `.S`):
2–3 stack guard, 4–7 prologue (`push %rbp`, `sub $0x60`, rbx spill at rsp + 16),
9–10 `cmp $0x70,%rcx; jne L_345`, 11–13 spills of rax, rdi, rbx at rsp + 8, + 32, + 16,
14 `test %al,(%rax)`, 15–17 `add $0x8,%rax; mov $0x8,%ecx; callq Slot.UnmarshalSSZ`,
18–19 `test %rax,%rax; je L_b9`, 46 `L_b9`, 47–55 arguments (54 `nop`) and
`callq ValidatorIndex.UnmarshalSSZ`, 56–57 `test; je L_154`, 85 `L_154`, 86–87 spills of rbx, rax (both 0) at rsp − 56, rsp − 64; ends at 88.

The callees are used only through `Prysm.Slot.Decode.accept_function_spec` / `ViUAccC`.
Stack (rsp = s.regs.rsp at entry): return slot; saved rbp at rsp − 8; argument spills at
rsp + 8 (receiver), rsp + 16 (buf.ptr), rsp + 32 (buf.cap); the callees' return slot at
rsp − 112; their saved rbp at rsp − 120 and their rbx spill at rsp − 96 (the frame word
0x8(%rsp) of this function).
-/

open Machine Runtime TestTarget Prysm.AttestationData.Code E2eScal.BhCode E2eScal Codec
variable [Host]

namespace E2eScal.Bh

theorem bha_slot (x : BitVec 64) : x - 8#64 - 96 - 8#64 = x - 112 := by bv_omega

theorem bha_call (x : BitVec 64) : x - 104 - 8#64 = x - 112 := by bv_omega

theorem bha_ret (x : BitVec 64) : ({ toBitVec := x - 112 } + 8 : UInt64) = { toBitVec := x - 104 } := by
  apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega

theorem bha_guard (x : BitVec 64) (g : Nat) (h : g + 112 < x.toNat) : g < (x - 112).toNat := by bv_omega

/-- Address equation by `toNat` and `omega` (as `kaddr`, with `Width.bits` reduced). -/
macro "bhaddr" : tactic => `(tactic| (
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_neg, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat,
    UInt64.toNat_toBitVec, UInt64.toBitVec_add, UInt64.toBitVec_ofNat, Width.bits, Nat.reducePow]
  all_goals omega))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- Segment 1: from the entry through `L_154` (directive 85) and the two spills 86–87 to directive 88, through the length check and
the Slot and ValidatorIndex callees. -/
theorem bh_e2e_head (k : Nat) (hk : BhUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh BhUnmarshal k)
    (hsl : Prysm.Slot.Decode.accept_function_spec) (hvi : ViUAccC)
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
  kat hk BhUnmarshal 15
  kat hk BhUnmarshal 16
  kat hk BhUnmarshal 17
  apply store_step_at _ _ (rsp.toBitVec - 112) _ _ _ rslot _ _ (bha_slot _) (by ecancel) (by exact hrs)
  intro m6' H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  rw [bha_slot] at *
  rw [show (8 : BitVec 64) + rax.toBitVec = rax.toBitVec + 8 from BitVec.add_comm _ _]
  refine eventually_trans _ _ _ _ (hsl _ (Host.addrOf (k + 17 + 1)) in0 lf sp1 a8 guard _
    hin0 hlf hsp1 ha8 rfl (bha_guard _ _ hguard)
    (by dsimp only; rw [show rsp.toBitVec - 112 - 8 = rsp.toBitVec - 120 by bv_omega,
      show rsp.toBitVec - 112 + 16 = rsp.toBitVec - 96 by bv_omega]; ecancel)) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrax2, hrbx2, hrsp2, hrbp2, hr142, Hm2⟩
  dsimp only at hpc2 hrax2 hrbx2 hrsp2 hrbp2 hr142 Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := d2
  simp only at hrax2 hrbx2 hrsp2 hrbp2 hr142 Hm2
  rw [bha_ret] at hrsp2
  subst rax2 rbx2 rsp2 rbp2 r142
  rw [show rsp.toBitVec - 112 - 8 = rsp.toBitVec - 120 by bv_omega,
    show rsp.toBitVec - 112 + 16 = rsp.toBitVec - 96 by bv_omega] at Hm2
  kat hk BhUnmarshal 18
  intro _
  kat hk BhUnmarshal 19
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf BhUnmarshal 46
  kat hk BhUnmarshal 46
  kat hk BhUnmarshal 47
  apply load_step_at _ _ (rsp.toBitVec + 16) _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by bhaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BhUnmarshal 48
  kat hk BhUnmarshal 49
  apply load_step_at _ _ (rsp.toBitVec + 32) _ _ (Int.toBytes 8 rdi.toBitVec.toInt) _ _ (by bhaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BhUnmarshal 50
  kat hk BhUnmarshal 51
  apply load_step_at _ _ (rsp.toBitVec + 8) _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by bhaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BhUnmarshal 52
  kat hk BhUnmarshal 53
  kat hk BhUnmarshal 54
  kat hk BhUnmarshal 55
  apply store_step_at _ _ (rsp.toBitVec - 112) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 17 + 1)).toBitVec.toInt) _ _
    (bha_call _) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m7' H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  rw [bha_call] at *
  rw [show (8 : BitVec 64) + rbx.toBitVec = rbx.toBitVec + 8 from BitVec.add_comm _ _,
    show (16 : BitVec 64) + rax.toBitVec = rax.toBitVec + 16 from BitVec.add_comm _ _]
  rw [show Eq ((Int.toBytes 8 (rsp.toBitVec - 8#64).toInt).At (rsp.toBitVec - 120))
      = Eq ((Int.toBytes 8 (rsp.toBitVec - 8#64).toInt).At (rsp.toBitVec - 120)) from rfl] at H7
  refine eventually_trans _ _ _ _ (hvi _ (Host.addrOf (k + 55 + 1)) in1 (Int.toBytes 8 (rsp.toBitVec - 8#64).toInt)
    (Int.toBytes 8 rbx.toBitVec.toInt) a16 guard _
    hin1 (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) ha16 rfl (bha_guard _ _ hguard)
    (by dsimp only; rw [show rsp.toBitVec - 112 - 8 = rsp.toBitVec - 120 by bv_omega,
      show rsp.toBitVec - 112 + 16 = rsp.toBitVec - 96 by bv_omega]; ecancel)) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrax3, hrbx3, hrsp3, hrbp3, hr143, Hm3⟩
  dsimp only at hpc3 hrax3 hrbx3 hrsp3 hrbp3 hr143 Hm3
  subst hpc3
  obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,
    zmms3, flags3, mem3⟩ := d3
  simp only at hrax3 hrbx3 hrsp3 hrbp3 hr143 Hm3
  rw [bha_ret] at hrsp3
  subst rax3 rbx3 rsp3 rbp3 r143
  rw [show rsp.toBitVec - 112 - 8 = rsp.toBitVec - 120 by bv_omega,
    show rsp.toBitVec - 112 + 16 = rsp.toBitVec - 96 by bv_omega] at Hm3
  kat hk BhUnmarshal 56
  intro _
  kat hk BhUnmarshal 57
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf BhUnmarshal 85
  kat hk BhUnmarshal 85
  kat hk BhUnmarshal 86
  apply store_step_at _ _ (rsp.toBitVec - 56) _ _ _ s30 _ _ (by bv_omega) (by ecancel) (by exact hs30)
  intro m8' H8
  simp only [Width.bytes, Width.bits] at H8
  kunfold
  kat hk BhUnmarshal 87
  apply store_step_at _ _ (rsp.toBitVec - 64) _ _ _ s28 _ _ (by bv_omega) (by ecancel) (by exact hs28)
  intro m9' H9
  simp only [Width.bytes, Width.bits] at H9
  kunfold
  apply Eventually.done
  rw [show k + 55 + 1 = k + 56 from rfl] at H9
  rw [show Eq ((Int.toBytes 8 (rsp.toBitVec - 8#64).toInt).At (rsp.toBitVec - 120))
      = Eq ((Int.toBytes 8 (rsp.toBitVec - 8#64).toInt).At (rsp.toBitVec - 120)) from rfl] at H9
  refine ⟨rfl, ?_, ?_, rfl, ?_⟩
  rotate_right
  · rw [hcs]; simp only [Std.ExtHashMap.sep_assoc]; ecancel
  all_goals (apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_sub, UInt64.toBitVec_ofNat]; try rfl)

end E2eScal.Bh
