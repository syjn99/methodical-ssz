import Fk.Contracts
import Fk.Frame
import E2eAd.Prims
import E2eAd.Data

/-!
# Real Prysm `(*v1alpha1.AttestationData).UnmarshalSSZ`, accept path, segment 1

    func (a *AttestationData) UnmarshalSSZ(buf []byte) error {        // phase0.ssz.go:273
        if uint64(len(buf)) != 128 { return ssz.ErrSize }
        if err = a.Slot.UnmarshalSSZ(buf[0:8]); err != nil { return fmt.Errorf("Slot: %w", err) }
        if err = a.CommitteeIndex.UnmarshalSSZ(buf[8:16]); err != nil { ... }
        ...

Directive indices of `E2eAd.Code.AdUnmarshal` (the Go 1.26.10 `.S`, index = line − 1):
2–3 stack guard, 4–7 prologue (`push %rbp`, `sub $0x70`, rbx spill at rsp + 16),
9–10 `cmp $0x80,%rcx; jne L_3ad`, 11–13 spills of rax, rbx, rdi at rsp + 8, + 16, + 32,
14 `test %al,(%rax)` (nil check, byte 0 of `state`), 15–17 `add $0x8,%rax; mov $0x8,%ecx;
callq Slot.UnmarshalSSZ`, 18–19 `test %rax,%rax; je L_c7`, 47 `L_c7`, 48–55 arguments and
`callq CommitteeIndex.UnmarshalSSZ`, 56–57 `test; je L_167`, 85 `L_167` (end of this segment).

The callees are used only through `SlUAccC` / `CiUAccC` (hypotheses of this segment
lemma; `ad_e2e_accept_main` discharges them by `sl_uacc_holds` / `ci_uacc_holds`).

Stack (rsp = s.regs.rsp at entry): return slot; saved rbp at rsp − 8; argument spills at
rsp + 8 (receiver), rsp + 16 (buf.ptr), rsp + 32 (buf.cap); the callees' return slot at
rsp − 128; their saved rbp at rsp − 136 and their rbx spill at rsp − 112 (the frame word
0x8(%rsp) of this function).
-/

open Fk E2eAd.Code
variable [Host]

namespace E2eAd

theorem ada_slot (x : BitVec 64) : x - 8#64 - 112 - 8#64 = x - 128 := by bv_omega

theorem ada_call (x : BitVec 64) : x - 120 - 8#64 = x - 128 := by bv_omega

theorem ada_ret (x : BitVec 64) : ({ toBitVec := x - 128 } + 8 : UInt64) = { toBitVec := x - 120 } := by
  apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega

theorem ada_guard (x : BitVec 64) (g : Nat) (h : g + 224 < x.toNat) : g < (x - 128).toNat := by bv_omega

/-- Address equation by `toNat` and `omega` (as `kaddr`, with `Width.bits` reduced). -/
macro "adaddr" : tactic => `(tactic| (
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_neg, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat,
    UInt64.toNat_toBitVec, UInt64.toBitVec_add, UInt64.toBitVec_ofNat, Width.bits, Nat.reducePow]
  all_goals omega))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- Segment 1: from the entry to `L_167` (directive 85), through the length check and
the Slot and CommitteeIndex callees. -/
theorem ad_e2e_head (k : Nat) (hk : AdUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh AdUnmarshal k)
    (hsl : SlUAccC) (hci : CiUAccC)
    (in0 in1 : List UInt8) (hin0 : in0.length = 8) (hin1 : in1.length = 8)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 sp1 rslot lf ast a8 a16 : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h4 : s4.length = 8)
    (hsp1 : sp1.length = 8) (hrs : rslot.length = 8) (hlf : lf.length = 8)
    (hast : ast.length = 8) (ha8 : a8.length = 8) (ha16 : a16.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq (sp1.At (s.regs.rsp.toBitVec - 112)) ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 128))
      ⋆ Eq (lf.At (s.regs.rsp.toBitVec - 136))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (in0.At s.regs.rbx.toBitVec) ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 8))
      ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (a8.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (a16.At (s.regs.rax.toBitVec + 16)) ⋆ R)
    (hguard : guard.toNat + 224 < s.regs.rsp.toNat) (hlen : s.regs.rcx = 128) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 85) ∧ st.data.regs.rsp = s.regs.rsp - 120
        ∧ st.data.regs.rbp = s.regs.rsp - 8 ∧ st.data.regs.r14 = s.regs.r14 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rbx.toBitVec + 8).toInt).At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 56)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rsp.toBitVec - 8#64).toInt).At (s.regs.rsp.toBitVec - 136))
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
  kat hk AdUnmarshal 0
  kat hk AdUnmarshal 1
  kat hk AdUnmarshal 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk AdUnmarshal 3
  split
  · rename_i h; exfalso
    simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk AdUnmarshal 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1' H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk AdUnmarshal 5
  kat hk AdUnmarshal 6
  kat hk AdUnmarshal 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by bv_omega) (by ecancel) (by exact h2)
  intro m2' H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk AdUnmarshal 8
  kat hk AdUnmarshal 9
  kat hk AdUnmarshal 10
  split
  case isTrue h => exact absurd h (by decide)
  simp only [Effects.All]
  kat hk AdUnmarshal 11
  apply store_step_at _ _ (rsp.toBitVec + 8) _ _ _ s1 _ _ (by bv_omega) (by ecancel) (by exact h1)
  intro m3' H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk AdUnmarshal 12
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by bv_omega) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m4' H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  kat hk AdUnmarshal 13
  apply store_step_at _ _ (rsp.toBitVec + 32) _ _ _ s4 _ _ (by bv_omega) (by ecancel) (by exact h4)
  intro m5' H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  kat hk AdUnmarshal 14
  apply load_step _ _ _ _ (ast.take 1) _ _ (by ecancel) (by simp [hast])
  kunfold
  intro _
  kat hk AdUnmarshal 15
  kat hk AdUnmarshal 16
  kat hk AdUnmarshal 17
  apply store_step_at _ _ (rsp.toBitVec - 128) _ _ _ rslot _ _ (ada_slot _) (by ecancel) (by exact hrs)
  intro m6' H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  rw [ada_slot] at *
  rw [show (8 : BitVec 64) + rax.toBitVec = rax.toBitVec + 8 from BitVec.add_comm _ _]
  refine eventually_trans _ _ _ _ (hsl _ (Host.addrOf (k + 17 + 1)) in0 lf sp1 a8 guard _
    hin0 hlf hsp1 ha8 rfl (ada_guard _ _ hguard)
    (by dsimp only; rw [show rsp.toBitVec - 128 - 8 = rsp.toBitVec - 136 by bv_omega,
      show rsp.toBitVec - 128 + 16 = rsp.toBitVec - 112 by bv_omega]; ecancel)) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrax2, hrbx2, hrsp2, hrbp2, hr142, Hm2⟩
  dsimp only at hpc2 hrax2 hrbx2 hrsp2 hrbp2 hr142 Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := d2
  simp only at hrax2 hrbx2 hrsp2 hrbp2 hr142 Hm2
  rw [ada_ret] at hrsp2
  subst rax2 rbx2 rsp2 rbp2 r142
  rw [show rsp.toBitVec - 128 - 8 = rsp.toBitVec - 136 by bv_omega,
    show rsp.toBitVec - 128 + 16 = rsp.toBitVec - 112 by bv_omega] at Hm2
  kat hk AdUnmarshal 18
  intro _
  kat hk AdUnmarshal 19
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf AdUnmarshal 47
  kat hk AdUnmarshal 47
  kat hk AdUnmarshal 48
  apply load_step_at _ _ (rsp.toBitVec + 16) _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by adaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk AdUnmarshal 49
  kat hk AdUnmarshal 50
  apply load_step_at _ _ (rsp.toBitVec + 32) _ _ (Int.toBytes 8 rdi.toBitVec.toInt) _ _ (by adaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk AdUnmarshal 51
  kat hk AdUnmarshal 52
  apply load_step_at _ _ (rsp.toBitVec + 8) _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by adaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk AdUnmarshal 53
  kat hk AdUnmarshal 54
  kat hk AdUnmarshal 55
  apply store_step_at _ _ (rsp.toBitVec - 128) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 17 + 1)).toBitVec.toInt) _ _
    (ada_call _) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m7' H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  rw [ada_call] at *
  rw [show (8 : BitVec 64) + rbx.toBitVec = rbx.toBitVec + 8 from BitVec.add_comm _ _,
    show (16 : BitVec 64) + rax.toBitVec = rax.toBitVec + 16 from BitVec.add_comm _ _]
  rw [show Eq ((Int.toBytes 8 (rsp.toBitVec - 8#64).toInt).At (rsp.toBitVec - 136))
      = Eq ((Int.toBytes 8 (rsp.toBitVec - 8#64).toInt).At (rsp.toBitVec - 136)) from rfl] at H7
  refine eventually_trans _ _ _ _ (hci _ (Host.addrOf (k + 55 + 1)) in1 (Int.toBytes 8 (rsp.toBitVec - 8#64).toInt)
    (Int.toBytes 8 rbx.toBitVec.toInt) a16 guard _
    hin1 (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) ha16 rfl (ada_guard _ _ hguard)
    (by dsimp only; rw [show rsp.toBitVec - 128 - 8 = rsp.toBitVec - 136 by bv_omega,
      show rsp.toBitVec - 128 + 16 = rsp.toBitVec - 112 by bv_omega]; ecancel)) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrax3, hrbx3, hrsp3, hrbp3, hr143, Hm3⟩
  dsimp only at hpc3 hrax3 hrbx3 hrsp3 hrbp3 hr143 Hm3
  subst hpc3
  obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,
    zmms3, flags3, mem3⟩ := d3
  simp only at hrax3 hrbx3 hrsp3 hrbp3 hr143 Hm3
  rw [ada_ret] at hrsp3
  subst rax3 rbx3 rsp3 rbp3 r143
  rw [show rsp.toBitVec - 128 - 8 = rsp.toBitVec - 136 by bv_omega,
    show rsp.toBitVec - 128 + 16 = rsp.toBitVec - 112 by bv_omega] at Hm3
  kat hk AdUnmarshal 56
  intro _
  kat hk AdUnmarshal 57
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf AdUnmarshal 85
  apply Eventually.done
  rw [show k + 55 + 1 = k + 56 from rfl] at Hm3
  rw [show Eq ((Int.toBytes 8 (rsp.toBitVec - 8#64).toInt).At (rsp.toBitVec - 136))
      = Eq ((Int.toBytes 8 (rsp.toBitVec - 8#64).toInt).At (rsp.toBitVec - 136)) from rfl] at Hm3
  refine ⟨rfl, ?_, ?_, rfl, ?_⟩
  rotate_right
  · rw [hcs]; simp only [Std.ExtHashMap.sep_assoc]; ecancel
  all_goals (apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_sub, UInt64.toBitVec_ofNat]; try rfl)

end E2eAd
