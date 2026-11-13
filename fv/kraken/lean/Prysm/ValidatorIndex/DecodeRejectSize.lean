import Prysm.Epoch.DecodeRejectSize
import Prysm.BeaconBlockHeader.Code

/-!
# `(*primitives.ValidatorIndex).UnmarshalSSZ`, reject `len(buf) ≠ 8` (Go 1.26.10 machine code)

    return fmt.Errorf("expected buffer of length %d received %d", v.SizeSSZ(), len(buf))

Hand text: `Prysm.Epoch.Decode.reject_size` with the code constant `Prysm.Epoch.Code.unmarshalSSZ` replaced by
`unmarshalSSZ`. The two `.S` files are identical modulo labels, including the format operand
`go_string._+110057` (the Go linker keeps one copy of the string), so the `FmtErrorfDecimalDecimalContract` instance with
`ElfData.PrysmTarget.formatBufferLength` and `ElfData.PrysmTarget.typeInt_addr` is the same instance; `ConvT64Contract` likewise.
No new contract form. The helper lemmas `Prysm.Epoch.Decode.reject_*` and `Prysm.Epoch.Decode.reject_eight_bytes` / `Prysm.Epoch.Decode.reject_format_len` are reused.
-/

open Machine Runtime Prysm.ValidatorIndex.Code
variable [Host]

namespace Prysm.ValidatorIndex

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem Decode.reject_size (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh unmarshalSSZ k)
    (s : MachineData) (ra guard : UInt64) (fp s2 a40 a24 sp8 sp32 rslot : List UInt8)
    (hfp : fp.length = 8) (h2 : s2.length = 8) (ha40 : a40.length = 16) (ha24 : a24.length = 16)
    (hsp8 : sp8.length = 8) (hsp32 : sp32.length = 32) (hrs : rslot.length = 8)
    (S : Nat) (stk : List UInt8) (hstk : stk.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (a40.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (a24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (sp8.At (s.regs.rsp.toBitVec - 80)) ⋆ Eq (sp32.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (stk.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ElfData.PrysmTarget.formatBufferLength.At ElfData.PrysmTarget.formatBufferLength_addr) ⋆ Eq (ElfData.PrysmTarget.boxedEight.At ElfData.PrysmTarget.boxedEight_addr)
      ⋆ StaticBox 8 ⋆ StaticBox s.regs.rcx.toBitVec ⋆ Heap avail ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx ≠ 8) (hav : 8 + 40 + 40 + 8192 ≤ avail)
    (hct : ConvT64Contract Heap S) (hdd : FmtErrorfDecimalDecimalContract Heap ElfData.PrysmTarget.formatBufferLength ElfData.PrysmTarget.typeInt_addr S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax ≠ 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (bx : BitVec 64) (hb stk' sp' : List UInt8) (av' : Nat), stk'.length = S ∧ sp'.length = 40
          ∧ BoxIn bx s.regs.rcx.toBitVec hb ∧ av' ≤ avail ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 ElfData.PrysmTarget.typeInt_addr.toInt ++ Int.toBytes 8 ElfData.PrysmTarget.boxedEight_addr.toInt
              ++ Int.toBytes 8 ElfData.PrysmTarget.typeInt_addr.toInt ++ Int.toBytes 8 bx.toInt).At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (sp'.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 29)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (stk'.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ElfData.PrysmTarget.formatBufferLength.At ElfData.PrysmTarget.formatBufferLength_addr) ⋆ Eq (ElfData.PrysmTarget.boxedEight.At ElfData.PrysmTarget.boxedEight_addr)
          ⋆ StaticBox 8 ⋆ StaticBox s.regs.rcx.toBitVec ⋆ Eq (hb.At bx) ⋆ Heap av' ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; simp only [UInt64.size] at *
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
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  unfold_step
  step_directive hk unmarshalSSZ 5
  step_directive hk unmarshalSSZ 6
  step_directive hk unmarshalSSZ 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by bv_omega) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  unfold_step
  step_directive hk unmarshalSSZ 8
  step_directive hk unmarshalSSZ 9
  step_directive hk unmarshalSSZ 10
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    exact hlen (UInt64.toBitVec_inj.mp (Prysm.Epoch.Decode.reject_eq _ h))
  simp only [Effects.All]
  step_directive hk unmarshalSSZ 11
  step_directive hk unmarshalSSZ 12
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  unfold_step
  rw [show rsp.toBitVec - 8#64 - 72 + 40 = rsp.toBitVec - 40 by bv_omega]
  apply Machine.store_avx_step _ _ _ _ a40 _ _ (by ecancel) (by exact ha40) (by decide)
  intro m3 H3
  unfold_step
  step_directive hk unmarshalSSZ 13
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  unfold_step
  rw [show rsp.toBitVec - 40 + 16 = rsp.toBitVec - 24 by bv_omega]
  apply Machine.store_avx_step _ _ _ _ a24 _ _ (by ecancel) (by exact ha24) (by decide)
  intro m4 H4
  unfold_step
  rw [Machine.at_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 40), Machine.at_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 24),
    show rsp.toBitVec - 40 + 8 = rsp.toBitVec - 32 by bv_omega,
    show rsp.toBitVec - 24 + 8 = rsp.toBitVec - 16 by bv_omega] at H4
  step_directive hk unmarshalSSZ 14
  step_directive hk unmarshalSSZ 15
  apply store_step_at _ _ (rsp.toBitVec - 40) _ _ _ ((Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).take 8)
    _ _ (by checkpoint_addr) (by ecancel) (by rw [List.length_take, Int.toBytes_length]; rfl)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  unfold_step
  step_directive hk unmarshalSSZ 16
  step_directive hk unmarshalSSZ 17
  apply store_step_at _ _ (rsp.toBitVec - 32) _ _ _ ((Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8)
    _ _ (by checkpoint_addr) (by ecancel) (by simp [Int.toBytes_length])
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  unfold_step
  step_directive hk unmarshalSSZ 18
  step_directive hk unmarshalSSZ 19
  apply store_step_at _ _ (rsp.toBitVec - 88) _ _ _ rslot _ _ (Prysm.Epoch.Decode.reject_call _) (by ecancel) (by exact hrs)
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  unfold_step
  rw [Prysm.Epoch.Decode.reject_call] at *
  refine eventually_trans _ _ _ _ (hct _ (Host.addrOf (k + 19 + 1)) avail stk sp8 _ (by omega) hstk hsp8
    (by dsimp only; rw [show rsp.toBitVec - 88 + 8 = rsp.toBitVec - 80 by bv_omega]; ecancel)) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrsp2, hr142, stk2, sp2, hb, av2, hstk2, hsp2, hbox, hav2a, hav2b, Hm2⟩
  dsimp only at hpc2 hrsp2 hr142 hbox Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := d2
  simp only at hrsp2 hr142 hbox Hm2
  rw [Prysm.Epoch.Decode.reject_ret] at hrsp2
  subst rsp2 r142
  rw [show rsp.toBitVec - 88 + 8 = rsp.toBitVec - 80 by bv_omega] at Hm2
  step_directive hk unmarshalSSZ 20
  step_directive hk unmarshalSSZ 21
  apply store_step_at _ _ (rsp.toBitVec - 24) _ _ _ ((Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).take 8)
    _ _ (by checkpoint_addr) (by ecancel) (by rw [List.length_take, Int.toBytes_length]; rfl)
  intro m8 H8
  simp only [Width.bytes, Width.bits] at H8
  unfold_step
  step_directive hk unmarshalSSZ 22
  apply store_step_at _ _ (rsp.toBitVec - 16) _ _ _ ((Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8)
    _ _ (by checkpoint_addr) (by ecancel) (by simp [Int.toBytes_length])
  intro m9 H9
  simp only [Width.bytes, Width.bits] at H9
  unfold_step
  step_directive hk unmarshalSSZ 23
  step_directive hk unmarshalSSZ 24
  step_directive hk unmarshalSSZ 25
  step_directive hk unmarshalSSZ 26
  step_directive hk unmarshalSSZ 27
  step_directive hk unmarshalSSZ 28
  apply store_step_at _ _ (rsp.toBitVec - 88) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 19 + 1)).toBitVec.toInt) _ _
    (Prysm.Epoch.Decode.reject_second_call _) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m10 H10
  simp only [Width.bytes, Width.bits] at H10
  unfold_step
  rw [Prysm.Epoch.Decode.reject_second_call] at *
  rw [Prysm.Epoch.Decode.reject_eight_bytes] at H10
  simp only [ElfData.PrysmTarget.typeInt_addr, ElfData.PrysmTarget.boxedEight_addr, ElfData.PrysmTarget.formatBufferLength_addr] at H10 ⊢
  refine eventually_trans _ _ _ _ (hdd _ (Host.addrOf (k + 28 + 1)) av2 (Int.toBytes 8 (8 : BitVec 64).toInt) hb stk2
    (sp2 ++ sp32) (label "runtime.gcbits._" + 1432).toBitVec 8 rax2.toBitVec rcx.toBitVec ?F
    (by rw [Prysm.Epoch.Decode.reject_format_len]; rfl) rfl rfl (Or.inr rfl) hbox hstk2 (by simp [hsp2, hsp32])
    (by rw [Prysm.Epoch.Decode.reject_format_len]; omega) ?hpre) ?_
  case hpre =>
    dsimp only
    simp only [ElfData.PrysmTarget.typeInt_addr]
    rw [show rsp.toBitVec - 80 + 40 = rsp.toBitVec - 40 by bv_omega,
      show rsp.toBitVec - 88 + 8 = rsp.toBitVec - 80 by bv_omega]
    rw [← Prysm.Epoch.Decode.reject_join_spill sp2 sp32 hsp2 hsp32 (rsp.toBitVec - 80)
      (Eq ((Int.toBytes 8 (Host.addrOf (k + 28 + 1)).toBitVec.toInt).At (rsp.toBitVec - 88))
        ⋆ Eq (stk2.At (rsp.toBitVec - 88 - BitVec.ofNat 64 S)))]
    rw [← Prysm.Epoch.Decode.reject_args _ _ _ _ (Int.toBytes_length _ _) (Int.toBytes_length _ _) (Int.toBytes_length _ _)
      (Int.toBytes_length _ _) (rsp.toBitVec - 40)
      (Eq ((Int.toBytes 8 (Host.addrOf (k + 28 + 1)).toBitVec.toInt).At (rsp.toBitVec - 88))
        ⋆ Eq (stk2.At (rsp.toBitVec - 88 - BitVec.ofNat 64 S)) ⋆ Eq (sp2.At (rsp.toBitVec - 80))
        ⋆ Eq (sp32.At (rsp.toBitVec - 80 + 8)) ⋆ Eq (ElfData.PrysmTarget.formatBufferLength.At (label "go_string._" + 110057).toBitVec))]
    rw [show rsp.toBitVec - 80 + 8 = rsp.toBitVec - 72 by bv_omega,
      show rsp.toBitVec - 40 + 8 = rsp.toBitVec - 32 by bv_omega,
      show rsp.toBitVec - 40 + 16 = rsp.toBitVec - 24 by bv_omega,
      show rsp.toBitVec - 40 + 24 = rsp.toBitVec - 16 by bv_omega]
    ecancel
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrsp3, hr143, hrax3, stk3, sp3, av3, hstk3, hsp3, hav3, Hm3⟩
  dsimp only at hpc3 hrsp3 hr143 hrax3 Hm3
  subst hpc3
  obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,
    zmms3, flags3, mem3⟩ := d3
  simp only at hrsp3 hr143 hrax3 Hm3
  rw [Prysm.Epoch.Decode.reject_ret] at hrsp3
  subst rsp3 r143
  step_directive hk unmarshalSSZ 29
  intro _
  step_directive hk unmarshalSSZ 30
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    exact hrax3 (UInt64.toBitVec_inj.mp (by simpa using h))
  simp only [Effects.All]
  label_address hk hf unmarshalSSZ 39
  step_directive hk unmarshalSSZ 39
  step_directive hk unmarshalSSZ 40
  step_directive hk unmarshalSSZ 41
  apply load_step_at _ _ (rsp.toBitVec - 8) _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by checkpoint_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk unmarshalSSZ 42
  apply load_step_at _ _ rsp.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by checkpoint_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨?_, hrax3, ?_, ?_, ?_, rax2.toBitVec, hb, stk3, sp3, av3, hstk3, hsp3, hbox, by omega, ?hmem⟩
  case hmem =>
    rw [Prysm.Epoch.Decode.reject_eight_bytes]
    simp only [ElfData.PrysmTarget.typeInt_addr, ElfData.PrysmTarget.boxedEight_addr, ElfData.PrysmTarget.formatBufferLength_addr] at Hm3 ⊢
    rw [show k + 28 + 1 = k + 29 from rfl] at Hm3
    rw [show rsp.toBitVec - 88 + 8 = rsp.toBitVec - 80 by bv_omega,
      show rsp.toBitVec - 80 + 40 = rsp.toBitVec - 40 by bv_omega] at Hm3
    ecancel
  all_goals first
    | exact trivial
    | with_reducible rfl
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (apply UInt64.toBitVec_inj.mp; checkpoint_addr)

end Prysm.ValidatorIndex
