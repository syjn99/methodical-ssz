import Fk.Contracts
import Fk.Frame
import Fk.LuRejectCall
import E2e.CpAccept
import E2e.Data

/-!
# `(*primitives.Epoch).UnmarshalSSZ`, reject `len(buf) ≠ 8` (Go 1.26.10 machine code)

    return fmt.Errorf("expected buffer of length %d received %d", e.SizeSSZ(), len(buf))

Directives: 9–10 `cmp $0x8,%rcx; je` not taken; 11–17 the 32-byte argument
array at rsp − 40 (two `movups %xmm15`, then `type:int`, `&8` (static box
`e2eEight`), 18–19 `convT64(len)`, 20–22 `type:int`, box; 23–28
`fmt.errorf(format, args, 2, 2)`; 29–30 `test %rax,%rax; jne L_b5` taken
(the contract gives rax ≠ 0; the `newobject` fallback 31–38 is not executed);
39–42 epilogue. Contracts: `ConvT64C Heap S` and the `FmtErrorfDDC` instance
with the format `E2e.Data.e2eEpFmt` (40 bytes) and the type word
`E2e.Data.e2eIntType_addr` (`type:int` of the Go 1.26.10 ELF); existing forms only.
`StaticBox` uses the table `Fk.Data.staticuint64s` at `Fk.Data.staticuint64s_addr` (the existing
contract form reads the Fk.Data namespace); `ep_static_table` shows that the Go 1.26.10 ELF's table
(`e2eStaticuint64s`) has the same bytes and `ep_static_addr` that the two addresses are the same
term (review e2e-r2 N3).
Standalone obligation: from `Checkpoint.UnmarshalSSZ` this path is unreachable.
-/

open Fk E2e.Code
variable [Host]

namespace E2e

set_option maxRecDepth 100000 in
theorem ep_static_table : E2e.Data.e2eStaticuint64s = Fk.Data.staticuint64s := by rfl
-- The address that `Fk.StaticBox` reads is the Go 1.26.10 label `runtime.staticuint64s` (review e2e-r2 N3).
theorem ep_static_addr : E2e.Data.e2eStaticuint64s_addr = Fk.Data.staticuint64s_addr := rfl
theorem ep_eight_bytes : E2e.Data.e2eEight = Int.toBytes 8 (8 : BitVec 64).toInt := by decide
theorem ep_fmt_len : E2e.Data.e2eEpFmt.length = 40 := by decide
theorem epr_eq (x : BitVec 64) (h : x - 8#64 = 0#64) : x = 8 := by bv_omega
theorem epr_call (x : BitVec 64) : x - 8#64 - 72 - 8#64 = x - 88 := by bv_omega
theorem epr_call2 (x : BitVec 64) : x - 80 - 8#64 = x - 88 := by bv_omega
theorem epr_ret (x : BitVec 64) : ({ toBitVec := x - 88 } + 8 : UInt64) = { toBitVec := x - 80 } := by
  apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega

theorem epr_args (a b c d : List UInt8) (ha : a.length = 8) (hb : b.length = 8) (hc : c.length = 8)
    (hd : d.length = 8) (x : BitVec 64) (X : DataMem → Prop) :
    X ⋆ Eq (a.At x) ⋆ Eq (b.At (x + 8)) ⋆ Eq (c.At (x + 16)) ⋆ Eq (d.At (x + 24))
      = X ⋆ Eq ((a ++ b ++ c ++ d).At x) := by
  rw [at_app (a ++ b ++ c) d (b := x + 24) (by simp [ha, hb, hc] <;> bv_omega) (by simp [ha, hb, hc, hd]),
    at_app (a ++ b) c (b := x + 16) (by simp [ha, hb] <;> bv_omega) (by simp [ha, hb, hc]),
    at_app a b (b := x + 8) (by simp [ha] <;> rfl) (by simp [ha, hb])]
  simp only [Std.ExtHashMap.sep_assoc]

theorem epr_sp (a b : List UInt8) (ha : a.length = 8) (hb : b.length = 32) (x : BitVec 64) (X : DataMem → Prop) :
    X ⋆ Eq (a.At x) ⋆ Eq (b.At (x + 8)) = X ⋆ Eq ((a ++ b).At x) := by
  rw [at_app a b (b := x + 8) (by simp [ha] <;> rfl) (by simp [ha, hb])]
  simp only [Std.ExtHashMap.sep_assoc]

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem ep_unmarshal_reject_len_main (k : Nat) (hk : EpUnmarshal.IsInfixAt Host.prog k)
    (hf : LabelsFresh EpUnmarshal k)
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
      ⋆ Eq (E2e.Data.e2eEpFmt.At E2e.Data.e2eEpFmt_addr) ⋆ Eq (E2e.Data.e2eEight.At E2e.Data.e2eEight_addr)
      ⋆ StaticBox 8 ⋆ StaticBox s.regs.rcx.toBitVec ⋆ Heap avail ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx ≠ 8) (hav : 8 + 40 + 40 + 8192 ≤ avail)
    (hct : ConvT64C Heap S) (hdd : FmtErrorfDDC Heap E2e.Data.e2eEpFmt E2e.Data.e2eIntType_addr S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax ≠ 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (bx : BitVec 64) (hb stk' sp' : List UInt8) (av' : Nat), stk'.length = S ∧ sp'.length = 40
          ∧ BoxIn bx s.regs.rcx.toBitVec hb ∧ av' ≤ avail ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 E2e.Data.e2eIntType_addr.toInt ++ Int.toBytes 8 E2e.Data.e2eEight_addr.toInt
              ++ Int.toBytes 8 E2e.Data.e2eIntType_addr.toInt ++ Int.toBytes 8 bx.toInt).At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (sp'.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 29)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (stk'.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (E2e.Data.e2eEpFmt.At E2e.Data.e2eEpFmt_addr) ⋆ Eq (E2e.Data.e2eEight.At E2e.Data.e2eEight_addr)
          ⋆ StaticBox 8 ⋆ StaticBox s.regs.rcx.toBitVec ⋆ Eq (hb.At bx) ⋆ Heap av' ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; simp only [UInt64.size] at *
  kat hk EpUnmarshal 0
  kat hk EpUnmarshal 1
  kat hk EpUnmarshal 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk EpUnmarshal 3
  split
  · rename_i h; exfalso
    simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk EpUnmarshal 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk EpUnmarshal 5
  kat hk EpUnmarshal 6
  kat hk EpUnmarshal 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by bv_omega) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk EpUnmarshal 8
  kat hk EpUnmarshal 9
  kat hk EpUnmarshal 10
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    exact hlen (UInt64.toBitVec_inj.mp (epr_eq _ h))
  simp only [Effects.All]
  kat hk EpUnmarshal 11
  kat hk EpUnmarshal 12
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  kunfold
  rw [show rsp.toBitVec - 8#64 - 72 + 40 = rsp.toBitVec - 40 by bv_omega]
  apply store_avx_step _ _ _ _ a40 _ _ (by ecancel) (by exact ha40) (by decide)
  intro m3 H3
  kunfold
  kat hk EpUnmarshal 13
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  kunfold
  rw [show rsp.toBitVec - 40 + 16 = rsp.toBitVec - 24 by bv_omega]
  apply store_avx_step _ _ _ _ a24 _ _ (by ecancel) (by exact ha24) (by decide)
  intro m4 H4
  kunfold
  rw [lr_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 40), lr_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 24),
    show rsp.toBitVec - 40 + 8 = rsp.toBitVec - 32 by bv_omega,
    show rsp.toBitVec - 24 + 8 = rsp.toBitVec - 16 by bv_omega] at H4
  kat hk EpUnmarshal 14
  kat hk EpUnmarshal 15
  apply store_step_at _ _ (rsp.toBitVec - 40) _ _ _ ((Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).take 8)
    _ _ (by eaddr) (by ecancel) (by rw [List.length_take, Int.toBytes_length]; rfl)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  kat hk EpUnmarshal 16
  kat hk EpUnmarshal 17
  apply store_step_at _ _ (rsp.toBitVec - 32) _ _ _ ((Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8)
    _ _ (by eaddr) (by ecancel) (by simp [Int.toBytes_length])
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  kat hk EpUnmarshal 18
  kat hk EpUnmarshal 19
  apply store_step_at _ _ (rsp.toBitVec - 88) _ _ _ rslot _ _ (epr_call _) (by ecancel) (by exact hrs)
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  rw [epr_call] at *
  refine eventually_trans _ _ _ _ (hct _ (Host.addrOf (k + 19 + 1)) avail stk sp8 _ (by omega) hstk hsp8
    (by dsimp only; rw [show rsp.toBitVec - 88 + 8 = rsp.toBitVec - 80 by bv_omega]; ecancel)) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrsp2, hr142, stk2, sp2, hb, av2, hstk2, hsp2, hbox, hav2a, hav2b, Hm2⟩
  dsimp only at hpc2 hrsp2 hr142 hbox Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := d2
  simp only at hrsp2 hr142 hbox Hm2
  rw [epr_ret] at hrsp2
  subst rsp2 r142
  rw [show rsp.toBitVec - 88 + 8 = rsp.toBitVec - 80 by bv_omega] at Hm2
  kat hk EpUnmarshal 20
  kat hk EpUnmarshal 21
  apply store_step_at _ _ (rsp.toBitVec - 24) _ _ _ ((Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).take 8)
    _ _ (by eaddr) (by ecancel) (by rw [List.length_take, Int.toBytes_length]; rfl)
  intro m8 H8
  simp only [Width.bytes, Width.bits] at H8
  kunfold
  kat hk EpUnmarshal 22
  apply store_step_at _ _ (rsp.toBitVec - 16) _ _ _ ((Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8)
    _ _ (by eaddr) (by ecancel) (by simp [Int.toBytes_length])
  intro m9 H9
  simp only [Width.bytes, Width.bits] at H9
  kunfold
  kat hk EpUnmarshal 23
  kat hk EpUnmarshal 24
  kat hk EpUnmarshal 25
  kat hk EpUnmarshal 26
  kat hk EpUnmarshal 27
  kat hk EpUnmarshal 28
  apply store_step_at _ _ (rsp.toBitVec - 88) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 19 + 1)).toBitVec.toInt) _ _
    (epr_call2 _) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m10 H10
  simp only [Width.bytes, Width.bits] at H10
  kunfold
  rw [epr_call2] at *
  rw [ep_eight_bytes] at H10
  simp only [E2e.Data.e2eIntType_addr, E2e.Data.e2eEight_addr, E2e.Data.e2eEpFmt_addr] at H10 ⊢
  refine eventually_trans _ _ _ _ (hdd _ (Host.addrOf (k + 28 + 1)) av2 (Int.toBytes 8 (8 : BitVec 64).toInt) hb stk2
    (sp2 ++ sp32) (label "runtime.gcbits._" + 1432).toBitVec 8 rax2.toBitVec rcx.toBitVec ?F
    (by rw [ep_fmt_len]; rfl) rfl rfl (Or.inr rfl) hbox hstk2 (by simp [hsp2, hsp32])
    (by rw [ep_fmt_len]; omega) ?hpre) ?_
  case hpre =>
    dsimp only
    simp only [E2e.Data.e2eIntType_addr]
    rw [show rsp.toBitVec - 80 + 40 = rsp.toBitVec - 40 by bv_omega,
      show rsp.toBitVec - 88 + 8 = rsp.toBitVec - 80 by bv_omega]
    rw [← epr_sp sp2 sp32 hsp2 hsp32 (rsp.toBitVec - 80)
      (Eq ((Int.toBytes 8 (Host.addrOf (k + 28 + 1)).toBitVec.toInt).At (rsp.toBitVec - 88))
        ⋆ Eq (stk2.At (rsp.toBitVec - 88 - BitVec.ofNat 64 S)))]
    rw [← epr_args _ _ _ _ (Int.toBytes_length _ _) (Int.toBytes_length _ _) (Int.toBytes_length _ _)
      (Int.toBytes_length _ _) (rsp.toBitVec - 40)
      (Eq ((Int.toBytes 8 (Host.addrOf (k + 28 + 1)).toBitVec.toInt).At (rsp.toBitVec - 88))
        ⋆ Eq (stk2.At (rsp.toBitVec - 88 - BitVec.ofNat 64 S)) ⋆ Eq (sp2.At (rsp.toBitVec - 80))
        ⋆ Eq (sp32.At (rsp.toBitVec - 80 + 8)) ⋆ Eq (Data.e2eEpFmt.At (label "go_string._" + 110057).toBitVec))]
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
  rw [epr_ret] at hrsp3
  subst rsp3 r143
  kat hk EpUnmarshal 29
  intro _
  kat hk EpUnmarshal 30
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    exact hrax3 (UInt64.toBitVec_inj.mp (by simpa using h))
  simp only [Effects.All]
  klabel hk hf EpUnmarshal 39
  kat hk EpUnmarshal 39
  kat hk EpUnmarshal 40
  kat hk EpUnmarshal 41
  apply load_step_at _ _ (rsp.toBitVec - 8) _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by eaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk EpUnmarshal 42
  apply load_step_at _ _ rsp.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by eaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨?_, hrax3, ?_, ?_, ?_, rax2.toBitVec, hb, stk3, sp3, av3, hstk3, hsp3, hbox, by omega, ?hmem⟩
  case hmem =>
    rw [ep_eight_bytes]
    simp only [E2e.Data.e2eIntType_addr, E2e.Data.e2eEight_addr, E2e.Data.e2eEpFmt_addr] at Hm3 ⊢
    rw [show k + 28 + 1 = k + 29 from rfl] at Hm3
    rw [show rsp.toBitVec - 88 + 8 = rsp.toBitVec - 80 by bv_omega,
      show rsp.toBitVec - 80 + 40 = rsp.toBitVec - 40 by bv_omega] at Hm3
    ecancel
  all_goals first
    | exact trivial
    | with_reducible rfl
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (apply UInt64.toBitVec_inj.mp; eaddr)

end E2e
