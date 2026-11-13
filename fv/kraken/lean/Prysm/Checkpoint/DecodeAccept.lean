import Runtime.Contracts
import Machine.Frame
import Prysm.Epoch.DecodeAccept
import Prysm.ElfData.PrysmTarget

/-!
# Real Prysm `(*v1alpha1.Checkpoint).UnmarshalSSZ`, accept path, Go 1.26.10 machine code

    func (c *Checkpoint) UnmarshalSSZ(buf []byte) error {
        if uint64(len(buf)) != 40 { return ssz.ErrSize }
        if err = c.Epoch.UnmarshalSSZ(buf[0:8]); err != nil { return fmt.Errorf("Epoch: %w", err) }
        c.Root = make([]byte, 0, 32); c.Root = append(c.Root, buf[8:40]...); return err }

Receiver: the protoc struct (`attestation.pb.go:277`, gc amd64 layout of
`prysm/ir/ir-mainnet.json`): `state` at 0 (8 bytes), `Epoch` at 8, `Root` at 16
(ptr, len, cap), `unknownFields` at 40 (24) and `sizeCache` at 64 (4) + 4 bytes
of padding (the 32-byte chunk `ctl`). Size 72.

Directive indices of `Prysm.Checkpoint.Code.unmarshalSSZ` (the Go 1.26.10 `.S`): 2–3 guard,
4–7 prologue (`sub $0x50`, rbx spill), 9–10 `cmp $0x28,%rcx; jne`, 11–12 spills,
13 `test %al,(%rax)` (nil check, reads byte 0 of `state`), 14–17 `add $0x8,%rax;
mov $0x8,%ecx; callq Epoch.UnmarshalSSZ`, 18–19 `test %rax,%rax; je L_b4`,
47 `L_b4`, 48–49 save the nil error at rsp − 40 / rsp − 48, 50–53 `makeslice`,
54–58 `Root.len = 0`, `Root.cap = 32`, writeBarrier test, 63 `L_ff`, 64–65 save
and store `Root.ptr`, 66–69 `memmove`, 70–77 `Root.len = Root.cap = 32`,
writeBarrier test, `jmp L_157`, 84–90 store `Root.ptr`, return the saved error.

The Epoch callee is used through `Prysm.Epoch.Decode.accept_function_spec`, discharged by `Prysm.Epoch.Decode.accept_function_spec_holds` from
the Epoch code's place in the host (`kE`, `hkE`, `hfE`): the statement has no
hypothesis about Epoch's behaviour.

Stack (rsp = s.regs.rsp at entry): return slot; saved rbp at rsp − 8; spills of
rax, rbx at rsp + 8, rsp + 16; locals at rsp − 32 (`Root.ptr`), rsp − 40, rsp − 48
(the error words); the 24-byte callee argument area at rsp − 88 (`m0 m1 m2`;
Epoch's rbx spill is `m1`, makeslice's spill is all of it); the callees' return
slot at rsp − 96; `S` scratch bytes below it (`S ≥ 8`: Epoch's saved rbp is its
top 8 bytes). Untouched on this path, so in `R`: rsp − 24 … rsp − 9 and rsp − 64
… rsp − 49.
-/

open Machine Runtime Prysm.Checkpoint.Code
variable [Host]

namespace Prysm.Checkpoint

theorem Decode.accept_slot (x : BitVec 64) : x - 8#64 - 80 - 8#64 = x - 96 := by bv_omega

theorem Decode.accept_call (x : BitVec 64) : x - 88 - 8#64 = x - 96 := by bv_omega

theorem Decode.accept_ret (x : BitVec 64) : ({ toBitVec := x - 96 } + 8 : UInt64) = { toBitVec := x - 88 } := by
  apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega

theorem Decode.accept_guard (x : BitVec 64) (g : Nat) (h : g + 96 < x.toNat) : g < (x - 96).toNat := by bv_omega

/-- Address equation by `toNat` and `omega` (as `kaddr`, with `Width.bits` reduced). -/
macro "checkpoint_addr" : tactic => `(tactic| (
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_neg, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat,
    UInt64.toNat_toBitVec, UInt64.toBitVec_add, UInt64.toBitVec_ofNat, Width.bits, Nat.reducePow]
  all_goals omega))

theorem Decode.accept_ofNat (S : Nat) (h8 : 8 ≤ S) (hS : S < 2 ^ 60) :
    BitVec.ofNat 64 S = BitVec.ofNat 64 (S - 8) + 8 := by
  apply BitVec.eq_of_toNat_eq; simp; omega

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- The accept path from `L_b4` (directive 47, after the Epoch callee returned nil)
to the return: the state that the first part of `Decode.accept` reaches.
`rsp0`, `rax0`, `rbx0`, `rbp0`, `r140` are the registers at the entry of
`UnmarshalSSZ`. -/
theorem Decode.accept_tail (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (e8 root : List UInt8) (he8 : e8.length = 8) (hroot : root.length = 32)
    (ra guard rax0 rbx0 rbp0 r140 rsp0 : UInt64)
    (l20 l28 l30 m0 m2 cst cP cL cC ctl : List UInt8)
    (hl20 : l20.length = 8) (hl28 : l28.length = 8) (hl30 : l30.length = 8) (hm0 : m0.length = 8)
    (hm2 : m2.length = 8) (hcst : cst.length = 8)
    (hcP : cP.length = 8) (hcL : cL.length = 8) (hcC : cC.length = 8) (hctl : ctl.length = 32)
    (R : DataMem → Prop) (S : Nat) (hS8 : 8 ≤ S) (hS : S < 2 ^ 60) (scratch : List UInt8) (hsc : scratch.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (s : MachineData) (hrax : s.regs.rax = 0) (hrbx : s.regs.rbx = 0)
    (hrsp : s.regs.rsp = { toBitVec := rsp0.toBitVec - 88 }) (hrbp : s.regs.rbp = { toBitVec := rsp0.toBitVec - 8#64 })
    (hr14 : s.regs.r14 = r140)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At rsp0.toBitVec)
      ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (rsp0.toBitVec - 8))
      ⋆ Eq ((Int.toBytes 8 rax0.toBitVec.toInt).At (rsp0.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 rbx0.toBitVec.toInt).At (rsp0.toBitVec + 16))
      ⋆ Eq (l20.At (rsp0.toBitVec - 32)) ⋆ Eq (l28.At (rsp0.toBitVec - 40)) ⋆ Eq (l30.At (rsp0.toBitVec - 48))
      ⋆ Eq (m2.At (rsp0.toBitVec - 72)) ⋆ Eq ((Int.toBytes 8 rbx0.toBitVec.toInt).At (rsp0.toBitVec - 80))
      ⋆ Eq (m0.At (rsp0.toBitVec - 88))
      ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 17 + 1)).toBitVec.toInt).At (rsp0.toBitVec - 96))
      ⋆ Eq ((scratch.take (S - 8)).At (rsp0.toBitVec - 96 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 (rsp0.toBitVec - 8#64).toInt).At (rsp0.toBitVec - 104))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (e8.At rbx0.toBitVec) ⋆ Eq (root.At (rbx0.toBitVec + 8))
      ⋆ Eq (cst.At rax0.toBitVec) ⋆ Eq (e8.At (rax0.toBitVec + 8))
      ⋆ Eq (cP.At (rax0.toBitVec + 16)) ⋆ Eq (cL.At (rax0.toBitVec + 24))
      ⋆ Eq (cC.At (rax0.toBitVec + 32)) ⋆ Eq (ctl.At (rax0.toBitVec + 40))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hsp : 96 < rsp0.toNat) (hav : 32 ≤ avail)
    (hms : MakesliceC Heap ElfData.PrysmTarget.typeUint8_addr 1 S) (hmm : MemmoveC S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = rsp0 + 8 ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        ∃ (p : BitVec 64) (scr mm : List UInt8), scr.length = S ∧ mm.length = 24 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At rsp0.toBitVec)
          ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (rsp0.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 rax0.toBitVec.toInt).At (rsp0.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 rbx0.toBitVec.toInt).At (rsp0.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (rsp0.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 0).At (rsp0.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 0).At (rsp0.toBitVec - 48))
          ⋆ Eq (mm.At (rsp0.toBitVec - 88))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 70)).toBitVec.toInt).At (rsp0.toBitVec - 96))
          ⋆ Eq (scr.At (rsp0.toBitVec - 96 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
          ⋆ Heap (avail - 32)
          ⋆ Eq (e8.At rbx0.toBitVec) ⋆ Eq (root.At (rbx0.toBitVec + 8))
          ⋆ Eq (cst.At rax0.toBitVec) ⋆ Eq (e8.At (rax0.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (rax0.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (rax0.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (rax0.toBitVec + 32))
          ⋆ Eq (ctl.At (rax0.toBitVec + 40)) ⋆ Eq (root.At p)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 47)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrax hrbx hrsp hrbp hr14 h_mem ⊢
  subst rax rbx rsp rbp r14
  have := rsp0.toNat_lt_size; simp only [UInt64.size] at *
  kat hk unmarshalSSZ 47
  kat hk unmarshalSSZ 48
  apply store_step_at _ _ (rsp0.toBitVec - 40) _ _ _ l28 _ _ (by checkpoint_addr) (by ecancel) (by exact hl28)
  intro m6' H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  kat hk unmarshalSSZ 49
  apply store_step_at _ _ (rsp0.toBitVec - 48) _ _ _ l30 _ _ (by checkpoint_addr) (by ecancel) (by exact hl30)
  intro m7' H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  kat hk unmarshalSSZ 50
  kat hk unmarshalSSZ 51
  intro _
  kat hk unmarshalSSZ 52
  kat hk unmarshalSSZ 53
  apply store_step_at _ _ (rsp0.toBitVec - 96) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 17 + 1)).toBitVec.toInt) _ _
    (Decode.accept_call _) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m8' H8
  simp only [Width.bytes, Width.bits] at H8
  kunfold
  rw [Decode.accept_call] at *
  have hjs : Eq ((scratch.take (S - 8) ++ Int.toBytes 8 (rsp0.toBitVec - 8#64).toInt).At
      (rsp0.toBitVec - 96 - BitVec.ofNat 64 S)) = Eq ((scratch.take (S - 8)).At (rsp0.toBitVec - 96 - BitVec.ofNat 64 S))
        ⋆ Eq ((Int.toBytes 8 (rsp0.toBitVec - 8#64).toInt).At (rsp0.toBitVec - 104)) := by
    refine at_app _ _ ?_ (by simp only [List.length_append, List.length_take, hsc, Int.toBytes_length]; omega)
    rw [List.length_take, hsc, Nat.min_eq_left (by omega), Decode.accept_ofNat S hS8 hS]
    bv_omega
  have hjm : Eq ((m0 ++ (Int.toBytes 8 rbx0.toBitVec.toInt ++ m2)).At (rsp0.toBitVec - 88)) =
      Eq (m0.At (rsp0.toBitVec - 88)) ⋆ Eq ((Int.toBytes 8 rbx0.toBitVec.toInt).At (rsp0.toBitVec - 80))
        ⋆ Eq (m2.At (rsp0.toBitVec - 72)) := by
    rw [at_app m0 _ (b := rsp0.toBitVec - 80) (by rw [hm0]; bv_omega)
        (by simp only [List.length_append, hm0, hm2, Int.toBytes_length]; omega),
      at_app _ m2 (b := rsp0.toBitVec - 72) (by rw [Int.toBytes_length]; bv_omega)
        (by simp only [hm2, Int.toBytes_length]; omega),
      Std.ExtHashMap.sep_assoc]
  have hjs88 : ∀ x : BitVec 64, x - 96 + 8 = x - 88 := fun x => by bv_omega
  have hjsX : ∀ X : DataMem → Prop, X ⋆ Eq ((scratch.take (S - 8) ++ Int.toBytes 8 (rsp0.toBitVec - 8#64).toInt).At
      (rsp0.toBitVec - 96 - BitVec.ofNat 64 S)) = X ⋆ Eq ((scratch.take (S - 8)).At (rsp0.toBitVec - 96 - BitVec.ofNat 64 S))
        ⋆ Eq ((Int.toBytes 8 (rsp0.toBitVec - 8#64).toInt).At (rsp0.toBitVec - 104)) := by
    intro X; rw [hjs, Std.ExtHashMap.sep_assoc]
  have hjmX : ∀ X : DataMem → Prop, X ⋆ Eq ((m0 ++ (Int.toBytes 8 rbx0.toBitVec.toInt ++ m2)).At (rsp0.toBitVec - 88)) =
      X ⋆ Eq (m0.At (rsp0.toBitVec - 88)) ⋆ Eq ((Int.toBytes 8 rbx0.toBitVec.toInt).At (rsp0.toBitVec - 80))
        ⋆ Eq (m2.At (rsp0.toBitVec - 72)) := by
    intro X; rw [hjm, ← Std.ExtHashMap.sep_assoc, ← Std.ExtHashMap.sep_assoc]
  let hret := Eq ((Int.toBytes 8 (Host.addrOf (k + 53 + 1)).toBitVec.toInt).At (rsp0.toBitVec - 96))
  let hlo := Eq ((scratch.take (S - 8)).At (rsp0.toBitVec - 96 - BitVec.ofNat 64 S))
  let hhi := Eq ((Int.toBytes 8 (rsp0.toBitVec - 8#64).toInt).At (rsp0.toBitVec - 104))
  refine eventually_trans _ _ _ _ (hms _ (Host.addrOf (k + 53 + 1)) 32 avail
    (scratch.take (S - 8) ++ Int.toBytes 8 (rsp0.toBitVec - 8#64).toInt) (m0 ++ (Int.toBytes 8 rbx0.toBitVec.toInt ++ m2)) _
    rfl (by simp) (by rfl) (by omega) (by unfold maxAlloc; omega) (by omega) (by simp only [List.length_append, List.length_take, hsc, Int.toBytes_length]; omega)
    (by simp only [List.length_append, hm0, hm2, Int.toBytes_length])
    (by dsimp only; rw [hjs88 rsp0.toBitVec, hjsX hret, hjmX (hret ⋆ hlo ⋆ hhi)]; dsimp only [hret, hlo, hhi]; ecancel)) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrsp3, hr143, hrbp3, stk3, spm3, hstk3, hspm3, Hm3⟩
  dsimp only at hpc3 hrsp3 hr143 hrbp3 Hm3
  subst hpc3
  obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,
    zmms3, flags3, mem3⟩ := d3
  simp only at hrsp3 hr143 hrbp3 Hm3
  rw [Decode.accept_ret] at hrsp3
  subst hrsp3 hr143 hrbp3
  rw [show rsp0.toBitVec - 96 + 8 = rsp0.toBitVec - 88 by bv_omega] at Hm3
  kat hk unmarshalSSZ 54
  apply load_step_at _ _ (rsp0.toBitVec + 8) _ _ (Int.toBytes 8 rax0.toBitVec.toInt) _ _ (by checkpoint_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk unmarshalSSZ 55
  apply store_step_at _ _ (rax0.toBitVec + 24) _ _ _ cL _ _ (by checkpoint_addr) (by ecancel) (by exact hcL)
  intro m9' H9
  simp only [Width.bytes, Width.bits] at H9
  kunfold
  kat hk unmarshalSSZ 56
  apply store_step_at _ _ (rax0.toBitVec + 32) _ _ _ cC _ _ (by checkpoint_addr) (by ecancel) (by exact hcC)
  intro m10' H10
  simp only [Width.bytes, Width.bits] at H10
  kunfold
  kat hk unmarshalSSZ 57
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk unmarshalSSZ 58
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf unmarshalSSZ 63
  kat hk unmarshalSSZ 63
  kat hk unmarshalSSZ 64
  apply store_step_at _ _ (rsp0.toBitVec - 32) _ _ _ l20 _ _ (by checkpoint_addr) (by ecancel) (by exact hl20)
  intro m11' H11
  simp only [Width.bytes, Width.bits] at H11
  kunfold
  kat hk unmarshalSSZ 65
  apply store_step_at _ _ (rax0.toBitVec + 16) _ _ _ cP _ _ (by checkpoint_addr) (by ecancel) (by exact hcP)
  intro m12' H12
  simp only [Width.bytes, Width.bits] at H12
  kunfold
  kat hk unmarshalSSZ 66
  apply load_step_at _ _ (rsp0.toBitVec + 16) _ _ (Int.toBytes 8 rbx0.toBitVec.toInt) _ _ (by checkpoint_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk unmarshalSSZ 67
  kat hk unmarshalSSZ 68
  kat hk unmarshalSSZ 69
  apply store_step_at _ _ (rsp0.toBitVec - 96) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 53 + 1)).toBitVec.toInt) _ _
    (Decode.accept_call _) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m13' H13
  simp only [Width.bytes, Width.bits] at H13
  kunfold
  rw [Decode.accept_call] at *
  refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (k + 69 + 1)) root (List.replicate (1 * 32) 0) stk3 _
    (by rw [hroot]; rfl) (by simp [hroot]) hstk3
    (by dsimp only; rw [show (8 : BitVec 64) + rbx0.toBitVec = rbx0.toBitVec + 8 from BitVec.add_comm _ _];
        ecancel)) ?_
  rintro ⟨d4, pc4⟩ ⟨hpc4, hrsp4, hr144, hrbp4, stk4, hstk4, Hm4⟩
  dsimp only at hpc4 hrsp4 hr144 hrbp4 Hm4
  subst hpc4
  obtain ⟨⟨rax4, rbx4, rcx4, rdx4, rsi4, rdi4, rsp4, rbp4, r84, r94, r104, r114, r124, r134, r144, r154⟩,
    zmms4, flags4, mem4⟩ := d4
  simp only at hrsp4 hr144 hrbp4 Hm4
  rw [Decode.accept_ret] at hrsp4
  subst hrsp4 hr144 hrbp4
  rw [show (8 : BitVec 64) + rbx0.toBitVec = rbx0.toBitVec + 8 from BitVec.add_comm _ _] at Hm4
  kat hk unmarshalSSZ 70
  apply load_step_at _ _ (rsp0.toBitVec + 8) _ _ (Int.toBytes 8 rax0.toBitVec.toInt) _ _ (by checkpoint_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk unmarshalSSZ 71
  apply store_step_at _ _ (rax0.toBitVec + 24) _ _ _ (Int.toBytes 8 (BitVec.toInt (0 : BitVec 64))) _ _ (by checkpoint_addr)
    (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m14' H14
  simp only [Width.bytes, Width.bits] at H14
  kunfold
  kat hk unmarshalSSZ 72
  apply store_step_at _ _ (rax0.toBitVec + 32) _ _ _ (Int.toBytes 8 (BitVec.toInt (32 : BitVec 64))) _ _ (by checkpoint_addr)
    (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m15' H15
  simp only [Width.bytes, Width.bits] at H15
  kunfold
  kat hk unmarshalSSZ 73
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk unmarshalSSZ 74
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk unmarshalSSZ 75
  apply load_step_at _ _ (rsp0.toBitVec - 32) _ _ (Int.toBytes 8 rax3.toBitVec.toInt) _ _ (by checkpoint_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk unmarshalSSZ 76
  kat hk unmarshalSSZ 77
  klabel hk hf unmarshalSSZ 84
  kat hk unmarshalSSZ 84
  kat hk unmarshalSSZ 85
  apply store_step_at _ _ (rax0.toBitVec + 16) _ _ _ (Int.toBytes 8 rax3.toBitVec.toInt) _ _ (by checkpoint_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m16' H16
  simp only [Width.bytes, Width.bits] at H16
  kunfold
  kat hk unmarshalSSZ 86
  apply load_step_at _ _ (rsp0.toBitVec - 48) _ _ (Int.toBytes 8 (0#64).toInt) _ _ (by checkpoint_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk unmarshalSSZ 87
  apply load_step_at _ _ (rsp0.toBitVec - 40) _ _ (Int.toBytes 8 (0#64).toInt) _ _ (by checkpoint_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk unmarshalSSZ 88
  kat hk unmarshalSSZ 89
  apply load_step_at _ _ (rsp0.toBitVec - 8) _ _ (Int.toBytes 8 rbp0.toBitVec.toInt) _ _ (by checkpoint_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk unmarshalSSZ 90
  apply load_step_at _ _ rsp0.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by checkpoint_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rax3.toBitVec, stk4, spm3, hstk4, hspm3, ?_⟩
  rotate_right
  · simp only [Nat.one_mul, show Int.toBytes 8 (BitVec.toInt (32 : BitVec 64)) = Int.toBytes 8 32 by decide,
      show Int.toBytes 8 (32#64).toInt = Int.toBytes 8 32 by decide,
      show Int.toBytes 8 (0#64).toInt = Int.toBytes 8 0 by decide,
      show Int.toBytes 8 (BitVec.toInt (0 : BitVec 64)) = Int.toBytes 8 0 by decide] at H16 ⊢
    rw [show k + 69 + 1 = k + 70 from rfl] at H16
    ecancel
  all_goals first
    | exact trivial
    | with_reducible rfl
    | (apply UInt64.toBitVec_inj.mp
       simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, Width.bits]
       done)
    | (apply UInt64.toBitVec_inj.mp; checkpoint_addr)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem Decode.accept (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (kE : Nat) (hkE : Prysm.Epoch.Code.unmarshalSSZ.IsInfixAt Host.prog kE) (hfE : LabelsFresh Prysm.Epoch.Code.unmarshalSSZ kE)
    (e8 root : List UInt8) (he8 : e8.length = 8) (hroot : root.length = 32)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 l20 l28 l30 m0 m1 m2 rslot cst c0 cP cL cC ctl : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (hl20 : l20.length = 8)
    (hl28 : l28.length = 8) (hl30 : l30.length = 8) (hm0 : m0.length = 8) (hm1 : m1.length = 8)
    (hm2 : m2.length = 8) (hrs : rslot.length = 8) (hcst : cst.length = 8) (hc0 : c0.length = 8)
    (hcP : cP.length = 8) (hcL : cL.length = 8) (hcC : cC.length = 8) (hctl : ctl.length = 32)
    (R : DataMem → Prop) (S : Nat) (hS8 : 8 ≤ S) (hS : S < 2 ^ 60) (scratch : List UInt8) (hsc : scratch.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l20.At (s.regs.rsp.toBitVec - 32)) ⋆ Eq (l28.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (l30.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (m2.At (s.regs.rsp.toBitVec - 72)) ⋆ Eq (m1.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (m0.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 96 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (e8.At s.regs.rbx.toBitVec) ⋆ Eq (root.At (s.regs.rbx.toBitVec + 8))
      ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq (c0.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (cP.At (s.regs.rax.toBitVec + 16)) ⋆ Eq (cL.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32)) ⋆ Eq (ctl.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat + 96 < s.regs.rsp.toNat) (hlen : s.regs.rcx = 40) (hav : 32 ≤ avail)
    (hms : MakesliceC Heap ElfData.PrysmTarget.typeUint8_addr 1 S) (hmm : MemmoveC S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (p : BitVec 64) (scr mm : List UInt8), scr.length = S ∧ mm.length = 24 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 0).At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 0).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (mm.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 70)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 96 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 32)
          ⋆ Eq (e8.At s.regs.rbx.toBitVec) ⋆ Eq (root.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq (e8.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (ctl.At (s.regs.rax.toBitVec + 40)) ⋆ Eq (root.At p)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  have hep : Prysm.Epoch.Decode.accept_function_spec := Prysm.Epoch.Decode.accept_function_spec_holds kE hkE hfE
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  subst hlen
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; simp only [UInt64.size] at *
  -- byte 0 of `state` (read by the nil check) and the top 8 scratch bytes (Epoch's saved rbp)
  have hcs : Eq (cst.At rax.toBitVec) = Eq ((cst.take 1).At rax.toBitVec) ⋆ Eq ((cst.drop 1).At (rax.toBitVec + 1)) := by
    conv => lhs; rw [← List.take_append_drop 1 cst]
    exact at_app _ _ (by rw [List.length_take, hcst]; rfl) (by simp [hcst])
  have hscr : Eq (scratch.At (rsp.toBitVec - 96 - BitVec.ofNat 64 S)) =
      Eq ((scratch.take (S - 8)).At (rsp.toBitVec - 96 - BitVec.ofNat 64 S))
        ⋆ Eq ((scratch.drop (S - 8)).At (rsp.toBitVec - 104)) := by
    conv => lhs; rw [← List.take_append_drop (S - 8) scratch]
    refine at_app _ _ ?_ (by simp [hsc]; omega)
    rw [List.length_take, hsc, Nat.min_eq_left (by omega), Decode.accept_ofNat S hS8 hS]
    bv_omega
  have hcsX : ∀ X : DataMem → Prop, X ⋆ Eq (cst.At rax.toBitVec) =
      X ⋆ Eq ((cst.take 1).At rax.toBitVec) ⋆ Eq ((cst.drop 1).At (rax.toBitVec + 1)) := by
    intro X; rw [hcs, Std.ExtHashMap.sep_assoc]
  rw [hcs, hscr] at h_mem
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
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by bv_omega) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m4' H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  kat hk unmarshalSSZ 13
  apply load_step _ _ _ _ (cst.take 1) _ _ (by ecancel) (by simp [hcst])
  kunfold
  intro _
  kat hk unmarshalSSZ 14
  kat hk unmarshalSSZ 15
  kat hk unmarshalSSZ 16
  kat hk unmarshalSSZ 17
  apply store_step_at _ _ (rsp.toBitVec - 96) _ _ _ rslot _ _ (Decode.accept_slot _) (by ecancel) (by exact hrs)
  intro m5' H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  rw [Decode.accept_slot] at *
  rw [show (8 : BitVec 64) + rax.toBitVec = rax.toBitVec + 8 from BitVec.add_comm _ _]
  refine eventually_trans _ _ _ _ (hep _ (Host.addrOf (k + 17 + 1)) e8 (scratch.drop (S - 8)) m1 c0 guard _
    he8 (by simp [hsc]; omega) hm1 hc0 rfl (Decode.accept_guard _ _ hguard)
    (by dsimp only; rw [show rsp.toBitVec - 96 - 8 = rsp.toBitVec - 104 by bv_omega,
      show rsp.toBitVec - 96 + 16 = rsp.toBitVec - 80 by bv_omega]; ecancel)) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrax2, hrbx2, hrsp2, hrbp2, hr142, Hm2⟩
  dsimp only at hpc2 hrax2 hrbx2 hrsp2 hrbp2 hr142 Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := d2
  simp only at hrax2 hrbx2 hrsp2 hrbp2 hr142 Hm2
  rw [Decode.accept_ret] at hrsp2
  subst rax2 rbx2 rsp2 rbp2 r142
  rw [show rsp.toBitVec - 96 - 8 = rsp.toBitVec - 104 by bv_omega,
    show rsp.toBitVec - 96 + 16 = rsp.toBitVec - 80 by bv_omega] at Hm2
  kat hk unmarshalSSZ 18
  intro _
  kat hk unmarshalSSZ 19
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf unmarshalSSZ 47
  exact Decode.accept_tail k hk hf e8 root he8 hroot ra guard rax rbx rbp r14 rsp l20 l28 l30 m0 m2 cst cP cL cC ctl
    hl20 hl28 hl30 hm0 hm2 hcst hcP hcL hcC hctl R S hS8 hS scratch hsc Heap avail _ rfl rfl rfl rfl rfl
    (by dsimp only; rw [hcsX]
        rw [show Eq ((Int.toBytes 8 (rsp.toBitVec - 8#64).toInt).At (rsp.toBitVec - 104))
              = Eq ((Int.toBytes 8 (rsp.toBitVec - 8#64).toInt).At (rsp.toBitVec - 104)) from rfl,
            show Eq ((Int.toBytes 8 (Host.addrOf (k + 17 + 1)).toBitVec.toInt).At (rsp.toBitVec - 96))
              = Eq ((Int.toBytes 8 (Host.addrOf (k + 17 + 1)).toBitVec.toInt).At (rsp.toBitVec - 96)) from rfl] at Hm2
        ecancel)
    (by omega) hav hms hmm

end Prysm.Checkpoint
