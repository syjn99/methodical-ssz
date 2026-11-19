module

public import Codec.SegmentAddress
public import Runtime.Contracts
public import Prysm.ElfData.PrysmTarget
public import Prysm.SingleAttestation.DecodeAcceptHead
public import Prysm.SingleAttestation.Code

@[expose] public section

/-!
# `(*v1alpha1.SingleAttestation).UnmarshalSSZ`, accept path, Signature segment

    c.Signature = make([]byte, 0, 96)
    c.Signature = append(c.Signature, buf[144:240]...)
    return err

Directive indices of `Prysm.SingleAttestation.Code.unmarshalSSZ`: 136 `L_234`, 137–138 spill of the nil error (rax, rbx)
at rsp0 − 80 and rsp0 − 72, 139–142 `makeslice(uint8, 0, 96)`, 143–145 reload the receiver, len = 0, cap = 96,
146–147 writeBarrier test (`je L_282`, taken), 152 `L_282`, 153–154 the Signature pointer at rsp0 − 64 and in the receiver,
155–159 `memmove(psig, buf + 144, 96)`, 160–162 len = cap = 96, 163–166 writeBarrier test (`jne`, not taken), the pointer
from rsp0 − 64, `jmp L_2e2`, 173 `L_2e2`, 174 the pointer store, 175–176 the nil error, 177–179 epilogue.
The proof text follows the Signature part of `Prysm.IndexedAttestation.Decode.accept` (its directives 217–260).
-/

open Machine Runtime Prysm.SingleAttestation.Code
variable [Host]

namespace Prysm.SingleAttestation

-- Measured cause: `label_address` for directive 173 unfolds the 198-directive program literal `unmarshalSSZ` with `simp`;
-- at the default `maxRecDepth` (512) that `simp` stops with "maximum recursion depth has been reached"; 1024 passes.
set_option maxRecDepth 1024 in
/-- Signature segment: from `L_234` (directive 136) to the return. -/
theorem Decode.signature (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (rsp0 r140 ra rbp0 : UInt64) (rcv bf : BitVec 64) (sig : List UInt8) (hsig : sig.length = 96)
    (l28 l30 l38 spA rslot lo aP aL aC : List UInt8)
    (hl28 : l28.length = 8) (hl30 : l30.length = 8) (hl38 : l38.length = 8) (hspA : spA.length = 24)
    (hrs : rslot.length = 8) (haP : aP.length = 8) (haL : aL.length = 8) (haC : aC.length = 8)
    (R : DataMem → Prop) (S : Nat) (hlo : lo.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 96 ≤ avail)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := rsp0.toBitVec - 120 })
    (hrbp : s.regs.rbp = { toBitVec := rsp0.toBitVec - 8#64 }) (hr14 : s.regs.r14 = r140)
    (hrax : s.regs.rax = 0) (hrbx : s.regs.rbx = 0)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At rsp0.toBitVec)
      ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (rsp0.toBitVec - 8))
      ⋆ Eq ((Int.toBytes 8 rcv.toInt).At (rsp0.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 bf.toInt).At (rsp0.toBitVec + 16))
      ⋆ Eq (l28.At (rsp0.toBitVec - 80)) ⋆ Eq (l30.At (rsp0.toBitVec - 72)) ⋆ Eq (l38.At (rsp0.toBitVec - 64))
      ⋆ Eq (spA.At (rsp0.toBitVec - 120))
      ⋆ Eq (rslot.At (rsp0.toBitVec - 128)) ⋆ Eq (lo.At (rsp0.toBitVec - 128 - BitVec.ofNat 64 S))
      ⋆ Heap avail
      ⋆ Eq (aP.At (rcv + 32)) ⋆ Eq (aL.At (rcv + 40)) ⋆ Eq (aC.At (rcv + 48))
      ⋆ Eq (sig.At (bf + 144))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hms : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 S) (hmm : MemmoveContract S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = rsp0 + 8 ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        ∃ (psig : BitVec 64) (spA' lo' : List UInt8), spA'.length = 24 ∧ lo'.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At rsp0.toBitVec)
          ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (rsp0.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 rcv.toInt).At (rsp0.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 bf.toInt).At (rsp0.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 0).At (rsp0.toBitVec - 80)) ⋆ Eq ((Int.toBytes 8 0).At (rsp0.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 psig.toInt).At (rsp0.toBitVec - 64))
          ⋆ Eq (spA'.At (rsp0.toBitVec - 120))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 160)).toBitVec.toInt).At (rsp0.toBitVec - 128))
          ⋆ Eq (lo'.At (rsp0.toBitVec - 128 - BitVec.ofNat 64 S))
          ⋆ Heap (avail - 96)
          ⋆ Eq ((Int.toBytes 8 psig.toInt).At (rcv + 32)) ⋆ Eq ((Int.toBytes 8 96).At (rcv + 40))
          ⋆ Eq ((Int.toBytes 8 96).At (rcv + 48))
          ⋆ Eq (sig.At psig)
          ⋆ Eq (sig.At (bf + 144))
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 136)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp hrbp hr14 hrax hrbx h_mem ⊢
  subst rsp rbp r14 rax rbx
  have := rsp0.toNat_lt_size; simp only [UInt64.size] at *
  have e0 : Int.toBytes 8 (BitVec.toInt (0 : BitVec 64)) = Int.toBytes 8 0 := by decide
  have e96 : Int.toBytes 8 (BitVec.toInt (96 : BitVec 64)) = Int.toBytes 8 96 := by decide
  -- 136–142: the nil error at rsp0 − 80, rsp0 − 72; `makeslice(uint8, 0, 96)`
  step_directive hk unmarshalSSZ 136
  step_directive hk unmarshalSSZ 137
  apply store_step_at _ _ (rsp0.toBitVec - 80) _ _ _ l28 _ _ (by segment_addr) (by ecancel) (by exact hl28)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  unfold_step
  step_directive hk unmarshalSSZ 138
  apply store_step_at _ _ (rsp0.toBitVec - 72) _ _ _ l30 _ _ (by segment_addr) (by ecancel) (by exact hl30)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  unfold_step
  step_directive hk unmarshalSSZ 139
  step_directive hk unmarshalSSZ 140
  intro _
  step_directive hk unmarshalSSZ 141
  step_directive hk unmarshalSSZ 142
  apply store_step_at _ _ (rsp0.toBitVec - 128) _ _ _ rslot _ _ (Decode.call_return_slot _) (by ecancel) (by exact hrs)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  unfold_step
  rw [Decode.call_return_slot] at *
  refine eventually_trans _ _ _ _ (hms _ (Host.addrOf (k + 142 + 1)) 96 avail lo spA _
    rfl (by show (0 : Nat) ≤ 96; omega) (by rfl) (by omega) (by unfold maxAlloc; omega) (by omega) hlo hspA
    (by dsimp only; rw [show rsp0.toBitVec - 128 + 8 = rsp0.toBitVec - 120 by segment_addr]; ecancel)) ?_
  rintro ⟨d4, pc4⟩ ⟨hpc4, hrsp4, hr144, hrbp4, stk4, spm4, hstk4, hspm4, Hm4⟩
  dsimp only at hpc4 hrsp4 hr144 hrbp4 Hm4
  subst hpc4
  obtain ⟨⟨rax4, rbx4, rcx4, rdx4, rsi4, rdi4, rsp4, rbp4, r84, r94, r104, r114, r124, r134, r144, r154⟩,
    zmms4, flags4, mem4⟩ := d4
  simp only at hrsp4 hr144 hrbp4 Hm4
  rw [Decode.return_rsp] at hrsp4
  subst hrsp4 hr144 hrbp4
  rw [show rsp0.toBitVec - 128 + 8 = rsp0.toBitVec - 120 by segment_addr] at Hm4
  simp only [Nat.one_mul] at Hm4
  -- 143–147: len = 0, cap = 96, writeBarrier = 0
  step_directive hk unmarshalSSZ 143
  apply load_step_at _ _ (rsp0.toBitVec + 8) _ _ (Int.toBytes 8 rcv.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  try simp only [ofInt_ofBytes_toBytes64]
  step_directive hk unmarshalSSZ 144
  apply store_step_at _ _ (rcv + 40) _ _ _ aL _ _ (by segment_addr) (by ecancel) (by exact haL)
  intro m5 H5
  simp only [Width.bytes, Width.bits, e0] at H5
  unfold_step
  step_directive hk unmarshalSSZ 145
  apply store_step_at _ _ (rcv + 48) _ _ _ aC _ _ (by segment_addr) (by ecancel) (by exact haC)
  intro m6 H6
  simp only [Width.bytes, Width.bits, e96] at H6
  unfold_step
  step_directive hk unmarshalSSZ 146
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  unfold_step
  step_directive hk unmarshalSSZ 147
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  label_address hk hf unmarshalSSZ 152
  -- 152–159: the pointer at rsp0 − 64 and in the receiver, `memmove(psig, buf + 144, 96)`
  step_directive hk unmarshalSSZ 152
  step_directive hk unmarshalSSZ 153
  apply store_step_at _ _ (rsp0.toBitVec - 64) _ _ _ l38 _ _ (by segment_addr) (by ecancel) (by exact hl38)
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  unfold_step
  step_directive hk unmarshalSSZ 154
  apply store_step_at _ _ (rcv + 32) _ _ _ aP _ _ (by segment_addr) (by ecancel) (by exact haP)
  intro m8 H8
  simp only [Width.bytes, Width.bits] at H8
  unfold_step
  step_directive hk unmarshalSSZ 155
  apply load_step_at _ _ (rsp0.toBitVec + 16) _ _ (Int.toBytes 8 bf.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  try simp only [ofInt_ofBytes_toBytes64]
  step_directive hk unmarshalSSZ 156
  step_directive hk unmarshalSSZ 157
  step_directive hk unmarshalSSZ 158
  step_directive hk unmarshalSSZ 159
  apply store_step_at _ _ (rsp0.toBitVec - 128) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 142 + 1)).toBitVec.toInt) _ _
    (Decode.call_return_slot _) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m9 H9
  simp only [Width.bytes, Width.bits] at H9
  unfold_step
  rw [Decode.call_return_slot] at *
  refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (k + 159 + 1)) sig (List.replicate 96 0) stk4 _
    (by rw [hsig]; rfl) (by simp [hsig]) hstk4
    (by
      dsimp only
      try rw [show 144 + bf = bf + 144 by segment_addr]
      ecancel)) ?_
  rintro ⟨d10, pc10⟩ ⟨hpc10, hrsp10, hr1410, hrbp10, stk10, hstk10, Hm10⟩
  dsimp only at hpc10 hrsp10 hr1410 hrbp10 Hm10
  subst hpc10
  obtain ⟨⟨rax10, rbx10, rcx10, rdx10, rsi10, rdi10, rsp10, rbp10, r810, r910, r1010, r1110, r1210, r1310, r1410, r1510⟩,
    zmms10, flags10, mem10⟩ := d10
  simp only at hrsp10 hr1410 hrbp10 Hm10
  rw [Decode.return_rsp] at hrsp10
  subst hrsp10 hr1410 hrbp10
  try rw [show 144 + bf = bf + 144 by segment_addr] at Hm10
  -- 160–179: len = cap = 96, writeBarrier = 0, the pointer, rax = rbx = 0 (the spilled nil error), epilogue
  step_directive hk unmarshalSSZ 160
  apply load_step_at _ _ (rsp0.toBitVec + 8) _ _ (Int.toBytes 8 rcv.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  try simp only [ofInt_ofBytes_toBytes64]
  step_directive hk unmarshalSSZ 161
  apply store_step_at _ _ (rcv + 40) _ _ _ (Int.toBytes 8 0) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m11 H11
  simp only [Width.bytes, Width.bits, e96] at H11
  unfold_step
  step_directive hk unmarshalSSZ 162
  apply store_step_at _ _ (rcv + 48) _ _ _ (Int.toBytes 8 96) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m12 H12
  simp only [Width.bytes, Width.bits, e96] at H12
  unfold_step
  step_directive hk unmarshalSSZ 163
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  unfold_step
  step_directive hk unmarshalSSZ 164
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  step_directive hk unmarshalSSZ 165
  apply load_step_at _ _ (rsp0.toBitVec - 64) _ _ (Int.toBytes 8 rax4.toBitVec.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  try simp only [ofInt_ofBytes_toBytes64]
  step_directive hk unmarshalSSZ 166
  label_address hk hf unmarshalSSZ 173
  step_directive hk unmarshalSSZ 173
  step_directive hk unmarshalSSZ 174
  apply store_step_at _ _ (rcv + 32) _ _ _ (Int.toBytes 8 rax4.toBitVec.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m13 H13
  simp only [Width.bytes, Width.bits] at H13
  unfold_step
  step_directive hk unmarshalSSZ 175
  apply load_step_at _ _ (rsp0.toBitVec - 80) _ _ (Int.toBytes 8 (0#64).toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk unmarshalSSZ 176
  apply load_step_at _ _ (rsp0.toBitVec - 72) _ _ (Int.toBytes 8 (0#64).toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk unmarshalSSZ 177
  try intro _
  step_directive hk unmarshalSSZ 178
  apply load_step_at _ _ (rsp0.toBitVec - 8) _ _ (Int.toBytes 8 rbp0.toBitVec.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk unmarshalSSZ 179
  apply load_step_at _ _ rsp0.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  apply Eventually.done
  have e00 : Int.toBytes 8 (0#64).toInt = Int.toBytes 8 0 := by decide
  rw [e00, show k + 159 + 1 = k + 160 from rfl] at H13
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rax4.toBitVec, spm4, stk10, hspm4, hstk10, ?_⟩
  rotate_right
  · ecancel
  all_goals first
    | exact trivial
    | with_reducible rfl
    | (apply UInt64.toBitVec_inj.mp
       simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, Width.bits]
       done)
    | (apply UInt64.toBitVec_inj.mp; segment_addr)

end Prysm.SingleAttestation
