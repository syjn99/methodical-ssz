import Prysm.PendingPartialWithdrawal.DecodeAccept
import Runtime.CopyModel
import Machine.WitnessHost

/-!
# Witness of `Decode.accept` (PendingPartialWithdrawal decoder accept path)

Hand-written (the text of `WitBhA.lean` without heap and runtime callees). It shows that
the premises of the independent hand statement `Prysm.PendingPartialWithdrawal.Decode.accept_statement` are satisfiable.
Host: one label, the real Go 1.26.10 `(*v1alpha1.PendingPartialWithdrawal).UnmarshalSSZ` (index 1),
`(*primitives.ValidatorIndex).UnmarshalSSZ` (110) and `(*primitives.Epoch).UnmarshalSSZ` (173).
One memory block at `0x10000`: guard word (r14 = 0xfff0), the 24 input bytes (rbx = 0x10008), the 64-byte
receiver (rax = 0x10020; protoc struct, `prysm/ir/ir-mainnet.json` gc amd64 layout, size 64: `state` 0,
`Index` 8, `Amount` 16, `WithdrawableEpoch` 24, `unknownFields` 32 and `sizeCache` 56 zero), the callee
frame-pointer slot (rsp − 96), the callee return slot (rsp − 88), 8 untouched bytes, the callee rbx spill
(rsp − 72), 56 untouched frame bytes, the saved-rbp slot, the return slot (rsp = 0x100c0), the spill slots
rsp + 8, + 16, an unused slot and the spill slot rsp + 32. The frame `R` is the receiver's last 32 bytes, the
two untouched frame ranges and the unused slot. For every 24-byte input every premise holds and the decoder
returns nil. The receiver is a Go value of `v1alpha1.PendingPartialWithdrawal` (all fields zero).
-/

open Machine Runtime TestTarget Machine.Witness Codec Prysm.PendingPartialWithdrawal.Code

namespace Prysm.PendingPartialWithdrawal.Witness.DecodeAccept

set_option maxRecDepth 100000

def P : Program := [.label "pad0"] ++ unmarshalSSZ ++ Prysm.ValidatorIndex.Code.unmarshalSSZ ++ Prysm.Epoch.Code.unmarshalSSZ

theorem P_len : P.length = 236 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem prog_eq : Host.prog = P := rfl

theorem hk1 : unmarshalSSZ.IsInfixAt Host.prog 1 :=
  infixAt_of [.label "pad0"] (Prysm.ValidatorIndex.Code.unmarshalSSZ ++ Prysm.Epoch.Code.unmarshalSSZ) (by simp [prog_eq, P, List.append_assoc]) rfl
theorem hk110 : Prysm.ValidatorIndex.Code.unmarshalSSZ.IsInfixAt Host.prog 110 :=
  infixAt_of ([.label "pad0"] ++ unmarshalSSZ) Prysm.Epoch.Code.unmarshalSSZ
    (by simp [prog_eq, P, List.append_assoc]) (by rfl)
theorem hk173 : Prysm.Epoch.Code.unmarshalSSZ.IsInfixAt Host.prog 173 :=
  infixAt_of ([.label "pad0"] ++ unmarshalSSZ ++ Prysm.ValidatorIndex.Code.unmarshalSSZ) []
    (by simp [prog_eq, P, List.append_assoc]) (by rfl)

theorem hf1 : LabelsFresh unmarshalSSZ 1 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf110 : LabelsFresh Prysm.ValidatorIndex.Code.unmarshalSSZ 110 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf173 : LabelsFresh Prysm.Epoch.Code.unmarshalSSZ 173 := labelsFresh_of (by rw [prog_eq]; decide)

abbrev z (k : Nat) : List UInt8 := List.replicate k 0
abbrev w0 : List UInt8 := Int.toBytes 8 (0 : UInt64).toBitVec.toInt

/-- guard · input (3 × 8) · receiver (state, Index, Amount, WithdrawableEpoch, tail 32) · callee frame-pointer
slot · callee return slot · 8 untouched · callee rbx spill · 56 untouched · saved rbp · return slot · spill rax ·
spill rbx · unused slot · spill rdi. -/
def block (in0 in1 in2 : List UInt8) : List UInt8 :=
  w0 ++ (in0 ++ (in1 ++ (in2 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 32 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 56 ++ (z 8 ++ (w0 ++ (z 8 ++ (z 8 ++ (z 8 ++ z 8))))))))))))))))))

def mem (in0 in1 in2 : List UInt8) : DataMem := (block in0 in1 in2).At (0x10000 : BitVec 64)

def cs0 (in0 in1 in2 : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10020, 0x10008, 24, 0, 0, 24, 0x100c0, 0, 0, 0, 0, 0, 0, 0, 0xfff0, 0⟩, zmms, flags, mem in0 in1 in2⟩

/-- The frame of the witness: the receiver tail, the two untouched frame ranges and the unused slot rsp + 24. -/
def R0 : DataMem → Prop :=
  Eq ((z 32).At (0x10040 : BitVec 64)) ⋆ Eq ((z 8).At (0x10070 : BitVec 64)) ⋆ Eq ((z 56).At (0x10080 : BitVec 64))
    ⋆ Eq ((z 8).At (0x100d8 : BitVec 64))

set_option maxHeartbeats 16000000 in
/-- **Non-vacuity of `Decode.accept`** (premises of `Decode.accept_statement`). -/
theorem runs (in0 in1 in2 : List UInt8) (hin0 : in0.length = 8) (hin1 : in1.length = 8)
    (hin2 : in2.length = 8) (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨cs0 in0 in1 in2 zmms flags, Host.addrOf 1⟩ :=
  eventually_mono (Decode.accept 1 hk1 hf1 110 hk110 hf110 173 hk173 hf173
    in0 in1 in2 hin0 hin1 hin2 (cs0 in0 in1 in2 zmms flags)
    0 0 (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    R0
    (by
      have H : Eq ((block in0 in1 in2).At (0x10000 : BitVec 64)) (mem in0 in1 in2) := rfl
      wit_split [hin0, hin1, hin2]
      simp only [cs0, R0, w0, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd, BitVec.reduceSub] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by simp [cs0]) rfl)
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

/-- Zero input; a representative input; all-0xff input. -/
example (z' : RegZmms) (f : StatusFlags) := runs (z 8) (z 8) (z 8) rfl rfl rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs (Int.toBytes 8 0x0123456789abcdef) (Int.toBytes 8 32000000000) (Int.toBytes 8 7)
    (by decide) (by decide) (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs (List.replicate 8 0xff) (List.replicate 8 0xff) (List.replicate 8 0xff) rfl rfl rfl z' f

end Prysm.PendingPartialWithdrawal.Witness.DecodeAccept
