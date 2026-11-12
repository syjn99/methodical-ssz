import E2eScal.Gen5F24BbrDec
import Fk.RtCopy
import Fk.WHost

/-!
# Witness of the generated `bbr_g5dec_accept` (`v1alpha1.BeaconBlocksByRangeRequest` decoder accept path; FLAT24 / H7)

Written by the FLAT24 evaluator with its evidence script `f24wit.py`: the text of the G5-C witness `WitSaGA.lean`
(frame `0x38`, one Slot callee) with the v1alpha1.BeaconBlocksByRangeRequest host and layout (3 input words). It shows that the premises of
the generated accept theorem (statement = kind instance) are satisfiable. Host: one label, the real Go 1.26.10
`(*v1alpha1.BeaconBlocksByRangeRequest).UnmarshalSSZ` (index 1) and `primitives.Slot` UnmarshalSSZ (76).
One memory block at `0x10000`: guard · input (3 × 8) · receiver (state, 3 fields,
then the untouched tail) · callee frame-pointer slot (rsp − 80) · callee return slot (rsp − 72) · 8 untouched · callee
rbx spill (rsp − 56) · 40 untouched · saved rbp · return slot (rsp = 0x100b0) · spill rax · spill rbx. The receiver is
at rax = 0x10020 (protoc struct, `prysm/ir/ir-mainnet.json` gc amd64 layout: `state` 0, fields at 8 …). The frame
`R` is the untouched receiver tail and frame ranges. For every 24-byte input every premise holds and the decoder
returns nil. The receiver is a Go value of `v1alpha1.BeaconBlocksByRangeRequest` (all zero).
-/

open Fk Fk.W E2e E2eScal E2eScal.F24Code

namespace E2eScal.WitBbrGA

set_option maxRecDepth 100000

def P : Program := [.label "pad0"] ++ BbrUnmarshal ++ E2eAd.Code.SlUnmarshal

theorem P_len : P.length = 139 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem prog_eq : Host.prog = P := rfl

theorem hk1 : BbrUnmarshal.IsInfixAt Host.prog 1 :=
  infixAt_of [.label "pad0"] (E2eAd.Code.SlUnmarshal) (by simp [prog_eq, P, List.append_assoc]) rfl
theorem hf1 : LabelsFresh BbrUnmarshal 1 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hk76 : E2eAd.Code.SlUnmarshal.IsInfixAt Host.prog 76 :=
  infixAt_of ([.label "pad0"] ++ BbrUnmarshal) ([])
    (by simp [prog_eq, P, List.append_assoc]) (by rfl)
theorem hf76 : LabelsFresh E2eAd.Code.SlUnmarshal 76 := labelsFresh_of (by rw [prog_eq]; decide)

abbrev z (k : Nat) : List UInt8 := List.replicate k 0
abbrev w0 : List UInt8 := Int.toBytes 8 (0 : UInt64).toBitVec.toInt

def block (in0 in1 in2 : List UInt8) : List UInt8 :=
  w0 ++ (in0 ++ (in1 ++ (in2 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 32 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 40 ++ (z 8 ++ (w0 ++ (z 8 ++ (z 8)))))))))))))))))

def mem (in0 in1 in2 : List UInt8) : DataMem := (block in0 in1 in2).At (0x10000 : BitVec 64)

def cs0 (in0 in1 in2 : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10020, 0x10008, 24, 0, 0, 24, 0x100b0, 0, 0, 0, 0, 0, 0, 0, 0xfff0, 0⟩, zmms, flags, mem in0 in1 in2⟩

/-- The frame of the witness: unused bytes, the receiver tail and the untouched frame ranges. -/
def R0 : DataMem → Prop :=
  Eq ((z 32).At (0x10040 : BitVec 64)) ⋆ Eq ((z 8).At (0x10070 : BitVec 64))
    ⋆ Eq ((z 40).At (0x10080 : BitVec 64))

set_option maxHeartbeats 16000000 in
/-- **Non-vacuity of the generated `bbr_g5dec_accept`** (premises of the kind instance). -/
theorem bbr_accept_runs (in0 in1 in2 : List UInt8) (hin0 : in0.length = 8) (hin1 : in1.length = 8) (hin2 : in2.length = 8)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨cs0 in0 in1 in2 zmms flags, Host.addrOf 1⟩ :=
  eventually_mono (E2eScal.Gen.bbr_g5dec_accept 1 hk1 hf1 76 hk76 hf76
    in0 in1 in2 hin0 hin1 hin2 (cs0 in0 in1 in2 zmms flags)
    0 0 (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
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
example (z' : RegZmms) (f : StatusFlags) := bbr_accept_runs (z 8) (z 8) (z 8) rfl rfl rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  bbr_accept_runs (Int.toBytes 8 0x0123456789abcdef) (Int.toBytes 8 7) (Int.toBytes 8 0x40) (by decide) (by decide) (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) :=
  bbr_accept_runs (List.replicate 8 0xff) (List.replicate 8 0xff) (List.replicate 8 0xff) rfl rfl rfl z' f

end E2eScal.WitBbrGA
