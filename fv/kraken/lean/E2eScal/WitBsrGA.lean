import E2eScal.Gen5F24BsrDec
import Runtime.CopyModel
import Machine.WitnessHost

/-!
# Witness of the generated `bsr_g5dec_accept` (`v1alpha1.BlobSidecarsByRangeRequest` decoder accept path; FLAT24 / H7)

Written by the FLAT24 evaluator with its evidence script `f24wit.py`: the text of the G5-C witness `WitSaGA.lean`
(frame `0x38`, one Slot callee) with the v1alpha1.BlobSidecarsByRangeRequest host and layout (2 input words). It shows that the premises of
the generated accept theorem (statement = kind instance) are satisfiable. Host: one label, the real Go 1.26.10
`(*v1alpha1.BlobSidecarsByRangeRequest).UnmarshalSSZ` (index 1) and `primitives.Slot` UnmarshalSSZ (74).
One memory block at `0x10000`: guard · input (2 × 8) · 8 unused · receiver (state, 2 fields,
then the untouched tail) · callee frame-pointer slot (rsp − 80) · callee return slot (rsp − 72) · 8 untouched · callee
rbx spill (rsp − 56) · 40 untouched · saved rbp · return slot (rsp = 0x100b0) · spill rax · spill rbx. The receiver is
at rax = 0x10020 (protoc struct, `prysm/ir/ir-mainnet.json` gc amd64 layout: `state` 0, fields at 8 …). The frame
`R` is the untouched receiver tail and frame ranges. For every 16-byte input every premise holds and the decoder
returns nil. The receiver is a Go value of `v1alpha1.BlobSidecarsByRangeRequest` (all zero).
-/

open Machine Runtime TestTarget Machine.Witness E2e E2eScal Codec E2eScal.F24Code

namespace E2eScal.WitBsrGA

set_option maxRecDepth 100000

def P : Program := [.label "pad0"] ++ BsrUnmarshal ++ E2eAd.Code.SlUnmarshal

theorem P_len : P.length = 137 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem prog_eq : Host.prog = P := rfl

theorem hk1 : BsrUnmarshal.IsInfixAt Host.prog 1 :=
  infixAt_of [.label "pad0"] (E2eAd.Code.SlUnmarshal) (by simp [prog_eq, P, List.append_assoc]) rfl
theorem hf1 : LabelsFresh BsrUnmarshal 1 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hk74 : E2eAd.Code.SlUnmarshal.IsInfixAt Host.prog 74 :=
  infixAt_of ([.label "pad0"] ++ BsrUnmarshal) ([])
    (by simp [prog_eq, P, List.append_assoc]) (by rfl)
theorem hf74 : LabelsFresh E2eAd.Code.SlUnmarshal 74 := labelsFresh_of (by rw [prog_eq]; decide)

abbrev z (k : Nat) : List UInt8 := List.replicate k 0
abbrev w0 : List UInt8 := Int.toBytes 8 (0 : UInt64).toBitVec.toInt

def block (in0 in1 : List UInt8) : List UInt8 :=
  w0 ++ (in0 ++ (in1 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 40 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 40 ++ (z 8 ++ (w0 ++ (z 8 ++ (z 8))))))))))))))))

def mem (in0 in1 : List UInt8) : DataMem := (block in0 in1).At (0x10000 : BitVec 64)

def cs0 (in0 in1 : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10020, 0x10008, 16, 0, 0, 16, 0x100b0, 0, 0, 0, 0, 0, 0, 0, 0xfff0, 0⟩, zmms, flags, mem in0 in1⟩

/-- The frame of the witness: unused bytes, the receiver tail and the untouched frame ranges. -/
def R0 : DataMem → Prop :=
  Eq ((z 8).At (0x10018 : BitVec 64)) ⋆ Eq ((z 40).At (0x10038 : BitVec 64)) ⋆ Eq ((z 8).At (0x10070 : BitVec 64))
    ⋆ Eq ((z 40).At (0x10080 : BitVec 64))

set_option maxHeartbeats 16000000 in
/-- **Non-vacuity of the generated `bsr_g5dec_accept`** (premises of the kind instance). -/
theorem bsr_accept_runs (in0 in1 : List UInt8) (hin0 : in0.length = 8) (hin1 : in1.length = 8)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨cs0 in0 in1 zmms flags, Host.addrOf 1⟩ :=
  eventually_mono (E2eScal.Gen.bsr_g5dec_accept 1 hk1 hf1 74 hk74 hf74
    in0 in1 hin0 hin1 (cs0 in0 in1 zmms flags)
    0 0 (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
    R0
    (by
      have H : Eq ((block in0 in1).At (0x10000 : BitVec 64)) (mem in0 in1) := rfl
      wit_split [hin0, hin1]
      simp only [cs0, R0, w0, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd, BitVec.reduceSub] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by simp [cs0]) rfl)
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

/-- Zero input; a representative input; all-0xff input. -/
example (z' : RegZmms) (f : StatusFlags) := bsr_accept_runs (z 8) (z 8) rfl rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  bsr_accept_runs (Int.toBytes 8 0x0123456789abcdef) (Int.toBytes 8 7) (by decide) (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) :=
  bsr_accept_runs (List.replicate 8 0xff) (List.replicate 8 0xff) rfl rfl z' f

end E2eScal.WitBsrGA
