import Prysm.BeaconBlocksByRangeRequest.GeneratedDecodeAccept
import Runtime.CopyModel
import Machine.WitnessHost

/-!
# Witness of the generated `Decode.generated_accept` (`v1alpha1.BeaconBlocksByRangeRequest` decoder accept path; 24 flat hold-out types)

Written by the evidence script `flat_types_witness.py`: the text of the generated accept witness `Prysm/SyncAggregatorSelectionData/WitnessGeneratedDecodeAccept.lean`
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

open Machine Runtime Machine.Witness Codec Prysm.BeaconBlocksByRangeRequest.Code

namespace Prysm.BeaconBlocksByRangeRequest.Witness.GeneratedDecodeAccept

set_option maxRecDepth 100000

def program : Program := [.label "pad0"] ++ unmarshalSSZ ++ Prysm.Slot.Code.unmarshalSSZ

theorem program_length : program.length = 139 := by rfl

instance host : Host := mkHost program (by rw [program_length]; decide)

theorem host_program_eq : Host.prog = program := rfl

theorem placed_at_1 : unmarshalSSZ.IsInfixAt Host.prog 1 :=
  infixAt_of [.label "pad0"] (Prysm.Slot.Code.unmarshalSSZ) (by simp [host_program_eq, program, List.append_assoc]) rfl
theorem labels_fresh_at_1 : LabelsFresh unmarshalSSZ 1 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem placed_at_76 : Prysm.Slot.Code.unmarshalSSZ.IsInfixAt Host.prog 76 :=
  infixAt_of ([.label "pad0"] ++ unmarshalSSZ) ([])
    (by simp [host_program_eq, program, List.append_assoc]) (by rfl)
theorem labels_fresh_at_76 : LabelsFresh Prysm.Slot.Code.unmarshalSSZ 76 := labelsFresh_of (by rw [host_program_eq]; decide)

abbrev zeros (k : Nat) : List UInt8 := List.replicate k 0
abbrev zero_word_bytes : List UInt8 := Int.toBytes 8 (0 : UInt64).toBitVec.toInt

def block (in0 in1 in2 : List UInt8) : List UInt8 :=
  zero_word_bytes ++ (in0 ++ (in1 ++ (in2 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 32 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 40 ++ (zeros 8 ++ (zero_word_bytes ++ (zeros 8 ++ (zeros 8)))))))))))))))))

def mem (in0 in1 in2 : List UInt8) : DataMem := (block in0 in1 in2).At (0x10000 : BitVec 64)

def initial_state (in0 in1 in2 : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10020, 0x10008, 24, 0, 0, 24, 0x100b0, 0, 0, 0, 0, 0, 0, 0, 0xfff0, 0⟩, zmms, flags, mem in0 in1 in2⟩

/-- The frame of the witness: unused bytes, the receiver tail and the untouched frame ranges. -/
def frame_rest : DataMem → Prop :=
  Eq ((zeros 32).At (0x10040 : BitVec 64)) ⋆ Eq ((zeros 8).At (0x10070 : BitVec 64))
    ⋆ Eq ((zeros 40).At (0x10080 : BitVec 64))

set_option maxHeartbeats 16000000 in
/-- **Non-vacuity of the generated `Decode.generated_accept`** (premises of the kind instance). -/
theorem runs (in0 in1 in2 : List UInt8) (hin0 : in0.length = 8) (hin1 : in1.length = 8) (hin2 : in2.length = 8)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨initial_state in0 in1 in2 zmms flags, Host.addrOf 1⟩ :=
  eventually_mono (Prysm.BeaconBlocksByRangeRequest.Decode.generated_accept 1 placed_at_1 labels_fresh_at_1 76 placed_at_76 labels_fresh_at_76
    in0 in1 in2 hin0 hin1 hin2 (initial_state in0 in1 in2 zmms flags)
    0 0 (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    frame_rest
    (by
      have H : Eq ((block in0 in1 in2).At (0x10000 : BitVec 64)) (mem in0 in1 in2) := rfl
      witness_split [hin0, hin1, hin2]
      simp only [initial_state, frame_rest, zero_word_bytes, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd, BitVec.reduceSub] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by simp [initial_state]) rfl)
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

/-- Zero input; a representative input; all-0xff input. -/
example (z' : RegZmms) (f : StatusFlags) := runs (zeros 8) (zeros 8) (zeros 8) rfl rfl rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs (Int.toBytes 8 0x0123456789abcdef) (Int.toBytes 8 7) (Int.toBytes 8 0x40) (by decide) (by decide) (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs (List.replicate 8 0xff) (List.replicate 8 0xff) (List.replicate 8 0xff) rfl rfl rfl z' f

end Prysm.BeaconBlocksByRangeRequest.Witness.GeneratedDecodeAccept
