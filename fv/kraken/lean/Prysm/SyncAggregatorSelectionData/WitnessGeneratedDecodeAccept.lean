import Prysm.SyncAggregatorSelectionData.GeneratedDecodeAccept
import Runtime.CopyModel
import Machine.WitnessHost

/-!
# Witness of the generated `Decode.generated_accept` (SyncAggregatorSelectionData decoder accept path)

The text of `Prysm/VoluntaryExit/WitnessDecodeAccept.lean` with the SyncAggregatorSelectionData host and layout. It shows that the
premises of the generated accept theorem (statement = kind instance) are satisfiable. Host: one label, the real
Go 1.26.10 `(*v1alpha1.SyncAggregatorSelectionData).UnmarshalSSZ` (index 1) and `primitives.Slot` (74).
One memory block at `0x10000`: guard · input (2 × 8) · 8 unused · receiver (state, field 1, field 2, tail 32) · 8 unused · callee
frame-pointer slot (rsp − 80) · callee return slot (rsp − 72) · 8 untouched · callee rbx spill (rsp − 56) ·
40 untouched · saved rbp · return slot (rsp = 0x100b0) · spill rax · spill rbx (no rdi spill in this frame). The receiver is at rax = 0x10020 (protoc struct,
`prysm/ir/ir-mainnet.json` gc amd64 layout, size 56: `state` 0, fields 8 and 16, `unknownFields` 24 and `sizeCache`
48 zero). The frame `R` is the receiver tail with the unused bytes and the untouched frame ranges. For every 16-byte
input every premise holds and the decoder returns nil. The receiver is a Go value of `v1alpha1.SyncAggregatorSelectionData` (all zero).
-/

open Machine Runtime Machine.Witness Codec Prysm.SyncAggregatorSelectionData.Code

namespace Prysm.SyncAggregatorSelectionData.Witness.GeneratedDecodeAccept

set_option maxRecDepth 100000

def program : Program := [.label "pad0"] ++ unmarshalSSZ ++ Prysm.Slot.Code.unmarshalSSZ

theorem program_length : program.length = 137 := by rfl

instance host : Host := mkHost program (by rw [program_length]; decide)

theorem host_program_eq : Host.prog = program := rfl

theorem placed_at_1 : unmarshalSSZ.IsInfixAt Host.prog 1 :=
  infixAt_of [.label "pad0"] (Prysm.Slot.Code.unmarshalSSZ) (by simp [host_program_eq, program, List.append_assoc]) rfl
theorem labels_fresh_at_1 : LabelsFresh unmarshalSSZ 1 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem placed_at_74 : Prysm.Slot.Code.unmarshalSSZ.IsInfixAt Host.prog 74 :=
  infixAt_of ([.label "pad0"] ++ unmarshalSSZ) ([])
    (by simp [host_program_eq, program, List.append_assoc]) (by rfl)
theorem labels_fresh_at_74 : LabelsFresh Prysm.Slot.Code.unmarshalSSZ 74 := labelsFresh_of (by rw [host_program_eq]; decide)

abbrev zeros (k : Nat) : List UInt8 := List.replicate k 0
abbrev zero_word_bytes : List UInt8 := Int.toBytes 8 (0 : UInt64).toBitVec.toInt

/-- guard · input (2 × 8) · 8 unused · receiver (state, field 1, field 2, tail 32) · 8 unused · callee
frame-pointer slot (rsp − 80) · callee return slot (rsp − 72) · 8 untouched · callee rbx spill (rsp − 56) ·
40 untouched · saved rbp · return slot (rsp = 0x100b0) · spill rax · spill rbx (no rdi spill in this frame). -/
def block (in0 in1 : List UInt8) : List UInt8 :=
  zero_word_bytes ++ (in0 ++ (in1 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 40 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 40 ++ (zeros 8 ++ (zero_word_bytes ++ (zeros 8 ++ zeros 8)))))))))))))))

def mem (in0 in1 : List UInt8) : DataMem := (block in0 in1).At (0x10000 : BitVec 64)

def initial_state (in0 in1 : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10020, 0x10008, 16, 0, 0, 16, 0x100b0, 0, 0, 0, 0, 0, 0, 0, 0xfff0, 0⟩, zmms, flags, mem in0 in1⟩

/-- The frame of the witness: unused bytes, the receiver tail and the untouched frame ranges. -/
def frame_rest : DataMem → Prop :=
  Eq ((zeros 8).At (0x10018 : BitVec 64)) ⋆ Eq ((zeros 40).At (0x10038 : BitVec 64)) ⋆ Eq ((zeros 8).At (0x10070 : BitVec 64))
    ⋆ Eq ((zeros 40).At (0x10080 : BitVec 64))

set_option maxHeartbeats 16000000 in
/-- **Non-vacuity of the generated `Decode.generated_accept`** (premises of the kind instance). -/
theorem runs (in0 in1 : List UInt8) (hin0 : in0.length = 8) (hin1 : in1.length = 8)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨initial_state in0 in1 zmms flags, Host.addrOf 1⟩ :=
  eventually_mono (Prysm.SyncAggregatorSelectionData.Decode.generated_accept 1 placed_at_1 labels_fresh_at_1 74 placed_at_74 labels_fresh_at_74
    in0 in1 hin0 hin1 (initial_state in0 in1 zmms flags)
    0 0 (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
    frame_rest
    (by
      have H : Eq ((block in0 in1).At (0x10000 : BitVec 64)) (mem in0 in1) := rfl
      witness_split [hin0, hin1]
      simp only [initial_state, frame_rest, zero_word_bytes, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd, BitVec.reduceSub] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by simp [initial_state]) rfl)
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

/-- Zero input; a representative input; all-0xff input. -/
example (z' : RegZmms) (f : StatusFlags) := runs (zeros 8) (zeros 8) rfl rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs (Int.toBytes 8 0x0123456789abcdef) (Int.toBytes 8 7) (by decide) (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs (List.replicate 8 0xff) (List.replicate 8 0xff) rfl rfl z' f

end Prysm.SyncAggregatorSelectionData.Witness.GeneratedDecodeAccept
