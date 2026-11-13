import Prysm.VoluntaryExit.DecodeAcceptExample
import Runtime.CopyModel
import Machine.WitnessHost

/-!
# Witness of `Decode.example_accept` (VoluntaryExit decoder accept path; worked example)

Hand-written (the text of `Prysm/PendingPartialWithdrawal/WitnessDecodeAccept.lean` with two fields). It shows that the premises of
the kind instance `decAcceptKindAnyFrame unmarshalSSZ (layoutCalleeCalls [EpUnmarshal, Prysm.ValidatorIndex.Code.unmarshalSSZ] 56) [.u64, .u64]` are
satisfiable. Host: one label, the real Go 1.26.10 `(*v1alpha1.VoluntaryExit).UnmarshalSSZ` (index 1),
`(*primitives.Epoch).UnmarshalSSZ` (108) and `(*primitives.ValidatorIndex).UnmarshalSSZ` (171).
One memory block at `0x10000`: guard word (r14 = 0xfff0), the 16 input bytes (rbx = 0x10008), 8 unused bytes,
the 56-byte receiver (rax = 0x10020; protoc struct, `prysm/ir/ir-mainnet.json` gc amd64 layout, size 56:
`state` 0, `Epoch` 8, `ValidatorIndex` 16, `unknownFields` 24 and `sizeCache` 48 zero), 8 unused bytes, the
callee frame-pointer slot (rsp − 96), the callee return slot (rsp − 88), 8 untouched bytes, the callee rbx
spill (rsp − 72), 56 untouched frame bytes, the saved-rbp slot, the return slot (rsp = 0x100c0), the spill
slots rsp + 8, + 16, an unused slot and the spill slot rsp + 32. The frame `R` is the receiver's last 32
bytes, the unused bytes and the untouched frame ranges. For every 16-byte input every premise holds and the
decoder returns nil. The receiver is a Go value of `v1alpha1.VoluntaryExit` (all fields zero).
-/

open Machine Runtime Machine.Witness Codec Prysm.VoluntaryExit.Code

namespace Prysm.VoluntaryExit.Witness.DecodeAccept

set_option maxRecDepth 100000

def program : Program := [.label "pad0"] ++ unmarshalSSZ ++ Prysm.Epoch.Code.unmarshalSSZ ++ Prysm.ValidatorIndex.Code.unmarshalSSZ

theorem program_length : program.length = 234 := by rfl

instance host : Host := mkHost program (by rw [program_length]; decide)

theorem host_program_eq : Host.prog = program := rfl

theorem placed_at_1 : unmarshalSSZ.IsInfixAt Host.prog 1 :=
  infixAt_of [.label "pad0"] (Prysm.Epoch.Code.unmarshalSSZ ++ Prysm.ValidatorIndex.Code.unmarshalSSZ) (by simp [host_program_eq, program, List.append_assoc]) rfl
theorem placed_at_108 : Prysm.Epoch.Code.unmarshalSSZ.IsInfixAt Host.prog 108 :=
  infixAt_of ([.label "pad0"] ++ unmarshalSSZ) Prysm.ValidatorIndex.Code.unmarshalSSZ
    (by simp [host_program_eq, program, List.append_assoc]) (by rfl)
theorem placed_at_171 : Prysm.ValidatorIndex.Code.unmarshalSSZ.IsInfixAt Host.prog 171 :=
  infixAt_of ([.label "pad0"] ++ unmarshalSSZ ++ Prysm.Epoch.Code.unmarshalSSZ) []
    (by simp [host_program_eq, program, List.append_assoc]) (by rfl)

theorem labels_fresh_at_1 : LabelsFresh unmarshalSSZ 1 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_108 : LabelsFresh Prysm.Epoch.Code.unmarshalSSZ 108 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_171 : LabelsFresh Prysm.ValidatorIndex.Code.unmarshalSSZ 171 := labelsFresh_of (by rw [host_program_eq]; decide)

abbrev zeros (k : Nat) : List UInt8 := List.replicate k 0
abbrev zero_word_bytes : List UInt8 := Int.toBytes 8 (0 : UInt64).toBitVec.toInt

/-- guard · input (2 × 8) · 8 unused · receiver (state, Epoch, ValidatorIndex, tail 32) · 8 unused · callee
frame-pointer slot · callee return slot · 8 untouched · callee rbx spill · 56 untouched · saved rbp · return
slot · spill rax · spill rbx · unused slot · spill rdi. -/
def block (in0 in1 : List UInt8) : List UInt8 :=
  zero_word_bytes ++ (in0 ++ (in1 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 40 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 56 ++ (zeros 8 ++ (zero_word_bytes ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ zeros 8)))))))))))))))))

def mem (in0 in1 : List UInt8) : DataMem := (block in0 in1).At (0x10000 : BitVec 64)

def initial_state (in0 in1 : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10020, 0x10008, 16, 0, 0, 16, 0x100c0, 0, 0, 0, 0, 0, 0, 0, 0xfff0, 0⟩, zmms, flags, mem in0 in1⟩

/-- The frame of the witness: the unused bytes after the input, the receiver tail with the unused bytes after
it, the two untouched frame ranges and the unused slot rsp + 24. -/
def frame_rest : DataMem → Prop :=
  Eq ((zeros 8).At (0x10018 : BitVec 64)) ⋆ Eq ((zeros 40).At (0x10038 : BitVec 64)) ⋆ Eq ((zeros 8).At (0x10070 : BitVec 64))
    ⋆ Eq ((zeros 56).At (0x10080 : BitVec 64)) ⋆ Eq ((zeros 8).At (0x100d8 : BitVec 64))

set_option maxHeartbeats 16000000 in
/-- **Non-vacuity of `Decode.example_accept`** (premises of the kind instance). -/
theorem runs (in0 in1 : List UInt8) (hin0 : in0.length = 8) (hin1 : in1.length = 8)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨initial_state in0 in1 zmms flags, Host.addrOf 1⟩ :=
  eventually_mono (Decode.example_accept 1 placed_at_1 labels_fresh_at_1 108 placed_at_108 labels_fresh_at_108 171 placed_at_171 labels_fresh_at_171
    in0 in1 hin0 hin1 (initial_state in0 in1 zmms flags)
    0 0 (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
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

end Prysm.VoluntaryExit.Witness.DecodeAccept
