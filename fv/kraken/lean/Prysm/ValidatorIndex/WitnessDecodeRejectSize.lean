import Prysm.ValidatorIndex.DecodeRejectSize
import Runtime.ErrorModel
import Machine.WitnessHost

/-!
# Witnesses of `Prysm.ValidatorIndex.Decode.reject_size` (len 7, 9 and 300)

Hand text: `Prysm/Epoch/WitnessDecodeRejectSize.lean` with `Prysm.Epoch.Code.unmarshalSSZ` replaced by `Code.unmarshalSSZ` (same directive count, same
host layout and indices). The original description follows, with the type name replaced.

Host: four data labels (`go_string._` at 0x10000, `runtime.gcbits._` 0x10001,
`runtime.staticuint64s` 0x10002, `runtime.modelBumpPointer` 0x10003), the real Go 1.26.10
`(*primitives.ValidatorIndex).UnmarshalSSZ` (index 4) and `ErrorfConvT64Model` (index 67: the
`model_convT64` model on the bump heap, `model_errorf_decimal_decimal`). One memory block from
0x10003 to the format string at `go_string._ + 110057`: bump pointer, the
`staticuint64s` entries 7 and 8, the static box `boxedEight`, an 8280-byte heap,
the guard word, the 112-byte stack window (rsp = 0x12659), and the 40 format
bytes `formatBufferLength`; the fillers between them and the unused rax spill slot are the
frame `R`. With `len(buf) = 7` the decoder returns a non-nil error.
-/

open Machine Runtime Machine.Witness Prysm.Checkpoint.Code Prysm.ValidatorIndex.Code

namespace Prysm.ValidatorIndex.Witness.DecodeRejectSize

set_option maxRecDepth 100000

def dataLabels : Program :=
  [.label "go_string._", .label "runtime.gcbits._", .label "runtime.staticuint64s", .label "runtime.modelBumpPointer"]

def program : Program := dataLabels ++ Code.unmarshalSSZ ++ ErrorfConvT64Model

theorem program_length : program.length = 82 := by rfl

instance host : Host := mkHost program (by rw [program_length]; decide)

theorem host_program_eq : Host.prog = program := rfl

theorem placed_at_4 : Code.unmarshalSSZ.IsInfixAt Host.prog 4 :=
  infixAt_of dataLabels ErrorfConvT64Model (by simp [host_program_eq, program, List.append_assoc]) rfl
theorem placed_at_67 : ErrorfConvT64Model.IsInfixAt Host.prog 67 :=
  infixAt_of (dataLabels ++ Code.unmarshalSSZ) [] (by simp [host_program_eq, program, List.append_assoc]) (by rfl)
theorem labels_fresh_at_4 : LabelsFresh Code.unmarshalSSZ 4 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_67 : LabelsFresh ErrorfConvT64Model 67 := labelsFresh_of (by rw [host_program_eq]; decide)

theorem label_go_string : label "go_string._" = 0x10000 := mk_label program _ 0 _ (by simp [program, dataLabels]) (by simp [programLabels])
theorem label_gcbits : label "runtime.gcbits._" = 0x10001 := mk_label program _ 1 _ (by simp [program, dataLabels]) (by decide)
theorem label_staticuint64s : label "runtime.staticuint64s" = 0x10002 := mk_label program _ 2 _ (by simp [program, dataLabels]) (by decide)
theorem label_bump_pointer : label "runtime.modelBumpPointer" = 0x10003 := mk_label program _ 3 _ (by simp [program, dataLabels]) (by decide)

theorem eight_length : ElfData.PrysmTarget.boxedEight.length = 8 := by decide

abbrev zeros (k : Nat) : List UInt8 := List.replicate k 0
abbrev word_bytes (v : UInt64) : List UInt8 := Int.toBytes 8 v.toBitVec.toInt

/-- bump ptr · F1 · box 7 · box 8 · F2 · eight · heap · guard · rslot · sp8 · sp32 · a40 · a24 · fp · ret · s1 · s2 · F3 · fs. -/
def block : List UInt8 :=
  Int.toBytes 8 (0x105a1 : BitVec 64).toInt ++ (zeros 47 ++ (Int.toBytes 8 (7 : BitVec 64).toInt
    ++ (Int.toBytes 8 (8 : BitVec 64).toInt ++ (zeros 1359 ++ (ElfData.PrysmTarget.boxedEight ++ (zeros 8280 ++ (word_bytes 0 ++ (zeros 8 ++ (zeros 8
    ++ (zeros 32 ++ (zeros 16 ++ (zeros 16 ++ (zeros 8 ++ (word_bytes 0 ++ (zeros 8 ++ (zeros 8 ++ (zeros 100216 ++ ElfData.PrysmTarget.formatBufferLength)))))))))))))))))

def mem : DataMem := block.At (0x10003 : BitVec 64)

def initial_state (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x13000, 0x14000, 7, 0, 0, 0, 0x12659, 0, 0, 0, 0, 0, 0, 0, 0x125e9, 0⟩, zmms, flags, mem⟩

def frame_rest : DataMem → Prop :=
  Eq ((zeros 47).At (0x1000b : BitVec 64)) ⋆ Eq ((zeros 1359).At (0x1004a : BitVec 64))
    ⋆ Eq ((zeros 8).At (0x12661 : BitVec 64)) ⋆ Eq ((zeros 100216).At (0x12671 : BitVec 64))

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x105a1 : BitVec 64).toInt).At (0x10003 : BitVec 64))
      ⋆ (Eq ((zeros 8280).At (0x105a1 : BitVec 64)) ⋆ X)) m) : (bumpHeap 8280 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x105a1, by decide, by rw [label_bump_pointer]; exact hm⟩) h

set_option maxHeartbeats 16000000 in
/-- **Non-vacuity of `Decode.reject_size`** (len 7). -/
theorem runs (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax ≠ 0)
      ⟨initial_state zmms flags, Host.addrOf 4⟩ :=
  eventually_mono (Decode.reject_size 4 placed_at_4 labels_fresh_at_4 (initial_state zmms flags) 0 0 (zeros 8) (zeros 8) (zeros 16) (zeros 16) (zeros 8) (zeros 32)
    (zeros 8) rfl rfl rfl rfl rfl rfl rfl 0 [] rfl bumpHeap 8280 frame_rest
    (by
      have H : Eq (block.At (0x10003 : BitVec 64)) mem := rfl
      witness_split [eight_length, Prysm.Epoch.Decode.reject_fmt_len]
      -- bump pointer, F1, box 7, box 8, F2, ... : move the heap next to the pointer
      rw [Std.ExtHashMap.sep_comm_l (Eq (ElfData.PrysmTarget.boxedEight.At _)) (Eq ((zeros 8280).At _)),
        Std.ExtHashMap.sep_comm_l (Eq ((zeros 1359).At _)) (Eq ((zeros 8280).At _)),
        Std.ExtHashMap.sep_comm_l (Eq ((Int.toBytes 8 (8#64).toInt).At _)) (Eq ((zeros 8280).At _)),
        Std.ExtHashMap.sep_comm_l (Eq ((Int.toBytes 8 (7#64).toInt).At _)) (Eq ((zeros 8280).At _)),
        Std.ExtHashMap.sep_comm_l (Eq ((zeros 47).At _)) (Eq ((zeros 8280).At _))] at H
      have H2 := lift_heap H
      rw [staticBox_of_lt (v := 8) (by decide), staticBox_of_lt (v := (initial_state zmms flags).regs.rcx.toBitVec) (by simp [initial_state])]
      simp only [initial_state, frame_rest, word_bytes, Runtime.Data.staticuint64s_addr, ElfData.PrysmTarget.formatBufferLength_addr, ElfData.PrysmTarget.boxedEight_addr, label_go_string,
        label_gcbits, label_staticuint64s, nil_At_emp, Std.ExtHashMap.sep_emp, Std.ExtHashMap.emp_sep, UInt64.toBitVec_ofNat,
        Int64.toBitVec_ofNat, Int64.toBitVec_add, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub,
        BitVec.reduceMul] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [initial_state]) (by simp [initial_state]) (by omega) (model_convT64 67 placed_at_67 labels_fresh_at_67 0)
    (model_errorf_decimal_decimal 67 placed_at_67 labels_fresh_at_67 bumpHeap ElfData.PrysmTarget.formatBufferLength ElfData.PrysmTarget.typeInt_addr 0))
    (fun _ h => ⟨h.1, h.2.1⟩)

/-! ## len 9 and len 300

Same Host and layout. len 9: the static entries 8 and 9 at 0x10042 and 0x1004a. len 300 (≥ 256):
`StaticBox 300` is empty and `convT64` takes the heap-box branch (`BoxIn` right disjunct: an 8-byte
allocation from the bump heap). -/

theorem staticBox_big (v : BitVec 64) (h : 256 ≤ v.toNat) : StaticBox v = Eq (([] : List UInt8).At 0) := by
  unfold StaticBox; rw [if_neg (by omega)]

namespace InputLength9

def block : List UInt8 :=
  Int.toBytes 8 (0x105a1 : BitVec 64).toInt ++ (zeros 55 ++ (Int.toBytes 8 (8 : BitVec 64).toInt
    ++ (Int.toBytes 8 (9 : BitVec 64).toInt ++ (zeros 1351 ++ (ElfData.PrysmTarget.boxedEight ++ (zeros 8280 ++ (word_bytes 0 ++ (zeros 8 ++ (zeros 8
    ++ (zeros 32 ++ (zeros 16 ++ (zeros 16 ++ (zeros 8 ++ (word_bytes 0 ++ (zeros 8 ++ (zeros 8 ++ (zeros 100216 ++ ElfData.PrysmTarget.formatBufferLength)))))))))))))))))

def mem : DataMem := block.At (0x10003 : BitVec 64)

def initial_state (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x13000, 0x14000, 9, 0, 0, 0, 0x12659, 0, 0, 0, 0, 0, 0, 0, 0x125e9, 0⟩, zmms, flags, mem⟩

def frame_rest : DataMem → Prop :=
  Eq ((zeros 55).At (0x1000b : BitVec 64)) ⋆ Eq ((zeros 1351).At (0x10052 : BitVec 64))
    ⋆ Eq ((zeros 8).At (0x12661 : BitVec 64)) ⋆ Eq ((zeros 100216).At (0x12671 : BitVec 64))

set_option maxHeartbeats 16000000 in
/-- **Non-vacuity of `Decode.reject_size`** (len 9, static box). -/
theorem runs9 (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax ≠ 0)
      ⟨initial_state zmms flags, Host.addrOf 4⟩ :=
  eventually_mono (Decode.reject_size 4 placed_at_4 labels_fresh_at_4 (initial_state zmms flags) 0 0 (zeros 8) (zeros 8) (zeros 16) (zeros 16) (zeros 8) (zeros 32)
    (zeros 8) rfl rfl rfl rfl rfl rfl rfl 0 [] rfl bumpHeap 8280 frame_rest
    (by
      have H : Eq (block.At (0x10003 : BitVec 64)) mem := rfl
      witness_split [eight_length, Prysm.Epoch.Decode.reject_fmt_len]
      rw [Std.ExtHashMap.sep_comm_l (Eq (ElfData.PrysmTarget.boxedEight.At _)) (Eq ((zeros 8280).At _)),
        Std.ExtHashMap.sep_comm_l (Eq ((zeros 1351).At _)) (Eq ((zeros 8280).At _)),
        Std.ExtHashMap.sep_comm_l (Eq ((Int.toBytes 8 (9#64).toInt).At _)) (Eq ((zeros 8280).At _)),
        Std.ExtHashMap.sep_comm_l (Eq ((Int.toBytes 8 (8#64).toInt).At _)) (Eq ((zeros 8280).At _)),
        Std.ExtHashMap.sep_comm_l (Eq ((zeros 55).At _)) (Eq ((zeros 8280).At _))] at H
      have H2 := lift_heap H
      rw [staticBox_of_lt (v := 8) (by decide), staticBox_of_lt (v := (initial_state zmms flags).regs.rcx.toBitVec) (by simp [initial_state])]
      simp only [initial_state, frame_rest, word_bytes, Runtime.Data.staticuint64s_addr, ElfData.PrysmTarget.formatBufferLength_addr, ElfData.PrysmTarget.boxedEight_addr, label_go_string,
        label_gcbits, label_staticuint64s, nil_At_emp, Std.ExtHashMap.sep_emp, Std.ExtHashMap.emp_sep, UInt64.toBitVec_ofNat,
        Int64.toBitVec_ofNat, Int64.toBitVec_add, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub,
        BitVec.reduceMul] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [initial_state]) (by simp [initial_state]) (by omega) (model_convT64 67 placed_at_67 labels_fresh_at_67 0)
    (model_errorf_decimal_decimal 67 placed_at_67 labels_fresh_at_67 bumpHeap ElfData.PrysmTarget.formatBufferLength ElfData.PrysmTarget.typeInt_addr 0))
    (fun _ h => ⟨h.1, h.2.1⟩)

end InputLength9

namespace InputLength300

def block : List UInt8 :=
  Int.toBytes 8 (0x105a1 : BitVec 64).toInt ++ (zeros 55 ++ (Int.toBytes 8 (8 : BitVec 64).toInt
    ++ (zeros 1359 ++ (ElfData.PrysmTarget.boxedEight ++ (zeros 8280 ++ (word_bytes 0 ++ (zeros 8 ++ (zeros 8
    ++ (zeros 32 ++ (zeros 16 ++ (zeros 16 ++ (zeros 8 ++ (word_bytes 0 ++ (zeros 8 ++ (zeros 8 ++ (zeros 100216 ++ ElfData.PrysmTarget.formatBufferLength))))))))))))))))

def mem : DataMem := block.At (0x10003 : BitVec 64)

def initial_state (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x13000, 0x14000, 300, 0, 0, 0, 0x12659, 0, 0, 0, 0, 0, 0, 0, 0x125e9, 0⟩, zmms, flags, mem⟩

def frame_rest : DataMem → Prop :=
  Eq ((zeros 55).At (0x1000b : BitVec 64)) ⋆ Eq ((zeros 1359).At (0x1004a : BitVec 64))
    ⋆ Eq ((zeros 8).At (0x12661 : BitVec 64)) ⋆ Eq ((zeros 100216).At (0x12671 : BitVec 64))

set_option maxHeartbeats 16000000 in
/-- **Non-vacuity of `Decode.reject_size`** (len 300 ≥ 256: heap box). -/
theorem runs300 (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax ≠ 0)
      ⟨initial_state zmms flags, Host.addrOf 4⟩ :=
  eventually_mono (Decode.reject_size 4 placed_at_4 labels_fresh_at_4 (initial_state zmms flags) 0 0 (zeros 8) (zeros 8) (zeros 16) (zeros 16) (zeros 8) (zeros 32)
    (zeros 8) rfl rfl rfl rfl rfl rfl rfl 0 [] rfl bumpHeap 8280 frame_rest
    (by
      have H : Eq (block.At (0x10003 : BitVec 64)) mem := rfl
      witness_split [eight_length, Prysm.Epoch.Decode.reject_fmt_len]
      rw [Std.ExtHashMap.sep_comm_l (Eq (ElfData.PrysmTarget.boxedEight.At _)) (Eq ((zeros 8280).At _)),
        Std.ExtHashMap.sep_comm_l (Eq ((zeros 1359).At _)) (Eq ((zeros 8280).At _)),
        Std.ExtHashMap.sep_comm_l (Eq ((Int.toBytes 8 (8#64).toInt).At _)) (Eq ((zeros 8280).At _)),
        Std.ExtHashMap.sep_comm_l (Eq ((zeros 55).At _)) (Eq ((zeros 8280).At _))] at H
      have H2 := lift_heap H
      rw [staticBox_of_lt (v := 8) (by decide), staticBox_big (initial_state zmms flags).regs.rcx.toBitVec (by simp [initial_state])]
      simp only [initial_state, frame_rest, word_bytes, Runtime.Data.staticuint64s_addr, ElfData.PrysmTarget.formatBufferLength_addr, ElfData.PrysmTarget.boxedEight_addr, label_go_string,
        label_gcbits, label_staticuint64s, nil_At_emp, Std.ExtHashMap.sep_emp, Std.ExtHashMap.emp_sep, UInt64.toBitVec_ofNat,
        Int64.toBitVec_ofNat, Int64.toBitVec_add, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub,
        BitVec.reduceMul] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [initial_state]) (by simp [initial_state]) (by omega) (model_convT64 67 placed_at_67 labels_fresh_at_67 0)
    (model_errorf_decimal_decimal 67 placed_at_67 labels_fresh_at_67 bumpHeap ElfData.PrysmTarget.formatBufferLength ElfData.PrysmTarget.typeInt_addr 0))
    (fun _ h => ⟨h.1, h.2.1⟩)

end InputLength300

end Prysm.ValidatorIndex.Witness.DecodeRejectSize
