import Prysm.DataColumnsByRootIdentifier.DecodeRejectAlignment
import Prysm.DataColumnsByRootIdentifier.DecodeRejectOverflow
import Runtime.ErrorModel
import Runtime.BumpAllocatorVariants
import Runtime.CopyModel
import Machine.WitnessHost
import Prysm.DataColumnsByRootIdentifier.Code

/-!
# Witnesses of `Decode.reject_alignment_error_word_nonzero` (alignment reject) and `Decode.reject_overflow_error_word_nonzero` (overflow reject)

The premises of the two statements (`Prysm/DataColumnsByRootIdentifier/StatementsDecodeErrorWordNonzero.lean`) are satisfiable.
This includes `e0 ≠ 0`, with a concrete non-zero itab word, and the four contract hypotheses.
Host: data labels (`runtime.writeBarrier` at 0x10000, `go_string._` at 0x10001, the bump pointer label at 0x10004).
Then the Go 1.26.10 `(*v1alpha1.DataColumnsByRootIdentifier).UnmarshalSSZ` (index 5).
Then the runtime models `BumpMakeslice1` (234: `bump_makeslice1`) and `MemmoveGrowsliceModel` (240: `model_memmove`).
Then `ErrorfConvT64Model` (266: `model_convT64`, `model_errorf_decimal_wrap`).
Then the labels `go_itab._errors.errorString_error` (0x10119, the value of `e0`) and `ssz.ErrIncorrectListSize` (0x10129).
Then the labels `ssz.ErrListTooBig` (0x10139) and `runtime.staticuint64s` (0x10149), with pad labels between.
A label's address is 0x10000 plus its index.
One memory block at 0x10000 holds the writeBarrier word 0 and the bump pointer.
It holds the type word of the itab (8 zero bytes) and the two error globals (itab, `e1` = 0x10180).
It holds the static entries of 4 and 129 and the errorString object (message "err").
It holds the frame (rsp = 0x10700, `S = 8`) and the guard word.
It holds the receiver at 0x10750 and the 36 input bytes at 0x10780 (32 zero root bytes, the offset 36).
Last are the 8400-byte heap at 0x10800 and the two format strings.
The decoder reads no more input bytes on these paths.
The frame `R` is `fun _ => True` (every other byte of the block).
Alignment reject: len = 40 (len − 36 = 4, misaligned; the box of 4 is the static entry).
Overflow reject: len = 36 + 8 · 129 (129 elements; the box of 129 is the static entry).
-/

open Machine Runtime Machine.Witness Prysm.DataColumnsByRootIdentifier.Code

namespace Prysm.DataColumnsByRootIdentifier.Witness.DecodeRejectAlignment

def dataLabels : Program :=
  [.label "runtime.writeBarrier", .label "go_string._", .label "pad2", .label "pad3", .label "runtime.modelBumpPointer"]

def tailLabels : Program := [.label "go_itab._errors.errorString_error", .label "pad_after_itab_0", .label "pad_after_itab_1", .label "pad_after_itab_2", .label "pad_after_itab_3", .label "pad_after_itab_4", .label "pad_after_itab_5", .label "pad_after_itab_6", .label "pad_after_itab_7", .label "pad_after_itab_8", .label "pad_after_itab_9", .label "pad_after_itab_10", .label "pad_after_itab_11", .label "pad_after_itab_12", .label "pad_after_itab_13", .label "pad_after_itab_14", .label "ssz.ErrIncorrectListSize", .label "pad_after_incorrect_list_size_0", .label "pad_after_incorrect_list_size_1", .label "pad_after_incorrect_list_size_2", .label "pad_after_incorrect_list_size_3", .label "pad_after_incorrect_list_size_4", .label "pad_after_incorrect_list_size_5", .label "pad_after_incorrect_list_size_6", .label "pad_after_incorrect_list_size_7", .label "pad_after_incorrect_list_size_8", .label "pad_after_incorrect_list_size_9", .label "pad_after_incorrect_list_size_10", .label "pad_after_incorrect_list_size_11", .label "pad_after_incorrect_list_size_12", .label "pad_after_incorrect_list_size_13", .label "pad_after_incorrect_list_size_14", .label "ssz.ErrListTooBig", .label "pad_after_list_too_big_0", .label "pad_after_list_too_big_1", .label "pad_after_list_too_big_2", .label "pad_after_list_too_big_3", .label "pad_after_list_too_big_4", .label "pad_after_list_too_big_5", .label "pad_after_list_too_big_6", .label "pad_after_list_too_big_7", .label "pad_after_list_too_big_8", .label "pad_after_list_too_big_9", .label "pad_after_list_too_big_10", .label "pad_after_list_too_big_11", .label "pad_after_list_too_big_12", .label "pad_after_list_too_big_13", .label "pad_after_list_too_big_14", .label "runtime.staticuint64s"]

def program : Program := dataLabels ++ unmarshalSSZ ++ BumpMakeslice1 ++ MemmoveGrowsliceModel ++ ErrorfConvT64Model ++ tailLabels

-- Measured cause: `rfl` on the 330-directive host program stops with "maximum recursion depth" at
-- the default (512) in `program_length` and `placed_at_266` only; 1024 passes. The other host facts need no option.
set_option maxRecDepth 1024 in
theorem program_length : program.length = 330 := by rfl

instance host : Host := mkHost program (by rw [program_length]; decide)

theorem host_program_eq : Host.prog = program := rfl

theorem placed_at_5 : unmarshalSSZ.IsInfixAt Host.prog 5 :=
  infixAt_of dataLabels (BumpMakeslice1 ++ MemmoveGrowsliceModel ++ ErrorfConvT64Model ++ tailLabels) (by simp [host_program_eq, program, List.append_assoc]) rfl
theorem placed_at_234 : BumpMakeslice1.IsInfixAt Host.prog 234 :=
  infixAt_of (dataLabels ++ unmarshalSSZ) (MemmoveGrowsliceModel ++ ErrorfConvT64Model ++ tailLabels) (by simp [host_program_eq, program, List.append_assoc]) (by rfl)
theorem placed_at_240 : MemmoveGrowsliceModel.IsInfixAt Host.prog 240 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ BumpMakeslice1) (ErrorfConvT64Model ++ tailLabels) (by simp [host_program_eq, program, List.append_assoc]) (by rfl)
set_option maxRecDepth 1024 in
theorem placed_at_266 : ErrorfConvT64Model.IsInfixAt Host.prog 266 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ BumpMakeslice1 ++ MemmoveGrowsliceModel) tailLabels (by simp [host_program_eq, program, List.append_assoc]) (by rfl)

theorem labels_fresh_at_5 : LabelsFresh unmarshalSSZ 5 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_240 : LabelsFresh MemmoveGrowsliceModel 240 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_266 : LabelsFresh ErrorfConvT64Model 266 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem no_label_before_234 : ∀ i < 234, Host.prog[i]? ≠ some (.label "runtime.makeslice") :=
  notLabel_of (by rw [host_program_eq]; decide)

theorem label_write_barrier : label "runtime.writeBarrier" = 0x10000 :=
  mk_label program _ 0 _ (by simp [program, dataLabels]) (by decide)
theorem label_go_string : label "go_string._" = 0x10001 :=
  mk_label program _ 1 _ (by simp [program, dataLabels]) (by decide)
theorem label_bump_pointer : label "runtime.modelBumpPointer" = 0x10004 :=
  mk_label program _ 4 _ (by simp [program, dataLabels]) (by decide)
theorem label_error_string_itab : label "go_itab._errors.errorString_error" = 0x10119 :=
  mk_label program _ 281 _ (by simp [program, dataLabels]; rfl) (by decide)
theorem label_err_incorrect_list_size : label "ssz.ErrIncorrectListSize" = 0x10129 :=
  mk_label program _ 297 _ (by simp [program, dataLabels]; rfl) (by decide)
theorem label_err_list_too_big : label "ssz.ErrListTooBig" = 0x10139 :=
  mk_label program _ 313 _ (by simp [program, dataLabels]; rfl) (by decide)
theorem label_staticuint64s : label "runtime.staticuint64s" = 0x10149 :=
  mk_label program _ 329 _ (by simp [program, dataLabels]; rfl) (by decide)

abbrev zeros (k : Nat) : List UInt8 := List.replicate k 0

def block : List UInt8 :=
  ([0, 0, 0, 0]) ++ ((Int.toBytes 8 (0x10800 : BitVec 64).toInt) ++ ((zeros 277) ++ ((zeros 8) ++ ((Int.toBytes 8 (0x10119 : BitVec 64).toInt) ++ ((Int.toBytes 8 (0x10180 : BitVec 64).toInt) ++ ((Int.toBytes 8 (0x10119 : BitVec 64).toInt) ++ ((Int.toBytes 8 (0x10180 : BitVec 64).toInt) ++ ((zeros 32) ++ ((Int.toBytes 8 (4 : BitVec 64).toInt) ++ ((zeros 15) ++ ((Int.toBytes 8 (0x10190 : BitVec 64).toInt) ++ ((Int.toBytes 8 (3 : BitVec 64).toInt) ++ (([101, 114, 114]) ++ ((zeros 958) ++ ((Int.toBytes 8 (129 : BitVec 64).toInt) ++ ((zeros 263) ++ ((zeros 8) ++ ((zeros 8) ++ ((zeros 40) ++ ((zeros 8) ++ ((zeros 8) ++ ((zeros 8) ++ ((zeros 8) ++ ((zeros 32) ++ ((zeros 32) ++ ((zeros 8) ++ ((Int.toBytes 8 (0 : BitVec 64).toInt) ++ ((zeros 8) ++ ((zeros 8) ++ ((zeros 8) ++ ((zeros 8) ++ ((zeros 24) ++ ((Int.toBytes 8 (0 : BitVec 64).toInt) ++ ((zeros 8) ++ ((zeros 8) ++ ((zeros 8) ++ ((zeros 8) ++ ((zeros 8) ++ ((zeros 16) ++ ((zeros 32) ++ (([0x24, 0, 0, 0]) ++ ((zeros 92) ++ ((zeros 8400) ++ ((zeros 141565) ++ ((ElfData.PrysmTarget.formatColumnsTooBig) ++ ((zeros 12760) ++ ((ElfData.PrysmTarget.formatColumnsMisaligned))))))))))))))))))))))))))))))))))))))))))))))))

def mem : DataMem := block.At (0x10000 : BitVec 64)

def start_state (len : Nat) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10750, 0x10780, UInt64.ofNat len, 0, 0, UInt64.ofNat len, 0x10700, 0, 0, 0, 0, 0, 0, 0, 0x10730, 0⟩, zmms, flags, mem⟩

/-- **Non-vacuity of `Decode.reject_alignment_error_word_nonzero` (alignment reject)**, len = 40, `e0` = the itab address 0x10119 (≠ 0). -/
theorem runs_alignment (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax ≠ 0)
      ⟨start_state 40 zmms flags, Host.addrOf 5⟩ :=
  eventually_mono (Decode.reject_alignment_error_word_nonzero 5 placed_at_5 labels_fresh_at_5 (zeros 32) rfl (start_state 40 zmms flags) 0 0 65817 65920
    (65936 : BitVec 64) [101, 114, 114] (zeros 8) (by rw [label_error_string_itab]; rfl) (by decide) rfl
    (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 32) (zeros 40) (zeros 8) (zeros 8)
    (zeros 8) (zeros 8) (zeros 8) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl 8 rfl bumpHeap 8400 (fun _ => True)
    (by
      have H : Eq (block.At (0x10000 : BitVec 64)) mem := rfl
      witness_split [formatColumnsMisaligned_length, formatColumnsTooBig_length]
      have H2 : ((Eq ((Int.toBytes 8 (67584#64).toInt).At 65540#64) ⋆ Eq ((zeros 8400).At 67584#64)) ⋆ (Eq ([0, 0, 0, 0].At 65536#64) ⋆ Eq ((zeros 277).At 65548#64) ⋆ Eq ((zeros 8).At 65825#64) ⋆ Eq ((Int.toBytes 8 (65817#64).toInt).At 65833#64) ⋆ Eq ((Int.toBytes 8 (65920#64).toInt).At 65841#64) ⋆ Eq ((Int.toBytes 8 (65817#64).toInt).At 65849#64) ⋆ Eq ((Int.toBytes 8 (65920#64).toInt).At 65857#64) ⋆ Eq ((zeros 32).At 65865#64) ⋆ Eq ((Int.toBytes 8 (4#64).toInt).At 65897#64) ⋆ Eq ((zeros 15).At 65905#64) ⋆ Eq ((Int.toBytes 8 (65936#64).toInt).At 65920#64) ⋆ Eq ((Int.toBytes 8 (3#64).toInt).At 65928#64) ⋆ Eq ([101, 114, 114].At 65936#64) ⋆ Eq ((zeros 958).At 65939#64) ⋆ Eq ((Int.toBytes 8 (129#64).toInt).At 66897#64) ⋆ Eq ((zeros 263).At 66905#64) ⋆ Eq ((zeros 8).At 67168#64) ⋆ Eq ((zeros 8).At 67176#64) ⋆ Eq ((zeros 40).At 67184#64) ⋆ Eq ((zeros 8).At 67224#64) ⋆ Eq ((zeros 8).At 67232#64) ⋆ Eq ((zeros 8).At 67240#64) ⋆ Eq ((zeros 8).At 67248#64) ⋆ Eq ((zeros 32).At 67256#64) ⋆ Eq ((zeros 32).At 67288#64) ⋆ Eq ((zeros 8).At 67320#64) ⋆ Eq ((Int.toBytes 8 (0#64).toInt).At 67328#64) ⋆ Eq ((zeros 8).At 67336#64) ⋆ Eq ((zeros 8).At 67344#64) ⋆ Eq ((zeros 8).At 67352#64) ⋆ Eq ((zeros 8).At 67360#64) ⋆ Eq ((zeros 24).At 67368#64) ⋆ Eq ((Int.toBytes 8 (0#64).toInt).At 67392#64) ⋆ Eq ((zeros 8).At 67400#64) ⋆ Eq ((zeros 8).At 67408#64) ⋆ Eq ((zeros 8).At 67416#64) ⋆ Eq ((zeros 8).At 67424#64) ⋆ Eq ((zeros 8).At 67432#64) ⋆ Eq ((zeros 16).At 67440#64) ⋆ Eq ((zeros 32).At 67456#64) ⋆ Eq ([36, 0, 0, 0].At 67488#64) ⋆ Eq ((zeros 92).At 67492#64) ⋆ Eq ((zeros 141565).At 75984#64) ⋆ Eq (ElfData.PrysmTarget.formatColumnsTooBig.At 217549#64) ⋆ Eq ((zeros 12760).At 217612#64) ⋆ Eq (ElfData.PrysmTarget.formatColumnsMisaligned.At 230372#64))) mem := by ecancel
      have H3 := sep_mono_left (P' := bumpHeap 8400)
        (fun m hm => ⟨67584#64, by decide, by rw [label_bump_pointer]; exact hm⟩) H2
      apply sep_true
      simp only [start_state, ErrStr, ErrObj, ElfData.PrysmTarget.sszErrIncorrectListSize_addr_eq, formatColumnsMisaligned_addr_eq, label_err_incorrect_list_size, label_error_string_itab, label_go_string,
        label_write_barrier, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, Int64.toBitVec_add, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd, BitVec.reduceSub, Nat.reduceAdd, uint64_toBitVec_ofNat, offsetBytes, List.length_cons, List.length_nil]
      rw [staticBox_of_lt (by decide), Mem.At_append_sep _ _ _ (by simp [Int.toBytes_length])]
      simp only [Data.staticuint64s_addr, label_staticuint64s, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd,
        BitVec.reduceMul, Int.toBytes_length]
      ecancel)
    (by show (0 : UInt64).toNat + 16 < (0x10700 : UInt64).toNat; decide)
    (by show 36 ≤ (UInt64.ofNat 40).toNat; decide)
    (by show ((UInt64.ofNat 40).toNat - 36) % 8 ≠ 0; decide) (by rw [formatColumnsMisaligned_length]; decide)
    (bump_makeslice1 234 placed_at_234 no_label_before_234 _) (model_memmove 240 placed_at_240 labels_fresh_at_240 8)
    (model_convT64 266 placed_at_266 labels_fresh_at_266 8) (model_errorf_decimal_wrap 266 placed_at_266 labels_fresh_at_266 bumpHeap _ _ 8))
    (fun _ h => ⟨h.1, h.2.1⟩)

/-- **Non-vacuity of `Decode.reject_overflow_error_word_nonzero` (overflow reject)**, len = 36 + 8 · 129, `e0` = the itab address 0x10119 (≠ 0). -/
theorem runs_overflow (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax ≠ 0)
      ⟨start_state 1068 zmms flags, Host.addrOf 5⟩ :=
  eventually_mono (Decode.reject_overflow_error_word_nonzero 5 placed_at_5 labels_fresh_at_5 (zeros 32) rfl (start_state 1068 zmms flags) 0 0 65817 65920
    (65936 : BitVec 64) [101, 114, 114] (zeros 8) (by rw [label_error_string_itab]; rfl) (by decide) rfl
    (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 32) (zeros 40) (zeros 8) (zeros 8)
    (zeros 8) (zeros 8) (zeros 8) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl 8 rfl bumpHeap 8400 (fun _ => True)
    (by
      have H : Eq (block.At (0x10000 : BitVec 64)) mem := rfl
      witness_split [formatColumnsMisaligned_length, formatColumnsTooBig_length]
      have H2 : ((Eq ((Int.toBytes 8 (67584#64).toInt).At 65540#64) ⋆ Eq ((zeros 8400).At 67584#64)) ⋆ (Eq ([0, 0, 0, 0].At 65536#64) ⋆ Eq ((zeros 277).At 65548#64) ⋆ Eq ((zeros 8).At 65825#64) ⋆ Eq ((Int.toBytes 8 (65817#64).toInt).At 65833#64) ⋆ Eq ((Int.toBytes 8 (65920#64).toInt).At 65841#64) ⋆ Eq ((Int.toBytes 8 (65817#64).toInt).At 65849#64) ⋆ Eq ((Int.toBytes 8 (65920#64).toInt).At 65857#64) ⋆ Eq ((zeros 32).At 65865#64) ⋆ Eq ((Int.toBytes 8 (4#64).toInt).At 65897#64) ⋆ Eq ((zeros 15).At 65905#64) ⋆ Eq ((Int.toBytes 8 (65936#64).toInt).At 65920#64) ⋆ Eq ((Int.toBytes 8 (3#64).toInt).At 65928#64) ⋆ Eq ([101, 114, 114].At 65936#64) ⋆ Eq ((zeros 958).At 65939#64) ⋆ Eq ((Int.toBytes 8 (129#64).toInt).At 66897#64) ⋆ Eq ((zeros 263).At 66905#64) ⋆ Eq ((zeros 8).At 67168#64) ⋆ Eq ((zeros 8).At 67176#64) ⋆ Eq ((zeros 40).At 67184#64) ⋆ Eq ((zeros 8).At 67224#64) ⋆ Eq ((zeros 8).At 67232#64) ⋆ Eq ((zeros 8).At 67240#64) ⋆ Eq ((zeros 8).At 67248#64) ⋆ Eq ((zeros 32).At 67256#64) ⋆ Eq ((zeros 32).At 67288#64) ⋆ Eq ((zeros 8).At 67320#64) ⋆ Eq ((Int.toBytes 8 (0#64).toInt).At 67328#64) ⋆ Eq ((zeros 8).At 67336#64) ⋆ Eq ((zeros 8).At 67344#64) ⋆ Eq ((zeros 8).At 67352#64) ⋆ Eq ((zeros 8).At 67360#64) ⋆ Eq ((zeros 24).At 67368#64) ⋆ Eq ((Int.toBytes 8 (0#64).toInt).At 67392#64) ⋆ Eq ((zeros 8).At 67400#64) ⋆ Eq ((zeros 8).At 67408#64) ⋆ Eq ((zeros 8).At 67416#64) ⋆ Eq ((zeros 8).At 67424#64) ⋆ Eq ((zeros 8).At 67432#64) ⋆ Eq ((zeros 16).At 67440#64) ⋆ Eq ((zeros 32).At 67456#64) ⋆ Eq ([36, 0, 0, 0].At 67488#64) ⋆ Eq ((zeros 92).At 67492#64) ⋆ Eq ((zeros 141565).At 75984#64) ⋆ Eq (ElfData.PrysmTarget.formatColumnsTooBig.At 217549#64) ⋆ Eq ((zeros 12760).At 217612#64) ⋆ Eq (ElfData.PrysmTarget.formatColumnsMisaligned.At 230372#64))) mem := by ecancel
      have H3 := sep_mono_left (P' := bumpHeap 8400)
        (fun m hm => ⟨67584#64, by decide, by rw [label_bump_pointer]; exact hm⟩) H2
      apply sep_true
      simp only [start_state, ErrStr, ErrObj, ElfData.PrysmTarget.sszErrListTooBig_addr_eq, formatColumnsTooBig_addr_eq, label_err_list_too_big, label_error_string_itab, label_go_string,
        label_write_barrier, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, Int64.toBitVec_add, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd, BitVec.reduceSub, Nat.reduceAdd, offsetBytes, List.length_cons, List.length_nil]
      rw [UInt64.toNat_ofNat_of_lt' (by decide), show (1068 - 36) / 8 = 129 from rfl]
      rw [staticBox_of_lt (by decide), Mem.At_append_sep _ _ _ (by simp [Int.toBytes_length])]
      simp only [Data.staticuint64s_addr, label_staticuint64s, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd,
        BitVec.reduceMul, Int.toBytes_length]
      ecancel)
    (by show (0 : UInt64).toNat + 16 < (0x10700 : UInt64).toNat; decide)
    (by show 36 ≤ (UInt64.ofNat 1068).toNat; decide)
    (by show ((UInt64.ofNat 1068).toNat - 36) % 8 = 0; decide)
    (by show 128 < ((UInt64.ofNat 1068).toNat - 36) / 8; decide) (by rw [formatColumnsTooBig_length]; decide)
    (bump_makeslice1 234 placed_at_234 no_label_before_234 _) (model_memmove 240 placed_at_240 labels_fresh_at_240 8)
    (model_convT64 266 placed_at_266 labels_fresh_at_266 8) (model_errorf_decimal_wrap 266 placed_at_266 labels_fresh_at_266 bumpHeap _ _ 8))
    (fun _ h => ⟨h.1, h.2.1⟩)

end Prysm.DataColumnsByRootIdentifier.Witness.DecodeRejectAlignment
