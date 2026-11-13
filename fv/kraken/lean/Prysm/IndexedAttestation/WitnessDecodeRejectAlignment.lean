import Prysm.IndexedAttestation.DecodeRejectAlignment
import Runtime.ErrorModel
import Runtime.BumpAllocatorVariants
import Machine.WitnessHost
import Prysm.IndexedAttestation.DecodeRejectOverflow

/-!
# Witnesses of `Decode.reject_alignment_error_word_nonzero` (alignment reject) and `Decode.reject_overflow_error_word_nonzero` (overflow reject)

The premises of the corrected statements (`Prysm/IndexedAttestation/StatementsErrorWordNonzero.lean`) are satisfiable, `e0 ≠ 0` included, with a concrete
non-zero itab word. The text of the witness of the precedent misaligned reject of the Go 1.26.3 test type ListU64 (a module that is no longer in the tree).
Host: data labels (`go_string._` at 0x10001, the bump pointer label at 0x10004), the real Go 1.26.10
`(*v1alpha1.IndexedAttestation).UnmarshalSSZ` (index 5), `ErrorfConvT64Model` (284: `model_convT64`, `model_errorf_decimal_wrap`), then the
labels `go_itab._errors.errorString_error` (0x1012b, the value of `e0`), `ssz.ErrIncorrectListSize` (0x1013b),
`ssz.ErrListTooBig` (0x1014b) and `runtime.staticuint64s` (0x1015b), with pad labels between (a label's address is
0x10000 plus its index). One memory block at 0x10000: the bump pointer, the type word of the itab (0 bytes), the two
error globals (itab, `e1` = 0x10170), the static entry of 1, the errorString object (message "err"), the frame
(rsp = 0x10300, `S = 8`), the guard word, the 4 offset bytes of the input (the decoder reads no more bytes on these
paths), the 8320-byte heap, and the two format strings at `go_string._ + 163839` and `go_string._ + 171319`. The
frame `R` is `fun _ => True` (every other byte of the block).
Alignment reject: len = 229 (len − 228 = 1, misaligned; the box of 1 is the static entry). Overflow reject: len = 228 + 8 · 2049 (2049 > 2048
elements; the box is on the heap).
-/

open Machine Runtime Machine.Witness Prysm.IndexedAttestation.Code

namespace Prysm.IndexedAttestation.Witness.DecodeRejectAlignment


def dataLabels : Program :=
  [.label "runtime.writeBarrier", .label "go_string._", .label "pad2", .label "pad3", .label "runtime.modelBumpPointer"]

def tailLabels : Program := [.label "go_itab._errors.errorString_error", .label "pad_after_itab_0", .label "pad_after_itab_1", .label "pad_after_itab_2", .label "pad_after_itab_3", .label "pad_after_itab_4", .label "pad_after_itab_5", .label "pad_after_itab_6", .label "pad_after_itab_7", .label "pad_after_itab_8", .label "pad_after_itab_9", .label "pad_after_itab_10", .label "pad_after_itab_11", .label "pad_after_itab_12", .label "pad_after_itab_13", .label "pad_after_itab_14", .label "ssz.ErrIncorrectListSize", .label "pad_after_incorrect_list_size_0", .label "pad_after_incorrect_list_size_1", .label "pad_after_incorrect_list_size_2", .label "pad_after_incorrect_list_size_3", .label "pad_after_incorrect_list_size_4", .label "pad_after_incorrect_list_size_5", .label "pad_after_incorrect_list_size_6", .label "pad_after_incorrect_list_size_7", .label "pad_after_incorrect_list_size_8", .label "pad_after_incorrect_list_size_9", .label "pad_after_incorrect_list_size_10", .label "pad_after_incorrect_list_size_11", .label "pad_after_incorrect_list_size_12", .label "pad_after_incorrect_list_size_13", .label "pad_after_incorrect_list_size_14", .label "ssz.ErrListTooBig", .label "pad_after_list_too_big_0", .label "pad_after_list_too_big_1", .label "pad_after_list_too_big_2", .label "pad_after_list_too_big_3", .label "pad_after_list_too_big_4", .label "pad_after_list_too_big_5", .label "pad_after_list_too_big_6", .label "pad_after_list_too_big_7", .label "pad_after_list_too_big_8", .label "pad_after_list_too_big_9", .label "pad_after_list_too_big_10", .label "pad_after_list_too_big_11", .label "pad_after_list_too_big_12", .label "pad_after_list_too_big_13", .label "pad_after_list_too_big_14", .label "runtime.staticuint64s"]

def program : Program := dataLabels ++ unmarshalSSZ ++ ErrorfConvT64Model ++ tailLabels

-- Measured cause: `rfl` on the 348-directive host program stops with "maximum recursion depth" at
-- the default (512) in `program_length` and `placed_at_284` only; 1024 passes. The other host facts need no option.
set_option maxRecDepth 1024 in
theorem program_length : program.length = 348 := by rfl

instance host : Host := mkHost program (by rw [program_length]; decide)

theorem host_program_eq : Host.prog = program := rfl

theorem placed_at_5 : unmarshalSSZ.IsInfixAt Host.prog 5 :=
  infixAt_of dataLabels (ErrorfConvT64Model ++ tailLabels) (by simp [host_program_eq, program, List.append_assoc]) rfl
set_option maxRecDepth 1024 in
theorem placed_at_284 : ErrorfConvT64Model.IsInfixAt Host.prog 284 :=
  infixAt_of (dataLabels ++ unmarshalSSZ) tailLabels (by simp [host_program_eq, program, List.append_assoc]) (by rfl)

theorem labels_fresh_at_5 : LabelsFresh unmarshalSSZ 5 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_284 : LabelsFresh ErrorfConvT64Model 284 := labelsFresh_of (by rw [host_program_eq]; decide)

theorem label_bump_pointer : label "runtime.modelBumpPointer" = 0x10004 :=
  mk_label program _ 4 _ (by simp [program, dataLabels]) (by decide)
theorem label_go_string : label "go_string._" = 0x10001 :=
  mk_label program _ 1 _ (by simp [program, dataLabels]) (by decide)
theorem label_error_string_itab : label "go_itab._errors.errorString_error" = 0x1012b :=
  mk_label program _ 299 _ (by simp [program, dataLabels]; rfl) (by decide)
theorem label_err_incorrect_list_size : label "ssz.ErrIncorrectListSize" = 0x1013b :=
  mk_label program _ 315 _ (by simp [program, dataLabels]; rfl) (by decide)
theorem label_err_list_too_big : label "ssz.ErrListTooBig" = 0x1014b :=
  mk_label program _ 331 _ (by simp [program, dataLabels]; rfl) (by decide)
theorem label_staticuint64s : label "runtime.staticuint64s" = 0x1015b :=
  mk_label program _ 347 _ (by simp [program, dataLabels]; rfl) (by decide)

abbrev zeros (k : Nat) : List UInt8 := List.replicate k 0

def block : List UInt8 :=
  (zeros 4) ++ ((Int.toBytes 8 (0x10400 : BitVec 64).toInt) ++ ((zeros 295) ++ ((zeros 8) ++ ((Int.toBytes 8 (65835#64).toInt) ++ ((Int.toBytes 8 (65904#64).toInt) ++ ((Int.toBytes 8 (65835#64).toInt) ++ ((Int.toBytes 8 (65904#64).toInt) ++ ((zeros 8) ++ ((Int.toBytes 8 (1#64).toInt) ++ ((zeros 5) ++ ((Int.toBytes 8 (65920#64).toInt) ++ ((Int.toBytes 8 (BitVec.ofNat 64 3).toInt) ++ (([101, 114, 114]) ++ ((zeros 189) ++ ((zeros 8) ++ ((zeros 8) ++ ((zeros 40) ++ ((zeros 56) ++ ((zeros 32) ++ ((zeros 32) ++ ((zeros 8) ++ ((zeros 8) ++ ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt) ++ ((zeros 8) ++ ((zeros 8) ++ ((zeros 8) ++ ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt) ++ ((zeros 8) ++ (([0xe4, 0, 0, 0]) ++ ((zeros 204) ++ ((zeros 8320) ++ ((zeros 154496) ++ ((ElfData.PrysmTarget.formatAttestingIndicesTooBig) ++ ((zeros 7407) ++ (ElfData.PrysmTarget.formatAttestingIndicesMisaligned)))))))))))))))))))))))))))))))))))

def mem : DataMem := block.At (0x10000 : BitVec 64)

def start_state (len : Nat) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0, 0x10330, UInt64.ofNat len, 0, 0, UInt64.ofNat len, 0x10300, 0, 0, 0, 0, 0, 0, 0, 0x10310, 0⟩, zmms, flags, mem⟩

/-- **Non-vacuity of `Decode.reject_alignment_error_word_nonzero` (alignment reject)**, len = 229, `e0` = the itab address 0x1012b (≠ 0). -/
theorem runs_alignment (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax ≠ 0)
      ⟨start_state 229 zmms flags, Host.addrOf 5⟩ :=
  eventually_mono (Decode.reject_alignment_error_word_nonzero 5 placed_at_5 labels_fresh_at_5 (start_state 229 zmms flags) 0 0 65835 65904 (65920 : BitVec 64)
    [101, 114, 114] (zeros 8) (by rw [label_error_string_itab]; rfl) (by decide) rfl
    (zeros 8) (zeros 8) (zeros 32) (zeros 40) (zeros 8) (zeros 8) rfl rfl rfl rfl rfl 8 rfl bumpHeap 8320 (fun _ => True)
    (by
      have H : Eq (block.At (0x10000 : BitVec 64)) mem := rfl
      witness_split [formatMisaligned_length, formatTooBig_length]
      simp only [UInt64.toBitVec_ofNat] at H
      have H2 : ((Eq ((Int.toBytes 8 (66560#64).toInt).At 65540#64) ⋆ Eq ((zeros 8320).At 66560#64)) ⋆ (Eq ((zeros 4).At 65536#64) ⋆ Eq ((zeros 295).At 65548#64) ⋆ Eq ((zeros 8).At 65843#64) ⋆ Eq ((Int.toBytes 8 (65835#64).toInt).At 65851#64) ⋆ Eq ((Int.toBytes 8 (65904#64).toInt).At 65859#64) ⋆ Eq ((Int.toBytes 8 (65835#64).toInt).At 65867#64) ⋆ Eq ((Int.toBytes 8 (65904#64).toInt).At 65875#64) ⋆ Eq ((zeros 8).At 65883#64) ⋆ Eq ((Int.toBytes 8 (1#64).toInt).At 65891#64) ⋆ Eq ((zeros 5).At 65899#64) ⋆ Eq ((Int.toBytes 8 (65920#64).toInt).At 65904#64) ⋆ Eq ((Int.toBytes 8 (3#64).toInt).At 65912#64) ⋆ Eq (([101, 114, 114]).At 65920#64) ⋆ Eq ((zeros 189).At 65923#64) ⋆ Eq ((zeros 8).At 66112#64) ⋆ Eq ((zeros 8).At 66120#64) ⋆ Eq ((zeros 40).At 66128#64) ⋆ Eq ((zeros 56).At 66168#64) ⋆ Eq ((zeros 32).At 66224#64) ⋆ Eq ((zeros 32).At 66256#64) ⋆ Eq ((zeros 8).At 66288#64) ⋆ Eq ((zeros 8).At 66296#64) ⋆ Eq ((Int.toBytes 8 (0#64).toInt).At 66304#64) ⋆ Eq ((zeros 8).At 66312#64) ⋆ Eq ((zeros 8).At 66320#64) ⋆ Eq ((zeros 8).At 66328#64) ⋆ Eq ((Int.toBytes 8 (0#64).toInt).At 66336#64) ⋆ Eq ((zeros 8).At 66344#64) ⋆ Eq (([228, 0, 0, 0]).At 66352#64) ⋆ Eq ((zeros 204).At 66356#64) ⋆ Eq ((zeros 154496).At 74880#64) ⋆ Eq ((ElfData.PrysmTarget.formatAttestingIndicesTooBig).At 229376#64) ⋆ Eq ((zeros 7407).At 229449#64) ⋆ Eq ((ElfData.PrysmTarget.formatAttestingIndicesMisaligned).At 236856#64))) mem := by ecancel
      have H3 := sep_mono_left (P' := bumpHeap 8320)
        (fun m hm => ⟨66560#64, by decide, by rw [label_bump_pointer]; exact hm⟩) H2
      apply sep_true
      simp only [start_state, ErrStr, ErrObj, ElfData.PrysmTarget.sszErrIncorrectListSize_addr_eq, ElfData.PrysmTarget.formatAttestingIndicesMisaligned_addr_eq, label_err_incorrect_list_size, label_error_string_itab, label_go_string,
        UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, Int64.toBitVec_add, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd,
        BitVec.reduceSub, Nat.reduceAdd, uint64_toBitVec_ofNat, offsetBytes, List.length_cons, List.length_nil]
      rw [staticBox_of_lt (by decide), Mem.At_append_sep _ _ _ (by simp [Int.toBytes_length])]
      simp only [Data.staticuint64s_addr, label_staticuint64s, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd,
        BitVec.reduceMul, Int.toBytes_length]
      ecancel)
    (by show (0 : UInt64).toNat + 48 < (0x10300 : UInt64).toNat; decide)
    (by show 228 ≤ (UInt64.ofNat 229).toNat; decide)
    (by show ((UInt64.ofNat 229).toNat - 228) % 8 ≠ 0; decide) (by rw [formatMisaligned_length]; decide)
    (model_convT64 284 placed_at_284 labels_fresh_at_284 8) (model_errorf_decimal_wrap 284 placed_at_284 labels_fresh_at_284 bumpHeap _ _ 8))
    (fun _ h => ⟨h.1, h.2.1⟩)


/-- **Non-vacuity of `Decode.reject_overflow_error_word_nonzero` (overflow reject)**, len = 228 + 8 · 2049, `e0` = the itab address 0x1012b (≠ 0). -/
theorem runs_overflow (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax ≠ 0)
      ⟨start_state 16620 zmms flags, Host.addrOf 5⟩ :=
  eventually_mono (Decode.reject_overflow_error_word_nonzero 5 placed_at_5 labels_fresh_at_5 (start_state 16620 zmms flags) 0 0 65835 65904 (65920 : BitVec 64)
    [101, 114, 114] (zeros 8) (by rw [label_error_string_itab]; rfl) (by decide) rfl
    (zeros 8) (zeros 8) (zeros 32) (zeros 40) (zeros 8) (zeros 8) rfl rfl rfl rfl rfl 8 rfl bumpHeap 8320 (fun _ => True)
    (by
      have H : Eq (block.At (0x10000 : BitVec 64)) mem := rfl
      witness_split [formatMisaligned_length, formatTooBig_length]
      simp only [UInt64.toBitVec_ofNat] at H
      have H2 : ((Eq ((Int.toBytes 8 (66560#64).toInt).At 65540#64) ⋆ Eq ((zeros 8320).At 66560#64)) ⋆ (Eq ((zeros 4).At 65536#64) ⋆ Eq ((zeros 295).At 65548#64) ⋆ Eq ((zeros 8).At 65843#64) ⋆ Eq ((Int.toBytes 8 (65835#64).toInt).At 65851#64) ⋆ Eq ((Int.toBytes 8 (65904#64).toInt).At 65859#64) ⋆ Eq ((Int.toBytes 8 (65835#64).toInt).At 65867#64) ⋆ Eq ((Int.toBytes 8 (65904#64).toInt).At 65875#64) ⋆ Eq ((zeros 8).At 65883#64) ⋆ Eq ((Int.toBytes 8 (1#64).toInt).At 65891#64) ⋆ Eq ((zeros 5).At 65899#64) ⋆ Eq ((Int.toBytes 8 (65920#64).toInt).At 65904#64) ⋆ Eq ((Int.toBytes 8 (3#64).toInt).At 65912#64) ⋆ Eq (([101, 114, 114]).At 65920#64) ⋆ Eq ((zeros 189).At 65923#64) ⋆ Eq ((zeros 8).At 66112#64) ⋆ Eq ((zeros 8).At 66120#64) ⋆ Eq ((zeros 40).At 66128#64) ⋆ Eq ((zeros 56).At 66168#64) ⋆ Eq ((zeros 32).At 66224#64) ⋆ Eq ((zeros 32).At 66256#64) ⋆ Eq ((zeros 8).At 66288#64) ⋆ Eq ((zeros 8).At 66296#64) ⋆ Eq ((Int.toBytes 8 (0#64).toInt).At 66304#64) ⋆ Eq ((zeros 8).At 66312#64) ⋆ Eq ((zeros 8).At 66320#64) ⋆ Eq ((zeros 8).At 66328#64) ⋆ Eq ((Int.toBytes 8 (0#64).toInt).At 66336#64) ⋆ Eq ((zeros 8).At 66344#64) ⋆ Eq (([228, 0, 0, 0]).At 66352#64) ⋆ Eq ((zeros 204).At 66356#64) ⋆ Eq ((zeros 154496).At 74880#64) ⋆ Eq ((ElfData.PrysmTarget.formatAttestingIndicesTooBig).At 229376#64) ⋆ Eq ((zeros 7407).At 229449#64) ⋆ Eq ((ElfData.PrysmTarget.formatAttestingIndicesMisaligned).At 236856#64))) mem := by ecancel
      have H3 := sep_mono_left (P' := bumpHeap 8320)
        (fun m hm => ⟨66560#64, by decide, by rw [label_bump_pointer]; exact hm⟩) H2
      apply sep_true
      simp only [start_state, ErrStr, ErrObj, ElfData.PrysmTarget.sszErrListTooBig_addr_eq, ElfData.PrysmTarget.formatAttestingIndicesTooBig_addr_eq, label_err_list_too_big, label_error_string_itab, label_go_string,
        UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, Int64.toBitVec_add, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd,
        BitVec.reduceSub, Nat.reduceAdd, offsetBytes, List.length_cons, List.length_nil]
      rw [UInt64.toNat_ofNat_of_lt' (by decide), show (16620 - 228) / 8 = 2049 from rfl]
      simp only [StaticBox, show ((BitVec.ofNat 64 2049).toNat < 256) = False from by decide, ↓reduceIte]
      rw [nil_At_emp, Mem.At_append_sep _ _ _ (by simp [Int.toBytes_length])]
      simp only [BitVec.reduceAdd, Int.toBytes_length]
      ecancel)
    (by show (0 : UInt64).toNat + 48 < (0x10300 : UInt64).toNat; decide)
    (by show 228 ≤ (UInt64.ofNat 16620).toNat; decide)
    (by show ((UInt64.ofNat 16620).toNat - 228) % 8 = 0; decide)
    (by show 2048 < ((UInt64.ofNat 16620).toNat - 228) / 8; decide) (by rw [formatTooBig_length]; decide)
    (model_convT64 284 placed_at_284 labels_fresh_at_284 8) (model_errorf_decimal_wrap 284 placed_at_284 labels_fresh_at_284 bumpHeap _ _ 8))
    (fun _ h => ⟨h.1, h.2.1⟩)

end Prysm.IndexedAttestation.Witness.DecodeRejectAlignment
