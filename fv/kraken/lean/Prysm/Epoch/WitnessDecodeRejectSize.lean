import Prysm.Epoch.DecodeRejectSize
import Runtime.ErrorModel
import Machine.WitnessHost

/-!
# Witnesses of `Decode.reject_size` (len 7, 9 and 300)

Host: four data labels (`go_string._` at 0x10000, `runtime.gcbits._` 0x10001,
`runtime.staticuint64s` 0x10002, `runtime.fvBump` 0x10003), the real Go 1.26.10
`(*primitives.Epoch).UnmarshalSSZ` (index 4) and `RtErr` (index 67: the
`rt_convT64` model on the bump heap, `rt_errorf_dd`). One memory block from
0x10003 to the format string at `go_string._ + 110057`: bump pointer, the
`staticuint64s` entries 7 and 8, the static box `e2eEight`, an 8280-byte heap,
the guard word, the 112-byte stack window (rsp = 0x12659), and the 40 format
bytes `e2eEpFmt`; the fillers between them and the unused rax spill slot are the
frame `R`. With `len(buf) = 7` the decoder returns a non-nil error.
-/

open Machine Runtime Machine.Witness Prysm.Epoch.Code

namespace Prysm.Epoch.Witness.DecodeRejectSize

set_option maxRecDepth 100000

def dataLabels : Program :=
  [.label "go_string._", .label "runtime.gcbits._", .label "runtime.staticuint64s", .label "runtime.fvBump"]

def P : Program := dataLabels ++ unmarshalSSZ ++ RtErr

theorem P_len : P.length = 82 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem prog_eq : Host.prog = P := rfl

theorem hk4 : unmarshalSSZ.IsInfixAt Host.prog 4 :=
  infixAt_of dataLabels RtErr (by simp [prog_eq, P, List.append_assoc]) rfl
theorem hk67 : RtErr.IsInfixAt Host.prog 67 :=
  infixAt_of (dataLabels ++ unmarshalSSZ) [] (by simp [prog_eq, P, List.append_assoc]) (by rfl)
theorem hf4 : LabelsFresh unmarshalSSZ 4 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf67 : LabelsFresh RtErr 67 := labelsFresh_of (by rw [prog_eq]; decide)

theorem label_gs : label "go_string._" = 0x10000 := mk_label P _ 0 _ (by simp [P, dataLabels]) (by simp [labs])
theorem label_gc : label "runtime.gcbits._" = 0x10001 := mk_label P _ 1 _ (by simp [P, dataLabels]) (by decide)
theorem label_st : label "runtime.staticuint64s" = 0x10002 := mk_label P _ 2 _ (by simp [P, dataLabels]) (by decide)
theorem label_bump : label "runtime.fvBump" = 0x10003 := mk_label P _ 3 _ (by simp [P, dataLabels]) (by decide)

theorem eight_len : ElfData.PrysmTarget.e2eEight.length = 8 := by decide

abbrev z (k : Nat) : List UInt8 := List.replicate k 0
abbrev w (v : UInt64) : List UInt8 := Int.toBytes 8 v.toBitVec.toInt

/-- bump ptr · F1 · box 7 · box 8 · F2 · eight · heap · guard · rslot · sp8 · sp32 · a40 · a24 · fp · ret · s1 · s2 · F3 · fs. -/
def block : List UInt8 :=
  Int.toBytes 8 (0x105a1 : BitVec 64).toInt ++ (z 47 ++ (Int.toBytes 8 (7 : BitVec 64).toInt
    ++ (Int.toBytes 8 (8 : BitVec 64).toInt ++ (z 1359 ++ (ElfData.PrysmTarget.e2eEight ++ (z 8280 ++ (w 0 ++ (z 8 ++ (z 8
    ++ (z 32 ++ (z 16 ++ (z 16 ++ (z 8 ++ (w 0 ++ (z 8 ++ (z 8 ++ (z 100216 ++ ElfData.PrysmTarget.e2eEpFmt)))))))))))))))))

def mem : DataMem := block.At (0x10003 : BitVec 64)

def cs0 (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x13000, 0x14000, 7, 0, 0, 0, 0x12659, 0, 0, 0, 0, 0, 0, 0, 0x125e9, 0⟩, zmms, flags, mem⟩

def R0 : DataMem → Prop :=
  Eq ((z 47).At (0x1000b : BitVec 64)) ⋆ Eq ((z 1359).At (0x1004a : BitVec 64))
    ⋆ Eq ((z 8).At (0x12661 : BitVec 64)) ⋆ Eq ((z 100216).At (0x12671 : BitVec 64))

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x105a1 : BitVec 64).toInt).At (0x10003 : BitVec 64))
      ⋆ (Eq ((z 8280).At (0x105a1 : BitVec 64)) ⋆ X)) m) : (bumpHeap 8280 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x105a1, by decide, by rw [label_bump]; exact hm⟩) h

set_option maxHeartbeats 16000000 in
/-- **Non-vacuity of `Decode.reject_size`** (len 7). -/
theorem runs (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax ≠ 0)
      ⟨cs0 zmms flags, Host.addrOf 4⟩ :=
  eventually_mono (Decode.reject_size 4 hk4 hf4 (cs0 zmms flags) 0 0 (z 8) (z 8) (z 16) (z 16) (z 8) (z 32)
    (z 8) rfl rfl rfl rfl rfl rfl rfl 0 [] rfl bumpHeap 8280 R0
    (by
      have H : Eq (block.At (0x10003 : BitVec 64)) mem := rfl
      wit_split [eight_len, Decode.reject_fmt_len]
      -- bump pointer, F1, box 7, box 8, F2, ... : move the heap next to the pointer
      rw [Std.ExtHashMap.sep_comm_l (Eq (ElfData.PrysmTarget.e2eEight.At _)) (Eq ((z 8280).At _)),
        Std.ExtHashMap.sep_comm_l (Eq ((z 1359).At _)) (Eq ((z 8280).At _)),
        Std.ExtHashMap.sep_comm_l (Eq ((Int.toBytes 8 (8#64).toInt).At _)) (Eq ((z 8280).At _)),
        Std.ExtHashMap.sep_comm_l (Eq ((Int.toBytes 8 (7#64).toInt).At _)) (Eq ((z 8280).At _)),
        Std.ExtHashMap.sep_comm_l (Eq ((z 47).At _)) (Eq ((z 8280).At _))] at H
      have H2 := lift_heap H
      rw [staticBox_of_lt (v := 8) (by decide), staticBox_of_lt (v := (cs0 zmms flags).regs.rcx.toBitVec) (by simp [cs0])]
      simp only [cs0, R0, w, Runtime.Data.staticuint64s_addr, ElfData.PrysmTarget.e2eEpFmt_addr, ElfData.PrysmTarget.e2eEight_addr, label_gs,
        label_gc, label_st, nil_At_emp, Std.ExtHashMap.sep_emp, Std.ExtHashMap.emp_sep, UInt64.toBitVec_ofNat,
        Int64.toBitVec_ofNat, Int64.toBitVec_add, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub,
        BitVec.reduceMul] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [cs0]) (by simp [cs0]) (by omega) (rt_convT64 67 hk67 hf67 0)
    (rt_errorf_dd 67 hk67 hf67 bumpHeap ElfData.PrysmTarget.e2eEpFmt ElfData.PrysmTarget.e2eIntType_addr 0))
    (fun _ h => ⟨h.1, h.2.1⟩)

/-! ## len 9 and len 300

Same Host and layout. len 9: the static entries 8 and 9 at 0x10042 and 0x1004a. len 300 (≥ 256):
`StaticBox 300` is empty and `convT64` takes the heap-box branch (`BoxIn` right disjunct: an 8-byte
allocation from the bump heap). -/

theorem staticBox_big (v : BitVec 64) (h : 256 ≤ v.toNat) : StaticBox v = Eq (([] : List UInt8).At 0) := by
  unfold StaticBox; rw [if_neg (by omega)]

namespace InputLength9

def block : List UInt8 :=
  Int.toBytes 8 (0x105a1 : BitVec 64).toInt ++ (z 55 ++ (Int.toBytes 8 (8 : BitVec 64).toInt
    ++ (Int.toBytes 8 (9 : BitVec 64).toInt ++ (z 1351 ++ (ElfData.PrysmTarget.e2eEight ++ (z 8280 ++ (w 0 ++ (z 8 ++ (z 8
    ++ (z 32 ++ (z 16 ++ (z 16 ++ (z 8 ++ (w 0 ++ (z 8 ++ (z 8 ++ (z 100216 ++ ElfData.PrysmTarget.e2eEpFmt)))))))))))))))))

def mem : DataMem := block.At (0x10003 : BitVec 64)

def cs0 (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x13000, 0x14000, 9, 0, 0, 0, 0x12659, 0, 0, 0, 0, 0, 0, 0, 0x125e9, 0⟩, zmms, flags, mem⟩

def R0 : DataMem → Prop :=
  Eq ((z 55).At (0x1000b : BitVec 64)) ⋆ Eq ((z 1351).At (0x10052 : BitVec 64))
    ⋆ Eq ((z 8).At (0x12661 : BitVec 64)) ⋆ Eq ((z 100216).At (0x12671 : BitVec 64))

set_option maxHeartbeats 16000000 in
/-- **Non-vacuity of `Decode.reject_size`** (len 9, static box). -/
theorem runs (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax ≠ 0)
      ⟨cs0 zmms flags, Host.addrOf 4⟩ :=
  eventually_mono (Decode.reject_size 4 hk4 hf4 (cs0 zmms flags) 0 0 (z 8) (z 8) (z 16) (z 16) (z 8) (z 32)
    (z 8) rfl rfl rfl rfl rfl rfl rfl 0 [] rfl bumpHeap 8280 R0
    (by
      have H : Eq (block.At (0x10003 : BitVec 64)) mem := rfl
      wit_split [eight_len, Decode.reject_fmt_len]
      rw [Std.ExtHashMap.sep_comm_l (Eq (ElfData.PrysmTarget.e2eEight.At _)) (Eq ((z 8280).At _)),
        Std.ExtHashMap.sep_comm_l (Eq ((z 1351).At _)) (Eq ((z 8280).At _)),
        Std.ExtHashMap.sep_comm_l (Eq ((Int.toBytes 8 (9#64).toInt).At _)) (Eq ((z 8280).At _)),
        Std.ExtHashMap.sep_comm_l (Eq ((Int.toBytes 8 (8#64).toInt).At _)) (Eq ((z 8280).At _)),
        Std.ExtHashMap.sep_comm_l (Eq ((z 55).At _)) (Eq ((z 8280).At _))] at H
      have H2 := lift_heap H
      rw [staticBox_of_lt (v := 8) (by decide), staticBox_of_lt (v := (cs0 zmms flags).regs.rcx.toBitVec) (by simp [cs0])]
      simp only [cs0, R0, w, Runtime.Data.staticuint64s_addr, ElfData.PrysmTarget.e2eEpFmt_addr, ElfData.PrysmTarget.e2eEight_addr, label_gs,
        label_gc, label_st, nil_At_emp, Std.ExtHashMap.sep_emp, Std.ExtHashMap.emp_sep, UInt64.toBitVec_ofNat,
        Int64.toBitVec_ofNat, Int64.toBitVec_add, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub,
        BitVec.reduceMul] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [cs0]) (by simp [cs0]) (by omega) (rt_convT64 67 hk67 hf67 0)
    (rt_errorf_dd 67 hk67 hf67 bumpHeap ElfData.PrysmTarget.e2eEpFmt ElfData.PrysmTarget.e2eIntType_addr 0))
    (fun _ h => ⟨h.1, h.2.1⟩)

end InputLength9

namespace InputLength300

def block : List UInt8 :=
  Int.toBytes 8 (0x105a1 : BitVec 64).toInt ++ (z 55 ++ (Int.toBytes 8 (8 : BitVec 64).toInt
    ++ (z 1359 ++ (ElfData.PrysmTarget.e2eEight ++ (z 8280 ++ (w 0 ++ (z 8 ++ (z 8
    ++ (z 32 ++ (z 16 ++ (z 16 ++ (z 8 ++ (w 0 ++ (z 8 ++ (z 8 ++ (z 100216 ++ ElfData.PrysmTarget.e2eEpFmt))))))))))))))))

def mem : DataMem := block.At (0x10003 : BitVec 64)

def cs0 (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x13000, 0x14000, 300, 0, 0, 0, 0x12659, 0, 0, 0, 0, 0, 0, 0, 0x125e9, 0⟩, zmms, flags, mem⟩

def R0 : DataMem → Prop :=
  Eq ((z 55).At (0x1000b : BitVec 64)) ⋆ Eq ((z 1359).At (0x1004a : BitVec 64))
    ⋆ Eq ((z 8).At (0x12661 : BitVec 64)) ⋆ Eq ((z 100216).At (0x12671 : BitVec 64))

set_option maxHeartbeats 16000000 in
/-- **Non-vacuity of `Decode.reject_size`** (len 300 ≥ 256: heap box). -/
theorem runs (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax ≠ 0)
      ⟨cs0 zmms flags, Host.addrOf 4⟩ :=
  eventually_mono (Decode.reject_size 4 hk4 hf4 (cs0 zmms flags) 0 0 (z 8) (z 8) (z 16) (z 16) (z 8) (z 32)
    (z 8) rfl rfl rfl rfl rfl rfl rfl 0 [] rfl bumpHeap 8280 R0
    (by
      have H : Eq (block.At (0x10003 : BitVec 64)) mem := rfl
      wit_split [eight_len, Decode.reject_fmt_len]
      rw [Std.ExtHashMap.sep_comm_l (Eq (ElfData.PrysmTarget.e2eEight.At _)) (Eq ((z 8280).At _)),
        Std.ExtHashMap.sep_comm_l (Eq ((z 1359).At _)) (Eq ((z 8280).At _)),
        Std.ExtHashMap.sep_comm_l (Eq ((Int.toBytes 8 (8#64).toInt).At _)) (Eq ((z 8280).At _)),
        Std.ExtHashMap.sep_comm_l (Eq ((z 55).At _)) (Eq ((z 8280).At _))] at H
      have H2 := lift_heap H
      rw [staticBox_of_lt (v := 8) (by decide), staticBox_big (cs0 zmms flags).regs.rcx.toBitVec (by simp [cs0])]
      simp only [cs0, R0, w, Runtime.Data.staticuint64s_addr, ElfData.PrysmTarget.e2eEpFmt_addr, ElfData.PrysmTarget.e2eEight_addr, label_gs,
        label_gc, label_st, nil_At_emp, Std.ExtHashMap.sep_emp, Std.ExtHashMap.emp_sep, UInt64.toBitVec_ofNat,
        Int64.toBitVec_ofNat, Int64.toBitVec_add, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub,
        BitVec.reduceMul] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [cs0]) (by simp [cs0]) (by omega) (rt_convT64 67 hk67 hf67 0)
    (rt_errorf_dd 67 hk67 hf67 bumpHeap ElfData.PrysmTarget.e2eEpFmt ElfData.PrysmTarget.e2eIntType_addr 0))
    (fun _ h => ⟨h.1, h.2.1⟩)

end InputLength300

end Prysm.Epoch.Witness.DecodeRejectSize
