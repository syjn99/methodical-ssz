import Prysm.Checkpoint.EncodeCover
import Runtime.CopyModel
import Machine.WitnessHost
import Machine.WitnessSplit

/-!
# Witness of `Encode.reject_length_cover`: `len(Root) ≠ 32`, every capacity range

Host: data labels (the bump pointer, `ssz.ErrBytesLength` at 0x10008), the real Go 1.26.10
`(*v1alpha1.Checkpoint).MarshalSSZTo` (index 9) and `MemmoveGrowsliceModel` (index 100: `model_growslice` — new capacity `2·newLen + 192` from the bump heap — and `model_memmove`,
both with `S = 0`). One memory block at `0x10000`: bump pointer, the two `ssz.ErrBytesLength` words
(stand-ins 0x10e8, 0x2b: the real values are set by the runtime's init; non-nil-ness is not proved),
a 9000-byte heap, guard word (r14 = 0x12330), the 72-byte receiver (`Root` = (0x5000, rl, 48),
`rl ≠ 32`), the stack window (rsp = 0x12408) and `dst` at 0x12428 = a 30-byte prefix and `n` spare
bytes. Frame `R` = `emp`. Instances: n = 0 (cap = len: first growslice, then the reject), 3, 8
(cap = len + 8: no growth), 40; nil `dst`.
-/

open Machine Runtime Machine.Witness Prysm.Checkpoint.Code EthLib.Serialization.Ssz

namespace Prysm.Checkpoint.Witness.EncodeRejectLengthCover

set_option maxRecDepth 100000

def dataLabels : Program :=
  [.label "runtime.modelBumpPointer", .label "pad1", .label "pad2", .label "pad3", .label "pad4", .label "pad5",
   .label "pad6", .label "pad7", .label "ssz.ErrBytesLength"]

def program : Program := dataLabels ++ marshalSSZTo ++ MemmoveGrowsliceModel

theorem program_length : program.length = 126 := by rfl

instance host : Host := mkHost program (by rw [program_length]; decide)

theorem host_program_eq : Host.prog = program := rfl

theorem placed_at_9 : marshalSSZTo.IsInfixAt Host.prog 9 :=
  infixAt_of dataLabels MemmoveGrowsliceModel (by simp [host_program_eq, program, List.append_assoc]) rfl

theorem placed_at_100 : MemmoveGrowsliceModel.IsInfixAt Host.prog 100 :=
  infixAt_of (dataLabels ++ marshalSSZTo) [] (by simp [host_program_eq, program, List.append_assoc]) (by rfl)

theorem labels_fresh_at_9 : LabelsFresh marshalSSZTo 9 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_100 : LabelsFresh MemmoveGrowsliceModel 100 := labelsFresh_of (by rw [host_program_eq]; decide)

theorem label_bump_pointer : label "runtime.modelBumpPointer" = 0x10000 :=
  mk_label program _ 0 _ (by simp [program, dataLabels]) (by simp [programLabels])

theorem label_err_bytes_length : label "ssz.ErrBytesLength" = 0x10008 :=
  mk_label program _ 8 _ (by simp [program, dataLabels]) (by decide)

abbrev zeros (k : Nat) : List UInt8 := List.replicate k 0
abbrev word_bytes (v : UInt64) : List UInt8 := Int.toBytes 8 v.toBitVec.toInt
def prefix30 : List UInt8 := (List.range 30).map (fun i => UInt8.ofNat (0x40 + i))

/-- bump pointer · ErrBytesLength words · heap (9000) · guard · receiver (72) · rslot · growslice spill (40)
· l72 · t40 (16) · t30 (16) · l32 · l24 · l16 · fp · return slot · spill rax · spill rbx · spill rcx · dst. -/
def block (e8 : List UInt8) (rl : UInt64) (dst : List UInt8) : List UInt8 :=
  Int.toBytes 8 (0x10018 : BitVec 64).toInt ++ (word_bytes 0x10e8 ++ (word_bytes 0x2b ++ (zeros 9000 ++ (word_bytes 0 ++ (zeros 8 ++ (e8 ++ (word_bytes 0x5000
    ++ (word_bytes rl ++ (word_bytes 48 ++ (zeros 32 ++ (zeros 8 ++ (zeros 40 ++ (zeros 8 ++ (zeros 16 ++ (zeros 16 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (word_bytes 0
    ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ dst)))))))))))))))))))))))

def mem (e8 : List UInt8) (rl : UInt64) (dst : List UInt8) : DataMem := (block e8 rl dst).At (0x10000 : BitVec 64)

def initial_state (e8 : List UInt8) (rl : UInt64) (dst : List UInt8) (rbx len cap : UInt64) (zmms : RegZmms) (flags : StatusFlags) :
    MachineData :=
  ⟨⟨0x12348, rbx, len, 0, 0, cap, 0x12408, 0, 0, 0, 0, 0, 0, 0, 0x12330, 0⟩, zmms, flags, mem e8 rl dst⟩

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x10018 : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((zeros 9000).At (0x10018 : BitVec 64)) ⋆ X)) m) : (bumpHeap 9000 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x10018, by decide, by rw [label_bump_pointer]; exact hm⟩) h

set_option maxHeartbeats 64000000 in
/-- **Non-vacuity of `Encode.reject_length_cover`**, len 30, cap 30 + n (n ≤ 64). -/
theorem runs (e8 : List UInt8) (he8 : e8.length = 8) (rl : UInt64) (hrl : rl ≠ 32) (n : Nat) (hn : n ≤ 64)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rcx = 0 ∧ st.data.regs.rdi = 0x10e8 ∧ st.data.regs.rsi = 0x2b)
      ⟨initial_state e8 rl (prefix30 ++ zeros n) 0x12428 30 (UInt64.ofNat (30 + n)) zmms flags, Host.addrOf 9⟩ := by
  have hc : (UInt64.ofNat (30 + n)).toNat = 30 + n := by simp; omega
  refine eventually_mono (Encode.reject_length_cover 9 placed_at_9 labels_fresh_at_9 (zeros 8) e8 (word_bytes 48) (zeros 32) prefix30 (zeros n) rfl he8 rfl rfl
    0x5000 rl 0x10e8 0x2b hrl (initial_state e8 rl (prefix30 ++ zeros n) 0x12428 30 (UInt64.ofNat (30 + n)) zmms flags) 0 0 rfl (by simp only [initial_state, hc]; simp [prefix30])
    (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 16) (zeros 16) (zeros 8) (zeros 40) (zeros 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    Std.ExtHashMap.emp 0 [] rfl bumpHeap 9000
    (by
      have H : Eq ((block e8 rl (prefix30 ++ zeros n)).At (0x10000 : BitVec 64)) (mem e8 rl (prefix30 ++ zeros n)) := rfl
      witness_split_n [he8, show prefix30.length = 30 from rfl]
      rw [Std.ExtHashMap.sep_comm_l (Eq ((word_bytes 0x2b).At _)) (Eq ((zeros 9000).At _)),
        Std.ExtHashMap.sep_comm_l (Eq ((word_bytes 0x10e8).At _)) (Eq ((zeros 9000).At _))] at H
      have H2 := lift_heap H
      rw [at_app prefix30 (zeros n) rfl (by simp [prefix30]; omega)]
      simp only [initial_state, word_bytes, nil_At_emp, List.nil_append, Std.ExtHashMap.sep_emp, Std.ExtHashMap.emp_sep,
        show prefix30.length = 30 from rfl, ElfData.PrysmTarget.sszErrBytesLength_addr, label_err_bytes_length,
        UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, Int64.toBitVec_add, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub,
        List.length_nil] at H2 ⊢
      generalize e8 = e8' at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [initial_state]) (by simp [initial_state]) (by simp [initial_state]; try omega) (by unfold maxAlloc; omega)
    (model_growslice 100 placed_at_100 labels_fresh_at_100 _ 0)) ?_
  rintro st ⟨f1, f2, f3, f4, f5, f6, -⟩
  exact ⟨f1, f2, f3, f4, f5, f6⟩

set_option maxHeartbeats 64000000 in
/-- **Non-vacuity of `Encode.reject_length_cover`** (nil dst). -/
theorem runs_nil (e8 : List UInt8) (he8 : e8.length = 8) (rl : UInt64) (hrl : rl ≠ 32)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rcx = 0 ∧ st.data.regs.rdi = 0x10e8 ∧ st.data.regs.rsi = 0x2b)
      ⟨initial_state e8 rl [] 0 0 0 zmms flags, Host.addrOf 9⟩ := by
  refine eventually_mono (Encode.reject_length_cover 9 placed_at_9 labels_fresh_at_9 (zeros 8) e8 (word_bytes 48) (zeros 32) [] [] rfl he8 rfl rfl
    0x5000 rl 0x10e8 0x2b hrl (initial_state e8 rl [] 0 0 0 zmms flags) 0 0 rfl rfl
    (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 16) (zeros 16) (zeros 8) (zeros 40) (zeros 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    Std.ExtHashMap.emp 0 [] rfl bumpHeap 9000
    (by
      have H : Eq ((block e8 rl []).At (0x10000 : BitVec 64)) (mem e8 rl []) := rfl
      witness_split_n [he8]
      rw [Std.ExtHashMap.sep_comm_l (Eq ((word_bytes 0x2b).At _)) (Eq ((zeros 9000).At _)),
        Std.ExtHashMap.sep_comm_l (Eq ((word_bytes 0x10e8).At _)) (Eq ((zeros 9000).At _))] at H
      have H2 := lift_heap H
      simp only [initial_state, word_bytes, nil_At_emp, List.nil_append, Std.ExtHashMap.sep_emp, Std.ExtHashMap.emp_sep,
        show prefix30.length = 30 from rfl, ElfData.PrysmTarget.sszErrBytesLength_addr, label_err_bytes_length,
        UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, Int64.toBitVec_add, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub,
        List.length_nil] at H2 ⊢
      generalize e8 = e8' at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [initial_state]) (by simp [initial_state]) (by simp [initial_state]) (by unfold maxAlloc; omega)
    (model_growslice 100 placed_at_100 labels_fresh_at_100 _ 0)) ?_
  rintro st ⟨f1, f2, f3, f4, f5, f6, -⟩
  exact ⟨f1, f2, f3, f4, f5, f6⟩

/-- cap = len, len + 3 (first growslice, then the reject), len + 8, len + 40 (no growth); nil dst; rl = 31, 0, 33. -/
example (z' : RegZmms) (f : StatusFlags) := runs (Int.toBytes 8 7) rfl 31 (by decide) 0 (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) := runs (Int.toBytes 8 7) rfl 0 (by decide) 3 (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) := runs (Int.toBytes 8 7) rfl 33 (by decide) 8 (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) := runs (Int.toBytes 8 7) rfl 31 (by decide) 40 (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) := runs_nil (Int.toBytes 8 7) rfl 31 (by decide) z' f

end Prysm.Checkpoint.Witness.EncodeRejectLengthCover
