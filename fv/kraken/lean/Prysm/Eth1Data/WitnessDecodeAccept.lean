import Prysm.Eth1Data.DecodeAccept
import Runtime.CopyModel
import Runtime.BumpAllocatorVariants
import Machine.WitnessHost

/-!
# Witness of `Decode.accept` (Eth1Data decoder accept path, hold-out)

Hand-written (the text of `Prysm/BeaconBlockHeader/WitnessDecodeAccept.lean` with the Eth1Data host and layout).
Host: data labels, the real Go 1.26.10 `(*v1alpha1.Eth1Data).UnmarshalSSZ` (index 9), the 1-byte bump
`runtime.makeslice` (117, `bump_makeslice1`) and `MemmoveGrowsliceModel` (123, `model_memmove`).
One memory block at `0x10000`: bump pointer, writeBarrier word, the 64-byte heap, guard word, the 72 input
bytes, the 96-byte receiver (`prysm/ir/ir-mainnet.json` gc amd64 layout, size 96: `state` 0, DepositRoot
header 8 with old pointer word `oP1` and len = cap = 0, DepositCount 32 (zero), BlockHash header 40 with old
pointer word `oP2` and len = cap = 0, `unknownFields` 64 + `sizeCache` 88 + padding = 32 bytes), the 16-byte
callee block (`S = 16`), the callee return slot, the argument area, the pointer save, the saved rbp and the
caller's slots (rsp = 0x1013c). The frame `R` is exactly the untouched receiver tail (32 bytes).
For every input and every old root pointer word (nil = zero, or any other bytes) every premise holds and
the decoder returns nil. The receiver is a Go value of `v1alpha1.Eth1Data` (zero `state`, zero-length root
slices, zero DepositCount).
-/

open Machine Runtime Machine.Witness Codec Prysm.Eth1Data.Code

namespace Prysm.Eth1Data.Witness.DecodeAccept

set_option maxRecDepth 100000

def dataLabels : Program :=
  [.label "runtime.modelBumpPointer", .label "pad1", .label "pad2", .label "pad3", .label "pad4", .label "pad5",
   .label "pad6", .label "pad7", .label "runtime.writeBarrier"]

def program : Program := dataLabels ++ unmarshalSSZ ++ BumpMakeslice1 ++ MemmoveGrowsliceModel

theorem program_length : program.length = 149 := by rfl

instance host : Host := mkHost program (by rw [program_length]; decide)

theorem host_program_eq : Host.prog = program := rfl

theorem placed_at_9 : unmarshalSSZ.IsInfixAt Host.prog 9 :=
  infixAt_of dataLabels (BumpMakeslice1 ++ MemmoveGrowsliceModel) (by simp [host_program_eq, program, List.append_assoc]) rfl
theorem placed_at_117 : BumpMakeslice1.IsInfixAt Host.prog 117 :=
  infixAt_of (dataLabels ++ unmarshalSSZ) MemmoveGrowsliceModel
    (by simp [host_program_eq, program, List.append_assoc]) (by rfl)
theorem placed_at_123 : MemmoveGrowsliceModel.IsInfixAt Host.prog 123 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ BumpMakeslice1) []
    (by simp [host_program_eq, program, List.append_assoc]) (by rfl)

theorem labels_fresh_at_9 : LabelsFresh unmarshalSSZ 9 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_123 : LabelsFresh MemmoveGrowsliceModel 123 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_117 : ∀ i < 117, Host.prog[i]? ≠ some (.label "runtime.makeslice") :=
  notLabel_of (by rw [host_program_eq]; decide)

theorem label_bump_pointer : label "runtime.modelBumpPointer" = 0x10000 :=
  mk_label program _ 0 _ (by simp [program, dataLabels]) (by simp [labs])

theorem label_write_barrier : label "runtime.writeBarrier" = 0x10008 :=
  mk_label program _ 8 _ (by simp [program, dataLabels]) (by decide)

abbrev zeros (k : Nat) : List UInt8 := List.replicate k 0
abbrev zero_word_bytes : List UInt8 := Int.toBytes 8 (0 : UInt64).toBitVec.toInt

/-- bump pointer (→ 0x1000c) · writeBarrier · heap (64) · guard · input (72: r1, cnt, r2) · receiver (96:
state, DepositRoot `oP1`/0/0, DepositCount 0, BlockHash `oP2`/0/0, tail 32) · callee block (16) · callee
return slot · argument area (24) · pointer save · saved rbp · return slot · spill rax · spill rbx. -/
def block (r1 cnt r2 oP1 oP2 : List UInt8) : List UInt8 :=
  Int.toBytes 8 (0x1000c : BitVec 64).toInt ++ ([0, 0, 0, 0] ++ (zeros 64 ++ (zero_word_bytes ++ (r1 ++ (cnt ++ (r2 ++ (zeros 8 ++ (oP1 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (oP2 ++ (zeros 8 ++ (zeros 8 ++ (zeros 32 ++ (zeros 16 ++ (zeros 8 ++ (zeros 24 ++ (zeros 8 ++ (zeros 8 ++ (zero_word_bytes ++ (zeros 8 ++ zeros 8))))))))))))))))))))))

def mem (r1 cnt r2 oP1 oP2 : List UInt8) : DataMem :=
  (block r1 cnt r2 oP1 oP2).At (0x10000 : BitVec 64)

def initial_state (r1 cnt r2 oP1 oP2 : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x1009c, 0x10054, 72, 0, 0, 72, 0x1013c, 0, 0, 0, 0, 0, 0, 0, 0x1003c, 0⟩, zmms, flags,
    mem r1 cnt r2 oP1 oP2⟩

/-- The frame of the witness: the untouched receiver tail (`unknownFields`, `sizeCache`, padding). -/
def frame_rest : DataMem → Prop := Eq ((zeros 32).At (0x100dc : BitVec 64))

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x1000c : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((zeros 64).At (0x1000c : BitVec 64)) ⋆ X)) m) : (bumpHeap 64 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x1000c, by decide, by rw [label_bump_pointer]; exact hm⟩) h

set_option maxHeartbeats 16000000 in
/-- **Non-vacuity of `Decode.accept`.** -/
theorem runs (r1 cnt r2 oP1 oP2 : List UInt8) (hr1 : r1.length = 32) (hcnt : cnt.length = 8)
    (hr2 : r2.length = 32) (h1 : oP1.length = 8) (h2 : oP2.length = 8)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨initial_state r1 cnt r2 oP1 oP2 zmms flags, Host.addrOf 9⟩ :=
  eventually_mono (Decode.accept 9 placed_at_9 labels_fresh_at_9 r1 cnt r2 hr1 hcnt hr2 (initial_state r1 cnt r2 oP1 oP2 zmms flags)
    0 0 (zeros 8) (zeros 8) (zeros 8) (zeros 24) (zeros 8) (zeros 8) (zeros 16) (zeros 8) oP1 (zeros 8) (zeros 8) (zeros 8) oP2 (zeros 8) (zeros 8)
    rfl rfl rfl rfl rfl rfl rfl h1 rfl rfl rfl h2 rfl rfl
    frame_rest 16 rfl bumpHeap 64
    (by
      have H : Eq ((block r1 cnt r2 oP1 oP2).At (0x10000 : BitVec 64)) (mem r1 cnt r2 oP1 oP2) := rfl
      witness_split [hr1, hcnt, hr2, h1, h2]
      rw [Std.ExtHashMap.sep_comm_l (Eq (([0, 0, 0, 0] : List UInt8).At _)) (Eq ((zeros 64).At _))] at H
      have H2 := lift_heap H
      simp only [initial_state, frame_rest, zero_word_bytes, label_write_barrier, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd, BitVec.reduceSub] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [initial_state]) rfl (Nat.le_refl _) (bump_makeslice1 117 placed_at_117 labels_fresh_at_117 _) (model_memmove 123 placed_at_123 labels_fresh_at_123 _))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

/-- Zero input with a fresh `&Eth1Data{}` (nil roots); a representative input with non-nil old root pointer
words; all-0xff input. -/
example (z' : RegZmms) (f : StatusFlags) :=
  runs (zeros 32) (zeros 8) (zeros 32) (zeros 8) (zeros 8) rfl rfl rfl rfl rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs ((List.range 32).map (fun i => UInt8.ofNat i)) (Int.toBytes 8 0x0123456789abcdef)
    (List.replicate 32 0x22) (Int.toBytes 8 0x20000) (Int.toBytes 8 0x30000)
    rfl (by decide) rfl (by decide) (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs (List.replicate 32 0xff) (List.replicate 8 0xff) (List.replicate 32 0xff) (List.replicate 8 0xff)
    (List.replicate 8 0xff) rfl rfl rfl rfl rfl z' f

end Prysm.Eth1Data.Witness.DecodeAccept
