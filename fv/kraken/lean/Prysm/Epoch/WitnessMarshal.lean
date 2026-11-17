import Prysm.Epoch.Marshal
import Runtime.CopyModel
import Machine.WitnessHost

/-!
# Witness of `Marshal.result` (MarshalSSZ, stack check passes)

Host: data labels, the Go 1.26.10 `(*primitives.Epoch).MarshalSSZ` (index 8) and `MemmoveGrowsliceModel`.
The model is at index 36, and the witness uses its `model_growslice` with S = 0.
This model takes a new capacity of 2·newLen + 192 from the bump heap.
One memory block starts at `0x10000`.
It holds the bump pointer and an 8224-byte bump heap.
The heap is at least the contract budget 2·nextSliceCap 8 0 + 8192.
Then it holds the guard word (r14 = 0x12018) and the 8-byte receiver `e8`.
Then it holds the stack window (rsp = 0x12090).
The window has the call return slot, the growslice spill area, a 24-byte gap and the value slot.
Last, it has the frame pointer slot and the return slot.
Frame `R`: the 24-byte gap at rsp − 40.
-/

open Machine Runtime Machine.Witness Prysm.Epoch.Code

namespace Prysm.Epoch.Witness.Marshal

def dataLabels : Program :=
  [.label "runtime.modelBumpPointer", .label "pad1", .label "pad2", .label "pad3", .label "pad4", .label "pad5",
   .label "pad6", .label "pad7"]

def program : Program := dataLabels ++ marshalSSZ ++ MemmoveGrowsliceModel

theorem program_length : program.length = 62 := by rfl

instance host : Host := mkHost program (by rw [program_length]; decide)

theorem host_program_eq : Host.prog = program := rfl

theorem placed_at_8 : marshalSSZ.IsInfixAt Host.prog 8 :=
  infixAt_of dataLabels MemmoveGrowsliceModel (by simp [host_program_eq, program, List.append_assoc]) rfl

theorem placed_at_36 : MemmoveGrowsliceModel.IsInfixAt Host.prog 36 :=
  infixAt_of (dataLabels ++ marshalSSZ) [] (by simp [host_program_eq, program, List.append_assoc]) (by rfl)

theorem labels_fresh_at_36 : LabelsFresh MemmoveGrowsliceModel 36 := labelsFresh_of (by rw [host_program_eq]; decide)

theorem label_bump_pointer : label "runtime.modelBumpPointer" = 0x10000 :=
  mk_label program _ 0 _ (by simp [program, dataLabels]) (by simp [programLabels])

abbrev zeros (k : Nat) : List UInt8 := List.replicate k 0
abbrev word_bytes (v : UInt64) : List UInt8 := Int.toBytes 8 v.toBitVec.toInt

/-- The block, in address order.
Bump pointer, heap (8224), guard, receiver (8), call return slot, growslice spill (40).
Then the gap (24), the value slot, fp and the return slot. -/
def block (e8 : List UInt8) : List UInt8 :=
  Int.toBytes 8 (0x10008 : BitVec 64).toInt ++ (zeros 8224 ++ (word_bytes 0 ++ (e8 ++ (zeros 8 ++ (zeros 40
    ++ (zeros 24 ++ (zeros 8 ++ (zeros 8 ++ word_bytes 0))))))))

def mem (e8 : List UInt8) : DataMem := (block e8).At (0x10000 : BitVec 64)

def initial_state (e8 : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x12030, 0, 0, 0, 0, 0, 0x12090, 0, 0, 0, 0, 0, 0, 0, 0x12018, 0⟩, zmms, flags, mem e8⟩

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x10008 : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((zeros 8224).At (0x10008 : BitVec 64)) ⋆ X)) m) : (bumpHeap 8224 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x10008, by decide, by rw [label_bump_pointer]; exact hm⟩) h

/-- The memory premise of `Marshal.result`. -/
theorem mem_premise (e8 : List UInt8) (he8 : e8.length = 8) (zmms : RegZmms) (flags : StatusFlags) :
    (initial_state e8 zmms flags).dmem =⋆
      Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At (initial_state e8 zmms flags).regs.rsp.toBitVec)
      ⋆ Eq ((zeros 8).At ((initial_state e8 zmms flags).regs.rsp.toBitVec - 8))
      ⋆ Eq ((zeros 8).At ((initial_state e8 zmms flags).regs.rsp.toBitVec - 16))
      ⋆ Eq ((zeros 40).At ((initial_state e8 zmms flags).regs.rsp.toBitVec - 80))
      ⋆ Eq ((zeros 8).At ((initial_state e8 zmms flags).regs.rsp.toBitVec - 88))
      ⋆ Eq (([] : List UInt8).At ((initial_state e8 zmms flags).regs.rsp.toBitVec - 88 - BitVec.ofNat 64 0))
      ⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At ((initial_state e8 zmms flags).regs.r14.toBitVec + 16))
      ⋆ Eq (e8.At (initial_state e8 zmms flags).regs.rax.toBitVec)
      ⋆ bumpHeap 8224 ⋆ Eq ((zeros 24).At (0x12068 : BitVec 64)) := by
  have H : Eq ((block e8).At (0x10000 : BitVec 64)) (mem e8) := rfl
  witness_split [he8]
  have H2 := lift_heap H
  simp only [initial_state, word_bytes, nil_At_emp, Std.ExtHashMap.sep_emp, UInt64.toBitVec_ofNat,
    BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub] at H2 ⊢
  refine cast (congrFun (?_ : _ = _) _) H2
  ac_rfl

/-- **Non-vacuity of `Marshal.result`.**
Growslice runs, and MarshalSSZ returns `rbx = 8` with `new[0..8] = e8`. -/
theorem runs (e8 : List UInt8) (he8 : e8.length = 8) (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rbx = 8
        ∧ 8 ≤ st.data.regs.rcx.toNat ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0)
      ⟨initial_state e8 zmms flags, Host.addrOf 8⟩ :=
  eventually_mono (Prysm.Epoch.Marshal.result 8 placed_at_8 e8 he8 (initial_state e8 zmms flags) 0 0
    (zeros 8) (zeros 8) (zeros 8) (zeros 40) rfl rfl rfl rfl
    (Eq ((zeros 24).At (0x12068 : BitVec 64)))
    0 [] rfl bumpHeap 8224
    (mem_premise e8 he8 zmms flags)
    (by simp [initial_state]) (by decide)
    (by unfold maxAlloc; omega) (model_growslice 36 placed_at_36 labels_fresh_at_36 _ 0))
    (fun _ h => ⟨h.1, h.2.1, by
      have := h.2.2.1; rw [Prysm.Epoch.Marshal.result_next_slice_cap] at this; exact this,
      h.2.2.2.2.1, h.2.2.2.2.2.1⟩)

example (z' : RegZmms) (f : StatusFlags) := runs (Int.toBytes 8 0) (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) := runs (Int.toBytes 8 0x0123456789abcdef) (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) := runs (Int.toBytes 8 (2 ^ 64 - 1)) (by decide) z' f

end Prysm.Epoch.Witness.Marshal
