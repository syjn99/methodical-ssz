import Prysm.Slot.EncodeGrowFirstSite
import Runtime.CopyModel
import Machine.WitnessHost

/-!
# Witness of `Encode.grow_first_site` (encoder growslice path)

Host: data labels, the Go 1.26.10 `(*primitives.Slot).MarshalSSZTo` (index 8) and `MemmoveGrowsliceModel`.
The model is at index 59, and the witness uses its `model_growslice` with S = 0.
This model takes a new capacity of 2·newLen + 192 from the bump heap.
One memory block starts at `0x10000`.
It holds the bump pointer and an 8224-byte bump heap.
The heap is at least the contract budget 2·nextSliceCap (len + 8) cap + 8192 for both instances.
Then it holds the guard word (r14 = 0x12018) and the 8-byte receiver `e8`.
Then it holds the stack window (rsp = 0x12090).
The window has the call return slot, the growslice spill area, the 32-byte temp and the frame pointer slot.
It also has the return slot, a gap and the rbx and rcx spill slots.
Last, `dst` at 0x120b0 holds the prefix and the spare capacity.
Frame `R`: the gap at rsp + 8 and the spare capacity.
Instance 1: a 3-byte prefix with capacity 5 (nextSliceCap 11 5 = 11).
Instance 2: an empty prefix with capacity 0 (nextSliceCap 8 0 = 8).
-/

open Machine Runtime Machine.Witness Prysm.Slot.Code

namespace Prysm.Slot.Witness.EncodeGrowFirstSite

def dataLabels : Program :=
  [.label "runtime.modelBumpPointer", .label "pad1", .label "pad2", .label "pad3", .label "pad4", .label "pad5",
   .label "pad6", .label "pad7"]

def program : Program := dataLabels ++ marshalSSZTo ++ MemmoveGrowsliceModel

theorem program_length : program.length = 85 := by rfl

instance host : Host := mkHost program (by rw [program_length]; decide)

theorem host_program_eq : Host.prog = program := rfl

theorem placed_at_8 : marshalSSZTo.IsInfixAt Host.prog 8 :=
  infixAt_of dataLabels MemmoveGrowsliceModel (by simp [host_program_eq, program, List.append_assoc]) rfl

theorem placed_at_59 : MemmoveGrowsliceModel.IsInfixAt Host.prog 59 :=
  infixAt_of (dataLabels ++ marshalSSZTo) [] (by simp [host_program_eq, program, List.append_assoc]) (by rfl)

theorem labels_fresh_at_59 : LabelsFresh MemmoveGrowsliceModel 59 := labelsFresh_of (by rw [host_program_eq]; decide)

theorem label_bump_pointer : label "runtime.modelBumpPointer" = 0x10000 :=
  mk_label program _ 0 _ (by simp [program, dataLabels]) (by simp [programLabels])

abbrev zeros (k : Nat) : List UInt8 := List.replicate k 0
abbrev word_bytes (v : UInt64) : List UInt8 := Int.toBytes 8 v.toBitVec.toInt

/-- The block, in address order.
Bump pointer, heap (8224), guard, receiver (8), call return slot, growslice spill (40).
Then temp (16 + 16), fp, return slot, gap, spill rbx, spill rcx, `dst` = prefix and spare. -/
def block (e8 pre spare : List UInt8) : List UInt8 :=
  Int.toBytes 8 (0x10008 : BitVec 64).toInt ++ (zeros 8224 ++ (word_bytes 0 ++ (e8 ++ (zeros 8 ++ (zeros 40
    ++ (zeros 16 ++ (zeros 16 ++ (zeros 8 ++ (word_bytes 0 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8
    ++ (pre ++ spare)))))))))))))

def mem (e8 pre spare : List UInt8) : DataMem := (block e8 pre spare).At (0x10000 : BitVec 64)

def initial_state (e8 pre spare : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x12030, 0x120b0, UInt64.ofNat pre.length, 0, 0, UInt64.ofNat (pre.length + spare.length), 0x12090, 0,
    0, 0, 0, 0, 0, 0, 0x12018, 0⟩, zmms, flags, mem e8 pre spare⟩

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x10008 : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((zeros 8224).At (0x10008 : BitVec 64)) ⋆ X)) m) : (bumpHeap 8224 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x10008, by decide, by rw [label_bump_pointer]; exact hm⟩) h

theorem next_slice_cap_prefix : nextSliceCap 11 5 = 11 := by decide

theorem next_slice_cap_empty : nextSliceCap 8 0 = 8 := by decide

/-- The memory premise of `Encode.grow_first_site` for the 3-byte prefix instance. -/
theorem mem_prefix (e8 : List UInt8) (he8 : e8.length = 8) (zmms : RegZmms) (flags : StatusFlags) :
    (initial_state e8 [0xaa, 0xbb, 0xcc] (zeros 2) zmms flags).dmem =⋆
      Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At (initial_state e8 [0xaa, 0xbb, 0xcc] (zeros 2) zmms flags).regs.rsp.toBitVec)
      ⋆ Eq ((zeros 8).At ((initial_state e8 [0xaa, 0xbb, 0xcc] (zeros 2) zmms flags).regs.rsp.toBitVec - 8))
      ⋆ Eq ((zeros 8).At ((initial_state e8 [0xaa, 0xbb, 0xcc] (zeros 2) zmms flags).regs.rsp.toBitVec + 16))
      ⋆ Eq ((zeros 8).At ((initial_state e8 [0xaa, 0xbb, 0xcc] (zeros 2) zmms flags).regs.rsp.toBitVec + 24))
      ⋆ Eq ((zeros 16).At ((initial_state e8 [0xaa, 0xbb, 0xcc] (zeros 2) zmms flags).regs.rsp.toBitVec - 40))
      ⋆ Eq ((zeros 16).At ((initial_state e8 [0xaa, 0xbb, 0xcc] (zeros 2) zmms flags).regs.rsp.toBitVec - 24))
      ⋆ Eq ((zeros 40).At ((initial_state e8 [0xaa, 0xbb, 0xcc] (zeros 2) zmms flags).regs.rsp.toBitVec - 80))
      ⋆ Eq ((zeros 8).At ((initial_state e8 [0xaa, 0xbb, 0xcc] (zeros 2) zmms flags).regs.rsp.toBitVec - 88))
      ⋆ Eq (([] : List UInt8).At ((initial_state e8 [0xaa, 0xbb, 0xcc] (zeros 2) zmms flags).regs.rsp.toBitVec - 88
        - BitVec.ofNat 64 0))
      ⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At
        ((initial_state e8 [0xaa, 0xbb, 0xcc] (zeros 2) zmms flags).regs.r14.toBitVec + 16))
      ⋆ Eq (e8.At (initial_state e8 [0xaa, 0xbb, 0xcc] (zeros 2) zmms flags).regs.rax.toBitVec)
      ⋆ Eq (([0xaa, 0xbb, 0xcc] : List UInt8).At (initial_state e8 [0xaa, 0xbb, 0xcc] (zeros 2) zmms flags).regs.rbx.toBitVec)
      ⋆ bumpHeap 8224 ⋆ (Eq ((zeros 8).At (0x12098 : BitVec 64)) ⋆ Eq ((zeros 2).At (0x120b3 : BitVec 64))) := by
  have H : Eq ((block e8 [0xaa, 0xbb, 0xcc] (zeros 2)).At (0x10000 : BitVec 64))
    (mem e8 [0xaa, 0xbb, 0xcc] (zeros 2)) := rfl
  witness_split [he8]
  have H2 := lift_heap H
  simp only [initial_state, word_bytes, nil_At_emp, Std.ExtHashMap.sep_emp, UInt64.toBitVec_ofNat,
    BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, List.length_nil, List.length_cons,
    List.length_replicate] at H2 ⊢
  refine cast (congrFun (?_ : _ = _) _) H2
  ac_rfl

/-- **Non-vacuity of `Encode.grow_first_site`.** Prefix `[0xaa, 0xbb, 0xcc]`, capacity 5.
Growslice runs, and the encoder returns `rbx = 11` with `new[3..11] = e8` on the new block. -/
theorem runs (e8 : List UInt8) (he8 : e8.length = 8) (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rbx.toNat = 3 + 8
        ∧ 11 ≤ st.data.regs.rcx.toNat ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0)
      ⟨initial_state e8 [0xaa, 0xbb, 0xcc] (zeros 2) zmms flags, Host.addrOf 8⟩ :=
  eventually_mono (Encode.grow_first_site 8 placed_at_8 e8 [0xaa, 0xbb, 0xcc] he8
    (initial_state e8 [0xaa, 0xbb, 0xcc] (zeros 2) zmms flags) 0 0 rfl
    (zeros 8) (zeros 8) (zeros 8) (zeros 16) (zeros 16) (zeros 8) (zeros 40)
    rfl rfl rfl rfl rfl rfl rfl
    (Eq ((zeros 8).At (0x12098 : BitVec 64)) ⋆ Eq ((zeros 2).At (0x120b3 : BitVec 64)))
    0 [] rfl bumpHeap 8224
    (mem_prefix e8 he8 zmms flags)
    (by simp [initial_state]) (by simp only [initial_state]; decide) (by simp only [initial_state]; decide)
    (by simp only [initial_state]; decide)
    (by unfold maxAlloc; omega) (model_growslice 59 placed_at_59 labels_fresh_at_59 _ 0))
    (fun _ h => ⟨h.1, h.2.1, by
      have e : nextSliceCap ((initial_state e8 [0xaa, 0xbb, 0xcc] (zeros 2) zmms flags).regs.rcx.toNat + 8)
        (initial_state e8 [0xaa, 0xbb, 0xcc] (zeros 2) zmms flags).regs.rdi.toNat = 11 := by
        simp only [initial_state]; decide
      have := h.2.2.1; omega,
      h.2.2.2.1, h.2.2.2.2.1⟩)

/-- Empty prefix, capacity 0.
Growslice runs, and the encoder returns `rbx = 8` with `new[0..8] = e8`. -/
theorem runs_empty (e8 : List UInt8) (he8 : e8.length = 8) (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rbx.toNat = 0 + 8
        ∧ 8 ≤ st.data.regs.rcx.toNat ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0)
      ⟨initial_state e8 [] [] zmms flags, Host.addrOf 8⟩ :=
  eventually_mono (Encode.grow_first_site 8 placed_at_8 e8 [] he8
    (initial_state e8 [] [] zmms flags) 0 0 rfl
    (zeros 8) (zeros 8) (zeros 8) (zeros 16) (zeros 16) (zeros 8) (zeros 40)
    rfl rfl rfl rfl rfl rfl rfl
    (Eq ((zeros 8).At (0x12098 : BitVec 64)))
    0 [] rfl bumpHeap 8224
    (by
      have H : Eq ((block e8 [] []).At (0x10000 : BitVec 64)) (mem e8 [] []) := rfl
      witness_split [he8]
      have H2 := lift_heap H
      simp only [initial_state, word_bytes, nil_At_emp, Std.ExtHashMap.sep_emp, UInt64.toBitVec_ofNat,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, List.length_nil] at H2 ⊢
      sep_perm H2)
    (by simp [initial_state]) (by simp only [initial_state]; decide) (by simp only [initial_state]; decide)
    (by simp only [initial_state]; decide)
    (by unfold maxAlloc; omega) (model_growslice 59 placed_at_59 labels_fresh_at_59 _ 0))
    (fun _ h => ⟨h.1, h.2.1, by
      have e : nextSliceCap ((initial_state e8 [] [] zmms flags).regs.rcx.toNat + 8)
        (initial_state e8 [] [] zmms flags).regs.rdi.toNat = 8 := by
        simp only [initial_state]; decide
      have := h.2.2.1; omega,
      h.2.2.2.1, h.2.2.2.2.1⟩)

example (z' : RegZmms) (f : StatusFlags) := runs (Int.toBytes 8 0) (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) := runs (Int.toBytes 8 0x0123456789abcdef) (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) := runs_empty (Int.toBytes 8 (2 ^ 64 - 1)) (by decide) z' f

end Prysm.Slot.Witness.EncodeGrowFirstSite
