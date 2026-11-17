import Prysm.ValidatorIndex.EncodeCoverFramed
import Runtime.CopyModel
import Machine.WitnessHost

/-!
# Witness of `Encode.cover_framed`: both capacity ranges on one host

Host: data labels, the Go 1.26.10 `(*primitives.ValidatorIndex).MarshalSSZTo` (index 8) and `MemmoveGrowsliceModel`.
The model is at index 59, and the witness uses its `model_growslice` with `S = 0`.
This model takes a new capacity of `2·newLen + 192` from the bump heap.
One memory block starts at `0x10000`.
It holds the bump pointer and an 8640-byte heap, which is at least `4·len + 8608` for `len ≤ 8`.
Then it holds the guard word (r14 = 0x121b8) and the 8-byte receiver `uintBytes 8 x`.
Then it holds the stack window (rsp = 0x12230).
Last, `dst` at 0x12250 holds the prefix and the spare bytes (cap = len + spare).
Frame `R`: the gap at rsp + 8.
Instances: a 3-byte prefix with 0 or 7 spare bytes (growslice path).
Also a 3-byte prefix with 8 or 16 spare bytes (fast path), and an empty `dst` (growslice path).
-/

open Machine Runtime Machine.Witness Prysm.ValidatorIndex.Code EthLib.Serialization.Ssz

namespace Prysm.ValidatorIndex.Witness.EncodeCoverFramed

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

theorem labels_fresh_at_8 : LabelsFresh marshalSSZTo 8 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_59 : LabelsFresh MemmoveGrowsliceModel 59 := labelsFresh_of (by rw [host_program_eq]; decide)

theorem label_bump_pointer : label "runtime.modelBumpPointer" = 0x10000 :=
  mk_label program _ 0 _ (by simp [program, dataLabels]) (by simp [programLabels])

abbrev zeros (k : Nat) : List UInt8 := List.replicate k 0
abbrev word_bytes (v : UInt64) : List UInt8 := Int.toBytes 8 v.toBitVec.toInt

/-- The block, in address order.
Bump pointer, heap (8640), guard, receiver (8), call return slot, growslice spill (40).
Then temp (16 + 16), fp, return slot, gap, spill rbx, spill rcx, `dst`. -/
def block (e8 dst : List UInt8) : List UInt8 :=
  Int.toBytes 8 (0x10008 : BitVec 64).toInt ++ (zeros 8640 ++ (word_bytes 0 ++ (e8 ++ (zeros 8 ++ (zeros 40
    ++ (zeros 16 ++ (zeros 16 ++ (zeros 8 ++ (word_bytes 0 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ dst))))))))))))

def mem (e8 dst : List UInt8) : DataMem := (block e8 dst).At (0x10000 : BitVec 64)

def initial_state (e8 dst : List UInt8) (len : UInt64) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x121d0, 0x12250, len, 0, 0, UInt64.ofNat dst.length, 0x12230, 0, 0, 0, 0, 0, 0, 0, 0x121b8, 0⟩, zmms, flags,
    mem e8 dst⟩

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x10008 : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((zeros 8640).At (0x10008 : BitVec 64)) ⋆ X)) m) : (bumpHeap 8640 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x10008, by decide, by rw [label_bump_pointer]; exact hm⟩) h

/-- The memory premise of `Encode.cover_framed` for all receiver bytes `e8` and every `dst`. -/
theorem mem_premise (e8 dst : List UInt8) (he8 : e8.length = 8) (hdst : dst.length ≤ 72) (len : UInt64) (zmms : RegZmms) (flags : StatusFlags) :
    (initial_state e8 dst len zmms flags).dmem =⋆
      Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At (initial_state e8 dst len zmms flags).regs.rsp.toBitVec)
      ⋆ Eq ((zeros 8).At ((initial_state e8 dst len zmms flags).regs.rsp.toBitVec - 8))
      ⋆ Eq ((zeros 8).At ((initial_state e8 dst len zmms flags).regs.rsp.toBitVec + 16))
      ⋆ Eq ((zeros 8).At ((initial_state e8 dst len zmms flags).regs.rsp.toBitVec + 24))
      ⋆ Eq ((zeros 16).At ((initial_state e8 dst len zmms flags).regs.rsp.toBitVec - 40))
      ⋆ Eq ((zeros 16).At ((initial_state e8 dst len zmms flags).regs.rsp.toBitVec - 24))
      ⋆ Eq ((zeros 40).At ((initial_state e8 dst len zmms flags).regs.rsp.toBitVec - 80))
      ⋆ Eq ((zeros 8).At ((initial_state e8 dst len zmms flags).regs.rsp.toBitVec - 88))
      ⋆ Eq (([] : List UInt8).At ((initial_state e8 dst len zmms flags).regs.rsp.toBitVec - 88 - BitVec.ofNat 64 0))
      ⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At ((initial_state e8 dst len zmms flags).regs.r14.toBitVec + 16))
      ⋆ Eq (e8.At (initial_state e8 dst len zmms flags).regs.rax.toBitVec)
      ⋆ Eq (dst.At (initial_state e8 dst len zmms flags).regs.rbx.toBitVec)
      ⋆ bumpHeap 8640 ⋆ Eq ((zeros 8).At (0x12238 : BitVec 64)) := by
  have H : Eq ((block e8 dst).At (0x10000 : BitVec 64)) (mem e8 dst) := rfl
  witness_split [he8]
  have H2 := lift_heap H
  simp only [initial_state, word_bytes, nil_At_emp, Std.ExtHashMap.sep_emp, UInt64.toBitVec_ofNat,
    BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub] at H2 ⊢
  refine cast (congrFun (?_ : _ = _) _) H2
  ac_rfl

/-- **Non-vacuity of `Encode.cover_framed`.**
The prefix `pre` has at most 8 bytes, and cap = len + len(spare). -/
theorem runs (x : UInt64) (pre spare : List UInt8) (hpl : pre.length ≤ 8) (hsl : spare.length ≤ 64)
    (zmms : RegZmms) (flags : StatusFlags) :
    ∃ bs, serialize desc (.uint x.toNat) = .ok bs ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rbx.toNat = pre.length + 8)
      ⟨initial_state (uintBytes 8 x.toNat).toList (pre ++ spare) (UInt64.ofNat pre.length) zmms flags, Host.addrOf 8⟩ := by
  have he8 : (uintBytes 8 x.toNat).toList.length = 8 := by simp [Spec.uintBytes_size]
  have hc : (UInt64.ofNat pre.length).toNat = pre.length := by simp; omega
  have hd : (UInt64.ofNat (pre ++ spare).length).toNat = pre.length + spare.length := by simp; omega
  obtain ⟨bs, hs, -, he⟩ := Encode.cover_framed 8 placed_at_8 labels_fresh_at_8 x _ rfl pre spare
    (initial_state (uintBytes 8 x.toNat).toList (pre ++ spare) (UInt64.ofNat pre.length) zmms flags) 0 0
    (by simp only [initial_state, hc]) (by simp only [initial_state, hd])
    (zeros 8) (zeros 8) (zeros 8) (zeros 16) (zeros 16) (zeros 8) (zeros 40)
    rfl rfl rfl rfl rfl rfl rfl
    (Eq ((zeros 8).At (0x12238 : BitVec 64))) 0 [] rfl bumpHeap 8640
    (mem_premise _ _ he8 (by simp only [List.length_append]; omega) _ zmms flags)
    (by simp [initial_state]) (by simp only [initial_state, hc]; omega) (by unfold maxAlloc; omega)
    (model_growslice 59 placed_at_59 labels_fresh_at_59 _ 0)
  exact ⟨bs, hs, eventually_mono he (fun _ h => ⟨h.1, by have := h.2.1; simp only [initial_state, hc] at this; exact this⟩)⟩

/-- cap = len (3) and len + 7 take the growslice path.
cap = len + 8 and len + 16 take the fast path; the empty `dst` takes the growslice path. -/
example (x : UInt64) (z' : RegZmms) (f : StatusFlags) := runs x [0xaa, 0xbb, 0xcc] [] (by decide) (by decide) z' f
example (x : UInt64) (z' : RegZmms) (f : StatusFlags) := runs x [0xaa, 0xbb, 0xcc] (zeros 7) (by decide) (by decide) z' f
example (x : UInt64) (z' : RegZmms) (f : StatusFlags) := runs x [0xaa, 0xbb, 0xcc] (zeros 8) (by decide) (by decide) z' f
example (x : UInt64) (z' : RegZmms) (f : StatusFlags) := runs x [0xaa, 0xbb, 0xcc] (zeros 16) (by decide) (by decide) z' f
example (x : UInt64) (z' : RegZmms) (f : StatusFlags) := runs x [] [] (by decide) (by decide) z' f

end Prysm.ValidatorIndex.Witness.EncodeCoverFramed
