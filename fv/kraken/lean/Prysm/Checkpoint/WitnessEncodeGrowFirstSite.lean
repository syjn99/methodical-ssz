import Prysm.Checkpoint.EncodeGrowFirstSite
import Runtime.CopyModel
import Machine.WitnessHost
import Prysm.Checkpoint.GoValue

/-!
# Witness of `Encode.grow_first_site` (encoder growslice path)

Host: data labels, the real Go 1.26.10 `(*v1alpha1.Checkpoint).MarshalSSZTo`
(index 8) and `MemmoveGrowsliceModel` (index 99: `model_growslice`, new capacity 2·newLen + 192
from the bump heap, and `model_memmove`, both with S = 0). One memory block at
`0x10000`: bump pointer, an 8336-byte bump heap (= 2·nextSliceCap 38 36 + 8192,
the contract budget), guard word (r14 = 0x12088), the 72-byte receiver
(`Epoch` = `e8`, `Root` = (0x120e8, 32, 32)), the 32 root bytes, the stack
window (rsp = 0x12180) and `dst` at 0x121a0 = a 30-byte prefix with capacity 36
(`len + 8 > cap`: the first site grows; nextSliceCap 38 36 = 72 ≥ 70). Frame
`R`: the 8-byte frame gap at rsp − 72 and the 6 spare bytes.
-/

open Machine Runtime Machine.Witness Prysm.Checkpoint.Code

namespace Prysm.Checkpoint.Witness.EncodeGrowFirstSite

set_option maxRecDepth 100000

def dataLabels : Program :=
  [.label "runtime.modelBumpPointer", .label "pad1", .label "pad2", .label "pad3", .label "pad4", .label "pad5",
   .label "pad6", .label "pad7"]

def program : Program := dataLabels ++ marshalSSZTo ++ MemmoveGrowsliceModel

theorem program_length : program.length = 125 := by rfl

instance host : Host := mkHost program (by rw [program_length]; decide)

theorem host_program_eq : Host.prog = program := rfl

theorem placed_at_8 : marshalSSZTo.IsInfixAt Host.prog 8 :=
  infixAt_of dataLabels MemmoveGrowsliceModel (by simp [host_program_eq, program, List.append_assoc]) rfl

theorem placed_at_99 : MemmoveGrowsliceModel.IsInfixAt Host.prog 99 :=
  infixAt_of (dataLabels ++ marshalSSZTo) [] (by simp [host_program_eq, program, List.append_assoc]) (by rfl)

theorem labels_fresh_at_8 : LabelsFresh marshalSSZTo 8 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_99 : LabelsFresh MemmoveGrowsliceModel 99 := labelsFresh_of (by rw [host_program_eq]; decide)

theorem label_bump_pointer : label "runtime.modelBumpPointer" = 0x10000 :=
  mk_label program _ 0 _ (by simp [program, dataLabels]) (by simp [programLabels])

abbrev zeros (k : Nat) : List UInt8 := List.replicate k 0
abbrev word_bytes (v : UInt64) : List UInt8 := Int.toBytes 8 v.toBitVec.toInt
def prefix30 : List UInt8 := (List.range 30).map (fun i => UInt8.ofNat (0x40 + i))

/-- bump pointer · heap (8336) · guard · receiver (72) · root (32) · rslot · growslice spill (40) · gap (8)
· t40 (16) · t30 (16) · l32 · l24 · l16 · fp · return slot · spill rax · spill rbx · spill rcx
· dst = prefix (30) · spare (6). -/
def block (e8 root : List UInt8) : List UInt8 :=
  Int.toBytes 8 (0x10008 : BitVec 64).toInt ++ (zeros 8336 ++ (word_bytes 0 ++ (zeros 8 ++ (e8 ++ (word_bytes 0x120e8 ++ (word_bytes 32 ++ (word_bytes 32
    ++ (zeros 32 ++ (root ++ (zeros 8 ++ (zeros 40 ++ (zeros 8 ++ (zeros 16 ++ (zeros 16 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (word_bytes 0
    ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (prefix30 ++ zeros 6)))))))))))))))))))))))

def mem (e8 root : List UInt8) : DataMem := (block e8 root).At (0x10000 : BitVec 64)

def initial_state (e8 root : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x120a0, 0x121a0, 30, 0, 0, 36, 0x12180, 0, 0, 0, 0, 0, 0, 0, 0x12088, 0⟩, zmms, flags, mem e8 root⟩

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x10008 : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((zeros 8336).At (0x10008 : BitVec 64)) ⋆ X)) m) : (bumpHeap 8336 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x10008, by decide, by rw [label_bump_pointer]; exact hm⟩) h

theorem next_slice_cap_eq : nextSliceCap 38 36 = 72 := by decide

set_option maxHeartbeats 16000000 in
/-- **Non-vacuity of `Encode.grow_first_site`.** len 30, cap 36: growslice runs,
the encoder returns `rbx = 70` and `dst[30..70] = e8 ++ root` on the new block. -/
theorem runs (e8 root : List UInt8) (he8 : e8.length = 8) (hroot : root.length = 32)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rbx.toNat = 30 + 40
        ∧ 72 ≤ st.data.regs.rcx.toNat ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0)
      ⟨initial_state e8 root zmms flags, Host.addrOf 8⟩ :=
  eventually_mono (Encode.grow_first_site 8 placed_at_8 labels_fresh_at_8 (zeros 8) e8 (word_bytes 32) (zeros 32) root prefix30 rfl he8 rfl rfl hroot
    0x120e8 (initial_state e8 root zmms flags) 0 0 rfl
    (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 16) (zeros 16) (zeros 8) (zeros 40)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (Eq ((zeros 8).At (0x12138 : BitVec 64)) ⋆ Eq ((zeros 6).At (0x121be : BitVec 64)))
    0 [] rfl bumpHeap 8336
    (by
      have H : Eq ((block e8 root).At (0x10000 : BitVec 64)) (mem e8 root) := rfl
      witness_split [he8, hroot, show prefix30.length = 30 from rfl]
      have H2 := lift_heap H
      simp only [initial_state, word_bytes, nil_At_emp, Std.ExtHashMap.sep_emp, Std.ExtHashMap.emp_sep, UInt64.toBitVec_ofNat,
        Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, List.length_nil] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [initial_state]) (by simp [initial_state]) (by simp [initial_state]) (by simp [initial_state])
    (by simp only [initial_state]; decide) (by simp only [initial_state]; decide)
    (by unfold maxAlloc; omega) (model_growslice 99 placed_at_99 labels_fresh_at_99 _ 0) (model_memmove 99 placed_at_99 labels_fresh_at_99 0))
    (fun _ h => ⟨h.1, h.2.1, by
      have e : nextSliceCap ((initial_state e8 root zmms flags).regs.rcx.toNat + 8) (initial_state e8 root zmms flags).regs.rdi.toNat
        = 72 := by simp only [initial_state]; decide
      have := h.2.2.1; omega,
      h.2.2.2.1, h.2.2.2.2.1⟩)

example (z' : RegZmms) (f : StatusFlags) := runs (Int.toBytes 8 0) (zeros 32) (by decide) rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs (Int.toBytes 8 0x0123456789abcdef) ((List.range 32).map (fun i => (UInt8.ofNat i))) (by decide) rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs (Int.toBytes 8 (2 ^ 64 - 1)) (List.replicate 32 0xff) (by decide) rfl z' f

/-- Go-value element: the receiver of this witness, read from the witness block at offset 0x20a0
(Root = (0x120e8, 32, 32)). -/
theorem receiver_go_value : goValue (receiverAt (block (Int.toBytes 8 0x0123456789abcdef) (List.replicate 32 0xff)) 0x20a0)
    = true := by decide

end Prysm.Checkpoint.Witness.EncodeGrowFirstSite
