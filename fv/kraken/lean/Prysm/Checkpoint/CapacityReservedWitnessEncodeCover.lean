import Prysm.Checkpoint.CapacityReservedEncodeSpec
import Runtime.CopyModel
import Machine.WitnessHost
import Machine.WitnessSplit
import Prysm.Checkpoint.GoValue

/-!
# OPT-size_reject_frame_rest witness of `CapacityReserved.Encode.cover` (every capacity range; instantiates `CapacityReserved.Encode.fast_path` and
`CapacityReserved.Encode.grow_first_site` inside the cover's proof)

Host: data labels, the reserve encoder `marshalSSZTo` (index 8) and `MemmoveGrowsliceModel` (index 143: `model_growslice` — new
capacity `2·newLen + 192` from the bump heap — and `model_memmove`, both with `S = 0`). One memory block at
`0x10000`: bump pointer, a 9000-byte heap (≥ `4·len + 8736`), guard word (r14 = 0x12320), the 72-byte
receiver (`Epoch` = `uintBytes 8 g.epoch`, `Root` = (0x12380, 32, 32)), the 32 root bytes, the stack window
rsp − 160 … rsp + 32 (rsp = 0x12440) and `dst` at 0x12460 = a 30-byte prefix and `n` spare bytes
(`cap = 30 + n`). Frame `R`: the 8-byte frame gap at rsp − 72. Instances: n = 0, 7, 8, 39 (grow path:
one growslice for newLen = 70), 40, 41 (fast path); `runs_nil`: nil `dst` (rbx = 0, len = cap = 0).
-/

open Machine Runtime Machine.Witness Prysm.Checkpoint.CapacityReserved Prysm.Checkpoint.CapacityReserved.Code EthLib.Serialization.Ssz

namespace Prysm.Checkpoint.Witness.CapacityReservedEncodeCover

set_option maxRecDepth 100000

def dataLabels : Program :=
  [.label "runtime.modelBumpPointer", .label "pad1", .label "pad2", .label "pad3", .label "pad4", .label "pad5",
   .label "pad6", .label "pad7"]

def program : Program := dataLabels ++ marshalSSZTo ++ MemmoveGrowsliceModel

theorem program_length : program.length = 169 := by rfl

instance host : Host := mkHost program (by rw [program_length]; decide)

theorem host_program_eq : Host.prog = program := rfl

theorem placed_at_8 : marshalSSZTo.IsInfixAt Host.prog 8 :=
  infixAt_of dataLabels MemmoveGrowsliceModel (by simp [host_program_eq, program, List.append_assoc]) rfl

theorem placed_at_143 : MemmoveGrowsliceModel.IsInfixAt Host.prog 143 :=
  infixAt_of (dataLabels ++ marshalSSZTo) [] (by simp [host_program_eq, program, List.append_assoc]) (by rfl)

theorem labels_fresh_at_8 : LabelsFresh marshalSSZTo 8 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_143 : LabelsFresh MemmoveGrowsliceModel 143 := labelsFresh_of (by rw [host_program_eq]; decide)

theorem label_bump_pointer : label "runtime.modelBumpPointer" = 0x10000 :=
  mk_label program _ 0 _ (by simp [program, dataLabels]) (by simp [programLabels])

abbrev zeros (k : Nat) : List UInt8 := List.replicate k 0
abbrev word_bytes (v : UInt64) : List UInt8 := Int.toBytes 8 v.toBitVec.toInt
def prefix30 : List UInt8 := (List.range 30).map (fun i => UInt8.ofNat (0x40 + i))

/-- bump pointer · heap (9000) · guard · receiver (72) · root (32) · rslot · growslice spill (40) · zA (16) ·
zB (16) · zC (8) · gap (8) · t40 (16) · t30 (16) · l32 · l24 · l16 · fp · return slot · spill rax · spill rbx ·
spill rcx · dst. -/
def block (e8 root dst : List UInt8) : List UInt8 :=
  Int.toBytes 8 (0x10008 : BitVec 64).toInt ++ (zeros 9000 ++ (word_bytes 0 ++ (zeros 8 ++ (e8 ++ (word_bytes 0x12380 ++ (word_bytes 32 ++ (word_bytes 32
    ++ (zeros 32 ++ (root ++ (zeros 8 ++ (zeros 40 ++ (zeros 16 ++ (zeros 16 ++ (zeros 8 ++ (zeros 8 ++ (zeros 16 ++ (zeros 16 ++ (zeros 8 ++ (zeros 8
    ++ (zeros 8 ++ (zeros 8 ++ (word_bytes 0 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ dst)))))))))))))))))))))))))

def mem (e8 root dst : List UInt8) : DataMem := (block e8 root dst).At (0x10000 : BitVec 64)

def initial_state (e8 root dst : List UInt8) (rbx len cap : UInt64) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x12338, rbx, len, 0, 0, cap, 0x12440, 0, 0, 0, 0, 0, 0, 0, 0x12320, 0⟩, zmms, flags, mem e8 root dst⟩

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x10008 : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((zeros 9000).At (0x10008 : BitVec 64)) ⋆ X)) m) : (bumpHeap 9000 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x10008, by decide, by rw [label_bump_pointer]; exact hm⟩) h

set_option maxHeartbeats 64000000 in
/-- **Non-vacuity of `CapacityReserved.Encode.cover`**, len 30, cap 30 + n (n ≤ 64). -/
theorem runs (g : SszValue) (n : Nat) (hn : n ≤ 64) (zmms : RegZmms) (flags : StatusFlags) :
    ∃ bs, serialize desc g.toValue = .ok bs ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rbx.toNat = 30 + 40)
      ⟨initial_state (uintBytes 8 g.epoch.toNat).toList g.root.toList (prefix30 ++ zeros n) 0x12460 30 (UInt64.ofNat (30 + n))
        zmms flags, Host.addrOf 8⟩ := by
  have he8 : (uintBytes 8 g.epoch.toNat).toList.length = 8 := by simp [Spec.uintBytes_size]
  have hroot : g.root.toList.length = 32 := by simp
  have hc : (UInt64.ofNat (30 + n)).toNat = 30 + n := by simp; omega
  obtain ⟨bs, hs, he⟩ := CapacityReserved.Encode.cover 8 placed_at_8 labels_fresh_at_8 g (zeros 8) (word_bytes 32) (zeros 32) prefix30 (zeros n) rfl rfl rfl
    0x12380 (initial_state (uintBytes 8 g.epoch.toNat).toList g.root.toList (prefix30 ++ zeros n) 0x12460 30 (UInt64.ofNat (30 + n))
      zmms flags) 0 0 rfl (by simp only [initial_state, hc]; simp [prefix30])
    (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 16) (zeros 16) (zeros 16) (zeros 16) (zeros 8) (zeros 40) (zeros 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (Eq ((zeros 8).At (0x123f8 : BitVec 64))) 0 [] rfl bumpHeap 9000
    (by
      have H : Eq ((block (uintBytes 8 g.epoch.toNat).toList g.root.toList (prefix30 ++ zeros n)).At (0x10000 : BitVec 64))
        (mem (uintBytes 8 g.epoch.toNat).toList g.root.toList (prefix30 ++ zeros n)) := rfl
      witness_split_n [he8, hroot, show prefix30.length = 30 from rfl]
      have H2 := lift_heap H
      rw [at_app prefix30 (zeros n) rfl (by simp [prefix30]; omega)]
      simp only [initial_state, word_bytes, nil_At_emp, Std.ExtHashMap.sep_emp, show Int.toBytes 8 (32#64).toInt = Int.toBytes 8 32 by decide, show prefix30.length = 30 from rfl, Std.ExtHashMap.emp_sep, UInt64.toBitVec_ofNat,
        Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, List.length_nil] at H2 ⊢
      generalize (uintBytes 8 g.epoch.toNat).toList = e8 at H2 ⊢
      generalize g.root.toList = root at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [initial_state]) (by simp only [initial_state, hc]; omega) (by simp [initial_state])
    (by unfold maxAlloc; omega) (model_growslice 143 placed_at_143 labels_fresh_at_143 _ 0) (model_memmove 143 placed_at_143 labels_fresh_at_143 0)
  exact ⟨bs, hs, eventually_mono he (fun _ h => ⟨h.1, h.2.1⟩)⟩

set_option maxHeartbeats 64000000 in
/-- Nil `dst` (rbx = 0, len = cap = 0): the reserve grows from nothing. -/
theorem runs_nil (g : SszValue) (zmms : RegZmms) (flags : StatusFlags) :
    ∃ bs, serialize desc g.toValue = .ok bs ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rbx.toNat = 0 + 40)
      ⟨initial_state (uintBytes 8 g.epoch.toNat).toList g.root.toList [] 0 0 0 zmms flags, Host.addrOf 8⟩ := by
  have he8 : (uintBytes 8 g.epoch.toNat).toList.length = 8 := by simp [Spec.uintBytes_size]
  have hroot : g.root.toList.length = 32 := by simp
  obtain ⟨bs, hs, he⟩ := CapacityReserved.Encode.cover 8 placed_at_8 labels_fresh_at_8 g (zeros 8) (word_bytes 32) (zeros 32) [] [] rfl rfl rfl
    0x12380 (initial_state (uintBytes 8 g.epoch.toNat).toList g.root.toList [] 0 0 0 zmms flags) 0 0 rfl rfl
    (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 16) (zeros 16) (zeros 16) (zeros 16) (zeros 8) (zeros 40) (zeros 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (Eq ((zeros 8).At (0x123f8 : BitVec 64))) 0 [] rfl bumpHeap 9000
    (by
      have H : Eq ((block (uintBytes 8 g.epoch.toNat).toList g.root.toList []).At (0x10000 : BitVec 64))
        (mem (uintBytes 8 g.epoch.toNat).toList g.root.toList []) := rfl
      witness_split_n [he8, hroot]
      have H2 := lift_heap H
      simp only [initial_state, word_bytes, nil_At_emp, List.nil_append, Std.ExtHashMap.sep_emp, show Int.toBytes 8 (32#64).toInt = Int.toBytes 8 32 by decide, Std.ExtHashMap.emp_sep,
        UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub,
        List.length_nil] at H2 ⊢
      generalize (uintBytes 8 g.epoch.toNat).toList = e8 at H2 ⊢
      generalize g.root.toList = root at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [initial_state]) (by simp [initial_state]) (by simp [initial_state])
    (by unfold maxAlloc; omega) (model_growslice 143 placed_at_143 labels_fresh_at_143 _ 0) (model_memmove 143 placed_at_143 labels_fresh_at_143 0)
  exact ⟨bs, hs, eventually_mono he (fun _ h => ⟨h.1, h.2.1⟩)⟩

/-- spare = cap − len ∈ {0, 7, 8, 39} (grow path), {40, 41} (fast path); nil dst. -/
example (g : SszValue) (z' : RegZmms) (f : StatusFlags) := runs g 0 (by decide) z' f
example (g : SszValue) (z' : RegZmms) (f : StatusFlags) := runs g 7 (by decide) z' f
example (g : SszValue) (z' : RegZmms) (f : StatusFlags) := runs g 8 (by decide) z' f
example (g : SszValue) (z' : RegZmms) (f : StatusFlags) := runs g 39 (by decide) z' f
example (g : SszValue) (z' : RegZmms) (f : StatusFlags) := runs g 40 (by decide) z' f
example (g : SszValue) (z' : RegZmms) (f : StatusFlags) := runs g 41 (by decide) z' f
example (g : SszValue) (z' : RegZmms) (f : StatusFlags) := runs_nil g z' f

/-- Go-value element: the receiver of this witness (offset 0x2338 of the block; Root = (0x12380, 32, 32)). -/
theorem recv : goValue (recvAt (block (Int.toBytes 8 0x0123456789abcdef) (List.replicate 32 0xff) []) 0x2338)
    = true := by decide

end Prysm.Checkpoint.Witness.CapacityReservedEncodeCover
