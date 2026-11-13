import Prysm.Checkpoint.EncodeCover
import Runtime.CopyModel
import Machine.WitnessHost
import Machine.WitnessSplit

/-!
# Witness of `Encode.cover`: every capacity range on one host

Host: data labels, the real Go 1.26.10 `(*v1alpha1.Checkpoint).MarshalSSZTo` (index 8) and `RtCopy`
(index 99: `rt_growslice` — new capacity `2·newLen + 192` from the bump heap — and `rt_memmove`,
both with `S = 0`). One memory block at `0x10000`: bump pointer, a 9000-byte heap (≥ `4·len + 8736`),
guard word (r14 = 0x12320), the 72-byte receiver (`Epoch` = `uintBytes 8 g.epoch`, `Root` =
(0x12380, 32, 32)), the 32 root bytes, the stack window (rsp = 0x12418) and `dst` at 0x12438 =
a 30-byte prefix and `n` spare bytes (cap = 30 + n). Frame `R` = `emp`. Instances: n = 0 (cap = len),
3, 8 (cap = len + 8), 39 (len + 39), 40 (len + 40, fast path); `runs_nil`: nil `dst`
(rbx = 0, len = cap = 0). With this growslice model the first growth gives `2·(len+8)+192 ≥ len + 40`,
so the run with `cap < len + 8` takes the left disjunct; the right disjunct (a second growslice after the
first) needs a runtime that returns a smaller capacity and is not exercised here (Go differential only).
-/

open Machine Runtime Machine.Witness Prysm.Checkpoint.Code EthLib.Serialization.Ssz

namespace Prysm.Checkpoint.Witness.EncodeCover

set_option maxRecDepth 100000

def dataLabels : Program :=
  [.label "runtime.fvBump", .label "pad1", .label "pad2", .label "pad3", .label "pad4", .label "pad5",
   .label "pad6", .label "pad7"]

def P : Program := dataLabels ++ marshalSSZTo ++ RtCopy

theorem P_len : P.length = 125 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem prog_eq : Host.prog = P := rfl

theorem hk8 : marshalSSZTo.IsInfixAt Host.prog 8 :=
  infixAt_of dataLabels RtCopy (by simp [prog_eq, P, List.append_assoc]) rfl

theorem hk99 : RtCopy.IsInfixAt Host.prog 99 :=
  infixAt_of (dataLabels ++ marshalSSZTo) [] (by simp [prog_eq, P, List.append_assoc]) (by rfl)

theorem hf8 : LabelsFresh marshalSSZTo 8 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf99 : LabelsFresh RtCopy 99 := labelsFresh_of (by rw [prog_eq]; decide)

theorem label_bump : label "runtime.fvBump" = 0x10000 :=
  mk_label P _ 0 _ (by simp [P, dataLabels]) (by simp [labs])

abbrev z (k : Nat) : List UInt8 := List.replicate k 0
abbrev w (v : UInt64) : List UInt8 := Int.toBytes 8 v.toBitVec.toInt
def pre30 : List UInt8 := (List.range 30).map (fun i => UInt8.ofNat (0x40 + i))

/-- bump pointer · heap (9000) · guard · receiver (72) · root (32) · rslot · growslice spill (40) · l72
· t40 (16) · t30 (16) · l32 · l24 · l16 · fp · return slot · spill rax · spill rbx · spill rcx · dst. -/
def block (e8 root dst : List UInt8) : List UInt8 :=
  Int.toBytes 8 (0x10008 : BitVec 64).toInt ++ (z 9000 ++ (w 0 ++ (z 8 ++ (e8 ++ (w 0x12380 ++ (w 32 ++ (w 32
    ++ (z 32 ++ (root ++ (z 8 ++ (z 40 ++ (z 8 ++ (z 16 ++ (z 16 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 8 ++ (w 0
    ++ (z 8 ++ (z 8 ++ (z 8 ++ dst))))))))))))))))))))))

def mem (e8 root dst : List UInt8) : DataMem := (block e8 root dst).At (0x10000 : BitVec 64)

def cs0 (e8 root dst : List UInt8) (rbx len cap : UInt64) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x12338, rbx, len, 0, 0, cap, 0x12418, 0, 0, 0, 0, 0, 0, 0, 0x12320, 0⟩, zmms, flags, mem e8 root dst⟩

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x10008 : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((z 9000).At (0x10008 : BitVec 64)) ⋆ X)) m) : (bumpHeap 9000 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x10008, by decide, by rw [label_bump]; exact hm⟩) h

set_option maxHeartbeats 64000000 in
/-- **Non-vacuity of `Encode.cover`**, len 30, cap 30 + n (n ≤ 64). -/
theorem runs (g : SszValue) (n : Nat) (hn : n ≤ 64) (zmms : RegZmms) (flags : StatusFlags) :
    ∃ bs, serialize desc g.toValue = .ok bs ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∨ st.pc = label "runtime.growslice")
      ⟨cs0 (uintBytes 8 g.epoch.toNat).toList g.root.toList (pre30 ++ z n) 0x12438 30 (UInt64.ofNat (30 + n))
        zmms flags, Host.addrOf 8⟩ := by
  have he8 : (uintBytes 8 g.epoch.toNat).toList.length = 8 := by simp [Spec.uintBytes_size]
  have hroot : g.root.toList.length = 32 := by simp
  have hc : (UInt64.ofNat (30 + n)).toNat = 30 + n := by simp; omega
  obtain ⟨bs, hs, he⟩ := Encode.cover 8 hk8 hf8 g (z 8) (w 32) (z 32) pre30 (z n) rfl rfl rfl
    0x12380 (cs0 (uintBytes 8 g.epoch.toNat).toList g.root.toList (pre30 ++ z n) 0x12438 30 (UInt64.ofNat (30 + n))
      zmms flags) 0 0 rfl (by simp only [cs0, hc]; simp [pre30])
    (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 16) (z 16) (z 8) (z 40) (z 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    Std.ExtHashMap.emp 0 [] rfl bumpHeap 9000
    (by
      have H : Eq ((block (uintBytes 8 g.epoch.toNat).toList g.root.toList (pre30 ++ z n)).At (0x10000 : BitVec 64))
        (mem (uintBytes 8 g.epoch.toNat).toList g.root.toList (pre30 ++ z n)) := rfl
      wit_split_n [he8, hroot, show pre30.length = 30 from rfl]
      have H2 := lift_heap H
      rw [at_app pre30 (z n) rfl (by simp [pre30]; omega)]
      simp only [cs0, w, nil_At_emp, Std.ExtHashMap.sep_emp, show Int.toBytes 8 (32#64).toInt = Int.toBytes 8 32 by decide, show pre30.length = 30 from rfl, Std.ExtHashMap.emp_sep, UInt64.toBitVec_ofNat,
        Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, List.length_nil] at H2 ⊢
      generalize (uintBytes 8 g.epoch.toNat).toList = e8 at H2 ⊢
      generalize g.root.toList = root at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [cs0]) (by simp [cs0]) (by simp only [cs0, hc]; omega) (by simp [cs0])
    (by unfold maxAlloc; omega) (rt_growslice 99 hk99 hf99 _ 0) (rt_memmove 99 hk99 hf99 0)
  exact ⟨bs, hs, eventually_mono he (fun _ h => h.imp (fun h' => h'.1) (fun h' => h'.1))⟩

set_option maxHeartbeats 64000000 in
/-- Nil `dst` (rbx = 0, len = cap = 0): the first append grows from nothing. -/
theorem runs_nil (g : SszValue) (zmms : RegZmms) (flags : StatusFlags) :
    ∃ bs, serialize desc g.toValue = .ok bs ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∨ st.pc = label "runtime.growslice")
      ⟨cs0 (uintBytes 8 g.epoch.toNat).toList g.root.toList [] 0 0 0 zmms flags, Host.addrOf 8⟩ := by
  have he8 : (uintBytes 8 g.epoch.toNat).toList.length = 8 := by simp [Spec.uintBytes_size]
  have hroot : g.root.toList.length = 32 := by simp
  obtain ⟨bs, hs, he⟩ := Encode.cover 8 hk8 hf8 g (z 8) (w 32) (z 32) [] [] rfl rfl rfl
    0x12380 (cs0 (uintBytes 8 g.epoch.toNat).toList g.root.toList [] 0 0 0 zmms flags) 0 0 rfl rfl
    (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 16) (z 16) (z 8) (z 40) (z 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    Std.ExtHashMap.emp 0 [] rfl bumpHeap 9000
    (by
      have H : Eq ((block (uintBytes 8 g.epoch.toNat).toList g.root.toList []).At (0x10000 : BitVec 64))
        (mem (uintBytes 8 g.epoch.toNat).toList g.root.toList []) := rfl
      wit_split_n [he8, hroot]
      have H2 := lift_heap H
      simp only [cs0, w, nil_At_emp, List.nil_append, Std.ExtHashMap.sep_emp, show Int.toBytes 8 (32#64).toInt = Int.toBytes 8 32 by decide, show pre30.length = 30 from rfl, Std.ExtHashMap.emp_sep,
        UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub,
        List.length_nil] at H2 ⊢
      generalize (uintBytes 8 g.epoch.toNat).toList = e8 at H2 ⊢
      generalize g.root.toList = root at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [cs0]) (by simp [cs0]) (by simp [cs0]) (by simp [cs0])
    (by unfold maxAlloc; omega) (rt_growslice 99 hk99 hf99 _ 0) (rt_memmove 99 hk99 hf99 0)
  exact ⟨bs, hs, eventually_mono he (fun _ h => h.imp (fun h' => h'.1) (fun h' => h'.1))⟩

/-- cap = len (30), len + 3, len + 8, len + 39 (second site grows), len + 40 (fast path); nil dst. -/
example (g : SszValue) (z' : RegZmms) (f : StatusFlags) := runs g 0 (by decide) z' f
example (g : SszValue) (z' : RegZmms) (f : StatusFlags) := runs g 3 (by decide) z' f
example (g : SszValue) (z' : RegZmms) (f : StatusFlags) := runs g 8 (by decide) z' f
example (g : SszValue) (z' : RegZmms) (f : StatusFlags) := runs g 39 (by decide) z' f
example (g : SszValue) (z' : RegZmms) (f : StatusFlags) := runs g 40 (by decide) z' f
example (g : SszValue) (z' : RegZmms) (f : StatusFlags) := runs_nil g z' f

end Prysm.Checkpoint.Witness.EncodeCover
