import Prysm.Checkpoint.DecodeAccept
import Runtime.CopyModel
import Runtime.BumpAllocatorVariants
import Machine.WitnessHost

/-!
# Witness of `Decode.accept` (decoder accept path)

Host: data labels, the real Go 1.26.10 `(*v1alpha1.Checkpoint).UnmarshalSSZ`
(index 5), the real `(*primitives.Epoch).UnmarshalSSZ` (index 113), the
1-byte bump `runtime.makeslice` (index 176, `bump_makeslice1`) and `RtCopy`
(index 182, `rt_memmove`). One memory block at `0x10000`: bump pointer,
writeBarrier word, the 32-byte heap, guard word, the 40 input bytes, the
72-byte receiver (`state`, `Epoch`, `Root` header, `unknownFields`,
`sizeCache` + padding, all zero: a fresh `&Checkpoint{}`), and the 128-byte
stack window (`S = 8`). The frame `R` is exactly the two untouched 16-byte
gaps of the frame (rsp − 64 … rsp − 49, rsp − 24 … rsp − 9). For every epoch
word and root, every premise holds and the decoder returns nil with the
receiver's `Epoch` = the 8 input bytes.
-/

open Machine Runtime TestTarget Machine.Witness Prysm.Checkpoint.Code

namespace Prysm.Checkpoint.Witness.DecodeAccept

set_option maxRecDepth 100000

def dataLabels : Program :=
  [.label "runtime.fvBump", .label "pad1", .label "pad2", .label "pad3", .label "pad4", .label "pad5",
   .label "pad6", .label "pad7", .label "runtime.writeBarrier"]

def P : Program := dataLabels ++ unmarshalSSZ ++ Prysm.Epoch.Code.unmarshalSSZ ++ BumpAlloc1 ++ RtCopy

theorem P_len : P.length = 212 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem prog_eq : Host.prog = P := rfl

theorem hk9 : unmarshalSSZ.IsInfixAt Host.prog 9 :=
  infixAt_of dataLabels (Prysm.Epoch.Code.unmarshalSSZ ++ BumpAlloc1 ++ RtCopy) (by simp [prog_eq, P, List.append_assoc]) rfl

theorem hk117 : Prysm.Epoch.Code.unmarshalSSZ.IsInfixAt Host.prog 117 :=
  infixAt_of (dataLabels ++ unmarshalSSZ) (BumpAlloc1 ++ RtCopy) (by simp [prog_eq, P, List.append_assoc]) (by rfl)

theorem hk180 : BumpAlloc1.IsInfixAt Host.prog 180 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ Prysm.Epoch.Code.unmarshalSSZ) RtCopy (by simp [prog_eq, P, List.append_assoc]) (by rfl)

theorem hk186 : RtCopy.IsInfixAt Host.prog 186 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ Prysm.Epoch.Code.unmarshalSSZ ++ BumpAlloc1) [] (by simp [prog_eq, P, List.append_assoc])
    (by rfl)

theorem hf9 : LabelsFresh unmarshalSSZ 9 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf117 : LabelsFresh Prysm.Epoch.Code.unmarshalSSZ 117 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf186 : LabelsFresh RtCopy 186 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf180 : ∀ i < 180, Host.prog[i]? ≠ some (.label "runtime.makeslice") :=
  notLabel_of (by rw [prog_eq]; decide)

theorem label_bump : label "runtime.fvBump" = 0x10000 :=
  mk_label P _ 0 _ (by simp [P, dataLabels]) (by simp [labs])

theorem label_wb : label "runtime.writeBarrier" = 0x10008 :=
  mk_label P _ 8 _ (by simp [P, dataLabels]) (by decide)

abbrev z (k : Nat) : List UInt8 := List.replicate k 0
abbrev w0 : List UInt8 := Int.toBytes 8 (0 : UInt64).toBitVec.toInt

/-- bump pointer (→ 0x1000c) · writeBarrier · heap (32) · guard · input (40) · receiver (72)
· stack window: scratch (8) · rslot · m0 · m1 · m2 · gap (16) · l30 · l28 · l20 · gap (16) · fp ·
return slot · spill rax · spill rbx. -/
def block (e8 root : List UInt8) : List UInt8 :=
  Int.toBytes 8 (0x1000c : BitVec 64).toInt ++ ([0, 0, 0, 0] ++ (z 32 ++ (w0 ++ (e8 ++ (root ++ (z 8 ++ (z 8 ++ (z 8
    ++ (z 8 ++ (z 8 ++ (z 32 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 16 ++ (z 8 ++ (z 8 ++ (z 8
    ++ (z 16 ++ (z 8 ++ (w0 ++ (z 8 ++ z 8))))))))))))))))))))))))

def mem (e8 root : List UInt8) : DataMem := (block e8 root).At (0x10000 : BitVec 64)

def cs0 (e8 root : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x1005c, 0x10034, 40, 0, 0, 0, 0x1010c, 0, 0, 0, 0, 0, 0, 0, 0x1001c, 0⟩, zmms, flags, mem e8 root⟩

/-- The frame of the witness: the two 16-byte gaps of the stack window. -/
def R0 : DataMem → Prop := Eq ((z 16).At (0x100cc : BitVec 64)) ⋆ Eq ((z 16).At (0x100f4 : BitVec 64))

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x1000c : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((z 32).At (0x1000c : BitVec 64)) ⋆ X)) m) : (bumpHeap 32 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x1000c, by decide, by rw [label_bump]; exact hm⟩) h

set_option maxHeartbeats 16000000 in
/-- **Non-vacuity of `Decode.accept`.** -/
theorem runs (e8 root : List UInt8) (he8 : e8.length = 8) (hroot : root.length = 32)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨cs0 e8 root zmms flags, Host.addrOf 9⟩ :=
  eventually_mono (Decode.accept 9 hk9 hf9 117 hk117 hf117 e8 root he8 hroot (cs0 e8 root zmms flags) 0 0
    (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 32)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl R0 8 (Nat.le_refl _) (by decide) (z 8) rfl
    bumpHeap 32
    (by
      have H : Eq ((block e8 root).At (0x10000 : BitVec 64)) (mem e8 root) := rfl
      wit_split [he8, hroot]
      rw [Std.ExtHashMap.sep_comm_l (Eq (([0, 0, 0, 0] : List UInt8).At _)) (Eq ((z 32).At _))] at H
      have H2 := lift_heap H
      simp only [cs0, R0, w0, label_wb, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd, BitVec.reduceSub] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [cs0]) rfl (by omega) (bump_makeslice1 180 hk180 hf180 _) (rt_memmove 186 hk186 hf186 8))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

/-- epoch 0 / root 0; a representative value and pattern root; 2^64 − 1 and 0xff root. -/
example (z' : RegZmms) (f : StatusFlags) := runs (Int.toBytes 8 0) (z 32) (by decide) rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs (Int.toBytes 8 0x0123456789abcdef) ((List.range 32).map (fun i => (UInt8.ofNat i))) (by decide) rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs (Int.toBytes 8 (2 ^ 64 - 1)) (List.replicate 32 0xff) (by decide) rfl z' f

end Prysm.Checkpoint.Witness.DecodeAccept
