import E2eScal.BiAccept
import Runtime.CopyModel
import Runtime.BumpAllocatorVariants
import Machine.WitnessHost

/-!
# Witness of `bi_e2e_accept_main` (BlobIdentifier decoder accept path, hold-out)

Hand-written (the text of `WitE1A.lean` with the BlobIdentifier host and layout).
Host: data labels, the real Go 1.26.10 `(*v1alpha1.BlobIdentifier).UnmarshalSSZ` (index 9), the 1-byte bump
`runtime.makeslice` (81, `bump_makeslice1`) and `RtCopy` (87, `rt_memmove`).
One memory block at `0x10000`: bump pointer, writeBarrier word, the 32-byte heap, guard word, the 40 input
bytes, the 72-byte receiver (`prysm/ir/ir-mainnet.json` gc amd64 layout, size 72: `state` 0, BlockRoot
header 8 with old pointer word `oP1` and len = cap = 0, Index 32 (zero), `unknownFields` 40 + `sizeCache` 64
+ padding = 32 bytes), the 16-byte callee block (`S = 16`), the callee return slot, the argument area, the
pointer save, the saved rbp and the caller's slots (rsp = 0x100e4). The frame `R` is exactly the untouched
receiver tail (32 bytes).
For every input and every old root pointer word every premise holds and the decoder returns nil.
The receiver is a Go value of `v1alpha1.BlobIdentifier` (zero `state`, zero-length root slice, zero Index).
-/

open Machine Runtime TestTarget Machine.Witness E2e E2eScal Codec E2eScal.H3Code E2eScal.Bi

namespace E2eScal.WitBiA

set_option maxRecDepth 100000

def dataLabels : Program :=
  [.label "runtime.fvBump", .label "pad1", .label "pad2", .label "pad3", .label "pad4", .label "pad5",
   .label "pad6", .label "pad7", .label "runtime.writeBarrier"]

def P : Program := dataLabels ++ BiUnmarshal ++ BumpAlloc1 ++ RtCopy

theorem P_len : P.length = 113 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem prog_eq : Host.prog = P := rfl

theorem hk9 : BiUnmarshal.IsInfixAt Host.prog 9 :=
  infixAt_of dataLabels (BumpAlloc1 ++ RtCopy) (by simp [prog_eq, P, List.append_assoc]) rfl
theorem hk81 : BumpAlloc1.IsInfixAt Host.prog 81 :=
  infixAt_of (dataLabels ++ BiUnmarshal) RtCopy
    (by simp [prog_eq, P, List.append_assoc]) (by rfl)
theorem hk87 : RtCopy.IsInfixAt Host.prog 87 :=
  infixAt_of (dataLabels ++ BiUnmarshal ++ BumpAlloc1) []
    (by simp [prog_eq, P, List.append_assoc]) (by rfl)

theorem hf9 : LabelsFresh BiUnmarshal 9 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf87 : LabelsFresh RtCopy 87 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf81 : ∀ i < 81, Host.prog[i]? ≠ some (.label "runtime.makeslice") :=
  notLabel_of (by rw [prog_eq]; decide)

theorem label_bump : label "runtime.fvBump" = 0x10000 :=
  mk_label P _ 0 _ (by simp [P, dataLabels]) (by simp [labs])

theorem label_wb : label "runtime.writeBarrier" = 0x10008 :=
  mk_label P _ 8 _ (by simp [P, dataLabels]) (by decide)

abbrev z (k : Nat) : List UInt8 := List.replicate k 0
abbrev w0 : List UInt8 := Int.toBytes 8 (0 : UInt64).toBitVec.toInt

/-- bump pointer (→ 0x1000c) · writeBarrier · heap (32) · guard · input (40: r1, idx) · receiver (72:
state, BlockRoot `oP1`/0/0, Index 0, tail 32) · callee block (16) · callee return slot · argument area (24) ·
pointer save · saved rbp · return slot · spill rax · spill rbx. -/
def block (r1 idx oP1 : List UInt8) : List UInt8 :=
  Int.toBytes 8 (0x1000c : BitVec 64).toInt ++ ([0, 0, 0, 0] ++ (z 32 ++ (w0 ++ (r1 ++ (idx ++ (z 8 ++ (oP1 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 32 ++ (z 16 ++ (z 8 ++ (z 24 ++ (z 8 ++ (z 8 ++ (w0 ++ (z 8 ++ z 8))))))))))))))))))

def mem (r1 idx oP1 : List UInt8) : DataMem :=
  (block r1 idx oP1).At (0x10000 : BitVec 64)

def cs0 (r1 idx oP1 : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x1005c, 0x10034, 40, 0, 0, 40, 0x100e4, 0, 0, 0, 0, 0, 0, 0, 0x1001c, 0⟩, zmms, flags,
    mem r1 idx oP1⟩

/-- The frame of the witness: the untouched receiver tail (`unknownFields`, `sizeCache`, padding). -/
def R0 : DataMem → Prop := Eq ((z 32).At (0x10084 : BitVec 64))

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x1000c : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((z 32).At (0x1000c : BitVec 64)) ⋆ X)) m) : (bumpHeap 32 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x1000c, by decide, by rw [label_bump]; exact hm⟩) h

set_option maxHeartbeats 16000000 in
/-- **Non-vacuity of `bi_e2e_accept_main`.** -/
theorem bi_accept_runs (r1 idx oP1 : List UInt8) (hr1 : r1.length = 32) (hidx : idx.length = 8)
    (h1 : oP1.length = 8) (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨cs0 r1 idx oP1 zmms flags, Host.addrOf 9⟩ :=
  eventually_mono (bi_e2e_accept_main 9 hk9 hf9 r1 idx hr1 hidx (cs0 r1 idx oP1 zmms flags)
    0 0 (z 8) (z 8) (z 8) (z 24) (z 8) (z 8) (z 16) (z 8) oP1 (z 8) (z 8) (z 8)
    rfl rfl rfl rfl rfl rfl rfl h1 rfl rfl rfl
    R0 16 rfl bumpHeap 32
    (by
      have H : Eq ((block r1 idx oP1).At (0x10000 : BitVec 64)) (mem r1 idx oP1) := rfl
      wit_split [hr1, hidx, h1]
      rw [Std.ExtHashMap.sep_comm_l (Eq (([0, 0, 0, 0] : List UInt8).At _)) (Eq ((z 32).At _))] at H
      have H2 := lift_heap H
      simp only [cs0, R0, w0, label_wb, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd, BitVec.reduceSub] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [cs0]) rfl (Nat.le_refl _) (bump_makeslice1 81 hk81 hf81 _) (rt_memmove 87 hk87 hf87 _))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

/-- Zero input with a fresh `&BlobIdentifier{}` (nil root); a representative input with a non-nil old root
pointer word; all-0xff input. -/
example (z' : RegZmms) (f : StatusFlags) :=
  bi_accept_runs (z 32) (z 8) (z 8) rfl rfl rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  bi_accept_runs ((List.range 32).map (fun i => UInt8.ofNat i)) (Int.toBytes 8 0x0123456789abcdef)
    (Int.toBytes 8 0x20000) rfl (by decide) (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) :=
  bi_accept_runs (List.replicate 32 0xff) (List.replicate 8 0xff) (List.replicate 8 0xff) rfl rfl rfl z' f

end E2eScal.WitBiA
