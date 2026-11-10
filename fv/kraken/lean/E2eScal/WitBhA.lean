import E2eScal.BhAccept
import Fk.RtCopy
import Fk.BumpMore
import Fk.WHost

/-!
# Witness of `bh_e2e_accept_main` (BeaconBlockHeader decoder accept path, H1 hold-out (ii))

Hand-written by the evaluation session (the text of `E2eAd/WitAdA.lean` with the BeaconBlockHeader host
and layout). Host: data labels, the real Go 1.26.10 `(*v1alpha1.BeaconBlockHeader).UnmarshalSSZ`
(index 9), `(*primitives.Slot).UnmarshalSSZ` (226), `(*primitives.ValidatorIndex).UnmarshalSSZ` (289),
the 1-byte bump `runtime.makeslice` (352, `bump_makeslice1`) and `RtCopy` (358, `rt_memmove`).
One memory block at `0x10000`: bump pointer, writeBarrier word, the 96-byte heap, guard word, the 112 input
bytes, the 128-byte receiver (`state`, Slot, ProposerIndex, three root headers with old pointer words
`oP1 oP2 oP3` and len = cap = 0, then `unknownFields` + `sizeCache` + padding = 32 bytes), the 16-byte callee
block (`S = 8`), the callee return slot, the argument area, the frame and the caller's slots
(rsp = 0x101e4). The frame `R` is exactly the untouched receiver tail (32 bytes), the untouched frame bytes
rsp − 80 … rsp − 65 (16) and rsp − 40 … rsp − 9 (32) and the unused spill slot rsp + 24. For every input and
every old root pointer word (nil = zero, or any other bytes) every premise holds and the decoder returns nil.
The receiver is a Go value of `v1alpha1.BeaconBlockHeader` (zero `state`, zero-length root slices).
-/

open Fk Fk.W E2e E2eAd E2eAd.Code E2eScal E2eScal.BhCode E2eScal.Bh

namespace E2eScal.WitBhA

set_option maxRecDepth 100000

def dataLabels : Program :=
  [.label "runtime.fvBump", .label "pad1", .label "pad2", .label "pad3", .label "pad4", .label "pad5",
   .label "pad6", .label "pad7", .label "runtime.writeBarrier"]

def P : Program := dataLabels ++ BhUnmarshal ++ SlUnmarshal ++ ViUnmarshal ++ BumpAlloc1 ++ RtCopy

theorem P_len : P.length = 384 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem prog_eq : Host.prog = P := rfl

theorem hk9 : BhUnmarshal.IsInfixAt Host.prog 9 :=
  infixAt_of dataLabels (SlUnmarshal ++ ViUnmarshal ++ BumpAlloc1 ++ RtCopy) (by simp [prog_eq, P, List.append_assoc]) rfl
theorem hk226 : SlUnmarshal.IsInfixAt Host.prog 226 :=
  infixAt_of (dataLabels ++ BhUnmarshal) (ViUnmarshal ++ BumpAlloc1 ++ RtCopy)
    (by simp [prog_eq, P, List.append_assoc]) (by rfl)
theorem hk289 : ViUnmarshal.IsInfixAt Host.prog 289 :=
  infixAt_of (dataLabels ++ BhUnmarshal ++ SlUnmarshal) (BumpAlloc1 ++ RtCopy)
    (by simp [prog_eq, P, List.append_assoc]) (by rfl)
theorem hk352 : BumpAlloc1.IsInfixAt Host.prog 352 :=
  infixAt_of (dataLabels ++ BhUnmarshal ++ SlUnmarshal ++ ViUnmarshal) RtCopy
    (by simp [prog_eq, P, List.append_assoc]) (by rfl)
theorem hk358 : RtCopy.IsInfixAt Host.prog 358 :=
  infixAt_of (dataLabels ++ BhUnmarshal ++ SlUnmarshal ++ ViUnmarshal ++ BumpAlloc1) []
    (by simp [prog_eq, P, List.append_assoc]) (by rfl)

theorem hf9 : LabelsFresh BhUnmarshal 9 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf226 : LabelsFresh SlUnmarshal 226 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf289 : LabelsFresh ViUnmarshal 289 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf358 : LabelsFresh RtCopy 358 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf352 : ∀ i < 352, Host.prog[i]? ≠ some (.label "runtime.makeslice") :=
  notLabel_of (by rw [prog_eq]; decide)

theorem label_bump : label "runtime.fvBump" = 0x10000 :=
  mk_label P _ 0 _ (by simp [P, dataLabels]) (by simp [labs])

theorem label_wb : label "runtime.writeBarrier" = 0x10008 :=
  mk_label P _ 8 _ (by simp [P, dataLabels]) (by decide)

abbrev z (k : Nat) : List UInt8 := List.replicate k 0
abbrev w0 : List UInt8 := Int.toBytes 8 (0 : UInt64).toBitVec.toInt

/-- bump pointer (→ 0x1000c) · writeBarrier · heap (96) · guard · input (112) · receiver (128: state, Slot,
ProposerIndex, ParentRoot `oP1`/0/0, StateRoot `oP2`/0/0, BodyRoot `oP3`/0/0, tail 32) · callee block (16)
· callee return slot · argument area (24) · frame gap (16) · error spills (2 × 8) · root pointer save ·
frame rest (32) · saved rbp · return slot · spill rax · spill rbx · unused slot · spill rdi. -/
def block (in0 in1 r1 r2 r3 oP1 oP2 oP3 : List UInt8) : List UInt8 :=
  Int.toBytes 8 (0x1000c : BitVec 64).toInt ++ ([0, 0, 0, 0] ++ (z 96 ++ (w0 ++ (in0 ++ (in1 ++ (r1 ++ (r2 ++ (r3 ++ (z 8 ++ (z 8 ++ (z 8 ++ (oP1 ++ (z 8 ++ (z 8 ++ (oP2 ++ (z 8 ++ (z 8 ++ (oP3 ++ (z 8 ++ (z 8 ++ (z 32 ++ (z 16 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 16 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 32 ++ (z 8 ++ (w0 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 8)))))))))))))))))))))))))))))))))))))

def mem (in0 in1 r1 r2 r3 oP1 oP2 oP3 : List UInt8) : DataMem :=
  (block in0 in1 r1 r2 r3 oP1 oP2 oP3).At (0x10000 : BitVec 64)

def cs0 (in0 in1 r1 r2 r3 oP1 oP2 oP3 : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x100e4, 0x10074, 112, 0, 0, 112, 0x101e4, 0, 0, 0, 0, 0, 0, 0, 0x1005c, 0⟩, zmms, flags,
    mem in0 in1 r1 r2 r3 oP1 oP2 oP3⟩

/-- The frame of the witness: the receiver tail, the two untouched frame ranges and the unused slot rsp + 24. -/
def R0 : DataMem → Prop :=
  Eq ((z 32).At (0x10144 : BitVec 64)) ⋆ Eq ((z 16).At (0x10194 : BitVec 64)) ⋆ Eq ((z 32).At (0x101bc : BitVec 64))
    ⋆ Eq ((z 8).At (0x101fc : BitVec 64))

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x1000c : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((z 96).At (0x1000c : BitVec 64)) ⋆ X)) m) : (bumpHeap 96 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x1000c, by decide, by rw [label_bump]; exact hm⟩) h

set_option maxHeartbeats 16000000 in
/-- **Non-vacuity of `bh_e2e_accept_main`.** -/
theorem bh_accept_runs (in0 in1 r1 r2 r3 oP1 oP2 oP3 : List UInt8) (hin0 : in0.length = 8)
    (hin1 : in1.length = 8) (hr1 : r1.length = 32) (hr2 : r2.length = 32) (hr3 : r3.length = 32)
    (h1 : oP1.length = 8) (h2 : oP2.length = 8) (h3 : oP3.length = 8)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨cs0 in0 in1 r1 r2 r3 oP1 oP2 oP3 zmms flags, Host.addrOf 9⟩ :=
  eventually_mono (bh_e2e_accept_main 9 hk9 hf9 226 hk226 hf226 289 hk289 hf289
    in0 in1 r1 r2 r3 hin0 hin1 hr1 hr2 hr3 (cs0 in0 in1 r1 r2 r3 oP1 oP2 oP3 zmms flags)
    0 0 (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 16) (z 8) (z 8) (z 8)
    oP1 (z 8) (z 8) oP2 (z 8) (z 8) oP3 (z 8) (z 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl h1 rfl rfl h2 rfl rfl h3 rfl rfl
    R0 8 (by decide) rfl bumpHeap 96
    (by
      have H : Eq ((block in0 in1 r1 r2 r3 oP1 oP2 oP3).At (0x10000 : BitVec 64))
        (mem in0 in1 r1 r2 r3 oP1 oP2 oP3) := rfl
      wit_split [hin0, hin1, hr1, hr2, hr3, h1, h2, h3]
      rw [Std.ExtHashMap.sep_comm_l (Eq (([0, 0, 0, 0] : List UInt8).At _)) (Eq ((z 96).At _))] at H
      have H2 := lift_heap H
      simp only [cs0, R0, w0, label_wb, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd, BitVec.reduceSub] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [cs0]) rfl (Nat.le_refl _) (bump_makeslice1 352 hk352 hf352 _) (rt_memmove 358 hk358 hf358 _))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

/-- Zero input with a fresh `&BeaconBlockHeader{}` (nil roots); a representative input with non-nil old
root pointer words; all-0xff input. -/
example (z' : RegZmms) (f : StatusFlags) :=
  bh_accept_runs (z 8) (z 8) (z 32) (z 32) (z 32) (z 8) (z 8) (z 8) rfl rfl rfl rfl rfl rfl rfl rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  bh_accept_runs (Int.toBytes 8 0x0123456789abcdef) (Int.toBytes 8 7) ((List.range 32).map (fun i => UInt8.ofNat i))
    (List.replicate 32 0x11) (List.replicate 32 0x22) (Int.toBytes 8 0x20000) (Int.toBytes 8 0x30000)
    (Int.toBytes 8 0x40000) (by decide) (by decide) rfl rfl rfl (by decide) (by decide) (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) :=
  bh_accept_runs (List.replicate 8 0xff) (List.replicate 8 0xff) (List.replicate 32 0xff) (List.replicate 32 0xff)
    (List.replicate 32 0xff) (List.replicate 8 0xff) (List.replicate 8 0xff) (List.replicate 8 0xff)
    rfl rfl rfl rfl rfl rfl rfl rfl z' f

end E2eScal.WitBhA
