import E2eAd.AdAccept
import E2eAd.BumpNew72
import Fk.RtCopy
import Fk.BumpMore
import Fk.WHost

/-!
# Witness of `ad_e2e_accept_main` (AttestationData decoder accept path)

Host (one per file: two `Host` instances in one file make instance resolution unfold both programs): data labels, the real Go 1.26.10
`(*v1alpha1.AttestationData).UnmarshalSSZ` (index 9), `(*primitives.Slot).UnmarshalSSZ` (252),
`(*primitives.CommitteeIndex).UnmarshalSSZ` (315), `(*v1alpha1.Checkpoint).UnmarshalSSZ` (378),
`(*primitives.Epoch).UnmarshalSSZ` (486), the 1-byte bump `runtime.makeslice` (549,
`bump_makeslice1`), `RtCopy` (555, `rt_memmove`) and the 72-byte bump `runtime.newobject`
(581, `bump_newobject72`). One memory block at `0x10000`: bump pointer, writeBarrier word, the
240-byte heap, guard word, the 128 input bytes, the 96-byte receiver (`state`, Slot,
CommitteeIndex, Root header, old Source / Target words `aS` / `aT`, then `unknownFields` +
`sizeCache` + padding), the 104-byte callee block (`S = 8`), the callee return slot, the frame and
the caller's slots. The frame `R` is exactly the untouched receiver tail (32 bytes), the untouched
frame bytes rsp − 96 … rsp − 17 (80) and the unused spill slot rsp + 24. For every input and every
old Source / Target word (nil = zero, or any other bytes) every premise holds and the decoder
returns nil.
-/

open Fk Fk.W E2e E2eAd E2eAd.Code

namespace E2eAd.WitAdA

set_option maxRecDepth 100000

def dataLabels : Program :=
  [.label "runtime.fvBump", .label "pad1", .label "pad2", .label "pad3", .label "pad4", .label "pad5",
   .label "pad6", .label "pad7", .label "runtime.writeBarrier"]

def P : Program := dataLabels ++ AdUnmarshal ++ SlUnmarshal ++ CiUnmarshal ++ E2e.Code.CpUnmarshal
  ++ E2e.Code.EpUnmarshal ++ BumpAlloc1 ++ RtCopy ++ BumpNew72

theorem P_len : P.length = 587 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem prog_eq : Host.prog = P := rfl

theorem hk9 : AdUnmarshal.IsInfixAt Host.prog 9 :=
  infixAt_of dataLabels (SlUnmarshal ++ CiUnmarshal ++ E2e.Code.CpUnmarshal ++ E2e.Code.EpUnmarshal ++ BumpAlloc1
    ++ RtCopy ++ BumpNew72) (by simp [prog_eq, P, List.append_assoc]) rfl
theorem hk252 : SlUnmarshal.IsInfixAt Host.prog 252 :=
  infixAt_of (dataLabels ++ AdUnmarshal) (CiUnmarshal ++ E2e.Code.CpUnmarshal ++ E2e.Code.EpUnmarshal ++ BumpAlloc1
    ++ RtCopy ++ BumpNew72) (by simp [prog_eq, P, List.append_assoc]) (by rfl)
theorem hk315 : CiUnmarshal.IsInfixAt Host.prog 315 :=
  infixAt_of (dataLabels ++ AdUnmarshal ++ SlUnmarshal) (E2e.Code.CpUnmarshal ++ E2e.Code.EpUnmarshal ++ BumpAlloc1
    ++ RtCopy ++ BumpNew72) (by simp [prog_eq, P, List.append_assoc]) (by rfl)
theorem hk378 : E2e.Code.CpUnmarshal.IsInfixAt Host.prog 378 :=
  infixAt_of (dataLabels ++ AdUnmarshal ++ SlUnmarshal ++ CiUnmarshal) (E2e.Code.EpUnmarshal ++ BumpAlloc1
    ++ RtCopy ++ BumpNew72) (by simp [prog_eq, P, List.append_assoc]) (by rfl)
theorem hk486 : E2e.Code.EpUnmarshal.IsInfixAt Host.prog 486 :=
  infixAt_of (dataLabels ++ AdUnmarshal ++ SlUnmarshal ++ CiUnmarshal ++ E2e.Code.CpUnmarshal) (BumpAlloc1
    ++ RtCopy ++ BumpNew72) (by simp [prog_eq, P, List.append_assoc]) (by rfl)
theorem hk549 : BumpAlloc1.IsInfixAt Host.prog 549 :=
  infixAt_of (dataLabels ++ AdUnmarshal ++ SlUnmarshal ++ CiUnmarshal ++ E2e.Code.CpUnmarshal ++ E2e.Code.EpUnmarshal)
    (RtCopy ++ BumpNew72) (by simp [prog_eq, P, List.append_assoc]) (by rfl)
theorem hk555 : RtCopy.IsInfixAt Host.prog 555 :=
  infixAt_of (dataLabels ++ AdUnmarshal ++ SlUnmarshal ++ CiUnmarshal ++ E2e.Code.CpUnmarshal ++ E2e.Code.EpUnmarshal
    ++ BumpAlloc1) BumpNew72 (by simp [prog_eq, P, List.append_assoc]) (by rfl)
theorem hk581 : BumpNew72.IsInfixAt Host.prog 581 :=
  infixAt_of (dataLabels ++ AdUnmarshal ++ SlUnmarshal ++ CiUnmarshal ++ E2e.Code.CpUnmarshal ++ E2e.Code.EpUnmarshal
    ++ BumpAlloc1 ++ RtCopy) [] (by simp [prog_eq, P, List.append_assoc]) (by rfl)

theorem hf9 : LabelsFresh AdUnmarshal 9 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf252 : LabelsFresh SlUnmarshal 252 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf315 : LabelsFresh CiUnmarshal 315 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf378 : LabelsFresh E2e.Code.CpUnmarshal 378 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf486 : LabelsFresh E2e.Code.EpUnmarshal 486 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf555 : LabelsFresh RtCopy 555 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf549 : ∀ i < 549, Host.prog[i]? ≠ some (.label "runtime.makeslice") :=
  notLabel_of (by rw [prog_eq]; decide)
theorem hf581 : ∀ i < 581, Host.prog[i]? ≠ some (.label "runtime.newobject") :=
  notLabel_of (by rw [prog_eq]; decide)

theorem label_bump : label "runtime.fvBump" = 0x10000 :=
  mk_label P _ 0 _ (by simp [P, dataLabels]) (by simp [labs])

theorem label_wb : label "runtime.writeBarrier" = 0x10008 :=
  mk_label P _ 8 _ (by simp [P, dataLabels]) (by decide)

abbrev z (k : Nat) : List UInt8 := List.replicate k 0
abbrev w0 : List UInt8 := Int.toBytes 8 (0 : UInt64).toBitVec.toInt

/-- bump pointer (→ 0x1000c) · writeBarrier · heap (240) · guard · input (128) · receiver (96:
state, Slot, CommitteeIndex, Root ptr/len/cap, Source `aS`, Target `aT`, tail 32) · callee block (104)
· callee return slot · argument area (24) · frame gap (80) · Root save · saved rbp · return slot ·
spill rax · spill rbx · unused slot · spill rdi. -/
def block (in0 in1 root se sroot te troot aS aT : List UInt8) : List UInt8 :=
  Int.toBytes 8 (0x1000c : BitVec 64).toInt ++ ([0, 0, 0, 0] ++ (z 240 ++ (w0 ++ (in0 ++ (in1 ++ (root ++ (se
    ++ (sroot ++ (te ++ (troot ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 8 ++ (aS ++ (aT ++ (z 32
    ++ (z 104 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 80 ++ (z 8 ++ (z 8 ++ (w0 ++ (z 8 ++ (z 8 ++ (z 8
    ++ z 8)))))))))))))))))))))))))))))))

def mem (in0 in1 root se sroot te troot aS aT : List UInt8) : DataMem :=
  (block in0 in1 root se sroot te troot aS aT).At (0x10000 : BitVec 64)

def cs0 (in0 in1 root se sroot te troot aS aT : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10184, 0x10104, 128, 0, 0, 128, 0x102cc, 0, 0, 0, 0, 0, 0, 0, 0x100ec, 0⟩, zmms, flags,
    mem in0 in1 root se sroot te troot aS aT⟩

/-- The frame of the witness: the receiver tail, the frame gap and the unused slot rsp + 24. -/
def R0 : DataMem → Prop :=
  Eq ((z 32).At (0x101c4 : BitVec 64)) ⋆ Eq ((z 80).At (0x1026c : BitVec 64)) ⋆ Eq ((z 8).At (0x102e4 : BitVec 64))

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x1000c : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((z 240).At (0x1000c : BitVec 64)) ⋆ X)) m) : (bumpHeap 240 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x1000c, by decide, by rw [label_bump]; exact hm⟩) h

set_option maxHeartbeats 64000000 in
/-- **Non-vacuity of `ad_e2e_accept_main`.** -/
theorem ad_accept_runs (in0 in1 root se sroot te troot aS aT : List UInt8) (hin0 : in0.length = 8)
    (hin1 : in1.length = 8) (hroot : root.length = 32) (hse : se.length = 8) (hsroot : sroot.length = 32)
    (hte : te.length = 8) (htroot : troot.length = 32) (haS : aS.length = 8) (haT : aT.length = 8)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨cs0 in0 in1 root se sroot te troot aS aT zmms flags, Host.addrOf 9⟩ :=
  eventually_mono (ad_e2e_accept_main 9 hk9 hf9 252 hk252 hf252 315 hk315 hf315 378 hk378 hf378 486 hk486 hf486
    in0 in1 root se sroot te troot hin0 hin1 hroot hse hsroot hte htroot (cs0 in0 in1 root se sroot te troot aS aT zmms flags)
    0 0 (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 104) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) aS aT
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl haS haT R0 8 (Nat.le_refl _) (by decide) rfl
    bumpHeap 240
    (by
      have H : Eq ((block in0 in1 root se sroot te troot aS aT).At (0x10000 : BitVec 64))
        (mem in0 in1 root se sroot te troot aS aT) := rfl
      wit_split [hin0, hin1, hroot, hse, hsroot, hte, htroot, haS, haT]
      rw [Std.ExtHashMap.sep_comm_l (Eq (([0, 0, 0, 0] : List UInt8).At _)) (Eq ((z 240).At _))] at H
      have H2 := lift_heap H
      simp only [cs0, R0, w0, label_wb, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd, BitVec.reduceSub] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [cs0]) rfl (Nat.le_refl _) (bump_makeslice1 549 hk549 hf549 _) (rt_memmove 555 hk555 hf555 8)
    (bump_makeslice1 549 hk549 hf549 _) (rt_memmove 555 hk555 hf555 _) (bump_newobject72 581 hk581 hf581 _))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

/-- Zero input with a fresh `&AttestationData{}` (nil Source / Target); a representative input
with non-nil old Source / Target words; all-0xff input. -/
example (z' : RegZmms) (f : StatusFlags) :=
  ad_accept_runs (z 8) (z 8) (z 32) (z 8) (z 32) (z 8) (z 32) (z 8) (z 8) rfl rfl rfl rfl rfl rfl rfl rfl rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  ad_accept_runs (Int.toBytes 8 0x0123456789abcdef) (Int.toBytes 8 7) ((List.range 32).map (fun i => UInt8.ofNat i))
    (Int.toBytes 8 3) (List.replicate 32 0x11) (Int.toBytes 8 4) (List.replicate 32 0x22)
    (Int.toBytes 8 0x20000) (Int.toBytes 8 0x30000) (by decide) (by decide) rfl (by decide) rfl (by decide) rfl
    (by decide) (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) :=
  ad_accept_runs (List.replicate 8 0xff) (List.replicate 8 0xff) (List.replicate 32 0xff) (List.replicate 8 0xff)
    (List.replicate 32 0xff) (List.replicate 8 0xff) (List.replicate 32 0xff) (List.replicate 8 0xff)
    (List.replicate 8 0xff) rfl rfl rfl rfl rfl rfl rfl rfl rfl z' f

end E2eAd.WitAdA
