import E2eScal.SmAccept
import Runtime.CopyModel
import Runtime.BumpAllocatorVariants
import Machine.WitnessHost

/-!
# Witness of `sm_e2e_accept_main` (SyncCommitteeMessage decoder accept path; hold-out, class C)

Hand-written (the text of `WitBhA.lean` with the SyncCommitteeMessage host and
layout). It shows that the premises of the independent hand statement `E2eScal.H5.sm_accept_stmt` are
satisfiable. Host: data labels, the real Go 1.26.10 `(*v1alpha1.SyncCommitteeMessage).UnmarshalSSZ` (index 9),
`(*primitives.Slot).UnmarshalSSZ` (188), `(*primitives.ValidatorIndex).UnmarshalSSZ` (251), the 1-byte bump
`runtime.makeslice` (314, `bump_makeslice1`) and `RtCopy` (320, `rt_memmove`).
One memory block at `0x10000`: bump pointer, writeBarrier word, the 128-byte heap, guard word, the 144 input
bytes, the 104-byte receiver (`state`, Slot, BlockRoot header with old pointer word `oP1` and len = cap = 0,
ValidatorIndex, Signature header with old pointer word `oP2` and len = cap = 0, then `unknownFields` +
`sizeCache` + padding = 32 bytes; `prysm/ir/ir-mainnet.json` gc amd64 layout), the 16-byte callee block (`S = 8`),
the callee return slot, the argument area, the frame and the caller's slots (rsp = 0x1020c). The frame `R` is
the untouched receiver tail (32 bytes), the untouched frame bytes rsp − 80 … rsp − 65 (16) and rsp − 40 … rsp − 9
(32) and the unused spill slot rsp + 24. For every input and every old pointer word every premise holds and the
decoder returns nil. The receiver is a Go value of `v1alpha1.SyncCommitteeMessage`.
-/

open Machine Runtime TestTarget Machine.Witness E2eAd E2eAd.Code E2eScal Codec E2eScal.H5Code E2eScal.BhCode E2eScal.H5

namespace E2eScal.WitSmA

set_option maxRecDepth 100000

def dataLabels : Program :=
  [.label "runtime.fvBump", .label "pad1", .label "pad2", .label "pad3", .label "pad4", .label "pad5",
   .label "pad6", .label "pad7", .label "runtime.writeBarrier"]

def P : Program := dataLabels ++ SmUnmarshal ++ SlUnmarshal ++ ViUnmarshal ++ BumpAlloc1 ++ RtCopy

theorem P_len : P.length = 346 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem prog_eq : Host.prog = P := rfl

theorem hk9 : SmUnmarshal.IsInfixAt Host.prog 9 :=
  infixAt_of dataLabels (SlUnmarshal ++ ViUnmarshal ++ BumpAlloc1 ++ RtCopy) (by simp [prog_eq, P, List.append_assoc]) rfl
theorem hk188 : SlUnmarshal.IsInfixAt Host.prog 188 :=
  infixAt_of (dataLabels ++ SmUnmarshal) (ViUnmarshal ++ BumpAlloc1 ++ RtCopy)
    (by simp [prog_eq, P, List.append_assoc]) (by rfl)
theorem hk251 : ViUnmarshal.IsInfixAt Host.prog 251 :=
  infixAt_of (dataLabels ++ SmUnmarshal ++ SlUnmarshal) (BumpAlloc1 ++ RtCopy)
    (by simp [prog_eq, P, List.append_assoc]) (by rfl)
theorem hk314 : BumpAlloc1.IsInfixAt Host.prog 314 :=
  infixAt_of (dataLabels ++ SmUnmarshal ++ SlUnmarshal ++ ViUnmarshal) RtCopy
    (by simp [prog_eq, P, List.append_assoc]) (by rfl)
theorem hk320 : RtCopy.IsInfixAt Host.prog 320 :=
  infixAt_of (dataLabels ++ SmUnmarshal ++ SlUnmarshal ++ ViUnmarshal ++ BumpAlloc1) []
    (by simp [prog_eq, P, List.append_assoc]) (by rfl)

theorem hf9 : LabelsFresh SmUnmarshal 9 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf188 : LabelsFresh SlUnmarshal 188 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf251 : LabelsFresh ViUnmarshal 251 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf320 : LabelsFresh RtCopy 320 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf314 : ∀ i < 314, Host.prog[i]? ≠ some (.label "runtime.makeslice") :=
  notLabel_of (by rw [prog_eq]; decide)

theorem label_bump : label "runtime.fvBump" = 0x10000 :=
  mk_label P _ 0 _ (by simp [P, dataLabels]) (by simp [labs])

theorem label_wb : label "runtime.writeBarrier" = 0x10008 :=
  mk_label P _ 8 _ (by simp [P, dataLabels]) (by decide)

abbrev z (k : Nat) : List UInt8 := List.replicate k 0
abbrev w0 : List UInt8 := Int.toBytes 8 (0 : UInt64).toBitVec.toInt

/-- bump pointer (→ 0x1000c) · writeBarrier · heap (128) · guard · input (144: Slot, BlockRoot, ValidatorIndex,
Signature) · receiver (104: state, Slot, BlockRoot `oP1`/0/0, ValidatorIndex, Signature `oP2`/0/0, tail 32) ·
callee block (16) · callee return slot · argument area (24) · frame gap (16) · error spills (2 × 8) · slice
pointer save · frame rest (32) · saved rbp · return slot · spill rax · spill rbx · unused slot · spill rdi. -/
def block (in0 rt in1 sig oP1 oP2 : List UInt8) : List UInt8 :=
  Int.toBytes 8 (0x1000c : BitVec 64).toInt ++ ([0, 0, 0, 0] ++ (z 128 ++ (w0 ++ (in0 ++ (rt ++ (in1 ++ (sig ++ (z 8 ++ (z 8 ++ (oP1 ++ (z 8 ++ (z 8 ++ (z 8 ++ (oP2 ++ (z 8 ++ (z 8 ++ (z 32 ++ (z 16 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 16 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 32 ++ (z 8 ++ (w0 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 8)))))))))))))))))))))))))))))))))

def mem (in0 rt in1 sig oP1 oP2 : List UInt8) : DataMem :=
  (block in0 rt in1 sig oP1 oP2).At (0x10000 : BitVec 64)

def cs0 (in0 rt in1 sig oP1 oP2 : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10124, 0x10094, 144, 0, 0, 144, 0x1020c, 0, 0, 0, 0, 0, 0, 0, 0x1007c, 0⟩, zmms, flags,
    mem in0 rt in1 sig oP1 oP2⟩

/-- The frame of the witness: the receiver tail, the two untouched frame ranges and the unused slot rsp + 24. -/
def R0 : DataMem → Prop :=
  Eq ((z 32).At (0x1016c : BitVec 64)) ⋆ Eq ((z 16).At (0x101bc : BitVec 64)) ⋆ Eq ((z 32).At (0x101e4 : BitVec 64))
    ⋆ Eq ((z 8).At (0x10224 : BitVec 64))

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x1000c : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((z 128).At (0x1000c : BitVec 64)) ⋆ X)) m) : (bumpHeap 128 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x1000c, by decide, by rw [label_bump]; exact hm⟩) h

set_option maxHeartbeats 16000000 in
/-- **Non-vacuity of `sm_e2e_accept_main`** (premises of `sm_accept_stmt`). -/
theorem sm_accept_runs (in0 rt in1 sig oP1 oP2 : List UInt8) (hin0 : in0.length = 8)
    (hrt : rt.length = 32) (hin1 : in1.length = 8) (hsig : sig.length = 96)
    (h1 : oP1.length = 8) (h2 : oP2.length = 8)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨cs0 in0 rt in1 sig oP1 oP2 zmms flags, Host.addrOf 9⟩ :=
  eventually_mono (sm_e2e_accept_main 9 hk9 hf9 188 hk188 hf188 251 hk251 hf251
    in0 rt in1 sig hin0 hrt hin1 hsig (cs0 in0 rt in1 sig oP1 oP2 zmms flags)
    0 0 (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 16) (z 8) (z 8)
    oP1 (z 8) (z 8) (z 8) oP2 (z 8) (z 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl h1 rfl rfl rfl h2 rfl rfl
    R0 8 (by decide) rfl bumpHeap 128
    (by
      have H : Eq ((block in0 rt in1 sig oP1 oP2).At (0x10000 : BitVec 64))
        (mem in0 rt in1 sig oP1 oP2) := rfl
      wit_split [hin0, hrt, hin1, hsig, h1, h2]
      rw [Std.ExtHashMap.sep_comm_l (Eq (([0, 0, 0, 0] : List UInt8).At _)) (Eq ((z 128).At _))] at H
      have H2 := lift_heap H
      simp only [cs0, R0, w0, label_wb, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd, BitVec.reduceSub] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [cs0]) rfl (Nat.le_refl _) (bump_makeslice1 314 hk314 hf314 _) (rt_memmove 320 hk320 hf320 _))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

/-- Zero input with a fresh `&SyncCommitteeMessage{}` (nil slices); a representative input with non-nil old
pointer words; all-0xff input. -/
example (z' : RegZmms) (f : StatusFlags) :=
  sm_accept_runs (z 8) (z 32) (z 8) (z 96) (z 8) (z 8) rfl rfl rfl rfl rfl rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  sm_accept_runs (Int.toBytes 8 0x0123456789abcdef) ((List.range 32).map (fun i => UInt8.ofNat i)) (Int.toBytes 8 7)
    (List.replicate 96 0x22) (Int.toBytes 8 0x20000) (Int.toBytes 8 0x30000)
    (by decide) rfl (by decide) rfl (by decide) (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) :=
  sm_accept_runs (List.replicate 8 0xff) (List.replicate 32 0xff) (List.replicate 8 0xff) (List.replicate 96 0xff)
    (List.replicate 8 0xff) (List.replicate 8 0xff) rfl rfl rfl rfl rfl rfl z' f

end E2eScal.WitSmA
