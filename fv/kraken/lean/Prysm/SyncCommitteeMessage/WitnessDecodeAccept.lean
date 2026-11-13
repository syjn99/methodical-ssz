import Prysm.SyncCommitteeMessage.DecodeAccept
import Runtime.CopyModel
import Runtime.BumpAllocatorVariants
import Machine.WitnessHost

/-!
# Witness of `Decode.accept` (SyncCommitteeMessage decoder accept path; hold-out, class C)

Hand-written (the text of `Prysm/BeaconBlockHeader/WitnessDecodeAccept.lean` with the SyncCommitteeMessage host and
layout). It shows that the premises of the independent hand statement `Prysm.SyncCommitteeMessage.Decode.accept_statement` are
satisfiable. Host: data labels, the real Go 1.26.10 `(*v1alpha1.SyncCommitteeMessage).UnmarshalSSZ` (index 9),
`(*primitives.Slot).UnmarshalSSZ` (188), `(*primitives.ValidatorIndex).UnmarshalSSZ` (251), the 1-byte bump
`runtime.makeslice` (314, `bump_makeslice1`) and `MemmoveGrowsliceModel` (320, `model_memmove`).
One memory block at `0x10000`: bump pointer, writeBarrier word, the 128-byte heap, guard word, the 144 input
bytes, the 104-byte receiver (`state`, Slot, BlockRoot header with old pointer word `oP1` and len = cap = 0,
ValidatorIndex, Signature header with old pointer word `oP2` and len = cap = 0, then `unknownFields` +
`sizeCache` + padding = 32 bytes; `prysm/ir/ir-mainnet.json` gc amd64 layout), the 16-byte callee block (`S = 8`),
the callee return slot, the argument area, the frame and the caller's slots (rsp = 0x1020c). The frame `R` is
the untouched receiver tail (32 bytes), the untouched frame bytes rsp − 80 … rsp − 65 (16) and rsp − 40 … rsp − 9
(32) and the unused spill slot rsp + 24. For every input and every old pointer word every premise holds and the
decoder returns nil. The receiver is a Go value of `v1alpha1.SyncCommitteeMessage`.
-/

open Machine Runtime Machine.Witness Prysm.AttestationData.Code Codec Prysm.SyncCommitteeMessage.Code

namespace Prysm.SyncCommitteeMessage.Witness.DecodeAccept

set_option maxRecDepth 100000

def dataLabels : Program :=
  [.label "runtime.modelBumpPointer", .label "pad1", .label "pad2", .label "pad3", .label "pad4", .label "pad5",
   .label "pad6", .label "pad7", .label "runtime.writeBarrier"]

def program : Program := dataLabels ++ Code.unmarshalSSZ ++ Prysm.Slot.Code.unmarshalSSZ ++ Prysm.ValidatorIndex.Code.unmarshalSSZ ++ BumpMakeslice1 ++ MemmoveGrowsliceModel

theorem program_length : program.length = 346 := by rfl

instance host : Host := mkHost program (by rw [program_length]; decide)

theorem host_program_eq : Host.prog = program := rfl

theorem placed_at_9 : Code.unmarshalSSZ.IsInfixAt Host.prog 9 :=
  infixAt_of dataLabels (Prysm.Slot.Code.unmarshalSSZ ++ Prysm.ValidatorIndex.Code.unmarshalSSZ ++ BumpMakeslice1 ++ MemmoveGrowsliceModel) (by simp [host_program_eq, program, List.append_assoc]) rfl
theorem placed_at_188 : Prysm.Slot.Code.unmarshalSSZ.IsInfixAt Host.prog 188 :=
  infixAt_of (dataLabels ++ Code.unmarshalSSZ) (Prysm.ValidatorIndex.Code.unmarshalSSZ ++ BumpMakeslice1 ++ MemmoveGrowsliceModel)
    (by simp [host_program_eq, program, List.append_assoc]) (by rfl)
theorem placed_at_251 : Prysm.ValidatorIndex.Code.unmarshalSSZ.IsInfixAt Host.prog 251 :=
  infixAt_of (dataLabels ++ Code.unmarshalSSZ ++ Prysm.Slot.Code.unmarshalSSZ) (BumpMakeslice1 ++ MemmoveGrowsliceModel)
    (by simp [host_program_eq, program, List.append_assoc]) (by rfl)
theorem placed_at_314 : BumpMakeslice1.IsInfixAt Host.prog 314 :=
  infixAt_of (dataLabels ++ Code.unmarshalSSZ ++ Prysm.Slot.Code.unmarshalSSZ ++ Prysm.ValidatorIndex.Code.unmarshalSSZ) MemmoveGrowsliceModel
    (by simp [host_program_eq, program, List.append_assoc]) (by rfl)
theorem placed_at_320 : MemmoveGrowsliceModel.IsInfixAt Host.prog 320 :=
  infixAt_of (dataLabels ++ Code.unmarshalSSZ ++ Prysm.Slot.Code.unmarshalSSZ ++ Prysm.ValidatorIndex.Code.unmarshalSSZ ++ BumpMakeslice1) []
    (by simp [host_program_eq, program, List.append_assoc]) (by rfl)

theorem labels_fresh_at_9 : LabelsFresh Code.unmarshalSSZ 9 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_188 : LabelsFresh Prysm.Slot.Code.unmarshalSSZ 188 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_251 : LabelsFresh Prysm.ValidatorIndex.Code.unmarshalSSZ 251 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_320 : LabelsFresh MemmoveGrowsliceModel 320 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_314 : ∀ i < 314, Host.prog[i]? ≠ some (.label "runtime.makeslice") :=
  notLabel_of (by rw [host_program_eq]; decide)

theorem label_bump_pointer : label "runtime.modelBumpPointer" = 0x10000 :=
  mk_label program _ 0 _ (by simp [program, dataLabels]) (by simp [labs])

theorem label_write_barrier : label "runtime.writeBarrier" = 0x10008 :=
  mk_label program _ 8 _ (by simp [program, dataLabels]) (by decide)

abbrev zeros (k : Nat) : List UInt8 := List.replicate k 0
abbrev zero_word_bytes : List UInt8 := Int.toBytes 8 (0 : UInt64).toBitVec.toInt

/-- bump pointer (→ 0x1000c) · writeBarrier · heap (128) · guard · input (144: Slot, BlockRoot, ValidatorIndex,
Signature) · receiver (104: state, Slot, BlockRoot `oP1`/0/0, ValidatorIndex, Signature `oP2`/0/0, tail 32) ·
callee block (16) · callee return slot · argument area (24) · frame gap (16) · error spills (2 × 8) · slice
pointer save · frame rest (32) · saved rbp · return slot · spill rax · spill rbx · unused slot · spill rdi. -/
def block (in0 rt in1 sig oP1 oP2 : List UInt8) : List UInt8 :=
  Int.toBytes 8 (0x1000c : BitVec 64).toInt ++ ([0, 0, 0, 0] ++ (zeros 128 ++ (zero_word_bytes ++ (in0 ++ (rt ++ (in1 ++ (sig ++ (zeros 8 ++ (zeros 8 ++ (oP1 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (oP2 ++ (zeros 8 ++ (zeros 8 ++ (zeros 32 ++ (zeros 16 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 16 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 32 ++ (zeros 8 ++ (zero_word_bytes ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8)))))))))))))))))))))))))))))))))

def mem (in0 rt in1 sig oP1 oP2 : List UInt8) : DataMem :=
  (block in0 rt in1 sig oP1 oP2).At (0x10000 : BitVec 64)

def initial_state (in0 rt in1 sig oP1 oP2 : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10124, 0x10094, 144, 0, 0, 144, 0x1020c, 0, 0, 0, 0, 0, 0, 0, 0x1007c, 0⟩, zmms, flags,
    mem in0 rt in1 sig oP1 oP2⟩

/-- The frame of the witness: the receiver tail, the two untouched frame ranges and the unused slot rsp + 24. -/
def frame_rest : DataMem → Prop :=
  Eq ((zeros 32).At (0x1016c : BitVec 64)) ⋆ Eq ((zeros 16).At (0x101bc : BitVec 64)) ⋆ Eq ((zeros 32).At (0x101e4 : BitVec 64))
    ⋆ Eq ((zeros 8).At (0x10224 : BitVec 64))

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x1000c : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((zeros 128).At (0x1000c : BitVec 64)) ⋆ X)) m) : (bumpHeap 128 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x1000c, by decide, by rw [label_bump_pointer]; exact hm⟩) h

set_option maxHeartbeats 16000000 in
/-- **Non-vacuity of `Decode.accept`** (premises of `Decode.accept_statement`). -/
theorem runs (in0 rt in1 sig oP1 oP2 : List UInt8) (hin0 : in0.length = 8)
    (hrt : rt.length = 32) (hin1 : in1.length = 8) (hsig : sig.length = 96)
    (h1 : oP1.length = 8) (h2 : oP2.length = 8)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨initial_state in0 rt in1 sig oP1 oP2 zmms flags, Host.addrOf 9⟩ :=
  eventually_mono (Decode.accept 9 placed_at_9 labels_fresh_at_9 188 placed_at_188 labels_fresh_at_188 251 placed_at_251 labels_fresh_at_251
    in0 rt in1 sig hin0 hrt hin1 hsig (initial_state in0 rt in1 sig oP1 oP2 zmms flags)
    0 0 (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 16) (zeros 8) (zeros 8)
    oP1 (zeros 8) (zeros 8) (zeros 8) oP2 (zeros 8) (zeros 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl h1 rfl rfl rfl h2 rfl rfl
    frame_rest 8 (by decide) rfl bumpHeap 128
    (by
      have H : Eq ((block in0 rt in1 sig oP1 oP2).At (0x10000 : BitVec 64))
        (mem in0 rt in1 sig oP1 oP2) := rfl
      witness_split [hin0, hrt, hin1, hsig, h1, h2]
      rw [Std.ExtHashMap.sep_comm_l (Eq (([0, 0, 0, 0] : List UInt8).At _)) (Eq ((zeros 128).At _))] at H
      have H2 := lift_heap H
      simp only [initial_state, frame_rest, zero_word_bytes, label_write_barrier, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd, BitVec.reduceSub] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [initial_state]) rfl (Nat.le_refl _) (bump_makeslice1 314 placed_at_314 labels_fresh_at_314 _) (model_memmove 320 placed_at_320 labels_fresh_at_320 _))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

/-- Zero input with a fresh `&SyncCommitteeMessage{}` (nil slices); a representative input with non-nil old
pointer words; all-0xff input. -/
example (z' : RegZmms) (f : StatusFlags) :=
  runs (zeros 8) (zeros 32) (zeros 8) (zeros 96) (zeros 8) (zeros 8) rfl rfl rfl rfl rfl rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs (Int.toBytes 8 0x0123456789abcdef) ((List.range 32).map (fun i => UInt8.ofNat i)) (Int.toBytes 8 7)
    (List.replicate 96 0x22) (Int.toBytes 8 0x20000) (Int.toBytes 8 0x30000)
    (by decide) rfl (by decide) rfl (by decide) (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs (List.replicate 8 0xff) (List.replicate 32 0xff) (List.replicate 8 0xff) (List.replicate 96 0xff)
    (List.replicate 8 0xff) (List.replicate 8 0xff) rfl rfl rfl rfl rfl rfl z' f

end Prysm.SyncCommitteeMessage.Witness.DecodeAccept
