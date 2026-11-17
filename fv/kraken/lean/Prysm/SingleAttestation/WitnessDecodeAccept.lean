import Prysm.SingleAttestation.DecodeAccept
import Prysm.RuntimeModel.BumpAllocatorUint64AndStructDispatch
import Runtime.CopyModel
import Machine.WitnessHost
import Prysm.SingleAttestation.Code
import Prysm.AttestationData.Code
import Prysm.Checkpoint.Code
import Prysm.CommitteeIndex.Code
import Prysm.ValidatorIndex.Code
import Prysm.Epoch.Code
import Prysm.Slot.Code

/-!
# Witness of `Decode.accept` (SingleAttestation decoder accept path)

It shows that the premises of the statement `Prysm.SingleAttestation.Decode.accept_statement` are satisfiable, the eight
contract hypotheses included: the three `MakesliceContract` instances come from the type-dispatching model
`Prysm.RuntimeModel.BumpMakesliceUint64Dispatch` (`Prysm.RuntimeModel.bump_makeslice_uint64_dispatch_size1`), the two
`NewobjectContract` instances from `Prysm.RuntimeModel.BumpNewobjectStructDispatch`
(`Prysm.RuntimeModel.bump_newobject_struct_dispatch_size96`, `Prysm.RuntimeModel.bump_newobject_struct_dispatch_size72`),
the three `MemmoveContract` instances from `MemmoveGrowsliceModel`.
Host: data labels, the Go 1.26.10 `(*v1alpha1.SingleAttestation).UnmarshalSSZ` (index 9),
`(*v1alpha1.AttestationData).UnmarshalSSZ` (207), `(*primitives.Slot).UnmarshalSSZ` (450),
`(*primitives.CommitteeIndex).UnmarshalSSZ` (513), `(*primitives.ValidatorIndex).UnmarshalSSZ` (576),
`(*v1alpha1.Checkpoint).UnmarshalSSZ` (639), `(*primitives.Epoch).UnmarshalSSZ` (747),
`Prysm.RuntimeModel.BumpMakesliceUint64Dispatch` (810), `MemmoveGrowsliceModel` (825), `Prysm.RuntimeModel.BumpNewobjectStructDispatch` (851).
One memory block at `0x10000`: bump pointer, writeBarrier word, the 432-byte heap, guard word, the 88-byte receiver
(`state`, CommitteeId `oCI`, AttesterIndex `oAI`, Data pointer `oD`, Signature header with old pointer word `oP`, then
`unknownFields` + `sizeCache` + padding), the 232-byte callee block (`Sd = 8`), the return slot, the spill area, the
frame (rsp = 0x10384), the caller's slots and the caller's word at rsp + 24, and last the 240-byte input.
The frame `R` is the receiver tail (32 bytes), the untouched frame bytes rsp − 56 … rsp − 9 (48) and the caller's word.
-/

open Machine Runtime Machine.Witness Prysm.SingleAttestation.Code

namespace Prysm.SingleAttestation.Witness.DecodeAccept

def dataLabels : Program :=
  [.label "runtime.modelBumpPointer", .label "pad1", .label "pad2", .label "pad3", .label "pad4", .label "pad5",
   .label "pad6", .label "pad7", .label "runtime.writeBarrier"]

def program : Program := dataLabels ++ unmarshalSSZ ++ Prysm.AttestationData.Code.unmarshalSSZ ++ Prysm.Slot.Code.unmarshalSSZ ++ Prysm.CommitteeIndex.Code.unmarshalSSZ ++ Prysm.ValidatorIndex.Code.unmarshalSSZ ++ Prysm.Checkpoint.Code.unmarshalSSZ ++ Prysm.Epoch.Code.unmarshalSSZ ++ Prysm.RuntimeModel.BumpMakesliceUint64Dispatch ++ MemmoveGrowsliceModel ++ Prysm.RuntimeModel.BumpNewobjectStructDispatch

-- Measured cause: `rfl` on the 866-directive host program stops with "maximum recursion depth" at the default (512) in
-- `program_length` and the prefix-length facts `placed_at_207` … `placed_at_851` only. `placed_at_207` passes at 1024;
-- `program_length` and `placed_at_450` … `placed_at_851` fail at 1024 and pass at 2048. The other host facts need no option.
set_option maxRecDepth 2048 in
theorem program_length : program.length = 866 := by rfl

instance host : Host := mkHost program (by rw [program_length]; decide)

theorem host_program_eq : Host.prog = program := rfl

theorem placed_at_9 : unmarshalSSZ.IsInfixAt Host.prog 9 :=
  infixAt_of dataLabels (Prysm.AttestationData.Code.unmarshalSSZ ++ Prysm.Slot.Code.unmarshalSSZ ++ Prysm.CommitteeIndex.Code.unmarshalSSZ ++ Prysm.ValidatorIndex.Code.unmarshalSSZ ++ Prysm.Checkpoint.Code.unmarshalSSZ ++ Prysm.Epoch.Code.unmarshalSSZ ++ Prysm.RuntimeModel.BumpMakesliceUint64Dispatch ++ MemmoveGrowsliceModel ++ Prysm.RuntimeModel.BumpNewobjectStructDispatch)
    (by simp [host_program_eq, program, List.append_assoc]) (by rfl)
set_option maxRecDepth 1024 in
theorem placed_at_207 : Prysm.AttestationData.Code.unmarshalSSZ.IsInfixAt Host.prog 207 :=
  infixAt_of (dataLabels ++ unmarshalSSZ) (Prysm.Slot.Code.unmarshalSSZ ++ Prysm.CommitteeIndex.Code.unmarshalSSZ ++ Prysm.ValidatorIndex.Code.unmarshalSSZ ++ Prysm.Checkpoint.Code.unmarshalSSZ ++ Prysm.Epoch.Code.unmarshalSSZ ++ Prysm.RuntimeModel.BumpMakesliceUint64Dispatch ++ MemmoveGrowsliceModel ++ Prysm.RuntimeModel.BumpNewobjectStructDispatch)
    (by simp [host_program_eq, program, List.append_assoc]) (by rfl)
set_option maxRecDepth 2048 in
theorem placed_at_450 : Prysm.Slot.Code.unmarshalSSZ.IsInfixAt Host.prog 450 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ Prysm.AttestationData.Code.unmarshalSSZ) (Prysm.CommitteeIndex.Code.unmarshalSSZ ++ Prysm.ValidatorIndex.Code.unmarshalSSZ ++ Prysm.Checkpoint.Code.unmarshalSSZ ++ Prysm.Epoch.Code.unmarshalSSZ ++ Prysm.RuntimeModel.BumpMakesliceUint64Dispatch ++ MemmoveGrowsliceModel ++ Prysm.RuntimeModel.BumpNewobjectStructDispatch)
    (by simp [host_program_eq, program, List.append_assoc]) (by rfl)
set_option maxRecDepth 2048 in
theorem placed_at_513 : Prysm.CommitteeIndex.Code.unmarshalSSZ.IsInfixAt Host.prog 513 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ Prysm.AttestationData.Code.unmarshalSSZ ++ Prysm.Slot.Code.unmarshalSSZ) (Prysm.ValidatorIndex.Code.unmarshalSSZ ++ Prysm.Checkpoint.Code.unmarshalSSZ ++ Prysm.Epoch.Code.unmarshalSSZ ++ Prysm.RuntimeModel.BumpMakesliceUint64Dispatch ++ MemmoveGrowsliceModel ++ Prysm.RuntimeModel.BumpNewobjectStructDispatch)
    (by simp [host_program_eq, program, List.append_assoc]) (by rfl)
set_option maxRecDepth 2048 in
theorem placed_at_576 : Prysm.ValidatorIndex.Code.unmarshalSSZ.IsInfixAt Host.prog 576 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ Prysm.AttestationData.Code.unmarshalSSZ ++ Prysm.Slot.Code.unmarshalSSZ ++ Prysm.CommitteeIndex.Code.unmarshalSSZ) (Prysm.Checkpoint.Code.unmarshalSSZ ++ Prysm.Epoch.Code.unmarshalSSZ ++ Prysm.RuntimeModel.BumpMakesliceUint64Dispatch ++ MemmoveGrowsliceModel ++ Prysm.RuntimeModel.BumpNewobjectStructDispatch)
    (by simp [host_program_eq, program, List.append_assoc]) (by rfl)
set_option maxRecDepth 2048 in
theorem placed_at_639 : Prysm.Checkpoint.Code.unmarshalSSZ.IsInfixAt Host.prog 639 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ Prysm.AttestationData.Code.unmarshalSSZ ++ Prysm.Slot.Code.unmarshalSSZ ++ Prysm.CommitteeIndex.Code.unmarshalSSZ ++ Prysm.ValidatorIndex.Code.unmarshalSSZ) (Prysm.Epoch.Code.unmarshalSSZ ++ Prysm.RuntimeModel.BumpMakesliceUint64Dispatch ++ MemmoveGrowsliceModel ++ Prysm.RuntimeModel.BumpNewobjectStructDispatch)
    (by simp [host_program_eq, program, List.append_assoc]) (by rfl)
set_option maxRecDepth 2048 in
theorem placed_at_747 : Prysm.Epoch.Code.unmarshalSSZ.IsInfixAt Host.prog 747 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ Prysm.AttestationData.Code.unmarshalSSZ ++ Prysm.Slot.Code.unmarshalSSZ ++ Prysm.CommitteeIndex.Code.unmarshalSSZ ++ Prysm.ValidatorIndex.Code.unmarshalSSZ ++ Prysm.Checkpoint.Code.unmarshalSSZ) (Prysm.RuntimeModel.BumpMakesliceUint64Dispatch ++ MemmoveGrowsliceModel ++ Prysm.RuntimeModel.BumpNewobjectStructDispatch)
    (by simp [host_program_eq, program, List.append_assoc]) (by rfl)
set_option maxRecDepth 2048 in
theorem placed_at_810 : Prysm.RuntimeModel.BumpMakesliceUint64Dispatch.IsInfixAt Host.prog 810 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ Prysm.AttestationData.Code.unmarshalSSZ ++ Prysm.Slot.Code.unmarshalSSZ ++ Prysm.CommitteeIndex.Code.unmarshalSSZ ++ Prysm.ValidatorIndex.Code.unmarshalSSZ ++ Prysm.Checkpoint.Code.unmarshalSSZ ++ Prysm.Epoch.Code.unmarshalSSZ) (MemmoveGrowsliceModel ++ Prysm.RuntimeModel.BumpNewobjectStructDispatch)
    (by simp [host_program_eq, program, List.append_assoc]) (by rfl)
set_option maxRecDepth 2048 in
theorem placed_at_825 : MemmoveGrowsliceModel.IsInfixAt Host.prog 825 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ Prysm.AttestationData.Code.unmarshalSSZ ++ Prysm.Slot.Code.unmarshalSSZ ++ Prysm.CommitteeIndex.Code.unmarshalSSZ ++ Prysm.ValidatorIndex.Code.unmarshalSSZ ++ Prysm.Checkpoint.Code.unmarshalSSZ ++ Prysm.Epoch.Code.unmarshalSSZ ++ Prysm.RuntimeModel.BumpMakesliceUint64Dispatch) Prysm.RuntimeModel.BumpNewobjectStructDispatch
    (by simp [host_program_eq, program, List.append_assoc]) (by rfl)
set_option maxRecDepth 2048 in
theorem placed_at_851 : Prysm.RuntimeModel.BumpNewobjectStructDispatch.IsInfixAt Host.prog 851 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ Prysm.AttestationData.Code.unmarshalSSZ ++ Prysm.Slot.Code.unmarshalSSZ ++ Prysm.CommitteeIndex.Code.unmarshalSSZ ++ Prysm.ValidatorIndex.Code.unmarshalSSZ ++ Prysm.Checkpoint.Code.unmarshalSSZ ++ Prysm.Epoch.Code.unmarshalSSZ ++ Prysm.RuntimeModel.BumpMakesliceUint64Dispatch ++ MemmoveGrowsliceModel) []
    (by simp [host_program_eq, program, List.append_assoc]) (by rfl)

theorem labels_fresh_at_9 : LabelsFresh unmarshalSSZ 9 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_207 : LabelsFresh Prysm.AttestationData.Code.unmarshalSSZ 207 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_450 : LabelsFresh Prysm.Slot.Code.unmarshalSSZ 450 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_513 : LabelsFresh Prysm.CommitteeIndex.Code.unmarshalSSZ 513 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_576 : LabelsFresh Prysm.ValidatorIndex.Code.unmarshalSSZ 576 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_639 : LabelsFresh Prysm.Checkpoint.Code.unmarshalSSZ 639 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_747 : LabelsFresh Prysm.Epoch.Code.unmarshalSSZ 747 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_810 : LabelsFresh Prysm.RuntimeModel.BumpMakesliceUint64Dispatch 810 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_825 : LabelsFresh MemmoveGrowsliceModel 825 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_851 : LabelsFresh Prysm.RuntimeModel.BumpNewobjectStructDispatch 851 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem no_label_before_810 : ∀ i < 810, Host.prog[i]? ≠ some (.label "runtime.makeslice") :=
  notLabel_of (by rw [host_program_eq]; decide)
theorem no_label_before_851 : ∀ i < 851, Host.prog[i]? ≠ some (.label "runtime.newobject") :=
  notLabel_of (by rw [host_program_eq]; decide)

theorem label_bump_pointer : label "runtime.modelBumpPointer" = 0x10000 :=
  mk_label program _ 0 _ (by simp [program, dataLabels]) (by simp [programLabels])

theorem label_write_barrier : label "runtime.writeBarrier" = 0x10008 :=
  mk_label program _ 8 _ (by simp [program, dataLabels]) (by decide)

theorem uint8_ne_uint64 : ElfData.PrysmTarget.typeUint8_addr ≠ ElfData.PrysmTarget.typeUint64_addr := by
  simp only [ElfData.PrysmTarget.typeUint8_addr, ElfData.PrysmTarget.typeUint64_addr, Int64.toBitVec_add, Int64.toBitVec_ofNat]
  bv_omega

theorem checkpoint_type_ne_attestation_data_type : ElfData.PrysmTarget.typeCheckpoint_addr ≠ ElfData.PrysmTarget.typeAttestationData_addr := by
  simp only [ElfData.PrysmTarget.typeCheckpoint_addr, ElfData.PrysmTarget.typeAttestationData_addr, Int64.toBitVec_add, Int64.toBitVec_ofNat]
  bv_omega

abbrev zeros (k : Nat) : List UInt8 := List.replicate k 0
abbrev zero_word_bytes : List UInt8 := Int.toBytes 8 (0 : UInt64).toBitVec.toInt

/-- bump pointer (→ 0x1000c) · writeBarrier · heap (432) · guard · receiver (88: state, `oCI`, `oAI`, `oD`, `oP`/0/0,
tail 32) · callee block (232) · return slot · spill area (40) · locals rsp − 80, rsp − 72, rsp − 64 · frame gap (48) ·
saved rbp · return address · spill rax · spill rbx · caller word · spill rdi · input (ci, ai, data 128, signature 96). -/
def block (ci ai ds di root se sroot te troot sig oCI oAI oD oP : List UInt8) : List UInt8 :=
  Int.toBytes 8 (0x1000c : BitVec 64).toInt ++ ([0, 0, 0, 0] ++ (zeros 432 ++ (zero_word_bytes ++ (zeros 8 ++ (oCI ++ (oAI ++ (oD ++ (oP ++ (zeros 8 ++ (zeros 8 ++ (zeros 32 ++ (zeros 232 ++ (zeros 8 ++ (zeros 40 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 48 ++ (zeros 8 ++ (zero_word_bytes ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (ci ++ (ai ++ (ds ++ (di ++ (root ++ (se ++ (sroot ++ (te ++ (troot ++ sig)))))))))))))))))))))))))))))))))

def mem (ci ai ds di root se sroot te troot sig oCI oAI oD oP : List UInt8) : DataMem :=
  (block ci ai ds di root se sroot te troot sig oCI oAI oD oP).At (0x10000 : BitVec 64)

def initial_state (ci ai ds di root se sroot te troot sig oCI oAI oD oP : List UInt8) (zmms : RegZmms)
    (flags : StatusFlags) : MachineData :=
  ⟨⟨0x101c4, 0x103ac, 240, 0, 0, 240, 0x10384, 0, 0, 0, 0, 0, 0, 0, 0x101ac, 0⟩, zmms, flags,
    mem ci ai ds di root se sroot te troot sig oCI oAI oD oP⟩

/-- The frame of the witness: the receiver tail (32 bytes at receiver + 56), the frame gap rsp − 56 … rsp − 9 (48)
and the caller's word at rsp + 24. -/
def frame_rest : DataMem → Prop :=
  Eq ((zeros 32).At (0x101fc : BitVec 64)) ⋆ Eq ((zeros 48).At (0x1034c : BitVec 64)) ⋆ Eq ((zeros 8).At (0x1039c : BitVec 64))

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x1000c : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((zeros 432).At (0x1000c : BitVec 64)) ⋆ X)) m) : (bumpHeap 432 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x1000c, by decide, by rw [label_bump_pointer]; exact hm⟩) h

-- Measured cause: the memory premise is closed by `simp` AC-normalization of the separating conjunction (35 chunks, as in
-- `Prysm.IndexedAttestation.Witness.DecodeAccept.runs`). Thresholds: 2000000 and 2750000 fail at `whnf`, 3500000 and 5000000
-- pass. Value: twice the passing value 3500000.
set_option maxHeartbeats 7000000 in
/-- **Non-vacuity of `Decode.accept` (the premises of the statement `Decode.accept_statement` are satisfiable)**,
for every input and every old receiver word. -/
theorem runs (ci ai ds di root se sroot te troot sig oCI oAI oD oP : List UInt8)
    (hci : ci.length = 8) (hai : ai.length = 8) (hds : ds.length = 8) (hdi : di.length = 8) (hroot : root.length = 32)
    (hse : se.length = 8) (hsroot : sroot.length = 32) (hte : te.length = 8) (htroot : troot.length = 32)
    (hsig : sig.length = 96) (h1 : oCI.length = 8) (h2 : oAI.length = 8) (hD : oD.length = 8) (hP : oP.length = 8)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨initial_state ci ai ds di root se sroot te troot sig oCI oAI oD oP zmms flags, Host.addrOf 9⟩ :=
  eventually_mono (Decode.accept 9 placed_at_9 labels_fresh_at_9 207 placed_at_207 labels_fresh_at_207
    450 placed_at_450 labels_fresh_at_450 513 placed_at_513 labels_fresh_at_513 576 placed_at_576 labels_fresh_at_576
    639 placed_at_639 labels_fresh_at_639 747 placed_at_747 labels_fresh_at_747
    ci ai ds di root se sroot te troot sig hci hai hds hdi hroot hse hsroot hte htroot hsig
    (initial_state ci ai ds di root se sroot te troot sig oCI oAI oD oP zmms flags) 0 0
    (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 40) (zeros 8) (zeros 232) (zeros 8)
    oCI oAI oD oP (zeros 8) (zeros 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl h1 h2 hD hP rfl rfl
    frame_rest 8 (Nat.le_refl _) (by decide) rfl bumpHeap 432
    (by
      have H : Eq ((block ci ai ds di root se sroot te troot sig oCI oAI oD oP).At (0x10000 : BitVec 64))
        (mem ci ai ds di root se sroot te troot sig oCI oAI oD oP) := rfl
      unfold block at H
      repeat rw [Mem.At_append_sep _ _ _ (by
          simp only [List.length_append, List.length_replicate, Int.toBytes_length, List.length_cons,
            List.length_nil, hci, hai, hds, hdi, hroot, hse, hsroot, hte, htroot, hsig, h1, h2, hD, hP]
          omega)] at H
      simp only [List.length_replicate, Int.toBytes_length, List.length_cons, List.length_nil, Nat.reduceAdd,
        hci, hai, hds, hdi, hroot, hse, hsroot, hte, htroot, h1, h2, hD, hP, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at H
      rw [Std.ExtHashMap.sep_comm_l (Eq (([0, 0, 0, 0] : List UInt8).At _)) (Eq ((zeros 432).At _))] at H
      have H2 := lift_heap H
      simp only [initial_state, frame_rest, zero_word_bytes, label_write_barrier, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, Nat.reduceAdd,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by show (0 : UInt64).toNat + 352 < (0x10384 : UInt64).toNat; decide)
    rfl (Nat.le_refl _)
    (Prysm.RuntimeModel.bump_newobject_struct_dispatch_size96 851 placed_at_851 no_label_before_851 labels_fresh_at_851)
    (Prysm.RuntimeModel.bump_makeslice_uint64_dispatch_size1 810 placed_at_810 no_label_before_810 _ uint8_ne_uint64)
    (model_memmove 825 placed_at_825 labels_fresh_at_825 _)
    (Prysm.RuntimeModel.bump_makeslice_uint64_dispatch_size1 810 placed_at_810 no_label_before_810 _ uint8_ne_uint64)
    (model_memmove 825 placed_at_825 labels_fresh_at_825 _)
    (Prysm.RuntimeModel.bump_makeslice_uint64_dispatch_size1 810 placed_at_810 no_label_before_810 _ uint8_ne_uint64)
    (model_memmove 825 placed_at_825 labels_fresh_at_825 _)
    (Prysm.RuntimeModel.bump_newobject_struct_dispatch_size72 851 placed_at_851 no_label_before_851 _ checkpoint_type_ne_attestation_data_type))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

/-- Zero input and a fresh `&SingleAttestation{}` (nil words). -/
example (z' : RegZmms) (f : StatusFlags) :=
  runs (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 32) (zeros 8) (zeros 32) (zeros 8) (zeros 32) (zeros 96)
    (zeros 8) (zeros 8) (zeros 8) (zeros 8)
    List.length_replicate List.length_replicate List.length_replicate List.length_replicate List.length_replicate
    List.length_replicate List.length_replicate List.length_replicate List.length_replicate List.length_replicate
    List.length_replicate List.length_replicate List.length_replicate List.length_replicate z' f
/-- A representative input and non-nil old words. -/
example (z' : RegZmms) (f : StatusFlags) :=
  runs (Int.toBytes 8 0x0123456789abcdef) (Int.toBytes 8 7) (Int.toBytes 8 3) (Int.toBytes 8 4) (List.replicate 32 0x11)
    (Int.toBytes 8 5) (List.replicate 32 0x22) (Int.toBytes 8 6) (List.replicate 32 0x33) (List.replicate 96 0x44)
    (Int.toBytes 8 9) (Int.toBytes 8 10) (Int.toBytes 8 0x20000) (Int.toBytes 8 0x30000)
    (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) List.length_replicate
    (Int.toBytes_length 8 _) List.length_replicate (Int.toBytes_length 8 _) List.length_replicate List.length_replicate
    (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) z' f
/-- All-0xff input and all-0xff old words. -/
example (z' : RegZmms) (f : StatusFlags) :=
  runs (List.replicate 8 0xff) (List.replicate 8 0xff) (List.replicate 8 0xff) (List.replicate 8 0xff)
    (List.replicate 32 0xff) (List.replicate 8 0xff) (List.replicate 32 0xff) (List.replicate 8 0xff)
    (List.replicate 32 0xff) (List.replicate 96 0xff) (List.replicate 8 0xff) (List.replicate 8 0xff)
    (List.replicate 8 0xff) (List.replicate 8 0xff)
    List.length_replicate List.length_replicate List.length_replicate List.length_replicate List.length_replicate
    List.length_replicate List.length_replicate List.length_replicate List.length_replicate List.length_replicate
    List.length_replicate List.length_replicate List.length_replicate List.length_replicate z' f

end Prysm.SingleAttestation.Witness.DecodeAccept
