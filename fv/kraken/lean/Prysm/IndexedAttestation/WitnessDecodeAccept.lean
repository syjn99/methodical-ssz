import Prysm.IndexedAttestation.DecodeAccept
import Prysm.RuntimeModel.BumpAllocatorUint64AndStructDispatch
import Runtime.CopyModel
import Machine.WitnessHost

/-!
# Witness of `Decode.accept` (IndexedAttestation decoder accept path)

The text of `Prysm/SyncCommittee/WitnessDecodeAccept.lean` and `Prysm/AttestationData/WitnessDecodeAccept.lean` with the IndexedAttestation host and layout. It shows that the premises of the
frozen statement `Prysm.IndexedAttestation.Decode.accept_statement` are satisfiable for every `n ≤ 2048`, the nine contract hypotheses
included: the four `MakesliceContract` instances come from the type-dispatching model `Prysm.RuntimeModel.BumpMakesliceUint64Dispatch` (`Prysm.RuntimeModel.bump_makeslice_uint64_dispatch_size8`,
`Prysm.RuntimeModel.bump_makeslice_uint64_dispatch_size1`), the two `NewobjectContract` instances from `Prysm.RuntimeModel.BumpNewobjectStructDispatch` (`Prysm.RuntimeModel.bump_newobject_struct_dispatch_size96`,
`Prysm.RuntimeModel.bump_newobject_struct_dispatch_size72`), the three `MemmoveContract` instances from `MemmoveGrowsliceModel`.
Host: data labels, the real Go 1.26.10 `(*v1alpha1.IndexedAttestation).UnmarshalSSZ` (index 9),
`(*v1alpha1.AttestationData).UnmarshalSSZ` (288), `(*primitives.Slot).UnmarshalSSZ` (531),
`(*primitives.CommitteeIndex).UnmarshalSSZ` (594), `(*v1alpha1.Checkpoint).UnmarshalSSZ` (657),
`(*primitives.Epoch).UnmarshalSSZ` (765), `Prysm.RuntimeModel.BumpMakesliceUint64Dispatch` (828), `MemmoveGrowsliceModel` (843), `Prysm.RuntimeModel.BumpNewobjectStructDispatch` (869).
One memory block at `0x10000`: bump pointer, writeBarrier word, the 16816-byte heap (`8 · 2048 + 432`), guard word,
the 96-byte receiver (`state`, AttestingIndices header with old pointer word `oP1`, Data pointer `oD`, Signature header
with old pointer word `oP2`, then `unknownFields` + `sizeCache` + padding), the 232-byte callee block (`Sd = 8`), the
return slot, the frame (rsp = 0x143c4), the caller's slots and the caller's word at rsp + 24, and last the input
`offsetBytes ‖ data ‖ signature ‖ ib` (so that no address depends on `n`). cap = len. The frame `R` is the receiver tail
(32 bytes), the untouched frame bytes rsp − 96 … rsp − 17 (80) and the caller's word.
-/

open Machine Runtime Machine.Witness Prysm.IndexedAttestation.Code

namespace Prysm.IndexedAttestation.Witness.DecodeAccept


theorem offsetBytes_length : offsetBytes.length = 4 := rfl

def dataLabels : Program :=
  [.label "runtime.modelBumpPointer", .label "pad1", .label "pad2", .label "pad3", .label "pad4", .label "pad5",
   .label "pad6", .label "pad7", .label "runtime.writeBarrier"]

def program : Program := dataLabels ++ unmarshalSSZ ++ Prysm.AttestationData.Code.unmarshalSSZ ++ Prysm.Slot.Code.unmarshalSSZ
  ++ Prysm.CommitteeIndex.Code.unmarshalSSZ ++ Prysm.Checkpoint.Code.unmarshalSSZ ++ Prysm.Epoch.Code.unmarshalSSZ ++ Prysm.RuntimeModel.BumpMakesliceUint64Dispatch ++ MemmoveGrowsliceModel ++ Prysm.RuntimeModel.BumpNewobjectStructDispatch

-- Measured cause: `rfl` on the 884-directive host program stops with "maximum recursion depth" at
-- the default (512) in `program_length` and the prefix-length facts `placed_at_288` … `placed_at_869` only. `placed_at_288` passes at 1024; `program_length`
-- and `placed_at_531` … `placed_at_869` fail at 1024 and pass at 2048. The other host facts need no option.
set_option maxRecDepth 2048 in
theorem program_length : program.length = 884 := by rfl

instance host : Host := mkHost program (by rw [program_length]; decide)

theorem host_program_eq : Host.prog = program := rfl

theorem placed_at_9 : unmarshalSSZ.IsInfixAt Host.prog 9 :=
  infixAt_of dataLabels (Prysm.AttestationData.Code.unmarshalSSZ ++ Prysm.Slot.Code.unmarshalSSZ ++ Prysm.CommitteeIndex.Code.unmarshalSSZ
    ++ Prysm.Checkpoint.Code.unmarshalSSZ ++ Prysm.Epoch.Code.unmarshalSSZ ++ Prysm.RuntimeModel.BumpMakesliceUint64Dispatch ++ MemmoveGrowsliceModel ++ Prysm.RuntimeModel.BumpNewobjectStructDispatch)
    (by simp [host_program_eq, program, List.append_assoc]) rfl
set_option maxRecDepth 1024 in
theorem placed_at_288 : Prysm.AttestationData.Code.unmarshalSSZ.IsInfixAt Host.prog 288 :=
  infixAt_of (dataLabels ++ unmarshalSSZ) (Prysm.Slot.Code.unmarshalSSZ ++ Prysm.CommitteeIndex.Code.unmarshalSSZ ++ Prysm.Checkpoint.Code.unmarshalSSZ
    ++ Prysm.Epoch.Code.unmarshalSSZ ++ Prysm.RuntimeModel.BumpMakesliceUint64Dispatch ++ MemmoveGrowsliceModel ++ Prysm.RuntimeModel.BumpNewobjectStructDispatch) (by simp [host_program_eq, program, List.append_assoc]) (by rfl)
set_option maxRecDepth 2048 in
theorem placed_at_531 : Prysm.Slot.Code.unmarshalSSZ.IsInfixAt Host.prog 531 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ Prysm.AttestationData.Code.unmarshalSSZ) (Prysm.CommitteeIndex.Code.unmarshalSSZ ++ Prysm.Checkpoint.Code.unmarshalSSZ
    ++ Prysm.Epoch.Code.unmarshalSSZ ++ Prysm.RuntimeModel.BumpMakesliceUint64Dispatch ++ MemmoveGrowsliceModel ++ Prysm.RuntimeModel.BumpNewobjectStructDispatch) (by simp [host_program_eq, program, List.append_assoc]) (by rfl)
set_option maxRecDepth 2048 in
theorem placed_at_594 : Prysm.CommitteeIndex.Code.unmarshalSSZ.IsInfixAt Host.prog 594 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ Prysm.AttestationData.Code.unmarshalSSZ ++ Prysm.Slot.Code.unmarshalSSZ) (Prysm.Checkpoint.Code.unmarshalSSZ
    ++ Prysm.Epoch.Code.unmarshalSSZ ++ Prysm.RuntimeModel.BumpMakesliceUint64Dispatch ++ MemmoveGrowsliceModel ++ Prysm.RuntimeModel.BumpNewobjectStructDispatch) (by simp [host_program_eq, program, List.append_assoc]) (by rfl)
set_option maxRecDepth 2048 in
theorem placed_at_657 : Prysm.Checkpoint.Code.unmarshalSSZ.IsInfixAt Host.prog 657 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ Prysm.AttestationData.Code.unmarshalSSZ ++ Prysm.Slot.Code.unmarshalSSZ ++ Prysm.CommitteeIndex.Code.unmarshalSSZ)
    (Prysm.Epoch.Code.unmarshalSSZ ++ Prysm.RuntimeModel.BumpMakesliceUint64Dispatch ++ MemmoveGrowsliceModel ++ Prysm.RuntimeModel.BumpNewobjectStructDispatch) (by simp [host_program_eq, program, List.append_assoc]) (by rfl)
set_option maxRecDepth 2048 in
theorem placed_at_765 : Prysm.Epoch.Code.unmarshalSSZ.IsInfixAt Host.prog 765 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ Prysm.AttestationData.Code.unmarshalSSZ ++ Prysm.Slot.Code.unmarshalSSZ ++ Prysm.CommitteeIndex.Code.unmarshalSSZ
    ++ Prysm.Checkpoint.Code.unmarshalSSZ) (Prysm.RuntimeModel.BumpMakesliceUint64Dispatch ++ MemmoveGrowsliceModel ++ Prysm.RuntimeModel.BumpNewobjectStructDispatch) (by simp [host_program_eq, program, List.append_assoc]) (by rfl)
set_option maxRecDepth 2048 in
theorem placed_at_828 : Prysm.RuntimeModel.BumpMakesliceUint64Dispatch.IsInfixAt Host.prog 828 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ Prysm.AttestationData.Code.unmarshalSSZ ++ Prysm.Slot.Code.unmarshalSSZ ++ Prysm.CommitteeIndex.Code.unmarshalSSZ
    ++ Prysm.Checkpoint.Code.unmarshalSSZ ++ Prysm.Epoch.Code.unmarshalSSZ) (MemmoveGrowsliceModel ++ Prysm.RuntimeModel.BumpNewobjectStructDispatch) (by simp [host_program_eq, program, List.append_assoc])
    (by rfl)
set_option maxRecDepth 2048 in
theorem placed_at_843 : MemmoveGrowsliceModel.IsInfixAt Host.prog 843 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ Prysm.AttestationData.Code.unmarshalSSZ ++ Prysm.Slot.Code.unmarshalSSZ ++ Prysm.CommitteeIndex.Code.unmarshalSSZ
    ++ Prysm.Checkpoint.Code.unmarshalSSZ ++ Prysm.Epoch.Code.unmarshalSSZ ++ Prysm.RuntimeModel.BumpMakesliceUint64Dispatch) Prysm.RuntimeModel.BumpNewobjectStructDispatch (by simp [host_program_eq, program, List.append_assoc])
    (by rfl)
set_option maxRecDepth 2048 in
theorem placed_at_869 : Prysm.RuntimeModel.BumpNewobjectStructDispatch.IsInfixAt Host.prog 869 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ Prysm.AttestationData.Code.unmarshalSSZ ++ Prysm.Slot.Code.unmarshalSSZ ++ Prysm.CommitteeIndex.Code.unmarshalSSZ
    ++ Prysm.Checkpoint.Code.unmarshalSSZ ++ Prysm.Epoch.Code.unmarshalSSZ ++ Prysm.RuntimeModel.BumpMakesliceUint64Dispatch ++ MemmoveGrowsliceModel) [] (by simp [host_program_eq, program, List.append_assoc])
    (by rfl)

theorem labels_fresh_at_9 : LabelsFresh unmarshalSSZ 9 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_288 : LabelsFresh Prysm.AttestationData.Code.unmarshalSSZ 288 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_531 : LabelsFresh Prysm.Slot.Code.unmarshalSSZ 531 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_594 : LabelsFresh Prysm.CommitteeIndex.Code.unmarshalSSZ 594 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_657 : LabelsFresh Prysm.Checkpoint.Code.unmarshalSSZ 657 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_765 : LabelsFresh Prysm.Epoch.Code.unmarshalSSZ 765 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_828 : LabelsFresh Prysm.RuntimeModel.BumpMakesliceUint64Dispatch 828 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_843 : LabelsFresh MemmoveGrowsliceModel 843 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_869 : LabelsFresh Prysm.RuntimeModel.BumpNewobjectStructDispatch 869 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem no_label_before_828 : ∀ i < 828, Host.prog[i]? ≠ some (.label "runtime.makeslice") :=
  notLabel_of (by rw [host_program_eq]; decide)
theorem no_label_before_869 : ∀ i < 869, Host.prog[i]? ≠ some (.label "runtime.newobject") :=
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

/-- bump pointer (→ 0x1000c) · writeBarrier · heap (16816) · guard · receiver (96: state, `oP1`/0/0, `oD`,
`oP2`/0/0, tail 32) · callee block (232) · return slot · spill area (40) · locals 0x28 0x30 0x38 0x40 0x48 · frame gap
(80) · Signature save · saved rbp · return address · spill rax · spill rbx · caller word · spill rdi · input
(`offsetBytes`, data 128, signature 96, `ib`). -/
def block (in0 in1 root se sroot te troot sig oP1 oD oP2 : List UInt8) : List UInt8 :=
  Int.toBytes 8 (0x1000c : BitVec 64).toInt ++ ([0, 0, 0, 0] ++ (zeros 16816 ++ (zero_word_bytes ++ (zeros 8 ++ (oP1 ++ (zeros 8 ++ (zeros 8
    ++ (oD ++ (oP2 ++ (zeros 8 ++ (zeros 8 ++ (zeros 32 ++ (zeros 232 ++ (zeros 8 ++ (zeros 40 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8
    ++ (zeros 80 ++ (zeros 8 ++ (zeros 8 ++ (zero_word_bytes ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (offsetBytes ++ (in0 ++ (in1 ++ (root ++ (se
    ++ (sroot ++ (te ++ (troot ++ sig))))))))))))))))))))))))))))))))))))

def mem (in0 in1 root se sroot te troot sig ib oP1 oD oP2 : List UInt8) : DataMem :=
  (block in0 in1 root se sroot te troot sig oP1 oD oP2 ++ ib).At (0x10000 : BitVec 64)

def initial_state (n : Nat) (in0 in1 root se sroot te troot sig ib oP1 oD oP2 : List UInt8) (zmms : RegZmms)
    (flags : StatusFlags) : MachineData :=
  ⟨⟨0x141c4, 0x143ec, UInt64.ofNat (228 + 8 * n), 0, 0, UInt64.ofNat (228 + 8 * n), 0x143c4, 0, 0, 0, 0, 0, 0, 0,
    0x141ac, 0⟩, zmms, flags, mem in0 in1 root se sroot te troot sig ib oP1 oD oP2⟩

/-- The frame of the witness: the receiver tail (32 bytes at receiver + 64), the frame gap rsp − 96 … rsp − 17 (80)
and the caller's word at rsp + 24. -/
def frame_rest : DataMem → Prop :=
  Eq ((zeros 32).At (0x14204 : BitVec 64)) ⋆ Eq ((zeros 80).At (0x14364 : BitVec 64)) ⋆ Eq ((zeros 8).At (0x143dc : BitVec 64))

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x1000c : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((zeros 16816).At (0x1000c : BitVec 64)) ⋆ X)) m) : (bumpHeap 16816 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x1000c, by decide, by rw [label_bump_pointer]; exact hm⟩) h

-- Measured cause: the memory premise is closed by `simp` AC-normalization of the separating
-- conjunction (38 chunks, as in `Prysm.SyncCommittee.Witness.DecodeAccept.runs`). The `ecancel` alternative fails on this goal (56 internal
-- PANIC messages of the tactic). Thresholds: 3000000 and 4000000 fail at `whnf`, 5000000
-- passes, also 6000000, 8000000, 12000000, 16000000. Value: twice the passing value.
set_option maxHeartbeats 10000000 in
/-- **Non-vacuity of `Decode.accept` (the premises of the frozen statement `Decode.accept_statement` are satisfiable)**,
for every `n ≤ 2048`, every input and every old pointer word. -/
theorem runs (n : Nat) (hn : n ≤ 2048) (in0 in1 root se sroot te troot sig ib oP1 oD oP2 : List UInt8)
    (hin0 : in0.length = 8) (hin1 : in1.length = 8) (hroot : root.length = 32) (hse : se.length = 8)
    (hsroot : sroot.length = 32) (hte : te.length = 8) (htroot : troot.length = 32) (hsig : sig.length = 96)
    (hib : ib.length = 8 * n) (h1 : oP1.length = 8) (hD : oD.length = 8) (h2 : oP2.length = 8)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨initial_state n in0 in1 root se sroot te troot sig ib oP1 oD oP2 zmms flags, Host.addrOf 9⟩ :=
  eventually_mono (Decode.accept 9 placed_at_9 labels_fresh_at_9 288 placed_at_288 labels_fresh_at_288 531 placed_at_531 labels_fresh_at_531 594 placed_at_594 labels_fresh_at_594 657 placed_at_657 labels_fresh_at_657
    765 placed_at_765 labels_fresh_at_765 n hn in0 in1 root se sroot te troot sig ib hin0 hin1 hroot hse hsroot hte htroot hsig hib
    (initial_state n in0 in1 root se sroot te troot sig ib oP1 oD oP2 zmms flags) 0 0
    (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 40) (zeros 8) (zeros 232) (zeros 8) oP1 (zeros 8) (zeros 8) oD oP2
    (zeros 8) (zeros 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl h1 rfl rfl hD h2 rfl rfl
    frame_rest 8 (Nat.le_refl _) (by decide) rfl bumpHeap 16816
    (by
      have H : Eq ((block in0 in1 root se sroot te troot sig oP1 oD oP2 ++ ib).At (0x10000 : BitVec 64))
        (mem in0 in1 root se sroot te troot sig ib oP1 oD oP2) := rfl
      -- `ib` (symbolic length) is split off first: `witness_split` on a block with a non-literal last length makes the
      -- elaborator reduce `literal + L` by unfolding; the rest of the block has literal lengths only
      have hbl : (block in0 in1 root se sroot te troot sig oP1 oD oP2).length = 17616 := by
        simp only [block, List.length_append, List.length_replicate, Int.toBytes_length, List.length_cons,
          List.length_nil, offsetBytes_length, hin0, hin1, hroot, hse, hsroot, hte, htroot, hsig, h1, hD, h2]
      rw [Mem.At_append_sep _ _ _ (by rw [hbl, hib]; omega), hbl] at H
      unfold block at H
      repeat rw [Mem.At_append_sep _ _ _ (by
          simp only [List.length_append, List.length_replicate, Int.toBytes_length, List.length_cons,
            List.length_nil, offsetBytes_length, hin0, hin1, hroot, hse, hsroot, hte, htroot, hsig, h1, hD, h2]
          omega)] at H
      simp only [List.length_replicate, Int.toBytes_length, List.length_cons, List.length_nil, Nat.reduceAdd,
        offsetBytes_length, hin0, hin1, hroot, hse, hsroot, hte, htroot, h1, hD, h2, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd] at H
      simp only [Std.ExtHashMap.sep_assoc] at H
      rw [Std.ExtHashMap.sep_comm_l (Eq (([0, 0, 0, 0] : List UInt8).At _)) (Eq ((zeros 16816).At _))] at H
      have H2 := lift_heap H
      simp only [initial_state, frame_rest, zero_word_bytes, label_write_barrier, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, Nat.reduceAdd,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by show (0 : UInt64).toNat + 408 < (0x143c4 : UInt64).toNat; decide)
    (UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega))
    (Nat.le_refl _)
    (by show (UInt64.ofNat (228 + 8 * n)).toNat < 2 ^ 63
        rw [UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)]; omega)
    (by omega)
    (Prysm.RuntimeModel.bump_makeslice_uint64_dispatch_size8 828 placed_at_828 no_label_before_828 labels_fresh_at_828) (Prysm.RuntimeModel.bump_makeslice_uint64_dispatch_size1 828 placed_at_828 no_label_before_828 _ uint8_ne_uint64)
    (model_memmove 843 placed_at_843 labels_fresh_at_843 _) (Prysm.RuntimeModel.bump_newobject_struct_dispatch_size96 869 placed_at_869 no_label_before_869 labels_fresh_at_869)
    (Prysm.RuntimeModel.bump_makeslice_uint64_dispatch_size1 828 placed_at_828 no_label_before_828 _ uint8_ne_uint64) (model_memmove 843 placed_at_843 labels_fresh_at_843 _)
    (Prysm.RuntimeModel.bump_makeslice_uint64_dispatch_size1 828 placed_at_828 no_label_before_828 _ uint8_ne_uint64) (model_memmove 843 placed_at_843 labels_fresh_at_843 _)
    (Prysm.RuntimeModel.bump_newobject_struct_dispatch_size72 869 placed_at_869 no_label_before_869 _ checkpoint_type_ne_attestation_data_type))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

/-- n = 0 (empty AttestingIndices), zero input, a fresh `&IndexedAttestation{}` (nil words). -/
example (z' : RegZmms) (f : StatusFlags) :=
  runs 0 (Nat.zero_le _) (zeros 8) (zeros 8) (zeros 32) (zeros 8) (zeros 32) (zeros 8) (zeros 32) (zeros 96) [] (zeros 8) (zeros 8) (zeros 8)
    List.length_replicate List.length_replicate List.length_replicate List.length_replicate List.length_replicate
    List.length_replicate List.length_replicate List.length_replicate rfl List.length_replicate
    List.length_replicate List.length_replicate z' f
/-- n = 1, a representative input and non-nil old words. -/
example (z' : RegZmms) (f : StatusFlags) :=
  runs 1 (by omega) (Int.toBytes 8 0x0123456789abcdef) (Int.toBytes 8 7) (List.replicate 32 0x11)
    (Int.toBytes 8 3) (List.replicate 32 0x22) (Int.toBytes 8 4) (List.replicate 32 0x33) (List.replicate 96 0x44)
    (Int.toBytes 8 9) (Int.toBytes 8 0x20000) (Int.toBytes 8 0x30000) (Int.toBytes 8 0x40000)
    (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) List.length_replicate (Int.toBytes_length 8 _)
    List.length_replicate (Int.toBytes_length 8 _) List.length_replicate List.length_replicate
    (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) z' f
/-- n = 2048 (the maximum), all-0xff input. -/
example (z' : RegZmms) (f : StatusFlags) :=
  runs 2048 (Nat.le_refl _) (List.replicate 8 0xff) (List.replicate 8 0xff) (List.replicate 32 0xff)
    (List.replicate 8 0xff) (List.replicate 32 0xff) (List.replicate 8 0xff) (List.replicate 32 0xff)
    (List.replicate 96 0xff) (List.replicate (8 * 2048) 0xff) (List.replicate 8 0xff) (List.replicate 8 0xff)
    (List.replicate 8 0xff)
    List.length_replicate List.length_replicate List.length_replicate List.length_replicate List.length_replicate
    List.length_replicate List.length_replicate List.length_replicate List.length_replicate List.length_replicate
    List.length_replicate List.length_replicate z' f

end Prysm.IndexedAttestation.Witness.DecodeAccept
