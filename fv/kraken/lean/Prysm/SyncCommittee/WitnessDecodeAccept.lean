import Prysm.SyncCommittee.DecodeAccept
import Prysm.RuntimeModel.BumpAllocatorByteSliceDispatch
import Runtime.CopyModel
import Machine.WitnessHost

/-!
# Witness of `Decode.accept` (SyncCommittee decoder accept path)

The text of `Prysm/SyncAggregate/WitnessDecodeAccept.lean` with the SyncCommittee host and layout. It shows that the premises of the frozen statement
`Prysm.SyncCommittee.Decode.accept_statement` are satisfiable, the three contract hypotheses included: both `MakesliceContract` instances come from
the one type-dispatching model `Prysm.RuntimeModel.BumpMakesliceByteSliceDispatch` (`Prysm.RuntimeModel.bump_makeslice_byte_slice_dispatch_size1`, `Prysm.RuntimeModel.bump_makeslice_byte_slice_dispatch_size24`), `MemmoveContract` from `MemmoveGrowsliceModel`.
Host: data labels, the real Go 1.26.10 `(*v1alpha1.SyncCommittee).UnmarshalSSZ` (index 9), `Prysm.RuntimeModel.BumpMakesliceByteSliceDispatch` (146) and
`MemmoveGrowsliceModel` (162).
One memory block at `0x10000`: bump pointer, writeBarrier word, the 36912-byte heap, guard word, the 24624 input bytes
(`pks.flatten ++ agg`), the 88-byte receiver (protoc struct, `prysm/ir/ir-mainnet.json` gc amd64 layout, size 88:
`state` 0, Pubkeys header 8 with old pointer word `oP1` and len = cap = 0, AggregatePubkey header 32 (`oP2`),
`unknownFields` 56 and `sizeCache` 80 zero), the 16-byte callee block (`S = 16`), the callee return slot, the 24-byte
argument area, the three loop locals, the saved rbp, the caller's slots (rsp = 0x1f11c) and the caller's word at
rsp + 24. The frame `R` is the receiver's last 32 bytes and that word. For every input of 512 blocks of 48 bytes and
every old pointer word every premise holds and the decoder returns nil.
-/

open Machine Runtime Machine.Witness Prysm.SyncCommittee.Code

namespace Prysm.SyncCommittee.Witness.DecodeAccept

def dataLabels : Program :=
  [.label "runtime.modelBumpPointer", .label "pad1", .label "pad2", .label "pad3", .label "pad4", .label "pad5",
   .label "pad6", .label "pad7", .label "runtime.writeBarrier"]

def program : Program := dataLabels ++ unmarshalSSZ ++ Prysm.RuntimeModel.BumpMakesliceByteSliceDispatch ++ MemmoveGrowsliceModel

theorem program_length : program.length = 188 := by rfl

instance host : Host := mkHost program (by rw [program_length]; decide)

theorem host_program_eq : Host.prog = program := rfl

theorem placed_at_9 : unmarshalSSZ.IsInfixAt Host.prog 9 :=
  infixAt_of dataLabels (Prysm.RuntimeModel.BumpMakesliceByteSliceDispatch ++ MemmoveGrowsliceModel) (by simp [host_program_eq, program, List.append_assoc]) rfl
theorem placed_at_146 : Prysm.RuntimeModel.BumpMakesliceByteSliceDispatch.IsInfixAt Host.prog 146 :=
  infixAt_of (dataLabels ++ unmarshalSSZ) MemmoveGrowsliceModel
    (by simp [host_program_eq, program, List.append_assoc]) (by rfl)
theorem placed_at_162 : MemmoveGrowsliceModel.IsInfixAt Host.prog 162 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ Prysm.RuntimeModel.BumpMakesliceByteSliceDispatch) []
    (by simp [host_program_eq, program, List.append_assoc]) (by rfl)

theorem labels_fresh_at_9 : LabelsFresh unmarshalSSZ 9 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_146 : LabelsFresh Prysm.RuntimeModel.BumpMakesliceByteSliceDispatch 146 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_162 : LabelsFresh MemmoveGrowsliceModel 162 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem no_label_before_146 : ∀ i < 146, Host.prog[i]? ≠ some (.label "runtime.makeslice") :=
  notLabel_of (by rw [host_program_eq]; decide)

theorem label_bump_pointer : label "runtime.modelBumpPointer" = 0x10000 :=
  mk_label program _ 0 _ (by simp [program, dataLabels]) (by simp [labs])

theorem label_write_barrier : label "runtime.writeBarrier" = 0x10008 :=
  mk_label program _ 8 _ (by simp [program, dataLabels]) (by decide)

theorem u8_ne_slice : ElfData.PrysmTarget.typeUint8_addr ≠ ElfData.PrysmTarget.typeUint8Slice_addr := by
  simp only [ElfData.PrysmTarget.typeUint8_addr, ElfData.PrysmTarget.typeUint8Slice_addr, Int64.toBitVec_add, Int64.toBitVec_ofNat]
  bv_omega

abbrev zeros (k : Nat) : List UInt8 := List.replicate k 0
abbrev zero_word_bytes : List UInt8 := Int.toBytes 8 (0 : UInt64).toBitVec.toInt

/-- bump pointer (→ 0x1000c) · writeBarrier · heap (36912) · guard · input (24624: pks.flatten, agg) · receiver (88:
state 0, Pubkeys `oP1`/0/0, AggregatePubkey `oP2`/0/0, unknownFields and sizeCache 0 (32 bytes)) · callee block (16) ·
callee return slot · argument area (24) · three loop locals · saved rbp · return slot · spill rax · spill rbx ·
caller word. -/
def block (pkb agg oP1 oP2 : List UInt8) : List UInt8 :=
  Int.toBytes 8 (0x1000c : BitVec 64).toInt ++ ([0, 0, 0, 0] ++ (zeros 36912 ++ (zero_word_bytes ++ (pkb ++ (agg ++ (zeros 8 ++ (oP1 ++ (zeros 8 ++ (zeros 8 ++ (oP2 ++ (zeros 8 ++ (zeros 8 ++ (zeros 32 ++ (zeros 16 ++ (zeros 8 ++ (zeros 24 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zero_word_bytes ++ (zeros 8 ++ (zeros 8 ++ zeros 8)))))))))))))))))))))))

def mem (pkb agg oP1 oP2 : List UInt8) : DataMem :=
  (block pkb agg oP1 oP2).At (0x10000 : BitVec 64)

def initial_state (pkb agg oP1 oP2 : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x1f074, 0x19044, 24624, 0, 0, 24624, 0x1f11c, 0, 0, 0, 0, 0, 0, 0, 0x1902c, 0⟩, zmms, flags,
    mem pkb agg oP1 oP2⟩

/-- The frame of the witness: the receiver's `unknownFields` / `sizeCache` words (32 bytes at receiver + 56) and the
caller's word at rsp + 24 (neither is touched on the accept path). -/
def frame_rest : DataMem → Prop := Eq ((zeros 32).At (0x1f0ac : BitVec 64)) ⋆ Eq ((zeros 8).At (0x1f134 : BitVec 64))

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x1000c : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((zeros 36912).At (0x1000c : BitVec 64)) ⋆ X)) m) : (bumpHeap 36912 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x1000c, by decide, by rw [label_bump_pointer]; exact hm⟩) h

-- Same cause as `Prysm.SyncAggregate.Witness.DecodeAccept.runs` (profile): the memory premise is closed by `simp`
-- AC-normalization of the separating conjunction (here 25 chunks). Without this option the declaration stops at `whnf`
-- with the default 200000 heartbeats after a 2.3 s `simp` (scratch copy).
-- Thresholds measured in separate runs: 200000, 400000 and 1000000 fail at `whnf`, 2000000 passes.
-- Value 4000000 (twice the lowest passing value; was 16000000): passes.
set_option maxHeartbeats 4000000 in
/-- **Non-vacuity of `Decode.accept` (the premises of the frozen statement `Decode.accept_statement` are satisfiable).** -/
theorem runs (pks : List (List UInt8)) (agg oP1 oP2 : List UInt8) (hpks : pks.length = 512)
    (hpk : ∀ e ∈ pks, e.length = 48) (hagg : agg.length = 48) (h1 : oP1.length = 8) (h2 : oP2.length = 8)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨initial_state pks.flatten agg oP1 oP2 zmms flags, Host.addrOf 9⟩ := by
  have hfl : pks.flatten.length = 24576 := by rw [Codec.flatten_length_of_length_48 pks hpk, hpks]
  exact eventually_mono (Decode.accept 9 placed_at_9 labels_fresh_at_9 pks agg hpks hpk hagg (initial_state pks.flatten agg oP1 oP2 zmms flags)
    0 0 (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 24) (zeros 8) (zeros 16) (zeros 8) oP1 (zeros 8) (zeros 8) oP2 (zeros 8) (zeros 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl h1 rfl rfl h2 rfl rfl
    frame_rest 16 rfl bumpHeap 36912
    (by
      have H : Eq ((block pks.flatten agg oP1 oP2).At (0x10000 : BitVec 64)) (mem pks.flatten agg oP1 oP2) := rfl
      witness_split [hfl, hagg, h1, h2]
      rw [Std.ExtHashMap.sep_comm_l (Eq (([0, 0, 0, 0] : List UInt8).At _)) (Eq ((zeros 36912).At _))] at H
      have H2 := lift_heap H
      simp only [initial_state, frame_rest, zero_word_bytes, label_write_barrier, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd, BitVec.reduceSub] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [initial_state]) rfl (by omega)
    (Prysm.RuntimeModel.bump_makeslice_byte_slice_dispatch_size1 146 placed_at_146 no_label_before_146 _ u8_ne_slice) (Prysm.RuntimeModel.bump_makeslice_byte_slice_dispatch_size24 146 placed_at_146 no_label_before_146 labels_fresh_at_146)
    (model_memmove 162 placed_at_162 labels_fresh_at_162 _))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

/-- Zero input with a fresh `&SyncCommittee{}` (nil slices); a representative input; all-0xff input. -/
example (z' : RegZmms) (f : StatusFlags) :=
  runs (List.replicate 512 (zeros 48)) (zeros 48) (zeros 8) (zeros 8)
    List.length_replicate (fun e he => by rw [List.eq_of_mem_replicate he]; exact List.length_replicate) rfl rfl rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs ((List.range 512).map fun i => List.replicate 48 (UInt8.ofNat i)) ((List.range 48).map UInt8.ofNat)
    (Int.toBytes 8 0x20000) (Int.toBytes 8 0x30000) (by simp) (by simp) (by simp) (by decide) (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs (List.replicate 512 (List.replicate 48 0xff)) (List.replicate 48 0xff) (List.replicate 8 0xff)
    (List.replicate 8 0xff)
    List.length_replicate (fun e he => by rw [List.eq_of_mem_replicate he]; exact List.length_replicate) rfl rfl rfl z' f

end Prysm.SyncCommittee.Witness.DecodeAccept
