import Prysm.SyncCommittee.DecodeAccept
import Prysm.RuntimeModel.BumpAllocatorByteSliceDispatch
import Runtime.CopyModel
import Machine.WitnessHost

/-!
# Witness of `Decode.accept` (SyncCommittee decoder accept path)

The text of `Prysm/SyncAggregate/WitnessDecodeAccept.lean` with the SyncCommittee host and layout. It shows that the premises of the frozen statement
`Prysm.SyncCommittee.Decode.accept_statement` are satisfiable, the three contract hypotheses included: both `MakesliceC` instances come from
the one type-dispatching model `Prysm.RuntimeModel.BumpAllocByteSliceDispatch` (`Prysm.RuntimeModel.bump_makeslice_byte_slice_dispatch_size1`, `Prysm.RuntimeModel.bump_makeslice_byte_slice_dispatch_size24`), `MemmoveC` from `RtCopy`.
Host: data labels, the real Go 1.26.10 `(*v1alpha1.SyncCommittee).UnmarshalSSZ` (index 9), `Prysm.RuntimeModel.BumpAllocByteSliceDispatch` (146) and
`RtCopy` (162).
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
  [.label "runtime.fvBump", .label "pad1", .label "pad2", .label "pad3", .label "pad4", .label "pad5",
   .label "pad6", .label "pad7", .label "runtime.writeBarrier"]

def P : Program := dataLabels ++ unmarshalSSZ ++ Prysm.RuntimeModel.BumpAllocByteSliceDispatch ++ RtCopy

theorem P_len : P.length = 188 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem prog_eq : Host.prog = P := rfl

theorem hk9 : unmarshalSSZ.IsInfixAt Host.prog 9 :=
  infixAt_of dataLabels (Prysm.RuntimeModel.BumpAllocByteSliceDispatch ++ RtCopy) (by simp [prog_eq, P, List.append_assoc]) rfl
theorem hk146 : Prysm.RuntimeModel.BumpAllocByteSliceDispatch.IsInfixAt Host.prog 146 :=
  infixAt_of (dataLabels ++ unmarshalSSZ) RtCopy
    (by simp [prog_eq, P, List.append_assoc]) (by rfl)
theorem hk162 : RtCopy.IsInfixAt Host.prog 162 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ Prysm.RuntimeModel.BumpAllocByteSliceDispatch) []
    (by simp [prog_eq, P, List.append_assoc]) (by rfl)

theorem hf9 : LabelsFresh unmarshalSSZ 9 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf146 : LabelsFresh Prysm.RuntimeModel.BumpAllocByteSliceDispatch 146 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf162 : LabelsFresh RtCopy 162 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hn146 : ∀ i < 146, Host.prog[i]? ≠ some (.label "runtime.makeslice") :=
  notLabel_of (by rw [prog_eq]; decide)

theorem label_bump : label "runtime.fvBump" = 0x10000 :=
  mk_label P _ 0 _ (by simp [P, dataLabels]) (by simp [labs])

theorem label_wb : label "runtime.writeBarrier" = 0x10008 :=
  mk_label P _ 8 _ (by simp [P, dataLabels]) (by decide)

theorem u8_ne_slice : ElfData.CheckpointAndEpoch.e2eU8Type_addr ≠ ElfData.SyncAggregateAndSyncCommittee.lvSliceType_addr := by
  simp only [ElfData.CheckpointAndEpoch.e2eU8Type_addr, ElfData.SyncAggregateAndSyncCommittee.lvSliceType_addr, Int64.toBitVec_add, Int64.toBitVec_ofNat]
  bv_omega

abbrev z (k : Nat) : List UInt8 := List.replicate k 0
abbrev w0 : List UInt8 := Int.toBytes 8 (0 : UInt64).toBitVec.toInt

/-- bump pointer (→ 0x1000c) · writeBarrier · heap (36912) · guard · input (24624: pks.flatten, agg) · receiver (88:
state 0, Pubkeys `oP1`/0/0, AggregatePubkey `oP2`/0/0, unknownFields and sizeCache 0 (32 bytes)) · callee block (16) ·
callee return slot · argument area (24) · three loop locals · saved rbp · return slot · spill rax · spill rbx ·
caller word. -/
def block (pkb agg oP1 oP2 : List UInt8) : List UInt8 :=
  Int.toBytes 8 (0x1000c : BitVec 64).toInt ++ ([0, 0, 0, 0] ++ (z 36912 ++ (w0 ++ (pkb ++ (agg ++ (z 8 ++ (oP1 ++ (z 8 ++ (z 8 ++ (oP2 ++ (z 8 ++ (z 8 ++ (z 32 ++ (z 16 ++ (z 8 ++ (z 24 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 8 ++ (w0 ++ (z 8 ++ (z 8 ++ z 8)))))))))))))))))))))))

def mem (pkb agg oP1 oP2 : List UInt8) : DataMem :=
  (block pkb agg oP1 oP2).At (0x10000 : BitVec 64)

def cs0 (pkb agg oP1 oP2 : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x1f074, 0x19044, 24624, 0, 0, 24624, 0x1f11c, 0, 0, 0, 0, 0, 0, 0, 0x1902c, 0⟩, zmms, flags,
    mem pkb agg oP1 oP2⟩

/-- The frame of the witness: the receiver's `unknownFields` / `sizeCache` words (32 bytes at receiver + 56) and the
caller's word at rsp + 24 (neither is touched on the accept path). -/
def R0 : DataMem → Prop := Eq ((z 32).At (0x1f0ac : BitVec 64)) ⋆ Eq ((z 8).At (0x1f134 : BitVec 64))

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x1000c : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((z 36912).At (0x1000c : BitVec 64)) ⋆ X)) m) : (bumpHeap 36912 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x1000c, by decide, by rw [label_bump]; exact hm⟩) h

-- Same cause as `Prysm.SyncAggregate.Witness.DecodeAccept.runs` (profile): the memory premise is closed by `simp`
-- AC-normalization of the separating conjunction (here 25 chunks). Without this option the declaration stops at `whnf`
-- with the default 200000 heartbeats after a 2.3 s `simp` (scratch copy).
-- Thresholds measured in independent reviewer runs: 200000, 400000 and 1000000 fail at `whnf`, 2000000 passes.
-- Value 4000000 (twice the reviewer's passing value; was 16000000): passes in the implementer's run.
set_option maxHeartbeats 4000000 in
/-- **Non-vacuity of `Decode.accept` (the premises of the frozen statement `Decode.accept_statement` are satisfiable).** -/
theorem runs (pks : List (List UInt8)) (agg oP1 oP2 : List UInt8) (hpks : pks.length = 512)
    (hpk : ∀ e ∈ pks, e.length = 48) (hagg : agg.length = 48) (h1 : oP1.length = 8) (h2 : oP2.length = 8)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨cs0 pks.flatten agg oP1 oP2 zmms flags, Host.addrOf 9⟩ := by
  have hfl : pks.flatten.length = 24576 := by rw [flatten_length pks hpk, hpks]
  exact eventually_mono (Decode.accept 9 hk9 hf9 pks agg hpks hpk hagg (cs0 pks.flatten agg oP1 oP2 zmms flags)
    0 0 (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 24) (z 8) (z 16) (z 8) oP1 (z 8) (z 8) oP2 (z 8) (z 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl h1 rfl rfl h2 rfl rfl
    R0 16 rfl bumpHeap 36912
    (by
      have H : Eq ((block pks.flatten agg oP1 oP2).At (0x10000 : BitVec 64)) (mem pks.flatten agg oP1 oP2) := rfl
      wit_split [hfl, hagg, h1, h2]
      rw [Std.ExtHashMap.sep_comm_l (Eq (([0, 0, 0, 0] : List UInt8).At _)) (Eq ((z 36912).At _))] at H
      have H2 := lift_heap H
      simp only [cs0, R0, w0, label_wb, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd, BitVec.reduceSub] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [cs0]) rfl (by omega)
    (Prysm.RuntimeModel.bump_makeslice_byte_slice_dispatch_size1 146 hk146 hn146 _ u8_ne_slice) (Prysm.RuntimeModel.bump_makeslice_byte_slice_dispatch_size24 146 hk146 hn146 hf146)
    (rt_memmove 162 hk162 hf162 _))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

/-- Zero input with a fresh `&SyncCommittee{}` (nil slices); a representative input; all-0xff input. -/
example (z' : RegZmms) (f : StatusFlags) :=
  runs (List.replicate 512 (z 48)) (z 48) (z 8) (z 8)
    List.length_replicate (fun e he => by rw [List.eq_of_mem_replicate he]; exact List.length_replicate) rfl rfl rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs ((List.range 512).map fun i => List.replicate 48 (UInt8.ofNat i)) ((List.range 48).map UInt8.ofNat)
    (Int.toBytes 8 0x20000) (Int.toBytes 8 0x30000) (by simp) (by simp) (by simp) (by decide) (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs (List.replicate 512 (List.replicate 48 0xff)) (List.replicate 48 0xff) (List.replicate 8 0xff)
    (List.replicate 8 0xff)
    List.length_replicate (fun e he => by rw [List.eq_of_mem_replicate he]; exact List.length_replicate) rfl rfl rfl z' f

end Prysm.SyncCommittee.Witness.DecodeAccept
