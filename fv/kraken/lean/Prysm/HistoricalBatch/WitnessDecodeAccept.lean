import Prysm.HistoricalBatch.DecodeAccept
import Prysm.RuntimeModel.BumpAllocatorByteSliceDispatch
import Runtime.CopyModel
import Machine.WitnessHost

/-!
# Witness of `Decode.accept` (HistoricalBatch decoder accept path)

The text of `Prysm.SyncCommittee.WitnessDecodeAccept` with the HistoricalBatch host and layout. It shows that the premises of the frozen
statement `Prysm.HistoricalBatch.Decode.accept_statement` are satisfiable, the three contract hypotheses included. The contract models are the
SyncCommittee ones, imported as they are: `Prysm.RuntimeModel.BumpAllocByteSliceDispatch` (`Prysm.RuntimeModel.bump_makeslice_byte_slice_dispatch_size1`, `Prysm.RuntimeModel.bump_makeslice_byte_slice_dispatch_size24`; the type word of the
HistoricalBatch backing arrays is the SyncCommittee one) and `RtCopy` (`rt_memmove`).
Host: data labels, the real Go 1.26.10 `(*v1alpha1.HistoricalBatch).UnmarshalSSZ` (index 9), `Prysm.RuntimeModel.BumpAllocByteSliceDispatch` (191) and
`RtCopy` (207).
One memory block at `0x10000`: bump pointer, writeBarrier word, the 917504-byte heap, guard word, the 524288 input
bytes (`brs.flatten ++ srs.flatten`), the 48-byte receiver (native struct, `prysm/ir/ir-mainnet.json` gc amd64
layout: BlockRoots header 0 with old pointer word `oP1` and len = cap = 0, StateRoots header 24 (`oP2`)), the
16-byte callee block (`S = 16`), the callee return slot, the 24-byte argument area, the four loop locals, the saved
rbp, the caller's slots (rsp = 0x17009c) and the caller's word at rsp + 24 (the frame `R`).
For every input of 2 × 8192 blocks of 32 bytes and every old pointer word every premise holds and the decoder
returns nil.
-/

open Machine Runtime Machine.Witness Prysm.HistoricalBatch.Code

namespace Prysm.HistoricalBatch.Witness.DecodeAccept

def dataLabels : Program :=
  [.label "runtime.fvBump", .label "pad1", .label "pad2", .label "pad3", .label "pad4", .label "pad5",
   .label "pad6", .label "pad7", .label "runtime.writeBarrier"]

def P : Program := dataLabels ++ unmarshalSSZ ++ Prysm.RuntimeModel.BumpAllocByteSliceDispatch ++ RtCopy

theorem P_len : P.length = 233 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem prog_eq : Host.prog = P := rfl

theorem hk9 : unmarshalSSZ.IsInfixAt Host.prog 9 :=
  infixAt_of dataLabels (Prysm.RuntimeModel.BumpAllocByteSliceDispatch ++ RtCopy) (by simp [prog_eq, P, List.append_assoc]) rfl
theorem hk191 : Prysm.RuntimeModel.BumpAllocByteSliceDispatch.IsInfixAt Host.prog 191 :=
  infixAt_of (dataLabels ++ unmarshalSSZ) RtCopy
    (by simp [prog_eq, P, List.append_assoc]) (by rfl)
theorem hk207 : RtCopy.IsInfixAt Host.prog 207 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ Prysm.RuntimeModel.BumpAllocByteSliceDispatch) []
    (by simp [prog_eq, P, List.append_assoc]) (by rfl)

theorem hf9 : LabelsFresh unmarshalSSZ 9 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf191 : LabelsFresh Prysm.RuntimeModel.BumpAllocByteSliceDispatch 191 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf207 : LabelsFresh RtCopy 207 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hn191 : ∀ i < 191, Host.prog[i]? ≠ some (.label "runtime.makeslice") :=
  notLabel_of (by rw [prog_eq]; decide)

theorem label_bump : label "runtime.fvBump" = 0x10000 :=
  mk_label P _ 0 _ (by simp [P, dataLabels]) (by simp [labs])

theorem label_wb : label "runtime.writeBarrier" = 0x10008 :=
  mk_label P _ 8 _ (by simp [P, dataLabels]) (by decide)

/-- The text of `Prysm.SyncCommittee.Witness.DecodeAccept.u8_ne_slice` (that module cannot be imported: it declares its own `Host` instance). -/
theorem u8_ne_slice : ElfData.CheckpointAndEpoch.e2eU8Type_addr ≠ ElfData.SyncAggregateAndSyncCommittee.lvSliceType_addr := by
  simp only [ElfData.CheckpointAndEpoch.e2eU8Type_addr, ElfData.SyncAggregateAndSyncCommittee.lvSliceType_addr, Int64.toBitVec_add, Int64.toBitVec_ofNat]
  bv_omega

abbrev z (k : Nat) : List UInt8 := List.replicate k 0
abbrev w0 : List UInt8 := Int.toBytes 8 (0 : UInt64).toBitVec.toInt

/-- bump pointer (→ 0x1000c) · writeBarrier · heap (917504) · guard · input (524288: brs.flatten, srs.flatten) ·
receiver (48: BlockRoots `oP1`/0/0, StateRoots `oP2`/0/0) · callee block (16) · callee return slot · argument area
(24) · four loop locals · saved rbp · return slot · spill rax · spill rbx · caller word. -/
def block (brb srb oP1 oP2 : List UInt8) : List UInt8 :=
  Int.toBytes 8 (0x1000c : BitVec 64).toInt ++ ([0, 0, 0, 0] ++ (z 917504 ++ (w0 ++ (brb ++ (srb ++ (oP1 ++ (z 8 ++
    (z 8 ++ (oP2 ++ (z 8 ++ (z 8 ++ (z 16 ++ (z 8 ++ (z 24 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 8 ++ (w0 ++ (z 8 ++
    (z 8 ++ z 8))))))))))))))))))))))

def mem (brb srb oP1 oP2 : List UInt8) : DataMem :=
  (block brb srb oP1 oP2).At (0x10000 : BitVec 64)

def cs0 (brb srb oP1 oP2 : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x170014, 0xf0014, 524288, 0, 0, 524288, 0x17009c, 0, 0, 0, 0, 0, 0, 0, 0xefffc, 0⟩, zmms, flags,
    mem brb srb oP1 oP2⟩

/-- The frame of the witness: the caller's word at rsp + 24 (not touched on the accept path). The native receiver
has no field outside the two slice headers. -/
def R0 : DataMem → Prop := Eq ((z 8).At (0x1700b4 : BitVec 64))

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x1000c : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((z 917504).At (0x1000c : BitVec 64)) ⋆ X)) m) : (bumpHeap 917504 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x1000c, by decide, by rw [label_bump]; exact hm⟩) h

-- Threshold measured on this module (one run each): 200000 (default) and 400000 fail at `whnf`;
-- 1000000 and 2000000 pass. Value 2000000 = twice the lowest passing value (the margin of `Prysm/SyncCommittee/WitnessDecodeAccept.lean`).
-- Cause (profiler): `simp` 11.8 s of the declaration (two calls, 9.5 s and 2.23 s): the memory premise is
-- closed by `simp` AC-normalization of the separating conjunction (24 chunks), as in `Prysm.SyncCommittee.Witness.DecodeAccept.runs`.
set_option maxHeartbeats 2000000 in
/-- **Non-vacuity of `Decode.accept` (the premises of the frozen statement `Decode.accept_statement` are satisfiable).** -/
theorem runs (brs srs : List (List UInt8)) (oP1 oP2 : List UInt8) (hbrs : brs.length = 8192)
    (hbr : ∀ e ∈ brs, e.length = 32) (hsrs : srs.length = 8192) (hsr : ∀ e ∈ srs, e.length = 32)
    (h1 : oP1.length = 8) (h2 : oP2.length = 8) (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨cs0 brs.flatten srs.flatten oP1 oP2 zmms flags, Host.addrOf 9⟩ := by
  have hfl1 : brs.flatten.length = 262144 := by rw [flatten_length brs hbr, hbrs]
  have hfl2 : srs.flatten.length = 262144 := by rw [flatten_length srs hsr, hsrs]
  exact eventually_mono (Decode.accept 9 hk9 hf9 brs srs hbrs hbr hsrs hsr
    (cs0 brs.flatten srs.flatten oP1 oP2 zmms flags)
    0 0 (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 24) (z 8) (z 16) oP1 (z 8) (z 8) oP2 (z 8) (z 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl h1 rfl rfl h2 rfl rfl
    R0 16 rfl bumpHeap 917504
    (by
      have H : Eq ((block brs.flatten srs.flatten oP1 oP2).At (0x10000 : BitVec 64))
        (mem brs.flatten srs.flatten oP1 oP2) := rfl
      wit_split [hfl1, hfl2, h1, h2]
      rw [Std.ExtHashMap.sep_comm_l (Eq (([0, 0, 0, 0] : List UInt8).At _)) (Eq ((z 917504).At _))] at H
      have H2 := lift_heap H
      simp only [cs0, R0, w0, label_wb, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd, BitVec.reduceSub] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [cs0]) rfl (by omega)
    (Prysm.RuntimeModel.bump_makeslice_byte_slice_dispatch_size1 191 hk191 hn191 _ u8_ne_slice) (Prysm.RuntimeModel.bump_makeslice_byte_slice_dispatch_size24 191 hk191 hn191 hf191)
    (rt_memmove 207 hk207 hf207 _))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

/-- Zero input with a fresh `&HistoricalBatch{}` (nil slices); a representative input; all-0xff input. -/
example (z' : RegZmms) (f : StatusFlags) :=
  runs (List.replicate 8192 (z 32)) (List.replicate 8192 (z 32)) (z 8) (z 8)
    List.length_replicate (fun e he => by rw [List.eq_of_mem_replicate he]; exact List.length_replicate)
    List.length_replicate (fun e he => by rw [List.eq_of_mem_replicate he]; exact List.length_replicate) rfl rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs ((List.range 8192).map fun i => List.replicate 32 (UInt8.ofNat i))
    ((List.range 8192).map fun i => List.replicate 32 (UInt8.ofNat (i + 1)))
    (Int.toBytes 8 0x20000) (Int.toBytes 8 0x30000) (by simp) (by simp) (by simp) (by simp) (by decide) (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs (List.replicate 8192 (List.replicate 32 0xff)) (List.replicate 8192 (List.replicate 32 0xff))
    (List.replicate 8 0xff) (List.replicate 8 0xff)
    List.length_replicate (fun e he => by rw [List.eq_of_mem_replicate he]; exact List.length_replicate)
    List.length_replicate (fun e he => by rw [List.eq_of_mem_replicate he]; exact List.length_replicate) rfl rfl z' f

end Prysm.HistoricalBatch.Witness.DecodeAccept
