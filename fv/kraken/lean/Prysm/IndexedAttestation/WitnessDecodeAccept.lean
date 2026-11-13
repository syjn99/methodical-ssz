import Prysm.IndexedAttestation.DecodeAccept
import Prysm.RuntimeModel.BumpAllocatorUint64AndStructDispatch
import Runtime.CopyModel
import Machine.WitnessHost

/-!
# Witness of `Decode.accept` (IndexedAttestation decoder accept path)

The text of `Prysm/SyncCommittee/WitnessDecodeAccept.lean` and `Prysm/AttestationData/WitnessDecodeAccept.lean` with the IndexedAttestation host and layout. It shows that the premises of the
frozen statement `Prysm.IndexedAttestation.Decode.accept_statement` are satisfiable for every `n ≤ 2048`, the nine contract hypotheses
included: the four `MakesliceC` instances come from the type-dispatching model `Prysm.RuntimeModel.BumpAllocUint64Dispatch` (`Prysm.RuntimeModel.bump_makeslice_uint64_dispatch_size8`,
`Prysm.RuntimeModel.bump_makeslice_uint64_dispatch_size1`), the two `NewobjectC` instances from `Prysm.RuntimeModel.BumpNewStructDispatch` (`Prysm.RuntimeModel.bump_newobject_struct_dispatch_size96`,
`Prysm.RuntimeModel.bump_newobject_struct_dispatch_size72`), the three `MemmoveC` instances from `RtCopy`.
Host: data labels, the real Go 1.26.10 `(*v1alpha1.IndexedAttestation).UnmarshalSSZ` (index 9),
`(*v1alpha1.AttestationData).UnmarshalSSZ` (288), `(*primitives.Slot).UnmarshalSSZ` (531),
`(*primitives.CommitteeIndex).UnmarshalSSZ` (594), `(*v1alpha1.Checkpoint).UnmarshalSSZ` (657),
`(*primitives.Epoch).UnmarshalSSZ` (765), `Prysm.RuntimeModel.BumpAllocUint64Dispatch` (828), `RtCopy` (843), `Prysm.RuntimeModel.BumpNewStructDispatch` (869).
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
  [.label "runtime.fvBump", .label "pad1", .label "pad2", .label "pad3", .label "pad4", .label "pad5",
   .label "pad6", .label "pad7", .label "runtime.writeBarrier"]

def P : Program := dataLabels ++ unmarshalSSZ ++ Prysm.AttestationData.Code.unmarshalSSZ ++ Prysm.AttestationData.Code.slotUnmarshalSSZ
  ++ Prysm.AttestationData.Code.committeeIndexUnmarshalSSZ ++ Prysm.Checkpoint.Code.unmarshalSSZ ++ Prysm.Epoch.Code.unmarshalSSZ ++ Prysm.RuntimeModel.BumpAllocUint64Dispatch ++ RtCopy ++ Prysm.RuntimeModel.BumpNewStructDispatch

-- Measured cause: `rfl` on the 884-directive host program stops with "maximum recursion depth" at
-- the default (512) in `P_len` and the prefix-length facts `hk288` … `hk869` only. `hk288` passes at 1024; `P_len`
-- and `hk531` … `hk869` fail at 1024 and pass at 2048. The other host facts need no option.
set_option maxRecDepth 2048 in
theorem P_len : P.length = 884 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem prog_eq : Host.prog = P := rfl

theorem hk9 : unmarshalSSZ.IsInfixAt Host.prog 9 :=
  infixAt_of dataLabels (Prysm.AttestationData.Code.unmarshalSSZ ++ Prysm.AttestationData.Code.slotUnmarshalSSZ ++ Prysm.AttestationData.Code.committeeIndexUnmarshalSSZ
    ++ Prysm.Checkpoint.Code.unmarshalSSZ ++ Prysm.Epoch.Code.unmarshalSSZ ++ Prysm.RuntimeModel.BumpAllocUint64Dispatch ++ RtCopy ++ Prysm.RuntimeModel.BumpNewStructDispatch)
    (by simp [prog_eq, P, List.append_assoc]) rfl
set_option maxRecDepth 1024 in
theorem hk288 : Prysm.AttestationData.Code.unmarshalSSZ.IsInfixAt Host.prog 288 :=
  infixAt_of (dataLabels ++ unmarshalSSZ) (Prysm.AttestationData.Code.slotUnmarshalSSZ ++ Prysm.AttestationData.Code.committeeIndexUnmarshalSSZ ++ Prysm.Checkpoint.Code.unmarshalSSZ
    ++ Prysm.Epoch.Code.unmarshalSSZ ++ Prysm.RuntimeModel.BumpAllocUint64Dispatch ++ RtCopy ++ Prysm.RuntimeModel.BumpNewStructDispatch) (by simp [prog_eq, P, List.append_assoc]) (by rfl)
set_option maxRecDepth 2048 in
theorem hk531 : Prysm.AttestationData.Code.slotUnmarshalSSZ.IsInfixAt Host.prog 531 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ Prysm.AttestationData.Code.unmarshalSSZ) (Prysm.AttestationData.Code.committeeIndexUnmarshalSSZ ++ Prysm.Checkpoint.Code.unmarshalSSZ
    ++ Prysm.Epoch.Code.unmarshalSSZ ++ Prysm.RuntimeModel.BumpAllocUint64Dispatch ++ RtCopy ++ Prysm.RuntimeModel.BumpNewStructDispatch) (by simp [prog_eq, P, List.append_assoc]) (by rfl)
set_option maxRecDepth 2048 in
theorem hk594 : Prysm.AttestationData.Code.committeeIndexUnmarshalSSZ.IsInfixAt Host.prog 594 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ Prysm.AttestationData.Code.unmarshalSSZ ++ Prysm.AttestationData.Code.slotUnmarshalSSZ) (Prysm.Checkpoint.Code.unmarshalSSZ
    ++ Prysm.Epoch.Code.unmarshalSSZ ++ Prysm.RuntimeModel.BumpAllocUint64Dispatch ++ RtCopy ++ Prysm.RuntimeModel.BumpNewStructDispatch) (by simp [prog_eq, P, List.append_assoc]) (by rfl)
set_option maxRecDepth 2048 in
theorem hk657 : Prysm.Checkpoint.Code.unmarshalSSZ.IsInfixAt Host.prog 657 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ Prysm.AttestationData.Code.unmarshalSSZ ++ Prysm.AttestationData.Code.slotUnmarshalSSZ ++ Prysm.AttestationData.Code.committeeIndexUnmarshalSSZ)
    (Prysm.Epoch.Code.unmarshalSSZ ++ Prysm.RuntimeModel.BumpAllocUint64Dispatch ++ RtCopy ++ Prysm.RuntimeModel.BumpNewStructDispatch) (by simp [prog_eq, P, List.append_assoc]) (by rfl)
set_option maxRecDepth 2048 in
theorem hk765 : Prysm.Epoch.Code.unmarshalSSZ.IsInfixAt Host.prog 765 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ Prysm.AttestationData.Code.unmarshalSSZ ++ Prysm.AttestationData.Code.slotUnmarshalSSZ ++ Prysm.AttestationData.Code.committeeIndexUnmarshalSSZ
    ++ Prysm.Checkpoint.Code.unmarshalSSZ) (Prysm.RuntimeModel.BumpAllocUint64Dispatch ++ RtCopy ++ Prysm.RuntimeModel.BumpNewStructDispatch) (by simp [prog_eq, P, List.append_assoc]) (by rfl)
set_option maxRecDepth 2048 in
theorem hk828 : Prysm.RuntimeModel.BumpAllocUint64Dispatch.IsInfixAt Host.prog 828 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ Prysm.AttestationData.Code.unmarshalSSZ ++ Prysm.AttestationData.Code.slotUnmarshalSSZ ++ Prysm.AttestationData.Code.committeeIndexUnmarshalSSZ
    ++ Prysm.Checkpoint.Code.unmarshalSSZ ++ Prysm.Epoch.Code.unmarshalSSZ) (RtCopy ++ Prysm.RuntimeModel.BumpNewStructDispatch) (by simp [prog_eq, P, List.append_assoc])
    (by rfl)
set_option maxRecDepth 2048 in
theorem hk843 : RtCopy.IsInfixAt Host.prog 843 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ Prysm.AttestationData.Code.unmarshalSSZ ++ Prysm.AttestationData.Code.slotUnmarshalSSZ ++ Prysm.AttestationData.Code.committeeIndexUnmarshalSSZ
    ++ Prysm.Checkpoint.Code.unmarshalSSZ ++ Prysm.Epoch.Code.unmarshalSSZ ++ Prysm.RuntimeModel.BumpAllocUint64Dispatch) Prysm.RuntimeModel.BumpNewStructDispatch (by simp [prog_eq, P, List.append_assoc])
    (by rfl)
set_option maxRecDepth 2048 in
theorem hk869 : Prysm.RuntimeModel.BumpNewStructDispatch.IsInfixAt Host.prog 869 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ Prysm.AttestationData.Code.unmarshalSSZ ++ Prysm.AttestationData.Code.slotUnmarshalSSZ ++ Prysm.AttestationData.Code.committeeIndexUnmarshalSSZ
    ++ Prysm.Checkpoint.Code.unmarshalSSZ ++ Prysm.Epoch.Code.unmarshalSSZ ++ Prysm.RuntimeModel.BumpAllocUint64Dispatch ++ RtCopy) [] (by simp [prog_eq, P, List.append_assoc])
    (by rfl)

theorem hf9 : LabelsFresh unmarshalSSZ 9 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf288 : LabelsFresh Prysm.AttestationData.Code.unmarshalSSZ 288 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf531 : LabelsFresh Prysm.AttestationData.Code.slotUnmarshalSSZ 531 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf594 : LabelsFresh Prysm.AttestationData.Code.committeeIndexUnmarshalSSZ 594 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf657 : LabelsFresh Prysm.Checkpoint.Code.unmarshalSSZ 657 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf765 : LabelsFresh Prysm.Epoch.Code.unmarshalSSZ 765 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf828 : LabelsFresh Prysm.RuntimeModel.BumpAllocUint64Dispatch 828 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf843 : LabelsFresh RtCopy 843 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf869 : LabelsFresh Prysm.RuntimeModel.BumpNewStructDispatch 869 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hn828 : ∀ i < 828, Host.prog[i]? ≠ some (.label "runtime.makeslice") :=
  notLabel_of (by rw [prog_eq]; decide)
theorem hn869 : ∀ i < 869, Host.prog[i]? ≠ some (.label "runtime.newobject") :=
  notLabel_of (by rw [prog_eq]; decide)

theorem label_bump : label "runtime.fvBump" = 0x10000 :=
  mk_label P _ 0 _ (by simp [P, dataLabels]) (by simp [labs])

theorem label_wb : label "runtime.writeBarrier" = 0x10008 :=
  mk_label P _ 8 _ (by simp [P, dataLabels]) (by decide)

theorem u8_ne_u64 : ElfData.CheckpointAndEpoch.e2eU8Type_addr ≠ ElfData.IndexedAttestation.lvU64Type_addr := by
  simp only [ElfData.CheckpointAndEpoch.e2eU8Type_addr, ElfData.IndexedAttestation.lvU64Type_addr, Int64.toBitVec_add, Int64.toBitVec_ofNat]
  bv_omega

theorem checkpoint_type_ne_attestation_data_type : ElfData.AttestationData.adCpType_addr ≠ ElfData.IndexedAttestation.lvAdType_addr := by
  simp only [ElfData.AttestationData.adCpType_addr, ElfData.IndexedAttestation.lvAdType_addr, Int64.toBitVec_add, Int64.toBitVec_ofNat]
  bv_omega

abbrev z (k : Nat) : List UInt8 := List.replicate k 0
abbrev w0 : List UInt8 := Int.toBytes 8 (0 : UInt64).toBitVec.toInt

/-- bump pointer (→ 0x1000c) · writeBarrier · heap (16816) · guard · receiver (96: state, `oP1`/0/0, `oD`,
`oP2`/0/0, tail 32) · callee block (232) · return slot · spill area (40) · locals 0x28 0x30 0x38 0x40 0x48 · frame gap
(80) · Signature save · saved rbp · return address · spill rax · spill rbx · caller word · spill rdi · input
(`offsetBytes`, data 128, signature 96, `ib`). -/
def block (in0 in1 root se sroot te troot sig oP1 oD oP2 : List UInt8) : List UInt8 :=
  Int.toBytes 8 (0x1000c : BitVec 64).toInt ++ ([0, 0, 0, 0] ++ (z 16816 ++ (w0 ++ (z 8 ++ (oP1 ++ (z 8 ++ (z 8
    ++ (oD ++ (oP2 ++ (z 8 ++ (z 8 ++ (z 32 ++ (z 232 ++ (z 8 ++ (z 40 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 8
    ++ (z 80 ++ (z 8 ++ (z 8 ++ (w0 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 8 ++ (offsetBytes ++ (in0 ++ (in1 ++ (root ++ (se
    ++ (sroot ++ (te ++ (troot ++ sig))))))))))))))))))))))))))))))))))))

def mem (in0 in1 root se sroot te troot sig ib oP1 oD oP2 : List UInt8) : DataMem :=
  (block in0 in1 root se sroot te troot sig oP1 oD oP2 ++ ib).At (0x10000 : BitVec 64)

def cs0 (n : Nat) (in0 in1 root se sroot te troot sig ib oP1 oD oP2 : List UInt8) (zmms : RegZmms)
    (flags : StatusFlags) : MachineData :=
  ⟨⟨0x141c4, 0x143ec, UInt64.ofNat (228 + 8 * n), 0, 0, UInt64.ofNat (228 + 8 * n), 0x143c4, 0, 0, 0, 0, 0, 0, 0,
    0x141ac, 0⟩, zmms, flags, mem in0 in1 root se sroot te troot sig ib oP1 oD oP2⟩

/-- The frame of the witness: the receiver tail (32 bytes at receiver + 64), the frame gap rsp − 96 … rsp − 17 (80)
and the caller's word at rsp + 24. -/
def R0 : DataMem → Prop :=
  Eq ((z 32).At (0x14204 : BitVec 64)) ⋆ Eq ((z 80).At (0x14364 : BitVec 64)) ⋆ Eq ((z 8).At (0x143dc : BitVec 64))

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x1000c : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((z 16816).At (0x1000c : BitVec 64)) ⋆ X)) m) : (bumpHeap 16816 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x1000c, by decide, by rw [label_bump]; exact hm⟩) h

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
      ⟨cs0 n in0 in1 root se sroot te troot sig ib oP1 oD oP2 zmms flags, Host.addrOf 9⟩ :=
  eventually_mono (Decode.accept 9 hk9 hf9 288 hk288 hf288 531 hk531 hf531 594 hk594 hf594 657 hk657 hf657
    765 hk765 hf765 n hn in0 in1 root se sroot te troot sig ib hin0 hin1 hroot hse hsroot hte htroot hsig hib
    (cs0 n in0 in1 root se sroot te troot sig ib oP1 oD oP2 zmms flags) 0 0
    (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 40) (z 8) (z 232) (z 8) oP1 (z 8) (z 8) oD oP2
    (z 8) (z 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl h1 rfl rfl hD h2 rfl rfl
    R0 8 (Nat.le_refl _) (by decide) rfl bumpHeap 16816
    (by
      have H : Eq ((block in0 in1 root se sroot te troot sig oP1 oD oP2 ++ ib).At (0x10000 : BitVec 64))
        (mem in0 in1 root se sroot te troot sig ib oP1 oD oP2) := rfl
      -- `ib` (symbolic length) is split off first: `wit_split` on a block with a non-literal last length makes the
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
      rw [Std.ExtHashMap.sep_comm_l (Eq (([0, 0, 0, 0] : List UInt8).At _)) (Eq ((z 16816).At _))] at H
      have H2 := lift_heap H
      simp only [cs0, R0, w0, label_wb, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, Nat.reduceAdd,
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
    (Prysm.RuntimeModel.bump_makeslice_uint64_dispatch_size8 828 hk828 hn828 hf828) (Prysm.RuntimeModel.bump_makeslice_uint64_dispatch_size1 828 hk828 hn828 _ u8_ne_u64)
    (rt_memmove 843 hk843 hf843 _) (Prysm.RuntimeModel.bump_newobject_struct_dispatch_size96 869 hk869 hn869 hf869)
    (Prysm.RuntimeModel.bump_makeslice_uint64_dispatch_size1 828 hk828 hn828 _ u8_ne_u64) (rt_memmove 843 hk843 hf843 _)
    (Prysm.RuntimeModel.bump_makeslice_uint64_dispatch_size1 828 hk828 hn828 _ u8_ne_u64) (rt_memmove 843 hk843 hf843 _)
    (Prysm.RuntimeModel.bump_newobject_struct_dispatch_size72 869 hk869 hn869 _ checkpoint_type_ne_attestation_data_type))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

/-- n = 0 (empty AttestingIndices), zero input, a fresh `&IndexedAttestation{}` (nil words). -/
example (z' : RegZmms) (f : StatusFlags) :=
  runs 0 (Nat.zero_le _) (z 8) (z 8) (z 32) (z 8) (z 32) (z 8) (z 32) (z 96) [] (z 8) (z 8) (z 8)
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
