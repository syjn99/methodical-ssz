import Prysm.Deposit.DecodeAccept
import Prysm.RuntimeModel.BumpAllocatorByteSliceDispatch
import Prysm.Deposit.WitnessBumpAllocator
import Runtime.CopyModel
import Machine.WitnessHost

/-!
# Witness of `Decode.accept` (Deposit decoder accept path)

The text of `Prysm.HistoricalBatch.WitnessDecodeAccept` with the Deposit host and layout. It shows that the premises of the frozen statement
`Prysm.Deposit.Decode.accept_statement` are satisfiable, the six contract hypotheses included: both `MakesliceContract` instances of the
Deposit decoder and the one of the Deposit_Data decoder from `Prysm.RuntimeModel.BumpMakesliceByteSliceDispatch`, `NewobjectContract … 120` from
`BumpNewobject120`, both `MemmoveContract` from `MemmoveGrowsliceModel`.
Host: data labels, the real Go 1.26.10 `(*v1alpha1.Deposit).UnmarshalSSZ` (index 9) and
`(*v1alpha1.Deposit_Data).UnmarshalSSZ` (165), `Prysm.RuntimeModel.BumpMakesliceByteSliceDispatch` (308), `BumpNewobject120` (324), `MemmoveGrowsliceModel` (330).
One memory block at `0x10000`: bump pointer, writeBarrier word, the 2144-byte heap, guard word, the 1240 input
bytes, the 72-byte receiver (protoc struct, `prysm/ir/ir-mainnet.json` gc amd64 layout, size 72: `state` 0, Proof
header 8 with old pointer word `oP` and len = cap = 0, Data pointer 32 (`oD`), `unknownFields` 40 and `sizeCache`
64 zero), our scratch (`Sd + 48` with `Sd = 16`, also the Deposit_Data decoder's frame), the return slot, the
24-byte spill area, the frame slots and the caller's slots (rsp = 0x10e3c). The frame `R` is the receiver's last
32 bytes, the two unused 16-byte frame gaps and the caller's word at rsp + 24.
For every input of 33 blocks of 32 bytes and a Deposit_Data, and every old pointer word, every premise holds and the
decoder returns nil.
-/

open Machine Runtime Machine.Witness Prysm.Deposit.Code

namespace Prysm.Deposit.Witness.DecodeAccept

def dataLabels : Program :=
  [.label "runtime.modelBumpPointer", .label "pad1", .label "pad2", .label "pad3", .label "pad4", .label "pad5",
   .label "pad6", .label "pad7", .label "runtime.writeBarrier"]

def program : Program := dataLabels ++ unmarshalSSZ ++ Prysm.Deposit_Data.Code.unmarshalSSZ ++ Prysm.RuntimeModel.BumpMakesliceByteSliceDispatch ++ BumpNewobject120 ++ MemmoveGrowsliceModel

-- `maxRecDepth` (builds of `Prysm.Deposit.WitnessDecodeAccept`, one run each; scoped per declaration): the default (512)
-- stops these list computations over the 356-directive host; 1000, 2000, 5000 and 20000 pass (measured with the
-- option file-wide). Value 2000 = twice the lowest passing value. Only `program_length`, `placed_at_308`, `placed_at_324`, `placed_at_330` need it.
set_option maxRecDepth 2000 in
theorem program_length : program.length = 356 := by rfl

instance host : Host := mkHost program (by rw [program_length]; decide)

theorem host_program_eq : Host.prog = program := rfl

theorem placed_at_9 : unmarshalSSZ.IsInfixAt Host.prog 9 :=
  infixAt_of dataLabels (Prysm.Deposit_Data.Code.unmarshalSSZ ++ Prysm.RuntimeModel.BumpMakesliceByteSliceDispatch ++ BumpNewobject120 ++ MemmoveGrowsliceModel)
    (by simp [host_program_eq, program, List.append_assoc]) rfl
theorem placed_at_165 : Prysm.Deposit_Data.Code.unmarshalSSZ.IsInfixAt Host.prog 165 :=
  infixAt_of (dataLabels ++ unmarshalSSZ) (Prysm.RuntimeModel.BumpMakesliceByteSliceDispatch ++ BumpNewobject120 ++ MemmoveGrowsliceModel)
    (by simp [host_program_eq, program, List.append_assoc]) (by rfl)
set_option maxRecDepth 2000 in
theorem placed_at_308 : Prysm.RuntimeModel.BumpMakesliceByteSliceDispatch.IsInfixAt Host.prog 308 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ Prysm.Deposit_Data.Code.unmarshalSSZ) (BumpNewobject120 ++ MemmoveGrowsliceModel)
    (by simp [host_program_eq, program, List.append_assoc]) (by rfl)
set_option maxRecDepth 2000 in
theorem placed_at_324 : BumpNewobject120.IsInfixAt Host.prog 324 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ Prysm.Deposit_Data.Code.unmarshalSSZ ++ Prysm.RuntimeModel.BumpMakesliceByteSliceDispatch) MemmoveGrowsliceModel
    (by simp [host_program_eq, program, List.append_assoc]) (by rfl)
set_option maxRecDepth 2000 in
theorem placed_at_330 : MemmoveGrowsliceModel.IsInfixAt Host.prog 330 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ Prysm.Deposit_Data.Code.unmarshalSSZ ++ Prysm.RuntimeModel.BumpMakesliceByteSliceDispatch ++ BumpNewobject120) []
    (by simp [host_program_eq, program, List.append_assoc]) (by rfl)

theorem labels_fresh_at_9 : LabelsFresh unmarshalSSZ 9 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_165 : LabelsFresh Prysm.Deposit_Data.Code.unmarshalSSZ 165 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_308 : LabelsFresh Prysm.RuntimeModel.BumpMakesliceByteSliceDispatch 308 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_330 : LabelsFresh MemmoveGrowsliceModel 330 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem no_label_before_308 : ∀ i < 308, Host.prog[i]? ≠ some (.label "runtime.makeslice") :=
  notLabel_of (by rw [host_program_eq]; decide)
theorem no_label_before_324 : ∀ i < 324, Host.prog[i]? ≠ some (.label "runtime.newobject") :=
  notLabel_of (by rw [host_program_eq]; decide)

theorem label_bump_pointer : label "runtime.modelBumpPointer" = 0x10000 :=
  mk_label program _ 0 _ (by simp [program, dataLabels]) (by simp [programLabels])

theorem label_write_barrier : label "runtime.writeBarrier" = 0x10008 :=
  mk_label program _ 8 _ (by simp [program, dataLabels]) (by decide)

/-- The text of `Prysm.SyncCommittee.Witness.DecodeAccept.uint8_ne_slice` (that module declares its own `Host` instance). -/
theorem uint8_ne_slice : ElfData.PrysmTarget.typeUint8_addr ≠ ElfData.PrysmTarget.typeUint8Slice_addr := by
  simp only [ElfData.PrysmTarget.typeUint8_addr, ElfData.PrysmTarget.typeUint8Slice_addr, Int64.toBitVec_add, Int64.toBitVec_ofNat]
  bv_omega

abbrev zeros (k : Nat) : List UInt8 := List.replicate k 0
abbrev zero_word_bytes : List UInt8 := Int.toBytes 8 (0 : UInt64).toBitVec.toInt

/-- bump pointer (→ 0x1000c) · writeBarrier · heap (2144) · guard · input (1240: proofs, pk, wc, amt, sig) ·
receiver (72: state 0, Proof `oP`/0/0, Data `oD`, unknownFields and sizeCache 0 (32 bytes)) · scratch (64) ·
return slot · spill area (24) · gap (16) · four loop locals · gap (16) · saved rbp · return slot · spill rax ·
spill rbx · caller word · spill rdi. -/
def block (prb pk wc amt sig oP oD : List UInt8) : List UInt8 :=
  Int.toBytes 8 (0x1000c : BitVec 64).toInt ++ ([0, 0, 0, 0] ++ (zeros 2144 ++ (zero_word_bytes ++ (prb ++ (pk ++ (wc ++ (amt ++
    (sig ++ (zeros 8 ++ (oP ++ (zeros 8 ++ (zeros 8 ++ (oD ++ (zeros 32 ++ (zeros 64 ++ (zeros 8 ++ (zeros 24 ++ (zeros 16 ++ (zeros 8 ++ (zeros 8 ++
    (zeros 8 ++ (zeros 8 ++ (zeros 16 ++ (zeros 8 ++ (zero_word_bytes ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ zeros 8))))))))))))))))))))))))))))

def mem (prb pk wc amt sig oP oD : List UInt8) : DataMem :=
  (block prb pk wc amt sig oP oD).At (0x10000 : BitVec 64)

def initial_state (prb pk wc amt sig oP oD : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10d4c, 0x10874, 1240, 0, 0, 1240, 0x10e3c, 0, 0, 0, 0, 0, 0, 0, 0x1085c, 0⟩, zmms, flags,
    mem prb pk wc amt sig oP oD⟩

/-- The frame of the witness: the receiver's last 32 bytes, the two unused 16-byte frame gaps (rsp − 72, rsp − 24)
and the caller's word at rsp + 24 (none is touched on the accept path). -/
def frame_rest : DataMem → Prop := Eq ((zeros 32).At (0x10d74 : BitVec 64)) ⋆ Eq ((zeros 16).At (0x10df4 : BitVec 64))
  ⋆ Eq ((zeros 16).At (0x10e24 : BitVec 64)) ⋆ Eq ((zeros 8).At (0x10e54 : BitVec 64))

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x1000c : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((zeros 2144).At (0x1000c : BitVec 64)) ⋆ X)) m) : (bumpHeap 2144 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x1000c, by decide, by rw [label_bump_pointer]; exact hm⟩) h

-- Threshold (builds of `Prysm.Deposit.WitnessDecodeAccept`, one run each): 200000 and 1000000 fail at `whnf`; 2000000 and 4000000 pass. Value 4000000 =
-- twice the lowest passing value. Cause (profiler): `simp` 20.1 s (15.1 s and 4.89 s), the AC-normalization
-- of the separating conjunction (33 chunks), as in `Prysm/HistoricalBatch/WitnessDecodeAccept.lean` / `Prysm/SyncCommittee/WitnessDecodeAccept.lean`.
set_option maxHeartbeats 4000000 in
/-- **Non-vacuity of `Decode.accept` (the premises of the frozen statement `Decode.accept_statement` are
satisfiable).** -/
theorem runs (proofs : List (List UInt8)) (pk wc amt sig oP oD : List UInt8) (hps : proofs.length = 33)
    (hp : ∀ e ∈ proofs, e.length = 32) (hpk : pk.length = 48) (hwc : wc.length = 32) (hamt : amt.length = 8)
    (hsig : sig.length = 96) (h1 : oP.length = 8) (h2 : oD.length = 8) (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨initial_state proofs.flatten pk wc amt sig oP oD zmms flags, Host.addrOf 9⟩ := by
  have hfl : proofs.flatten.length = 1056 := by rw [Codec.Segment.flat_len 32 proofs hp, hps]
  exact eventually_mono (Decode.accept 9 placed_at_9 labels_fresh_at_9 165 placed_at_165 labels_fresh_at_165 proofs hps hp pk wc amt sig hpk hwc hamt hsig
    (initial_state proofs.flatten pk wc amt sig oP oD zmms flags)
    0 0 (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 24) (zeros 8) (zeros 64) (zeros 8) oP (zeros 8) (zeros 8) oD
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl h1 rfl rfl h2
    frame_rest 16 (by decide) rfl bumpHeap 2144
    (by
      have H : Eq ((block proofs.flatten pk wc amt sig oP oD).At (0x10000 : BitVec 64))
        (mem proofs.flatten pk wc amt sig oP oD) := rfl
      witness_split [hfl, hpk, hwc, hamt, hsig, h1, h2]
      rw [Std.ExtHashMap.sep_comm_l (Eq (([0, 0, 0, 0] : List UInt8).At _)) (Eq ((zeros 2144).At _))] at H
      have H2 := lift_heap H
      simp only [initial_state, frame_rest, zero_word_bytes, label_write_barrier, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd, BitVec.reduceSub] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [initial_state]) rfl (Nat.le_refl _)
    (Prysm.RuntimeModel.bump_makeslice_byte_slice_dispatch_size24 308 placed_at_308 no_label_before_308 labels_fresh_at_308) (Prysm.RuntimeModel.bump_makeslice_byte_slice_dispatch_size1 308 placed_at_308 no_label_before_308 _ uint8_ne_slice)
    (model_memmove 330 placed_at_330 labels_fresh_at_330 _) (bump_newobject120 324 placed_at_324 no_label_before_324 _)
    (Prysm.RuntimeModel.bump_makeslice_byte_slice_dispatch_size1 308 placed_at_308 no_label_before_308 _ uint8_ne_slice) (model_memmove 330 placed_at_330 labels_fresh_at_330 _))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

/-- Zero input with a fresh `&Deposit{}`; a representative input; all-0xff input. -/
example (z' : RegZmms) (f : StatusFlags) :=
  runs (List.replicate 33 (zeros 32)) (zeros 48) (zeros 32) (zeros 8) (zeros 96) (zeros 8) (zeros 8)
    List.length_replicate (fun e he => by rw [List.eq_of_mem_replicate he]; exact List.length_replicate)
    rfl rfl rfl rfl rfl rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs ((List.range 33).map fun i => List.replicate 32 (UInt8.ofNat i)) ((List.range 48).map UInt8.ofNat)
    ((List.range 32).map UInt8.ofNat) (Int.toBytes 8 32000000000) ((List.range 96).map UInt8.ofNat)
    (Int.toBytes 8 0x20000) (Int.toBytes 8 0x30000) (by simp) (by simp) (by simp) (by simp) (by decide) (by simp)
    (by decide) (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs (List.replicate 33 (List.replicate 32 0xff)) (List.replicate 48 0xff) (List.replicate 32 0xff)
    (List.replicate 8 0xff) (List.replicate 96 0xff) (List.replicate 8 0xff) (List.replicate 8 0xff)
    List.length_replicate (fun e he => by rw [List.eq_of_mem_replicate he]; exact List.length_replicate)
    rfl rfl rfl rfl rfl rfl z' f

end Prysm.Deposit.Witness.DecodeAccept
