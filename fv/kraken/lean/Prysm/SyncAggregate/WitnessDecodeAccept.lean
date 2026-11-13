import Prysm.SyncAggregate.DecodeAccept
import Runtime.CopyModel
import Runtime.BumpAllocatorVariants
import Machine.WitnessHost

/-!
# Witness of `Decode.accept` (SyncAggregate decoder accept path)

The text of `Prysm/Deposit_Data/WitnessDecodeAccept.lean` with the SyncAggregate host and layout. It shows that the premises of the frozen
statement `Prysm.SyncAggregate.Decode.accept_statement` are satisfiable.
Host: data labels, the real Go 1.26.10 `(*v1alpha1.SyncAggregate).UnmarshalSSZ` (index 9), the 1-byte bump
`runtime.makeslice` (115, `bump_makeslice1`) and `MemmoveGrowsliceModel` (121, `model_memmove`).
One memory block at `0x10000`: bump pointer, writeBarrier word, the 160-byte heap, guard word, the 160 input bytes,
the 88-byte receiver (protoc struct; `prysm/ir/ir-mainnet.json` gc amd64 layout, size 88: `state` 0,
SyncCommitteeBits header 8 with old pointer word `oP1` and len = cap = 0, SyncCommitteeSignature header 32 (`oP2`),
`unknownFields` 56 and `sizeCache` 80 zero), the 16-byte callee block (`S = 16`), the callee return slot, the argument
area, the pointer save, the saved rbp, the caller's slots (rsp = 0x101ec) and the caller's word at rsp + 24. The frame
`R` is the receiver's last 32 bytes and that word. For every input and every old pointer word every premise holds and
the decoder returns nil. The receiver is a Go value of `v1alpha1.SyncAggregate` (zero `state`, zero-length slices).
-/

open Machine Runtime Machine.Witness Prysm.SyncAggregate.Code

namespace Prysm.SyncAggregate.Witness.DecodeAccept

def dataLabels : Program :=
  [.label "runtime.modelBumpPointer", .label "pad1", .label "pad2", .label "pad3", .label "pad4", .label "pad5",
   .label "pad6", .label "pad7", .label "runtime.writeBarrier"]

def program : Program := dataLabels ++ unmarshalSSZ ++ BumpMakeslice1 ++ MemmoveGrowsliceModel

theorem program_length : program.length = 147 := by rfl

instance host : Host := mkHost program (by rw [program_length]; decide)

theorem host_program_eq : Host.prog = program := rfl

theorem placed_at_9 : unmarshalSSZ.IsInfixAt Host.prog 9 :=
  infixAt_of dataLabels (BumpMakeslice1 ++ MemmoveGrowsliceModel) (by simp [host_program_eq, program, List.append_assoc]) rfl
theorem placed_at_115 : BumpMakeslice1.IsInfixAt Host.prog 115 :=
  infixAt_of (dataLabels ++ unmarshalSSZ) MemmoveGrowsliceModel
    (by simp [host_program_eq, program, List.append_assoc]) (by rfl)
theorem placed_at_121 : MemmoveGrowsliceModel.IsInfixAt Host.prog 121 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ BumpMakeslice1) []
    (by simp [host_program_eq, program, List.append_assoc]) (by rfl)

theorem labels_fresh_at_9 : LabelsFresh unmarshalSSZ 9 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_121 : LabelsFresh MemmoveGrowsliceModel 121 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_115 : ∀ i < 115, Host.prog[i]? ≠ some (.label "runtime.makeslice") :=
  notLabel_of (by rw [host_program_eq]; decide)

theorem label_bump_pointer : label "runtime.modelBumpPointer" = 0x10000 :=
  mk_label program _ 0 _ (by simp [program, dataLabels]) (by simp [labs])

theorem label_write_barrier : label "runtime.writeBarrier" = 0x10008 :=
  mk_label program _ 8 _ (by simp [program, dataLabels]) (by decide)

abbrev zeros (k : Nat) : List UInt8 := List.replicate k 0
abbrev zero_word_bytes : List UInt8 := Int.toBytes 8 (0 : UInt64).toBitVec.toInt

/-- bump pointer (→ 0x1000c) · writeBarrier · heap (160) · guard · input (160: bits, sig) · receiver (88: state 0,
SyncCommitteeBits `oP1`/0/0, SyncCommitteeSignature `oP2`/0/0, unknownFields and sizeCache 0 (32 bytes)) ·
callee block (16) · callee return slot · argument area (24) · pointer save · saved rbp · return slot · spill rax ·
spill rbx · caller word. -/
def block (bits sig oP1 oP2 : List UInt8) : List UInt8 :=
  Int.toBytes 8 (0x1000c : BitVec 64).toInt ++ ([0, 0, 0, 0] ++ (zeros 160 ++ (zero_word_bytes ++ (bits ++ (sig ++ (zeros 8 ++ (oP1 ++ (zeros 8 ++ (zeros 8 ++ (oP2 ++ (zeros 8 ++ (zeros 8 ++ (zeros 32 ++ (zeros 16 ++ (zeros 8 ++ (zeros 24 ++ (zeros 8 ++ (zeros 8 ++ (zero_word_bytes ++ (zeros 8 ++ (zeros 8 ++ zeros 8)))))))))))))))))))))

def mem (bits sig oP1 oP2 : List UInt8) : DataMem :=
  (block bits sig oP1 oP2).At (0x10000 : BitVec 64)

def initial_state (bits sig oP1 oP2 : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10154, 0x100b4, 160, 0, 0, 160, 0x101ec, 0, 0, 0, 0, 0, 0, 0, 0x1009c, 0⟩, zmms, flags,
    mem bits sig oP1 oP2⟩

/-- The frame of the witness: the receiver's `unknownFields` / `sizeCache` words (32 bytes at receiver + 56) and the
caller's word at rsp + 24 (neither is touched on the accept path). -/
def frame_rest : DataMem → Prop := Eq ((zeros 32).At (0x1018c : BitVec 64)) ⋆ Eq ((zeros 8).At (0x10204 : BitVec 64))

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x1000c : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((zeros 160).At (0x1000c : BitVec 64)) ⋆ X)) m) : (bumpHeap 160 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x1000c, by decide, by rw [label_bump_pointer]; exact hm⟩) h

-- Profiled cause (scratch copy, `profiler true`): the memory premise is closed by `simp` AC-normalization of
-- the 22-chunk separating conjunction (`sep_comm`, `sep_comm_l`: 7.03 s; the address `simp`: 2.08 s; simp total
-- 9.16 s of the declaration). The default 200000 heartbeats stop at `whnf`.
-- Thresholds measured in separate runs: 200000 and 400000 fail at `whnf`, 1000000 passes.
-- Value 2000000 (twice the lowest passing value; was 16000000, the value of `Prysm.Deposit_Data.Witness.DecodeAccept.runs`):
-- passes.
set_option maxHeartbeats 2000000 in
/-- **Non-vacuity of `Decode.accept` (the premises of the frozen statement `Decode.accept_statement` are satisfiable).** -/
theorem runs (bits sig oP1 oP2 : List UInt8) (hbits : bits.length = 64) (hsig : sig.length = 96)
    (h1 : oP1.length = 8) (h2 : oP2.length = 8) (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨initial_state bits sig oP1 oP2 zmms flags, Host.addrOf 9⟩ :=
  eventually_mono (Decode.accept 9 placed_at_9 labels_fresh_at_9 bits sig hbits hsig (initial_state bits sig oP1 oP2 zmms flags)
    0 0 (zeros 8) (zeros 8) (zeros 8) (zeros 24) (zeros 8) (zeros 8) (zeros 16) (zeros 8) oP1 (zeros 8) (zeros 8) oP2 (zeros 8) (zeros 8)
    rfl rfl rfl rfl rfl rfl rfl h1 rfl rfl h2 rfl rfl
    frame_rest 16 rfl bumpHeap 160
    (by
      have H : Eq ((block bits sig oP1 oP2).At (0x10000 : BitVec 64)) (mem bits sig oP1 oP2) := rfl
      witness_split [hbits, hsig, h1, h2]
      rw [Std.ExtHashMap.sep_comm_l (Eq (([0, 0, 0, 0] : List UInt8).At _)) (Eq ((zeros 160).At _))] at H
      have H2 := lift_heap H
      simp only [initial_state, frame_rest, zero_word_bytes, label_write_barrier, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd, BitVec.reduceSub] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [initial_state]) rfl (Nat.le_refl _) (bump_makeslice1 115 placed_at_115 labels_fresh_at_115 _) (model_memmove 121 placed_at_121 labels_fresh_at_121 _))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

/-- Zero input with a fresh `&SyncAggregate{}` (nil slices); a representative input with non-nil old pointer words;
all-0xff input. -/
example (z' : RegZmms) (f : StatusFlags) :=
  runs (zeros 64) (zeros 96) (zeros 8) (zeros 8) rfl rfl rfl rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs ((List.range 64).map (fun i => UInt8.ofNat i)) ((List.range 96).map (fun i => UInt8.ofNat (i + 100)))
    (Int.toBytes 8 0x20000) (Int.toBytes 8 0x30000) rfl rfl (by decide) (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs (List.replicate 64 0xff) (List.replicate 96 0xff) (List.replicate 8 0xff) (List.replicate 8 0xff)
    rfl rfl rfl rfl z' f

end Prysm.SyncAggregate.Witness.DecodeAccept
