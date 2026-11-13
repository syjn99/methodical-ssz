import Prysm.Deposit_Data.DecodeAccept
import Runtime.CopyModel
import Runtime.BumpAllocatorVariants
import Machine.WitnessHost

/-!
# Witness of `Decode.accept` (Deposit_Data decoder accept path, hold-out, type A)

Hand-written (the text of `Prysm/DepositMessage/WitnessDecodeAccept.lean` with the Deposit_Data host and layout).
It shows that the premises of the independent hand statement `Prysm.Deposit_Data.Decode.accept_statement` are satisfiable.
Host: data labels, the real Go 1.26.10 `(*v1alpha1.Deposit_Data).UnmarshalSSZ` (index 9), the 1-byte bump
`runtime.makeslice` (152, `bump_makeslice1`) and `MemmoveGrowsliceModel` (158, `model_memmove`).
One memory block at `0x10000`: bump pointer, writeBarrier word, the 176-byte heap, guard word, the 184 input
bytes, the 120-byte receiver (protoc struct; `prysm/ir/ir-mainnet.json` gc amd64 layout, size 120: `state` 0,
PublicKey header 8 with old pointer word `oP1` and len = cap = 0, WithdrawalCredentials header 32 (`oP2`),
Amount 56 (zero), Signature header 64 (`oP3`), `unknownFields` 88 and `sizeCache` 112 zero), the 16-byte callee
block (`S = 16`), the callee return slot, the argument area, the pointer save, the saved rbp, the caller's slots
(rsp = 0x10234) and the caller's word at rsp + 24. The frame `R` is the receiver's last 32 bytes and that word.
For every input and every old pointer word every premise holds and the decoder returns nil.
The receiver is a Go value of `v1alpha1.Deposit_Data` (zero `state`, zero-length slices, zero Amount).
-/

open Machine Runtime Machine.Witness Codec Prysm.Deposit_Data.Code

namespace Prysm.Deposit_Data.Witness.DecodeAccept

set_option maxRecDepth 100000

def dataLabels : Program :=
  [.label "runtime.modelBumpPointer", .label "pad1", .label "pad2", .label "pad3", .label "pad4", .label "pad5",
   .label "pad6", .label "pad7", .label "runtime.writeBarrier"]

def program : Program := dataLabels ++ unmarshalSSZ ++ BumpMakeslice1 ++ MemmoveGrowsliceModel

theorem program_length : program.length = 184 := by rfl

instance host : Host := mkHost program (by rw [program_length]; decide)

theorem host_program_eq : Host.prog = program := rfl

theorem placed_at_9 : unmarshalSSZ.IsInfixAt Host.prog 9 :=
  infixAt_of dataLabels (BumpMakeslice1 ++ MemmoveGrowsliceModel) (by simp [host_program_eq, program, List.append_assoc]) rfl
theorem placed_at_152 : BumpMakeslice1.IsInfixAt Host.prog 152 :=
  infixAt_of (dataLabels ++ unmarshalSSZ) MemmoveGrowsliceModel
    (by simp [host_program_eq, program, List.append_assoc]) (by rfl)
theorem placed_at_158 : MemmoveGrowsliceModel.IsInfixAt Host.prog 158 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ BumpMakeslice1) []
    (by simp [host_program_eq, program, List.append_assoc]) (by rfl)

theorem labels_fresh_at_9 : LabelsFresh unmarshalSSZ 9 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_158 : LabelsFresh MemmoveGrowsliceModel 158 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_152 : ∀ i < 152, Host.prog[i]? ≠ some (.label "runtime.makeslice") :=
  notLabel_of (by rw [host_program_eq]; decide)

theorem label_bump_pointer : label "runtime.modelBumpPointer" = 0x10000 :=
  mk_label program _ 0 _ (by simp [program, dataLabels]) (by simp [labs])

theorem label_write_barrier : label "runtime.writeBarrier" = 0x10008 :=
  mk_label program _ 8 _ (by simp [program, dataLabels]) (by decide)

abbrev zeros (k : Nat) : List UInt8 := List.replicate k 0
abbrev zero_word_bytes : List UInt8 := Int.toBytes 8 (0 : UInt64).toBitVec.toInt

/-- bump pointer (→ 0x1000c) · writeBarrier · heap (176) · guard · input (184: pk, wc, amt, sig) · receiver (120:
state 0, PublicKey `oP1`/0/0, WithdrawalCredentials `oP2`/0/0, Amount 0, Signature `oP3`/0/0, unknownFields and
sizeCache 0 (32 bytes)) · callee block (16) · callee return slot · argument area (24) · pointer save · saved rbp ·
return slot · spill rax · spill rbx · caller word. -/
def block (pk wc amt sig oP1 oP2 oP3 : List UInt8) : List UInt8 :=
  Int.toBytes 8 (0x1000c : BitVec 64).toInt ++ ([0, 0, 0, 0] ++ (zeros 176 ++ (zero_word_bytes ++ (pk ++ (wc ++ (amt ++ (sig ++ (zeros 8 ++ (oP1 ++ (zeros 8 ++ (zeros 8 ++ (oP2 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (oP3 ++ (zeros 8 ++ (zeros 8 ++ (zeros 32 ++ (zeros 16 ++ (zeros 8 ++ (zeros 24 ++ (zeros 8 ++ (zeros 8 ++ (zero_word_bytes ++ (zeros 8 ++ (zeros 8 ++ zeros 8)))))))))))))))))))))))))))

def mem (pk wc amt sig oP1 oP2 oP3 : List UInt8) : DataMem :=
  (block pk wc amt sig oP1 oP2 oP3).At (0x10000 : BitVec 64)

def initial_state (pk wc amt sig oP1 oP2 oP3 : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x1017c, 0x100c4, 184, 0, 0, 184, 0x10234, 0, 0, 0, 0, 0, 0, 0, 0x100ac, 0⟩, zmms, flags,
    mem pk wc amt sig oP1 oP2 oP3⟩

/-- The frame of the witness: the receiver's `unknownFields` / `sizeCache` words (32 bytes at receiver + 88) and the
caller's word at rsp + 24 (neither is touched on the accept path). -/
def frame_rest : DataMem → Prop := Eq ((zeros 32).At (0x101d4 : BitVec 64)) ⋆ Eq ((zeros 8).At (0x1024c : BitVec 64))

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x1000c : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((zeros 176).At (0x1000c : BitVec 64)) ⋆ X)) m) : (bumpHeap 176 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x1000c, by decide, by rw [label_bump_pointer]; exact hm⟩) h

set_option maxHeartbeats 16000000 in
/-- **Non-vacuity of `Decode.accept` (the premises of the hand statement `Decode.accept_statement` are satisfiable).** -/
theorem runs (pk wc amt sig oP1 oP2 oP3 : List UInt8) (hpk : pk.length = 48) (hwc : wc.length = 32)
    (hamt : amt.length = 8) (hsig : sig.length = 96) (h1 : oP1.length = 8) (h2 : oP2.length = 8) (h3 : oP3.length = 8)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨initial_state pk wc amt sig oP1 oP2 oP3 zmms flags, Host.addrOf 9⟩ :=
  eventually_mono (Decode.accept 9 placed_at_9 labels_fresh_at_9 pk wc amt sig hpk hwc hamt hsig (initial_state pk wc amt sig oP1 oP2 oP3 zmms flags)
    0 0 (zeros 8) (zeros 8) (zeros 8) (zeros 24) (zeros 8) (zeros 8) (zeros 16) (zeros 8) oP1 (zeros 8) (zeros 8) oP2 (zeros 8) (zeros 8) (zeros 8) oP3 (zeros 8) (zeros 8)
    rfl rfl rfl rfl rfl rfl rfl h1 rfl rfl h2 rfl rfl rfl h3 rfl rfl
    frame_rest 16 rfl bumpHeap 176
    (by
      have H : Eq ((block pk wc amt sig oP1 oP2 oP3).At (0x10000 : BitVec 64)) (mem pk wc amt sig oP1 oP2 oP3) := rfl
      witness_split [hpk, hwc, hamt, hsig, h1, h2, h3]
      rw [Std.ExtHashMap.sep_comm_l (Eq (([0, 0, 0, 0] : List UInt8).At _)) (Eq ((zeros 176).At _))] at H
      have H2 := lift_heap H
      simp only [initial_state, frame_rest, zero_word_bytes, label_write_barrier, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd, BitVec.reduceSub] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [initial_state]) rfl (Nat.le_refl _) (bump_makeslice1 152 placed_at_152 labels_fresh_at_152 _) (model_memmove 158 placed_at_158 labels_fresh_at_158 _))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

/-- Zero input with a fresh `&Deposit_Data{}` (nil slices); a representative input with non-nil old
pointer words; all-0xff input. -/
example (z' : RegZmms) (f : StatusFlags) :=
  runs (zeros 48) (zeros 32) (zeros 8) (zeros 96) (zeros 8) (zeros 8) (zeros 8) rfl rfl rfl rfl rfl rfl rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs ((List.range 48).map (fun i => UInt8.ofNat i)) (List.replicate 32 0x22)
    (Int.toBytes 8 0x0123456789abcdef) ((List.range 96).map (fun i => UInt8.ofNat (i + 100)))
    (Int.toBytes 8 0x20000) (Int.toBytes 8 0x30000) (Int.toBytes 8 0x40000)
    rfl rfl (by decide) rfl (by decide) (by decide) (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs (List.replicate 48 0xff) (List.replicate 32 0xff) (List.replicate 8 0xff) (List.replicate 96 0xff)
    (List.replicate 8 0xff) (List.replicate 8 0xff) (List.replicate 8 0xff) rfl rfl rfl rfl rfl rfl rfl z' f

end Prysm.Deposit_Data.Witness.DecodeAccept
