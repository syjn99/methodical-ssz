import Prysm.SyncAggregate.DecodeAccept
import Runtime.CopyModel
import Runtime.BumpAllocatorVariants
import Machine.WitnessHost

/-!
# Witness of `Decode.accept` (SyncAggregate decoder accept path)

The text of `E2eScal`'s `WitDdA.lean` with the SyncAggregate host and layout. It shows that the premises of the frozen
statement `Prysm.SyncAggregate.Decode.accept_statement` are satisfiable.
Host: data labels, the real Go 1.26.10 `(*v1alpha1.SyncAggregate).UnmarshalSSZ` (index 9), the 1-byte bump
`runtime.makeslice` (115, `bump_makeslice1`) and `RtCopy` (121, `rt_memmove`).
One memory block at `0x10000`: bump pointer, writeBarrier word, the 160-byte heap, guard word, the 160 input bytes,
the 88-byte receiver (protoc struct; `prysm/ir/ir-mainnet.json` gc amd64 layout, size 88: `state` 0,
SyncCommitteeBits header 8 with old pointer word `oP1` and len = cap = 0, SyncCommitteeSignature header 32 (`oP2`),
`unknownFields` 56 and `sizeCache` 80 zero), the 16-byte callee block (`S = 16`), the callee return slot, the argument
area, the pointer save, the saved rbp, the caller's slots (rsp = 0x101ec) and the caller's word at rsp + 24. The frame
`R` is the receiver's last 32 bytes and that word. For every input and every old pointer word every premise holds and
the decoder returns nil. The receiver is a Go value of `v1alpha1.SyncAggregate` (zero `state`, zero-length slices).
-/

open Machine Runtime TestTarget Machine.Witness Prysm.SyncAggregate.Code

namespace Prysm.SyncAggregate.Witness.DecodeAccept

def dataLabels : Program :=
  [.label "runtime.fvBump", .label "pad1", .label "pad2", .label "pad3", .label "pad4", .label "pad5",
   .label "pad6", .label "pad7", .label "runtime.writeBarrier"]

def P : Program := dataLabels ++ unmarshalSSZ ++ BumpAlloc1 ++ RtCopy

theorem P_len : P.length = 147 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem prog_eq : Host.prog = P := rfl

theorem hk9 : unmarshalSSZ.IsInfixAt Host.prog 9 :=
  infixAt_of dataLabels (BumpAlloc1 ++ RtCopy) (by simp [prog_eq, P, List.append_assoc]) rfl
theorem hk115 : BumpAlloc1.IsInfixAt Host.prog 115 :=
  infixAt_of (dataLabels ++ unmarshalSSZ) RtCopy
    (by simp [prog_eq, P, List.append_assoc]) (by rfl)
theorem hk121 : RtCopy.IsInfixAt Host.prog 121 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ BumpAlloc1) []
    (by simp [prog_eq, P, List.append_assoc]) (by rfl)

theorem hf9 : LabelsFresh unmarshalSSZ 9 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf121 : LabelsFresh RtCopy 121 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf115 : ∀ i < 115, Host.prog[i]? ≠ some (.label "runtime.makeslice") :=
  notLabel_of (by rw [prog_eq]; decide)

theorem label_bump : label "runtime.fvBump" = 0x10000 :=
  mk_label P _ 0 _ (by simp [P, dataLabels]) (by simp [labs])

theorem label_wb : label "runtime.writeBarrier" = 0x10008 :=
  mk_label P _ 8 _ (by simp [P, dataLabels]) (by decide)

abbrev z (k : Nat) : List UInt8 := List.replicate k 0
abbrev w0 : List UInt8 := Int.toBytes 8 (0 : UInt64).toBitVec.toInt

/-- bump pointer (→ 0x1000c) · writeBarrier · heap (160) · guard · input (160: bits, sig) · receiver (88: state 0,
SyncCommitteeBits `oP1`/0/0, SyncCommitteeSignature `oP2`/0/0, unknownFields and sizeCache 0 (32 bytes)) ·
callee block (16) · callee return slot · argument area (24) · pointer save · saved rbp · return slot · spill rax ·
spill rbx · caller word. -/
def block (bits sig oP1 oP2 : List UInt8) : List UInt8 :=
  Int.toBytes 8 (0x1000c : BitVec 64).toInt ++ ([0, 0, 0, 0] ++ (z 160 ++ (w0 ++ (bits ++ (sig ++ (z 8 ++ (oP1 ++ (z 8 ++ (z 8 ++ (oP2 ++ (z 8 ++ (z 8 ++ (z 32 ++ (z 16 ++ (z 8 ++ (z 24 ++ (z 8 ++ (z 8 ++ (w0 ++ (z 8 ++ (z 8 ++ z 8)))))))))))))))))))))

def mem (bits sig oP1 oP2 : List UInt8) : DataMem :=
  (block bits sig oP1 oP2).At (0x10000 : BitVec 64)

def cs0 (bits sig oP1 oP2 : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10154, 0x100b4, 160, 0, 0, 160, 0x101ec, 0, 0, 0, 0, 0, 0, 0, 0x1009c, 0⟩, zmms, flags,
    mem bits sig oP1 oP2⟩

/-- The frame of the witness: the receiver's `unknownFields` / `sizeCache` words (32 bytes at receiver + 56) and the
caller's word at rsp + 24 (neither is touched on the accept path). -/
def R0 : DataMem → Prop := Eq ((z 32).At (0x1018c : BitVec 64)) ⋆ Eq ((z 8).At (0x10204 : BitVec 64))

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x1000c : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((z 160).At (0x1000c : BitVec 64)) ⋆ X)) m) : (bumpHeap 160 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x1000c, by decide, by rw [label_bump]; exact hm⟩) h

-- Profiled cause (scratch copy, `profiler true`): the memory premise is closed by `simp` AC-normalization of
-- the 22-chunk separating conjunction (`sep_comm`, `sep_comm_l`: 7.03 s; the address `simp`: 2.08 s; simp total
-- 9.16 s of the declaration). The default 200000 heartbeats stop at `whnf`.
-- Thresholds measured in independent reviewer runs: 200000 and 400000 fail at `whnf`, 1000000 passes.
-- Value 2000000 (twice the reviewer's passing value; was 16000000, the value of `WitDdA.dd_accept_runs`):
-- passes in the implementer's run.
set_option maxHeartbeats 2000000 in
/-- **Non-vacuity of `Decode.accept` (the premises of the frozen statement `Decode.accept_statement` are satisfiable).** -/
theorem runs (bits sig oP1 oP2 : List UInt8) (hbits : bits.length = 64) (hsig : sig.length = 96)
    (h1 : oP1.length = 8) (h2 : oP2.length = 8) (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨cs0 bits sig oP1 oP2 zmms flags, Host.addrOf 9⟩ :=
  eventually_mono (Decode.accept 9 hk9 hf9 bits sig hbits hsig (cs0 bits sig oP1 oP2 zmms flags)
    0 0 (z 8) (z 8) (z 8) (z 24) (z 8) (z 8) (z 16) (z 8) oP1 (z 8) (z 8) oP2 (z 8) (z 8)
    rfl rfl rfl rfl rfl rfl rfl h1 rfl rfl h2 rfl rfl
    R0 16 rfl bumpHeap 160
    (by
      have H : Eq ((block bits sig oP1 oP2).At (0x10000 : BitVec 64)) (mem bits sig oP1 oP2) := rfl
      wit_split [hbits, hsig, h1, h2]
      rw [Std.ExtHashMap.sep_comm_l (Eq (([0, 0, 0, 0] : List UInt8).At _)) (Eq ((z 160).At _))] at H
      have H2 := lift_heap H
      simp only [cs0, R0, w0, label_wb, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd, BitVec.reduceSub] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [cs0]) rfl (Nat.le_refl _) (bump_makeslice1 115 hk115 hf115 _) (rt_memmove 121 hk121 hf121 _))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

/-- Zero input with a fresh `&SyncAggregate{}` (nil slices); a representative input with non-nil old pointer words;
all-0xff input. -/
example (z' : RegZmms) (f : StatusFlags) :=
  runs (z 64) (z 96) (z 8) (z 8) rfl rfl rfl rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs ((List.range 64).map (fun i => UInt8.ofNat i)) ((List.range 96).map (fun i => UInt8.ofNat (i + 100)))
    (Int.toBytes 8 0x20000) (Int.toBytes 8 0x30000) rfl rfl (by decide) (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs (List.replicate 64 0xff) (List.replicate 96 0xff) (List.replicate 8 0xff) (List.replicate 8 0xff)
    rfl rfl rfl rfl z' f

end Prysm.SyncAggregate.Witness.DecodeAccept
