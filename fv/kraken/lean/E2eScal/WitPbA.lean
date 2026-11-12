import E2eScal.PbAccept
import Fk.RtCopy
import Fk.BumpMore
import Fk.WHost

/-!
# Witness of `pb_e2e_accept_g4gen` (PowBlock decoder accept path, hold-out, full-proof type)

Hand-written (the text of `WitDdA.lean` with the PowBlock host and layout).
It shows that the premises of the independent hand statement `E2eScal.H6.pb_accept_stmt` are satisfiable.
Host: data labels, the real Go 1.26.10 `(*v1alpha1.PowBlock).UnmarshalSSZ` (index 9), the 1-byte bump
`runtime.makeslice` (150, `bump_makeslice1`) and `RtCopy` (156, `rt_memmove`).
One memory block at `0x10000`: bump pointer, writeBarrier word, the 96-byte heap, guard word, the 96 input bytes,
the 72-byte receiver (native struct; `prysm/ir/ir-mainnet.json` gc amd64 layout, size 72: BlockHash header 0 with
old pointer word `oP1` and len = cap = 0, ParentHash header 24 (`oP2`), TotalDifficulty header 48 (`oP3`)), the
16-byte callee block (`S = 16`), the callee return slot, the argument area, the pointer save, the saved rbp, the
caller's slots (rsp = 0x1015c) and the caller's word at rsp + 24. The frame `R` is that word.
For every input and every old pointer word every premise holds and the decoder returns nil.
The receiver is a Go value of `v1alpha1.PowBlock` (zero-length slices).
-/

open Fk Fk.W E2e E2eScal E2eScal.H6Code E2eScal.H6

namespace E2eScal.WitPbA

set_option maxRecDepth 100000

def dataLabels : Program :=
  [.label "runtime.fvBump", .label "pad1", .label "pad2", .label "pad3", .label "pad4", .label "pad5",
   .label "pad6", .label "pad7", .label "runtime.writeBarrier"]

def P : Program := dataLabels ++ PbUnmarshal ++ BumpAlloc1 ++ RtCopy

theorem P_len : P.length = 182 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem prog_eq : Host.prog = P := rfl

theorem hk9 : PbUnmarshal.IsInfixAt Host.prog 9 :=
  infixAt_of dataLabels (BumpAlloc1 ++ RtCopy) (by simp [prog_eq, P, List.append_assoc]) rfl
theorem hk150 : BumpAlloc1.IsInfixAt Host.prog 150 :=
  infixAt_of (dataLabels ++ PbUnmarshal) RtCopy
    (by simp [prog_eq, P, List.append_assoc]) (by rfl)
theorem hk156 : RtCopy.IsInfixAt Host.prog 156 :=
  infixAt_of (dataLabels ++ PbUnmarshal ++ BumpAlloc1) []
    (by simp [prog_eq, P, List.append_assoc]) (by rfl)

theorem hf9 : LabelsFresh PbUnmarshal 9 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf156 : LabelsFresh RtCopy 156 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf150 : ∀ i < 150, Host.prog[i]? ≠ some (.label "runtime.makeslice") :=
  notLabel_of (by rw [prog_eq]; decide)

theorem label_bump : label "runtime.fvBump" = 0x10000 :=
  mk_label P _ 0 _ (by simp [P, dataLabels]) (by simp [labs])

theorem label_wb : label "runtime.writeBarrier" = 0x10008 :=
  mk_label P _ 8 _ (by simp [P, dataLabels]) (by decide)

abbrev z (k : Nat) : List UInt8 := List.replicate k 0
abbrev w0 : List UInt8 := Int.toBytes 8 (0 : UInt64).toBitVec.toInt

/-- bump pointer (→ 0x1000c) · writeBarrier · heap (96) · guard · input (96: bh, ph, td) · receiver (72:
BlockHash `oP1`/0/0, ParentHash `oP2`/0/0, TotalDifficulty `oP3`/0/0) · callee block (16) · callee return slot ·
argument area (24) · pointer save · saved rbp · return slot · spill rax · spill rbx · caller word. -/
def block (bh ph td oP1 oP2 oP3 : List UInt8) : List UInt8 :=
  Int.toBytes 8 (0x1000c : BitVec 64).toInt ++ ([0, 0, 0, 0] ++ (z 96 ++ (w0 ++ (bh ++ (ph ++ (td ++ (oP1 ++ (z 8 ++ (z 8 ++ (oP2 ++ (z 8 ++ (z 8 ++ (oP3 ++ (z 8 ++ (z 8 ++ (z 16 ++ (z 8 ++ (z 24 ++ (z 8 ++ (z 8 ++ (w0 ++ (z 8 ++ (z 8 ++ z 8)))))))))))))))))))))))

def mem (bh ph td oP1 oP2 oP3 : List UInt8) : DataMem :=
  (block bh ph td oP1 oP2 oP3).At (0x10000 : BitVec 64)

def cs0 (bh ph td oP1 oP2 oP3 : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x100d4, 0x10074, 96, 0, 0, 96, 0x1015c, 0, 0, 0, 0, 0, 0, 0, 0x1005c, 0⟩, zmms, flags,
    mem bh ph td oP1 oP2 oP3⟩

/-- The frame of the witness: the caller's word at rsp + 24 (not touched on the accept path). -/
def R0 : DataMem → Prop := Eq ((z 8).At (0x10174 : BitVec 64))

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x1000c : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((z 96).At (0x1000c : BitVec 64)) ⋆ X)) m) : (bumpHeap 96 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x1000c, by decide, by rw [label_bump]; exact hm⟩) h

set_option maxHeartbeats 16000000 in
/-- **Non-vacuity of `pb_e2e_accept_g4gen` (the premises of the hand statement `pb_accept_stmt` are satisfiable).** -/
theorem pb_accept_runs (bh ph td oP1 oP2 oP3 : List UInt8) (hbh : bh.length = 32) (hph : ph.length = 32)
    (htd : td.length = 32) (h1 : oP1.length = 8) (h2 : oP2.length = 8) (h3 : oP3.length = 8)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨cs0 bh ph td oP1 oP2 oP3 zmms flags, Host.addrOf 9⟩ :=
  eventually_mono (pb_e2e_accept_g4gen 9 hk9 hf9 bh ph td hbh hph htd (cs0 bh ph td oP1 oP2 oP3 zmms flags)
    0 0 (z 8) (z 8) (z 8) (z 24) (z 8) (z 8) (z 16) oP1 (z 8) (z 8) oP2 (z 8) (z 8) oP3 (z 8) (z 8)
    rfl rfl rfl rfl rfl rfl h1 rfl rfl h2 rfl rfl h3 rfl rfl
    R0 16 rfl bumpHeap 96
    (by
      have H : Eq ((block bh ph td oP1 oP2 oP3).At (0x10000 : BitVec 64)) (mem bh ph td oP1 oP2 oP3) := rfl
      wit_split [hbh, hph, htd, h1, h2, h3]
      rw [Std.ExtHashMap.sep_comm_l (Eq (([0, 0, 0, 0] : List UInt8).At _)) (Eq ((z 96).At _))] at H
      have H2 := lift_heap H
      simp only [cs0, R0, w0, label_wb, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd, BitVec.reduceSub] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [cs0]) rfl (Nat.le_refl _) (bump_makeslice1 150 hk150 hf150 _) (rt_memmove 156 hk156 hf156 _))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

/-- Zero input with a fresh `&PowBlock{}` (nil slices); a representative input with non-nil old pointer words;
all-0xff input. -/
example (z' : RegZmms) (f : StatusFlags) :=
  pb_accept_runs (z 32) (z 32) (z 32) (z 8) (z 8) (z 8) rfl rfl rfl rfl rfl rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  pb_accept_runs ((List.range 32).map (fun i => UInt8.ofNat i)) (List.replicate 32 0x22)
    ((List.range 32).map (fun i => UInt8.ofNat (i + 100)))
    (Int.toBytes 8 0x20000) (Int.toBytes 8 0x30000) (Int.toBytes 8 0x40000)
    rfl rfl rfl (by decide) (by decide) (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) :=
  pb_accept_runs (List.replicate 32 0xff) (List.replicate 32 0xff) (List.replicate 32 0xff)
    (List.replicate 8 0xff) (List.replicate 8 0xff) (List.replicate 8 0xff) rfl rfl rfl rfl rfl rfl z' f

end E2eScal.WitPbA
