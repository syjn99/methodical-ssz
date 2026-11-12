import E2eScal.Gen5F24BdrDec
import Runtime.CopyModel
import Runtime.BumpAllocatorVariants
import Machine.WitnessHost

/-!
# Witness of the generated `bdr_g5dec_accept` (`v1.BuilderDepositRequest` decoder accept path; FLAT24 / H7)

Written by the FLAT24 evaluator with its evidence script `f24wit.py`: the text of `WitDdA.lean` with the
v1.BuilderDepositRequest host and layout. It shows that the premises of the generated accept theorem (statement = kind instance)
are satisfiable. Host: data labels, the real Go 1.26.10 `(*v1.BuilderDepositRequest).UnmarshalSSZ` (index 9),
the 1-byte bump `runtime.makeslice` (152, `bump_makeslice1`) and `RtCopy` (158, `rt_memmove`).
One memory block at `0x10000`: bump pointer, writeBarrier word, the 176-byte heap, guard word, the 184 input bytes,
the 120-byte receiver (`prysm/ir/ir-mainnet.json` gc amd64 layout: `state`, per byte field a slice header with an
old pointer word and len = cap = 0, per uint64 field a zero word, then 32 untouched tail bytes), the callee block
(`S = 16`), the return slot, the argument area, the untouched frame ranges, the slice pointer save, the saved rbp
and the caller's slots (rsp = 0x10234). The frame `R` is the receiver tail, the untouched frame ranges and the
caller's word at rsp + 24. For every input and every old pointer word every premise holds and the decoder returns
nil. The receiver is a Go value of `v1.BuilderDepositRequest` (zero `state`, zero-length slices, zero integers).
-/

open Machine Runtime TestTarget Machine.Witness E2eScal Codec E2eScal.F24Code

namespace E2eScal.WitBdrGA

set_option maxRecDepth 100000

def dataLabels : Program :=
  [.label "runtime.fvBump", .label "pad1", .label "pad2", .label "pad3", .label "pad4", .label "pad5",
   .label "pad6", .label "pad7", .label "runtime.writeBarrier"]

def P : Program := dataLabels ++ BdrUnmarshal ++ BumpAlloc1 ++ RtCopy

theorem P_len : P.length = 184 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem prog_eq : Host.prog = P := rfl

theorem hk9 : BdrUnmarshal.IsInfixAt Host.prog 9 :=
  infixAt_of dataLabels (BumpAlloc1 ++ RtCopy) (by simp [prog_eq, P, List.append_assoc]) rfl

theorem hk152 : BumpAlloc1.IsInfixAt Host.prog 152 :=
  infixAt_of (dataLabels ++ BdrUnmarshal) RtCopy
    (by simp [prog_eq, P, List.append_assoc]) (by rfl)
theorem hk158 : RtCopy.IsInfixAt Host.prog 158 :=
  infixAt_of (dataLabels ++ BdrUnmarshal ++ BumpAlloc1) []
    (by simp [prog_eq, P, List.append_assoc]) (by rfl)

theorem hf9 : LabelsFresh BdrUnmarshal 9 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf158 : LabelsFresh RtCopy 158 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf152 : ∀ i < 152, Host.prog[i]? ≠ some (.label "runtime.makeslice") :=
  notLabel_of (by rw [prog_eq]; decide)

theorem label_bump : label "runtime.fvBump" = 0x10000 :=
  mk_label P _ 0 _ (by simp [P, dataLabels]) (by simp [labs])

theorem label_wb : label "runtime.writeBarrier" = 0x10008 :=
  mk_label P _ 8 _ (by simp [P, dataLabels]) (by decide)

abbrev z (k : Nat) : List UInt8 := List.replicate k 0
abbrev w0 : List UInt8 := Int.toBytes 8 (0 : UInt64).toBitVec.toInt

def block (f0 f1 f2 f3 oP1 oP2 oP3 : List UInt8) : List UInt8 :=
  (Int.toBytes 8 (0x1000c : BitVec 64).toInt) ++ (([0, 0, 0, 0]) ++ ((z 176) ++ (w0 ++ (f0 ++ (f1 ++ (f2 ++ (f3 ++ ((z 8) ++ (oP1 ++ ((z 8) ++ ((z 8) ++ (oP2 ++ ((z 8) ++ ((z 8) ++ ((z 8) ++ (oP3 ++ ((z 8) ++ ((z 8) ++ ((z 32) ++ ((z 16) ++ ((z 8) ++ ((z 24) ++ ((z 8) ++ ((z 8) ++ (w0 ++ ((z 8) ++ ((z 8) ++ ((z 8)))))))))))))))))))))))))))))

def mem (f0 f1 f2 f3 oP1 oP2 oP3 : List UInt8) : DataMem :=
  (block f0 f1 f2 f3 oP1 oP2 oP3).At (0x10000 : BitVec 64)

def cs0 (f0 f1 f2 f3 oP1 oP2 oP3 : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x1017c, 0x100c4, 184, 0, 0, 184, 0x10234, 0, 0, 0, 0, 0, 0, 0, 0x100ac, 0⟩, zmms, flags,
    mem f0 f1 f2 f3 oP1 oP2 oP3⟩

/-- The frame of the witness. -/
def R0 : DataMem → Prop :=
  Eq ((z 32).At (0x101d4 : BitVec 64)) ⋆ Eq ((z 8).At (0x1024c : BitVec 64))

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x1000c : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((z 176).At (0x1000c : BitVec 64)) ⋆ X)) m) : (bumpHeap 176 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x1000c, by decide, by rw [label_bump]; exact hm⟩) h

set_option maxHeartbeats 16000000 in
/-- **Non-vacuity of the generated `bdr_g5dec_accept`** (premises of the kind instance are satisfiable). -/
theorem bdr_accept_runs (f0 f1 f2 f3 oP1 oP2 oP3 : List UInt8) (hf0 : f0.length = 48) (hf1 : f1.length = 32) (hf2 : f2.length = 8) (hf3 : f3.length = 96) (h1 : oP1.length = 8) (h2 : oP2.length = 8) (h3 : oP3.length = 8)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨cs0 f0 f1 f2 f3 oP1 oP2 oP3 zmms flags, Host.addrOf 9⟩ :=
  eventually_mono (E2eScal.Gen.bdr_g5dec_accept 9 hk9 hf9 
    f0 f1 f2 f3 hf0 hf1 hf2 hf3 (cs0 f0 f1 f2 f3 oP1 oP2 oP3 zmms flags)
    0 0 (z 8) (z 8) (z 8) (z 24) (z 8) (z 8) (z 16) (z 8) oP1 (z 8) (z 8) oP2 (z 8) (z 8) (z 8) oP3 (z 8) (z 8)
    rfl rfl rfl rfl rfl rfl rfl h1 rfl rfl h2 rfl rfl rfl h3 rfl rfl
    R0 16 rfl bumpHeap 176
    (by
      have H : Eq ((block f0 f1 f2 f3 oP1 oP2 oP3).At (0x10000 : BitVec 64)) (mem f0 f1 f2 f3 oP1 oP2 oP3) := rfl
      wit_split [hf0, hf1, hf2, hf3, h1, h2, h3]
      rw [Std.ExtHashMap.sep_comm_l (Eq (([0, 0, 0, 0] : List UInt8).At _)) (Eq ((z 176).At _))] at H
      have H2 := lift_heap H
      simp only [cs0, R0, w0, label_wb, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd, BitVec.reduceSub] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [cs0]) rfl (Nat.le_refl _) (bump_makeslice1 152 hk152 hf152 _) (rt_memmove 158 hk158 hf158 _))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

/-- Zero input with nil slices; a representative input with non-nil old pointer words; all-0xff input. -/
example (z' : RegZmms) (f : StatusFlags) :=
  bdr_accept_runs (z 48) (z 32) (z 8) (z 96) (z 8) (z 8) (z 8) rfl rfl rfl rfl rfl rfl rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  bdr_accept_runs ((List.range 48).map (fun i => UInt8.ofNat (i + 0))) ((List.range 32).map (fun i => UInt8.ofNat (i + 10))) (Int.toBytes 8 0x0123456789abcde2) ((List.range 96).map (fun i => UInt8.ofNat (i + 30))) (Int.toBytes 8 0x20000) (Int.toBytes 8 0x30000) (Int.toBytes 8 0x40000) rfl rfl (by decide) rfl (by decide) (by decide) (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) :=
  bdr_accept_runs (List.replicate 48 0xff) (List.replicate 32 0xff) (List.replicate 8 0xff) (List.replicate 96 0xff) (List.replicate 8 0xff) (List.replicate 8 0xff) (List.replicate 8 0xff) rfl rfl rfl rfl rfl rfl rfl z' f

end E2eScal.WitBdrGA
