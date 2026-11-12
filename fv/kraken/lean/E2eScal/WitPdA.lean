import E2eScal.PdAccept
import Fk.RtCopy
import Fk.BumpMore
import Fk.WHost

/-!
# Witness of `pd_e2e_accept_g4gen` (PendingDeposit decoder accept path; hold-out, full-proof type)

Hand-written (the text of `WitSmA.lean` with the PendingDeposit host and layout).
It shows that the premises of the independent hand statement `E2eScal.H6.pd_accept_stmt` are satisfiable.
Host: data labels, the real Go 1.26.10 `(*v1alpha1.PendingDeposit).UnmarshalSSZ` (index 9),
`(*primitives.Slot).UnmarshalSSZ` (191), the 1-byte bump `runtime.makeslice` (254, `bump_makeslice1`) and
`RtCopy` (260, `rt_memmove`).
One memory block at `0x10000`: bump pointer, writeBarrier word, the 176-byte heap, guard word, the 192 input
bytes, the 128-byte receiver (`state`, PublicKey header with old pointer word `oP1` and len = cap = 0,
WithdrawalCredentials header (`oP2`), Amount, Signature header (`oP3`), Slot, then `unknownFields` + `sizeCache` +
padding = 32 bytes; `prysm/ir/ir-mainnet.json` gc amd64 layout), the 16-byte callee block (`S = 8`), the callee
return slot, the argument area (24), two untouched frame ranges, the slice pointer save, the saved rbp and the
caller's slots (rsp = 0x10264). The frame `R` is the untouched receiver tail (32 bytes), the untouched frame bytes
rsp − 48 … rsp − 33 (16) and rsp − 24 … rsp − 9 (16) and the unused spill slot rsp + 24. For every input and
every old pointer word every premise holds and the decoder returns nil. The receiver is a Go value of
`v1alpha1.PendingDeposit`.
-/

open Fk Fk.W E2e E2eAd E2eAd.Code E2eScal E2eScal.H6Code E2eScal.H6

namespace E2eScal.WitPdA

set_option maxRecDepth 100000

def dataLabels : Program :=
  [.label "runtime.fvBump", .label "pad1", .label "pad2", .label "pad3", .label "pad4", .label "pad5",
   .label "pad6", .label "pad7", .label "runtime.writeBarrier"]

def P : Program := dataLabels ++ PdUnmarshal ++ SlUnmarshal ++ BumpAlloc1 ++ RtCopy

theorem P_len : P.length = 286 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem prog_eq : Host.prog = P := rfl

theorem hk9 : PdUnmarshal.IsInfixAt Host.prog 9 :=
  infixAt_of dataLabels (SlUnmarshal ++ BumpAlloc1 ++ RtCopy) (by simp [prog_eq, P, List.append_assoc]) rfl
theorem hk191 : SlUnmarshal.IsInfixAt Host.prog 191 :=
  infixAt_of (dataLabels ++ PdUnmarshal) (BumpAlloc1 ++ RtCopy)
    (by simp [prog_eq, P, List.append_assoc]) (by rfl)
theorem hk254 : BumpAlloc1.IsInfixAt Host.prog 254 :=
  infixAt_of (dataLabels ++ PdUnmarshal ++ SlUnmarshal) RtCopy
    (by simp [prog_eq, P, List.append_assoc]) (by rfl)
theorem hk260 : RtCopy.IsInfixAt Host.prog 260 :=
  infixAt_of (dataLabels ++ PdUnmarshal ++ SlUnmarshal ++ BumpAlloc1) []
    (by simp [prog_eq, P, List.append_assoc]) (by rfl)

theorem hf9 : LabelsFresh PdUnmarshal 9 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf191 : LabelsFresh SlUnmarshal 191 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf260 : LabelsFresh RtCopy 260 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf254 : ∀ i < 254, Host.prog[i]? ≠ some (.label "runtime.makeslice") :=
  notLabel_of (by rw [prog_eq]; decide)

theorem label_bump : label "runtime.fvBump" = 0x10000 :=
  mk_label P _ 0 _ (by simp [P, dataLabels]) (by simp [labs])

theorem label_wb : label "runtime.writeBarrier" = 0x10008 :=
  mk_label P _ 8 _ (by simp [P, dataLabels]) (by decide)

abbrev z (k : Nat) : List UInt8 := List.replicate k 0
abbrev w0 : List UInt8 := Int.toBytes 8 (0 : UInt64).toBitVec.toInt

/-- bump pointer (→ 0x1000c) · writeBarrier · heap (176) · guard · input (192: pk, wc, amt, sig, sl) · receiver
(128: state, PublicKey `oP1`/0/0, WithdrawalCredentials `oP2`/0/0, Amount, Signature `oP3`/0/0, Slot, tail 32) ·
callee block (16) · callee return slot · argument area (24) · frame gap (16) · slice pointer save · frame gap (16) ·
saved rbp · return slot · spill rax · spill rbx · unused slot · spill rdi. -/
def block (pk wc amt sig sl oP1 oP2 oP3 : List UInt8) : List UInt8 :=
  Int.toBytes 8 (0x1000c : BitVec 64).toInt ++ ([0, 0, 0, 0] ++ (z 176 ++ (w0 ++ (pk ++ (wc ++ (amt ++ (sig ++ (sl ++ (z 8 ++ (oP1 ++ (z 8 ++ (z 8 ++ (oP2 ++ (z 8 ++ (z 8 ++ (z 8 ++ (oP3 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 32 ++ (z 16 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 16 ++ (z 8 ++ (z 16 ++ (z 8 ++ (w0 ++ (z 8 ++ (z 8 ++ (z 8 ++ z 8))))))))))))))))))))))))))))))))))

def mem (pk wc amt sig sl oP1 oP2 oP3 : List UInt8) : DataMem :=
  (block pk wc amt sig sl oP1 oP2 oP3).At (0x10000 : BitVec 64)

def cs0 (pk wc amt sig sl oP1 oP2 oP3 : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10184, 0x100c4, 192, 0, 0, 192, 0x10264, 0, 0, 0, 0, 0, 0, 0, 0x100ac, 0⟩, zmms, flags,
    mem pk wc amt sig sl oP1 oP2 oP3⟩

/-- The frame of the witness: the receiver tail, the two untouched frame ranges and the unused slot rsp + 24. -/
def R0 : DataMem → Prop :=
  Eq ((z 32).At (0x101e4 : BitVec 64)) ⋆ Eq ((z 16).At (0x10234 : BitVec 64)) ⋆ Eq ((z 16).At (0x1024c : BitVec 64))
    ⋆ Eq ((z 8).At (0x1027c : BitVec 64))

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x1000c : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((z 176).At (0x1000c : BitVec 64)) ⋆ X)) m) : (bumpHeap 176 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x1000c, by decide, by rw [label_bump]; exact hm⟩) h

set_option maxHeartbeats 16000000 in
/-- **Non-vacuity of `pd_e2e_accept_g4gen`** (premises of `pd_accept_stmt`). -/
theorem pd_accept_runs (pk wc amt sig sl oP1 oP2 oP3 : List UInt8) (hpk : pk.length = 48)
    (hwc : wc.length = 32) (hamt : amt.length = 8) (hsig : sig.length = 96) (hsl : sl.length = 8)
    (h1 : oP1.length = 8) (h2 : oP2.length = 8) (h3 : oP3.length = 8)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨cs0 pk wc amt sig sl oP1 oP2 oP3 zmms flags, Host.addrOf 9⟩ :=
  eventually_mono (pd_e2e_accept_g4gen 9 hk9 hf9 191 hk191 hf191
    pk wc amt sig sl hpk hwc hamt hsig hsl (cs0 pk wc amt sig sl oP1 oP2 oP3 zmms flags)
    0 0 (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 16) (z 8)
    oP1 (z 8) (z 8) oP2 (z 8) (z 8) (z 8) oP3 (z 8) (z 8) (z 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl h1 rfl rfl h2 rfl rfl rfl h3 rfl rfl rfl
    R0 8 (by decide) rfl bumpHeap 176
    (by
      have H : Eq ((block pk wc amt sig sl oP1 oP2 oP3).At (0x10000 : BitVec 64))
        (mem pk wc amt sig sl oP1 oP2 oP3) := rfl
      wit_split [hpk, hwc, hamt, hsig, hsl, h1, h2, h3]
      rw [Std.ExtHashMap.sep_comm_l (Eq (([0, 0, 0, 0] : List UInt8).At _)) (Eq ((z 176).At _))] at H
      have H2 := lift_heap H
      simp only [cs0, R0, w0, label_wb, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd, BitVec.reduceSub] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [cs0]) rfl (Nat.le_refl _) (bump_makeslice1 254 hk254 hf254 _) (rt_memmove 260 hk260 hf260 _))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

/-- Zero input with a fresh `&PendingDeposit{}` (nil slices); a representative input with non-nil old pointer
words; all-0xff input. -/
example (z' : RegZmms) (f : StatusFlags) :=
  pd_accept_runs (z 48) (z 32) (z 8) (z 96) (z 8) (z 8) (z 8) (z 8) rfl rfl rfl rfl rfl rfl rfl rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  pd_accept_runs ((List.range 48).map (fun i => UInt8.ofNat i)) (List.replicate 32 0x22)
    (Int.toBytes 8 0x0123456789abcdef) ((List.range 96).map (fun i => UInt8.ofNat (i + 100))) (Int.toBytes 8 7)
    (Int.toBytes 8 0x20000) (Int.toBytes 8 0x30000) (Int.toBytes 8 0x40000)
    rfl rfl (by decide) rfl (by decide) (by decide) (by decide) (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) :=
  pd_accept_runs (List.replicate 48 0xff) (List.replicate 32 0xff) (List.replicate 8 0xff) (List.replicate 96 0xff)
    (List.replicate 8 0xff) (List.replicate 8 0xff) (List.replicate 8 0xff) (List.replicate 8 0xff)
    rfl rfl rfl rfl rfl rfl rfl rfl z' f

end E2eScal.WitPdA
