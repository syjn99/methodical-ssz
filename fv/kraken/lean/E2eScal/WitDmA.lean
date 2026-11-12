import E2eScal.DmAccept
import Runtime.CopyModel
import Runtime.BumpAllocatorVariants
import Machine.WitnessHost

/-!
# Witness of `dm_e2e_accept_main` (DepositMessage decoder accept path, hold-out)

Hand-written (the text of `WitE1A.lean` with the DepositMessage host and layout).
Host: data labels, the real Go 1.26.10 `(*v1alpha1.DepositMessage).UnmarshalSSZ` (index 9), the 1-byte bump
`runtime.makeslice` (118, `bump_makeslice1`) and `RtCopy` (124, `rt_memmove`).
One memory block at `0x10000`: bump pointer, writeBarrier word, the 80-byte heap, guard word, the 88 input
bytes, the 56-byte receiver (native Go struct; `prysm/ir/ir-mainnet.json` gc amd64 layout, size 56:
PublicKey header 0 with old pointer word `oP1` and len = cap = 0, WithdrawalCredentials header 24 with old
pointer word `oP2` and len = cap = 0, Amount 48 (zero)), the 16-byte callee block (`S = 16`), the callee
return slot, the argument area, the pointer save, the saved rbp, the caller's slots (rsp = 0x10134) and the
caller's word at rsp + 24. The receiver has no field outside the decoded ones, so the frame `R` is that
untouched caller word (8 bytes).
For every input and every old pointer word every premise holds and the decoder returns nil.
The receiver is a Go value of `v1alpha1.DepositMessage` (zero-length slices, zero Amount).
-/

open Machine Runtime TestTarget Machine.Witness E2eScal Codec E2eScal.H3Code E2eScal.Dm

namespace E2eScal.WitDmA

set_option maxRecDepth 100000

def dataLabels : Program :=
  [.label "runtime.fvBump", .label "pad1", .label "pad2", .label "pad3", .label "pad4", .label "pad5",
   .label "pad6", .label "pad7", .label "runtime.writeBarrier"]

def P : Program := dataLabels ++ DmUnmarshal ++ BumpAlloc1 ++ RtCopy

theorem P_len : P.length = 150 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem prog_eq : Host.prog = P := rfl

theorem hk9 : DmUnmarshal.IsInfixAt Host.prog 9 :=
  infixAt_of dataLabels (BumpAlloc1 ++ RtCopy) (by simp [prog_eq, P, List.append_assoc]) rfl
theorem hk118 : BumpAlloc1.IsInfixAt Host.prog 118 :=
  infixAt_of (dataLabels ++ DmUnmarshal) RtCopy
    (by simp [prog_eq, P, List.append_assoc]) (by rfl)
theorem hk124 : RtCopy.IsInfixAt Host.prog 124 :=
  infixAt_of (dataLabels ++ DmUnmarshal ++ BumpAlloc1) []
    (by simp [prog_eq, P, List.append_assoc]) (by rfl)

theorem hf9 : LabelsFresh DmUnmarshal 9 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf124 : LabelsFresh RtCopy 124 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf118 : ∀ i < 118, Host.prog[i]? ≠ some (.label "runtime.makeslice") :=
  notLabel_of (by rw [prog_eq]; decide)

theorem label_bump : label "runtime.fvBump" = 0x10000 :=
  mk_label P _ 0 _ (by simp [P, dataLabels]) (by simp [labs])

theorem label_wb : label "runtime.writeBarrier" = 0x10008 :=
  mk_label P _ 8 _ (by simp [P, dataLabels]) (by decide)

abbrev z (k : Nat) : List UInt8 := List.replicate k 0
abbrev w0 : List UInt8 := Int.toBytes 8 (0 : UInt64).toBitVec.toInt

/-- bump pointer (→ 0x1000c) · writeBarrier · heap (80) · guard · input (88: pk, wc, amt) · receiver (56:
PublicKey `oP1`/0/0, WithdrawalCredentials `oP2`/0/0, Amount 0) · callee block (16) · callee return slot ·
argument area (24) · pointer save · saved rbp · return slot · spill rax · spill rbx · caller word. -/
def block (pk wc amt oP1 oP2 : List UInt8) : List UInt8 :=
  Int.toBytes 8 (0x1000c : BitVec 64).toInt ++ ([0, 0, 0, 0] ++ (z 80 ++ (w0 ++ (pk ++ (wc ++ (amt ++ (oP1 ++ (z 8 ++ (z 8 ++ (oP2 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 16 ++ (z 8 ++ (z 24 ++ (z 8 ++ (z 8 ++ (w0 ++ (z 8 ++ (z 8 ++ z 8)))))))))))))))))))))

def mem (pk wc amt oP1 oP2 : List UInt8) : DataMem :=
  (block pk wc amt oP1 oP2).At (0x10000 : BitVec 64)

def cs0 (pk wc amt oP1 oP2 : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x100bc, 0x10064, 88, 0, 0, 88, 0x10134, 0, 0, 0, 0, 0, 0, 0, 0x1004c, 0⟩, zmms, flags,
    mem pk wc amt oP1 oP2⟩

/-- The frame of the witness: the caller's word at rsp + 24 (not touched on the accept path). -/
def R0 : DataMem → Prop := Eq ((z 8).At (0x1014c : BitVec 64))

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x1000c : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((z 80).At (0x1000c : BitVec 64)) ⋆ X)) m) : (bumpHeap 80 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x1000c, by decide, by rw [label_bump]; exact hm⟩) h

set_option maxHeartbeats 16000000 in
/-- **Non-vacuity of `dm_e2e_accept_main`.** -/
theorem dm_accept_runs (pk wc amt oP1 oP2 : List UInt8) (hpk : pk.length = 48) (hwc : wc.length = 32)
    (hamt : amt.length = 8) (h1 : oP1.length = 8) (h2 : oP2.length = 8)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨cs0 pk wc amt oP1 oP2 zmms flags, Host.addrOf 9⟩ :=
  eventually_mono (dm_e2e_accept_main 9 hk9 hf9 pk wc amt hpk hwc hamt (cs0 pk wc amt oP1 oP2 zmms flags)
    0 0 (z 8) (z 8) (z 8) (z 24) (z 8) (z 8) (z 16) oP1 (z 8) (z 8) oP2 (z 8) (z 8) (z 8)
    rfl rfl rfl rfl rfl rfl h1 rfl rfl h2 rfl rfl rfl
    R0 16 rfl bumpHeap 80
    (by
      have H : Eq ((block pk wc amt oP1 oP2).At (0x10000 : BitVec 64)) (mem pk wc amt oP1 oP2) := rfl
      wit_split [hpk, hwc, hamt, h1, h2]
      rw [Std.ExtHashMap.sep_comm_l (Eq (([0, 0, 0, 0] : List UInt8).At _)) (Eq ((z 80).At _))] at H
      have H2 := lift_heap H
      simp only [cs0, R0, w0, label_wb, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd, BitVec.reduceSub] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [cs0]) rfl (Nat.le_refl _) (bump_makeslice1 118 hk118 hf118 _) (rt_memmove 124 hk124 hf124 _))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

/-- Zero input with a fresh `&DepositMessage{}` (nil slices); a representative input with non-nil old
pointer words; all-0xff input. -/
example (z' : RegZmms) (f : StatusFlags) :=
  dm_accept_runs (z 48) (z 32) (z 8) (z 8) (z 8) rfl rfl rfl rfl rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  dm_accept_runs ((List.range 48).map (fun i => UInt8.ofNat i)) (List.replicate 32 0x22)
    (Int.toBytes 8 0x0123456789abcdef) (Int.toBytes 8 0x20000) (Int.toBytes 8 0x30000)
    rfl rfl (by decide) (by decide) (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) :=
  dm_accept_runs (List.replicate 48 0xff) (List.replicate 32 0xff) (List.replicate 8 0xff) (List.replicate 8 0xff)
    (List.replicate 8 0xff) rfl rfl rfl rfl rfl z' f

end E2eScal.WitDmA
