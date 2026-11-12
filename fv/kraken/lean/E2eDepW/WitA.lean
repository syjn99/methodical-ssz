import E2eDep.Accept
import E2eList.BumpT
import E2eDepW.BumpNew120
import Runtime.CopyModel
import Machine.WitnessHost

/-!
# Witness of `dep_e2e_accept_main` (Deposit decoder accept path)

The text of `E2eHb.WitHbA` with the Deposit host and layout. It shows that the premises of the frozen statement
`E2eDep.dep_accept_stmt` are satisfiable, the six contract hypotheses included: both `MakesliceC` instances of the
Deposit decoder and the one of the Deposit_Data decoder from `E2eList.BumpAllocT`, `NewobjectC … 120` from
`BumpNew120`, both `MemmoveC` from `RtCopy`.
Host: data labels, the real Go 1.26.10 `(*v1alpha1.Deposit).UnmarshalSSZ` (index 9) and
`(*v1alpha1.Deposit_Data).UnmarshalSSZ` (165), `BumpAllocT` (308), `BumpNew120` (324), `RtCopy` (330).
One memory block at `0x10000`: bump pointer, writeBarrier word, the 2144-byte heap, guard word, the 1240 input
bytes, the 72-byte receiver (protoc struct, `prysm/ir/ir-mainnet.json` gc amd64 layout, size 72: `state` 0, Proof
header 8 with old pointer word `oP` and len = cap = 0, Data pointer 32 (`oD`), `unknownFields` 40 and `sizeCache`
64 zero), our scratch (`Sd + 48` with `Sd = 16`, also the Deposit_Data decoder's frame), the return slot, the
24-byte spill area, the frame slots and the caller's slots (rsp = 0x10e3c). The frame `R` is the receiver's last
32 bytes, the two unused 16-byte frame gaps and the caller's word at rsp + 24.
For every input of 33 blocks of 32 bytes and a Deposit_Data, and every old pointer word, every premise holds and the
decoder returns nil.
-/

open Machine Runtime TestTarget Machine.Witness E2eList E2eDep E2eDep.Code E2eScal.H4Code E2eDepW

namespace E2eDepW.WitA

def dataLabels : Program :=
  [.label "runtime.fvBump", .label "pad1", .label "pad2", .label "pad3", .label "pad4", .label "pad5",
   .label "pad6", .label "pad7", .label "runtime.writeBarrier"]

def P : Program := dataLabels ++ DepUnmarshal ++ DdUnmarshal ++ BumpAllocT ++ BumpNew120 ++ RtCopy

-- `maxRecDepth` (builds of `E2eDepW.WitA`, one run each; scoped per declaration): the default (512)
-- stops these list computations over the 356-directive host; 1000, 2000, 5000 and 20000 pass (measured with the
-- option file-wide). Value 2000 = twice the lowest passing value. Only `P_len`, `hk308`, `hk324`, `hk330` need it.
set_option maxRecDepth 2000 in
theorem P_len : P.length = 356 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem prog_eq : Host.prog = P := rfl

theorem hk9 : DepUnmarshal.IsInfixAt Host.prog 9 :=
  infixAt_of dataLabels (DdUnmarshal ++ BumpAllocT ++ BumpNew120 ++ RtCopy)
    (by simp [prog_eq, P, List.append_assoc]) rfl
theorem hk165 : DdUnmarshal.IsInfixAt Host.prog 165 :=
  infixAt_of (dataLabels ++ DepUnmarshal) (BumpAllocT ++ BumpNew120 ++ RtCopy)
    (by simp [prog_eq, P, List.append_assoc]) (by rfl)
set_option maxRecDepth 2000 in
theorem hk308 : BumpAllocT.IsInfixAt Host.prog 308 :=
  infixAt_of (dataLabels ++ DepUnmarshal ++ DdUnmarshal) (BumpNew120 ++ RtCopy)
    (by simp [prog_eq, P, List.append_assoc]) (by rfl)
set_option maxRecDepth 2000 in
theorem hk324 : BumpNew120.IsInfixAt Host.prog 324 :=
  infixAt_of (dataLabels ++ DepUnmarshal ++ DdUnmarshal ++ BumpAllocT) RtCopy
    (by simp [prog_eq, P, List.append_assoc]) (by rfl)
set_option maxRecDepth 2000 in
theorem hk330 : RtCopy.IsInfixAt Host.prog 330 :=
  infixAt_of (dataLabels ++ DepUnmarshal ++ DdUnmarshal ++ BumpAllocT ++ BumpNew120) []
    (by simp [prog_eq, P, List.append_assoc]) (by rfl)

theorem hf9 : LabelsFresh DepUnmarshal 9 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf165 : LabelsFresh DdUnmarshal 165 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf308 : LabelsFresh BumpAllocT 308 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf330 : LabelsFresh RtCopy 330 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hn308 : ∀ i < 308, Host.prog[i]? ≠ some (.label "runtime.makeslice") :=
  notLabel_of (by rw [prog_eq]; decide)
theorem hn324 : ∀ i < 324, Host.prog[i]? ≠ some (.label "runtime.newobject") :=
  notLabel_of (by rw [prog_eq]; decide)

theorem label_bump : label "runtime.fvBump" = 0x10000 :=
  mk_label P _ 0 _ (by simp [P, dataLabels]) (by simp [labs])

theorem label_wb : label "runtime.writeBarrier" = 0x10008 :=
  mk_label P _ 8 _ (by simp [P, dataLabels]) (by decide)

/-- The text of `E2eList.WitScA.u8_ne_slice` (that module declares its own `Host` instance). -/
theorem u8_ne_slice : ElfData.CheckpointAndEpoch.e2eU8Type_addr ≠ E2eList.Data.lvSliceType_addr := by
  simp only [ElfData.CheckpointAndEpoch.e2eU8Type_addr, E2eList.Data.lvSliceType_addr, Int64.toBitVec_add, Int64.toBitVec_ofNat]
  bv_omega

abbrev z (k : Nat) : List UInt8 := List.replicate k 0
abbrev w0 : List UInt8 := Int.toBytes 8 (0 : UInt64).toBitVec.toInt

/-- bump pointer (→ 0x1000c) · writeBarrier · heap (2144) · guard · input (1240: proofs, pk, wc, amt, sig) ·
receiver (72: state 0, Proof `oP`/0/0, Data `oD`, unknownFields and sizeCache 0 (32 bytes)) · scratch (64) ·
return slot · spill area (24) · gap (16) · four loop locals · gap (16) · saved rbp · return slot · spill rax ·
spill rbx · caller word · spill rdi. -/
def block (prb pk wc amt sig oP oD : List UInt8) : List UInt8 :=
  Int.toBytes 8 (0x1000c : BitVec 64).toInt ++ ([0, 0, 0, 0] ++ (z 2144 ++ (w0 ++ (prb ++ (pk ++ (wc ++ (amt ++
    (sig ++ (z 8 ++ (oP ++ (z 8 ++ (z 8 ++ (oD ++ (z 32 ++ (z 64 ++ (z 8 ++ (z 24 ++ (z 16 ++ (z 8 ++ (z 8 ++
    (z 8 ++ (z 8 ++ (z 16 ++ (z 8 ++ (w0 ++ (z 8 ++ (z 8 ++ (z 8 ++ z 8))))))))))))))))))))))))))))

def mem (prb pk wc amt sig oP oD : List UInt8) : DataMem :=
  (block prb pk wc amt sig oP oD).At (0x10000 : BitVec 64)

def cs0 (prb pk wc amt sig oP oD : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10d4c, 0x10874, 1240, 0, 0, 1240, 0x10e3c, 0, 0, 0, 0, 0, 0, 0, 0x1085c, 0⟩, zmms, flags,
    mem prb pk wc amt sig oP oD⟩

/-- The frame of the witness: the receiver's last 32 bytes, the two unused 16-byte frame gaps (rsp − 72, rsp − 24)
and the caller's word at rsp + 24 (none is touched on the accept path). -/
def R0 : DataMem → Prop := Eq ((z 32).At (0x10d74 : BitVec 64)) ⋆ Eq ((z 16).At (0x10df4 : BitVec 64))
  ⋆ Eq ((z 16).At (0x10e24 : BitVec 64)) ⋆ Eq ((z 8).At (0x10e54 : BitVec 64))

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x1000c : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((z 2144).At (0x1000c : BitVec 64)) ⋆ X)) m) : (bumpHeap 2144 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x1000c, by decide, by rw [label_bump]; exact hm⟩) h

-- Threshold (builds of `E2eDepW.WitA`, one run each): 200000 and 1000000 fail at `whnf`; 2000000 and 4000000 pass. Value 4000000 =
-- twice the lowest passing value. Cause (profiler): `simp` 20.1 s (15.1 s and 4.89 s), the AC-normalization
-- of the separating conjunction (33 chunks), as in `WitHbA` / `WitScA`.
set_option maxHeartbeats 4000000 in
/-- **Non-vacuity of `dep_e2e_accept_main` (the premises of the frozen statement `dep_accept_stmt` are
satisfiable).** -/
theorem dep_accept_runs (proofs : List (List UInt8)) (pk wc amt sig oP oD : List UInt8) (hps : proofs.length = 33)
    (hp : ∀ e ∈ proofs, e.length = 32) (hpk : pk.length = 48) (hwc : wc.length = 32) (hamt : amt.length = 8)
    (hsig : sig.length = 96) (h1 : oP.length = 8) (h2 : oD.length = 8) (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨cs0 proofs.flatten pk wc amt sig oP oD zmms flags, Host.addrOf 9⟩ := by
  have hfl : proofs.flatten.length = 1056 := by rw [Codec.Segment.flat_len 32 proofs hp, hps]
  exact eventually_mono (dep_e2e_accept_main 9 hk9 hf9 165 hk165 hf165 proofs hps hp pk wc amt sig hpk hwc hamt hsig
    (cs0 proofs.flatten pk wc amt sig oP oD zmms flags)
    0 0 (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 24) (z 8) (z 64) (z 8) oP (z 8) (z 8) oD
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl h1 rfl rfl h2
    R0 16 (by decide) rfl bumpHeap 2144
    (by
      have H : Eq ((block proofs.flatten pk wc amt sig oP oD).At (0x10000 : BitVec 64))
        (mem proofs.flatten pk wc amt sig oP oD) := rfl
      wit_split [hfl, hpk, hwc, hamt, hsig, h1, h2]
      rw [Std.ExtHashMap.sep_comm_l (Eq (([0, 0, 0, 0] : List UInt8).At _)) (Eq ((z 2144).At _))] at H
      have H2 := lift_heap H
      simp only [cs0, R0, w0, label_wb, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd, BitVec.reduceSub] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [cs0]) rfl (Nat.le_refl _)
    (bump_makeslice_t24 308 hk308 hn308 hf308) (bump_makeslice_t1 308 hk308 hn308 _ u8_ne_slice)
    (rt_memmove 330 hk330 hf330 _) (bump_newobject120 324 hk324 hn324 _)
    (bump_makeslice_t1 308 hk308 hn308 _ u8_ne_slice) (rt_memmove 330 hk330 hf330 _))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

/-- Zero input with a fresh `&Deposit{}`; a representative input; all-0xff input. -/
example (z' : RegZmms) (f : StatusFlags) :=
  dep_accept_runs (List.replicate 33 (z 32)) (z 48) (z 32) (z 8) (z 96) (z 8) (z 8)
    List.length_replicate (fun e he => by rw [List.eq_of_mem_replicate he]; exact List.length_replicate)
    rfl rfl rfl rfl rfl rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  dep_accept_runs ((List.range 33).map fun i => List.replicate 32 (UInt8.ofNat i)) ((List.range 48).map UInt8.ofNat)
    ((List.range 32).map UInt8.ofNat) (Int.toBytes 8 32000000000) ((List.range 96).map UInt8.ofNat)
    (Int.toBytes 8 0x20000) (Int.toBytes 8 0x30000) (by simp) (by simp) (by simp) (by simp) (by decide) (by simp)
    (by decide) (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) :=
  dep_accept_runs (List.replicate 33 (List.replicate 32 0xff)) (List.replicate 48 0xff) (List.replicate 32 0xff)
    (List.replicate 8 0xff) (List.replicate 96 0xff) (List.replicate 8 0xff) (List.replicate 8 0xff)
    List.length_replicate (fun e he => by rw [List.eq_of_mem_replicate he]; exact List.length_replicate)
    rfl rfl rfl rfl rfl rfl z' f

end E2eDepW.WitA
