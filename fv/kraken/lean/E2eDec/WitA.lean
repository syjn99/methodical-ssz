import E2eDec.Accept
import E2eDec.BumpDc
import Fk.RtCopy
import Fk.WHost

/-!
# Witness of `dcd_e2e_accept_main` (ENC decoder accept path D3)

The text of `E2eList/WitIaA.lean` (branch `claude/ssz-fv-list-vector-20261112`, commit `a1c5d0d`) with this host and
layout. The premises of the frozen `dcd_accept_stmt` are satisfiable for every `n ≤ 128`, the three contract hypotheses
included: both `MakesliceC` instances from `BumpAllocDc` (`bump_makeslice_dc_8`, `bump_makeslice_dc_1`), `MemmoveC`
from `RtCopy`. Host: data labels (bump pointer at 0, `runtime.writeBarrier` at 8), the real Go 1.26.10
`(*v1alpha1.DataColumnsByRootIdentifier).UnmarshalSSZ` (index 9), `BumpAllocDc`, `RtCopy`. One memory block at
`0x10000`: bump pointer, writeBarrier word, the 1056-byte heap (`32 + 8 · 128`), guard word, the receiver window
(`state`, the old BlockRoot and Columns words), the stack window rsp − 152 … rsp + 40 (rsp = 0x10504, S = 0), and last
the input `root ‖ dcOff ‖ ib` (so that no address depends on `n`). cap = len. Frame `R`: `state` and the untouched
frame bytes rsp − 72 … rsp − 9 (64).
-/

open Fk Fk.W E2eEnc E2eDec E2eDec.Code

namespace E2eDec.WitA

def dataLabels : Program :=
  [.label "runtime.fvBump", .label "pad1", .label "pad2", .label "pad3", .label "pad4", .label "pad5",
   .label "pad6", .label "pad7", .label "runtime.writeBarrier"]

def P : Program := dataLabels ++ DcUnmarshal ++ BumpAllocDc ++ RtCopy

-- Measured (ENC logs 116, 117, 119): `rfl` on the 279-directive host program stops with "maximum recursion depth" at
-- the default in `P_len` and `hk253`; 1024 passes.
set_option maxRecDepth 1024 in
theorem P_len : P.length = 279 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem prog_eq : Host.prog = P := rfl

theorem hk9 : DcUnmarshal.IsInfixAt Host.prog 9 :=
  infixAt_of dataLabels (BumpAllocDc ++ RtCopy) (by simp [prog_eq, P, List.append_assoc]) rfl
theorem hk238 : BumpAllocDc.IsInfixAt Host.prog 238 :=
  infixAt_of (dataLabels ++ DcUnmarshal) RtCopy (by simp [prog_eq, P, List.append_assoc]) (by rfl)
set_option maxRecDepth 1024 in
theorem hk253 : RtCopy.IsInfixAt Host.prog 253 :=
  infixAt_of (dataLabels ++ DcUnmarshal ++ BumpAllocDc) [] (by simp [prog_eq, P, List.append_assoc]) (by rfl)
theorem hf9 : LabelsFresh DcUnmarshal 9 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf238 : LabelsFresh BumpAllocDc 238 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf253 : LabelsFresh RtCopy 253 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hn238 : ∀ i < 238, Host.prog[i]? ≠ some (.label "runtime.makeslice") :=
  notLabel_of (by rw [prog_eq]; decide)

theorem label_bump : label "runtime.fvBump" = 0x10000 :=
  mk_label P _ 0 _ (by simp [P, dataLabels]) (by simp [labs])

theorem label_wb : label "runtime.writeBarrier" = 0x10008 :=
  mk_label P _ 8 _ (by simp [P, dataLabels]) (by decide)

theorem u8_ne_u64 : E2e.Data.e2eU8Type_addr ≠ E2eList.Data.lvU64Type_addr := by
  simp only [E2e.Data.e2eU8Type_addr, E2eList.Data.lvU64Type_addr, Int64.toBitVec_add, Int64.toBitVec_ofNat]
  bv_omega

abbrev z (k : Nat) : List UInt8 := List.replicate k 0
abbrev w0 : List UInt8 := Int.toBytes 8 (0 : UInt64).toBitVec.toInt

theorem dcOff_length : dcOff.length = 4 := rfl

/-- bump pointer (→ 0x1000c) · writeBarrier · heap (1056) · guard · receiver (state, aP1 aL1 aC1 aP2 aL2 aC2) ·
rslot · spill (40) · locals x − 104, x − 96, x − 88, x − 80 · frame gap (64) · saved rbp · return address · spills
rax rbx rcx rdi · root · dcOff (the input; `ib` follows). -/
def block (root aP1 aL1 aC1 aP2 aL2 aC2 : List UInt8) : List UInt8 :=
  Int.toBytes 8 (0x1000c : BitVec 64).toInt ++ ([0, 0, 0, 0] ++ (z 1056 ++ (w0 ++ (z 8 ++ (aP1 ++ (aL1 ++ (aC1
    ++ (aP2 ++ (aL2 ++ (aC2 ++ (z 8 ++ (z 40 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 64 ++ (z 8 ++ (w0 ++ (z 8
    ++ (z 8 ++ (z 8 ++ (z 8 ++ (root ++ dcOff))))))))))))))))))))))))

def mem (root ib aP1 aL1 aC1 aP2 aL2 aC2 : List UInt8) : DataMem :=
  (block root aP1 aL1 aC1 aP2 aL2 aC2 ++ ib).At (0x10000 : BitVec 64)

def cs0 (n : Nat) (root ib aP1 aL1 aC1 aP2 aL2 aC2 : List UInt8) (zmms : RegZmms) (flags : StatusFlags) :
    MachineData :=
  ⟨⟨0x10434, 0x1052c, UInt64.ofNat (36 + 8 * n), 0, 0, UInt64.ofNat (36 + 8 * n), 0x10504, 0, 0, 0, 0, 0, 0, 0,
    0x1041c, 0⟩, zmms, flags, mem root ib aP1 aL1 aC1 aP2 aL2 aC2⟩

/-- The frame of the witness: `state` (8 bytes at the receiver) and the frame gap rsp − 72 … rsp − 9 (64). -/
def R0 : DataMem → Prop :=
  Eq ((z 8).At (0x10434 : BitVec 64)) ⋆ Eq ((z 64).At (0x104bc : BitVec 64))

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x1000c : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((z 1056).At (0x1000c : BitVec 64)) ⋆ X)) m) : (bumpHeap 1056 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x1000c, by decide, by rw [label_bump]; exact hm⟩) h

-- Measured (ENC log 118): 200000 and 1000000 fail at `whnf`, 4000000 passes. The time is the `simp` AC-normalization
-- of the memory premise (the cause of `WitF`, LV logs 26, 27).
set_option maxHeartbeats 4000000 in
/-- **Non-vacuity of `dcd_e2e_accept_main`** for every `n ≤ 128`, every input and every old receiver word. -/
theorem dcd_accept_runs (n : Nat) (hn : n ≤ 128) (root ib aP1 aL1 aC1 aP2 aL2 aC2 : List UInt8)
    (hroot : root.length = 32) (hib : ib.length = 8 * n) (h1 : aP1.length = 8) (h2 : aL1.length = 8)
    (h3 : aC1.length = 8) (h4 : aP2.length = 8) (h5 : aL2.length = 8) (h6 : aC2.length = 8)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨cs0 n root ib aP1 aL1 aC1 aP2 aL2 aC2 zmms flags, Host.addrOf 9⟩ :=
  eventually_mono (dcd_e2e_accept_main 9 hk9 hf9 n hn root ib hroot hib
    (cs0 n root ib aP1 aL1 aC1 aP2 aL2 aC2 zmms flags) 0 0
    (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 40) (z 8) [] aP1 aL1 aC1 aP2 aL2 aC2
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl h1 h2 h3 h4 h5 h6 0 rfl R0 bumpHeap 1056
    (by
      have H : Eq ((block root aP1 aL1 aC1 aP2 aL2 aC2 ++ ib).At (0x10000 : BitVec 64))
        (mem root ib aP1 aL1 aC1 aP2 aL2 aC2) := rfl
      have hbl : (block root aP1 aL1 aC1 aP2 aL2 aC2).length = 1360 := by
        simp only [block, List.length_append, List.length_replicate, Int.toBytes_length, List.length_cons,
          List.length_nil, dcOff_length, hroot, h1, h2, h3, h4, h5, h6]
      rw [Mem.At_append_sep _ _ _ (by rw [hbl, hib]; omega), hbl] at H
      unfold block at H
      repeat rw [Mem.At_append_sep _ _ _ (by
          simp only [List.length_append, List.length_replicate, Int.toBytes_length, List.length_cons,
            List.length_nil, dcOff_length, hroot, h1, h2, h3, h4, h5, h6]
          omega)] at H
      simp only [List.length_replicate, Int.toBytes_length, List.length_cons, List.length_nil, Nat.reduceAdd,
        dcOff_length, hroot, h1, h2, h3, h4, h5, h6, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at H
      simp only [Std.ExtHashMap.sep_assoc] at H
      rw [Std.ExtHashMap.sep_comm_l (Eq (([0, 0, 0, 0] : List UInt8).At _)) (Eq ((z 1056).At _))] at H
      have H2 := lift_heap H
      simp only [cs0, R0, w0, label_wb, nil_At_emp, Std.ExtHashMap.sep_emp, UInt64.toBitVec_ofNat,
        Int64.toBitVec_ofNat, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by show (0 : UInt64).toNat + 16 < (0x10504 : UInt64).toNat; decide)
    (UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega))
    (Nat.le_refl _)
    (by show (UInt64.ofNat (36 + 8 * n)).toNat < 2 ^ 63
        rw [UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)]; omega)
    (by omega)
    (bump_makeslice_dc_1 238 hk238 hn238 _ u8_ne_u64) (bump_makeslice_dc_8 238 hk238 hn238 hf238)
    (rt_memmove 253 hk253 hf253 _))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

/-- n = 0 (empty Columns), zero input, a fresh receiver (nil words). -/
example (z' : RegZmms) (f : StatusFlags) :=
  dcd_accept_runs 0 (Nat.zero_le _) (z 32) [] (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) List.length_replicate rfl
    List.length_replicate List.length_replicate List.length_replicate List.length_replicate List.length_replicate
    List.length_replicate z' f
/-- n = 1, a representative input and non-nil old words. -/
example (z' : RegZmms) (f : StatusFlags) :=
  dcd_accept_runs 1 (by omega) (List.replicate 32 0x11) (Int.toBytes 8 0x0123456789abcdef) (Int.toBytes 8 0x20000)
    (Int.toBytes 8 5) (Int.toBytes 8 7) (Int.toBytes 8 0x30000) (Int.toBytes 8 1) (Int.toBytes 8 2)
    List.length_replicate (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) (Int.toBytes_length 8 _)
    (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) z' f
/-- n = 128 (the maximum), all-0xff input. -/
example (z' : RegZmms) (f : StatusFlags) :=
  dcd_accept_runs 128 (Nat.le_refl _) (List.replicate 32 0xff) (List.replicate (8 * 128) 0xff) (z 8) (z 8) (z 8)
    (z 8) (z 8) (z 8) List.length_replicate List.length_replicate List.length_replicate List.length_replicate
    List.length_replicate List.length_replicate List.length_replicate List.length_replicate z' f

end E2eDec.WitA
