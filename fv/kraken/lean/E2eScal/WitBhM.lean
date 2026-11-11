import E2eScal.BhEncMain
import Fk.RtCopy
import Fk.WHost

/-!
# Witness of `bh_e2e_marshal_main` (BeaconBlockHeader encoder, fast path only)

Hand-written (the text of `E2e/WitCpM.lean` with the BeaconBlockHeader host and layout).
Host: the real Go 1.26.10 `(*v1alpha1.BeaconBlockHeader).MarshalSSZTo` (index 0) and `RtCopy` (index 195,
`rt_memmove`, S = 0). One memory block at `0x10000`: guard word (r14 = 0xfff0), the 128-byte receiver at
0x10008 (`state` 0, Slot = `sl`, ProposerIndex = `pi`, ParentRoot = (0x10088, 32, 32), StateRoot =
(0x100a8, 32, 32), BodyRoot = (0x100c8, 32, 32), `unknownFields`/`sizeCache`/padding = 32 zero bytes), the
three 32-byte root arrays, the stack window (rsp = 0x10190: `memmove` return slot at rsp − 168, frame,
saved rbp, return slot, the two argument spill slots) and `dst` at 0x101a8: the prefix, 8 + 8 + 32 + 32 + 32
bytes of old contents, the spare capacity. Frame `R`: the untouched receiver tail (32 bytes), the untouched
frame bytes rsp − 160 … rsp − 105 (56) and rsp − 24 … rsp − 17 (8), and the spare capacity.
The receiver is a Go value of `v1alpha1.BeaconBlockHeader` (zero `state`, three roots with len = cap = 32).
Two instances: empty prefix with `cap = 112`, and a 3-byte prefix with 5 spare bytes. For every Slot,
ProposerIndex and root contents every premise of the theorem holds.
-/

open Fk Fk.W E2eScal E2eScal.BhCode E2eScal.Bh

namespace E2eScal.WitBhM

set_option maxRecDepth 100000

def P : Program := BhMarshal ++ RtCopy

theorem P_len : P.length = 221 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem hk0 : BhMarshal.IsInfixAt Host.prog 0 := infixAt_of [] RtCopy (by simp [Host.prog, mkHost, P]) rfl
theorem hk195 : RtCopy.IsInfixAt Host.prog 195 := infixAt_of BhMarshal [] (by simp [Host.prog, mkHost, P]) (by rfl)
theorem hf0 : LabelsFresh BhMarshal 0 := fun i hi => absurd hi (Nat.not_lt_zero _)
theorem hf195 : LabelsFresh RtCopy 195 := labelsFresh_of (by decide)

abbrev z (k : Nat) : List UInt8 := List.replicate k 0
abbrev w (v : UInt64) : List UInt8 := Int.toBytes 8 v.toBitVec.toInt

/-- guard · receiver (`state`, Slot, ProposerIndex, three root headers, 32-byte tail) · r1 · r2 · r3 ·
rslot · gap (56) · l104 · l96 · t2a · t2b · t1a · t1b · gap (8) · l16 · fp · return slot · spill rax ·
spill rbx · dst = prefix · d0 (8) · d1 (8) · d2 (32) · d3 (32) · d4 (32) · spare. -/
def block (sl pi r1 r2 r3 pre spare : List UInt8) : List UInt8 :=
  w 0 ++ (z 8 ++ (sl ++ (pi ++ (w 0x10088 ++ (Int.toBytes 8 32 ++ (w 32 ++ (w 0x100a8 ++ (Int.toBytes 8 32 ++ (w 32 ++ (w 0x100c8 ++ (Int.toBytes 8 32 ++ (w 32 ++ (z 32 ++ (r1 ++ (r2 ++ (r3 ++ (z 8 ++ (z 56 ++ (z 8 ++ (z 8 ++ (z 16 ++ (z 16 ++ (z 16 ++ (z 16 ++ (z 8 ++ (z 8 ++ (z 8 ++ (w 0 ++ (z 8 ++ (z 8 ++ (pre ++ (z 8 ++ (z 8 ++ (z 32 ++ (z 32 ++ (z 32 ++ (spare)))))))))))))))))))))))))))))))))))))

def mem (sl pi r1 r2 r3 pre spare : List UInt8) : DataMem := (block sl pi r1 r2 r3 pre spare).At (0x10000 : BitVec 64)

def cs0 (sl pi r1 r2 r3 pre spare : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10008, 0x101a8, UInt64.ofNat pre.length, 0, 0, UInt64.ofNat (pre.length + 112 + spare.length), 0x10190, 0,
    0, 0, 0, 0, 0, 0, 0xfff0, 0⟩, zmms, flags, mem sl pi r1 r2 r3 pre spare⟩

set_option maxHeartbeats 16000000 in
/-- Empty prefix, `cap = 112`. -/
theorem bhm_runs_empty (sl pi r1 r2 r3 : List UInt8) (hsl : sl.length = 8) (hpi : pi.length = 8)
    (hr1 : r1.length = 32) (hr2 : r2.length = 32) (hr3 : r3.length = 32)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0x101a8
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0)
      ⟨cs0 sl pi r1 r2 r3 [] [] zmms flags, Host.addrOf 0⟩ :=
  eventually_mono (bh_e2e_marshal_main 0 hk0 hf0 (z 8) sl pi (w 32) (w 32) (w 32) r1 r2 r3 []
    (z 8) (z 8) (z 32) (z 32) (z 32) rfl hsl hpi rfl rfl rfl hr1 hr2 hr3 rfl rfl rfl rfl rfl
    0x10088 0x100a8 0x100c8 (cs0 sl pi r1 r2 r3 [] [] zmms flags) 0 0 rfl
    (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 16) (z 16) (z 16) (z 16) (z 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (Eq ((z 32).At (0x10068 : BitVec 64)) ⋆ Eq ((z 56).At (0x100f0 : BitVec 64))
      ⋆ Eq ((z 8).At (0x10178 : BitVec 64)))
    0 [] rfl
    (by
      have H : Eq ((block sl pi r1 r2 r3 [] []).At (0x10000 : BitVec 64))
        (mem sl pi r1 r2 r3 [] []) := rfl
      wit_split [hsl, hpi, hr1, hr2, hr3]
      simp only [cs0, w, nil_At_emp, Std.ExtHashMap.sep_emp, Std.ExtHashMap.emp_sep, UInt64.toBitVec_ofNat,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, List.length_nil,
        show (UInt64.ofNat 0).toBitVec = 0#64 from rfl] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by simp [cs0]) (by simp [cs0]) (by simp [cs0]) (by simp [cs0]) (rt_memmove 195 hk195 hf195 0))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩)

set_option maxHeartbeats 16000000 in
/-- Prefix `[0xaa, 0xbb, 0xcc]`, 5 spare bytes (`cap = len + 117`). -/
theorem bhm_runs_prefix (sl pi r1 r2 r3 : List UInt8) (hsl : sl.length = 8) (hpi : pi.length = 8)
    (hr1 : r1.length = 32) (hr2 : r2.length = 32) (hr3 : r3.length = 32)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0x101a8
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0)
      ⟨cs0 sl pi r1 r2 r3 [0xaa, 0xbb, 0xcc] (z 5) zmms flags, Host.addrOf 0⟩ :=
  eventually_mono (bh_e2e_marshal_main 0 hk0 hf0 (z 8) sl pi (w 32) (w 32) (w 32) r1 r2 r3 [0xaa, 0xbb, 0xcc]
    (z 8) (z 8) (z 32) (z 32) (z 32) rfl hsl hpi rfl rfl rfl hr1 hr2 hr3 rfl rfl rfl rfl rfl
    0x10088 0x100a8 0x100c8 (cs0 sl pi r1 r2 r3 [0xaa, 0xbb, 0xcc] (z 5) zmms flags) 0 0 rfl
    (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 16) (z 16) (z 16) (z 16) (z 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (Eq ((z 32).At (0x10068 : BitVec 64)) ⋆ Eq ((z 56).At (0x100f0 : BitVec 64))
      ⋆ Eq ((z 8).At (0x10178 : BitVec 64)) ⋆ Eq ((z 5).At (0x1021b : BitVec 64)))
    0 [] rfl
    (by
      have H : Eq ((block sl pi r1 r2 r3 [0xaa, 0xbb, 0xcc] (z 5)).At (0x10000 : BitVec 64))
        (mem sl pi r1 r2 r3 [0xaa, 0xbb, 0xcc] (z 5)) := rfl
      wit_split [hsl, hpi, hr1, hr2, hr3]
      simp only [cs0, w, nil_At_emp, Std.ExtHashMap.sep_emp, Std.ExtHashMap.emp_sep, UInt64.toBitVec_ofNat,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, List.length_nil, List.length_cons, List.length_replicate,
        show (UInt64.ofNat 3).toBitVec = 3#64 from rfl] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by simp [cs0]) (by simp [cs0]) (by simp [cs0]) (by simp [cs0]) (rt_memmove 195 hk195 hf195 0))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩)

example (z' : RegZmms) (f : StatusFlags) :=
  bhm_runs_empty (Int.toBytes 8 0) (Int.toBytes 8 0) (z 32) (z 32) (z 32) (by decide) (by decide) rfl rfl rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  bhm_runs_prefix (Int.toBytes 8 0x0123456789abcdef) (Int.toBytes 8 7) ((List.range 32).map (fun i => (UInt8.ofNat i)))
    (List.replicate 32 0x11) (List.replicate 32 0x22) (by decide) (by decide) rfl rfl rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  bhm_runs_prefix (Int.toBytes 8 (2 ^ 64 - 1)) (Int.toBytes 8 (2 ^ 64 - 1)) (List.replicate 32 0xff)
    (List.replicate 32 0xff) (List.replicate 32 0xff) (by decide) (by decide) rfl rfl rfl z' f

end E2eScal.WitBhM
