import Prysm.DataColumnsByRootIdentifier.EncodeRejectLength
import Runtime.CopyModel
import Machine.WitnessHost

/-!
# Witnesses of the two encoder rejects

- `RB`: Host `[label ssz.ErrBytesLength] ++ marshalSSZTo`. Memory at `0x10000`: the two words of `ssz.ErrBytesLength`
  (stand-in values: the real ones are set by the runtime's init), the guard word (r14 = 0x10000), the receiver window
  (`state`, BlockRoot ptr, len `bl`), the stack window rsp − 8 … rsp + 24 (rsp = 0x10038). Frame `R`: `state` and the
  rax spill slot. For every `bl ≠ 32` (instances 0, 31, 33).
- `RT`: Host `[label ssz.ErrListTooBig] ++ marshalSSZTo ++ RtCopy` (`rt_memmove`, S = 0). Memory at `0x10000`: the two
  error words, guard word, receiver window (48 bytes, Columns len n = 129), root (32), the stack window rsp − 144 …
  rsp + 24 (rsp = 0x100f8), `dst` at 0x10110 with len 0, cap 36. Frame `R`: the receiver words not read and the
  stack slots this path does not write.
-/

open Machine Runtime Machine.Witness Prysm.DataColumnsByRootIdentifier.Code

namespace Prysm.DataColumnsByRootIdentifier.Witness.EncodeRejectLength


abbrev z (k : Nat) : List UInt8 := List.replicate k 0
abbrev bw (v : BitVec 64) : List UInt8 := Int.toBytes 8 v.toInt

namespace RejectLength

def P : Program := [.label "ssz.ErrBytesLength"] ++ marshalSSZTo

theorem P_len : P.length = 119 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem hk1 : marshalSSZTo.IsInfixAt Host.prog 1 := infixAt_of [.label "ssz.ErrBytesLength"] [] (by simp [Host.prog, mkHost, P]) rfl
theorem hf1 : LabelsFresh marshalSSZTo 1 := labelsFresh_of (by decide)

theorem label_ebl : label "ssz.ErrBytesLength" = 0x10000 :=
  mk_label P _ 0 _ (by simp [P]) (by simp [labs])

/-- error words · guard · receiver (state, BlockRoot ptr, len) · fp · return address · spill rax · spill rbx. -/
def block (bl : BitVec 64) : List UInt8 :=
  bw 0x10e8 ++ (bw 0x2b ++ (bw 0 ++ (z 8 ++ (bw 0x5000 ++ (bw bl ++ (z 8 ++ (bw 0 ++ (z 8 ++ z 8))))))))

def mem (bl : BitVec 64) : DataMem := (block bl).At (0x10000 : BitVec 64)

def cs0 (bl : BitVec 64) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10018, 0x20000, 0, 0, 0, 0, 0x10038, 0, 0, 0, 0, 0, 0, 0, 0x10000, 0⟩, zmms, flags, mem bl⟩

/-- **Non-vacuity of `Encode.reject_length`.** -/
theorem runs (bl : BitVec 64) (hbl : bl ≠ 32) (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rcx = 0 ∧ st.data.regs.rdi = 0x10e8 ∧ st.data.regs.rsi = 0x2b)
      ⟨cs0 bl zmms flags, Host.addrOf 1⟩ :=
  eventually_mono (Encode.reject_length 1 hk1 hf1 (cs0 bl zmms flags) 0 0 0x10e8 0x2b 0x5000 bl hbl (z 8) (z 8)
    rfl rfl (Eq ((z 8).At (0x10018 : BitVec 64)) ⋆ Eq ((z 8).At (0x10040 : BitVec 64)))
    (by
      have H : Eq ((block bl).At (0x10000 : BitVec 64)) (mem bl) := rfl
      wit_split
      simp only [cs0, bw, ElfData.PrysmTarget.e2eErrBytesLength_addr, label_ebl, nil_At_emp, Std.ExtHashMap.sep_emp,
        UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, Int64.toBitVec_add,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, show (UInt64.ofNat 0).toBitVec = 0#64 from rfl,
        show (p : UInt64) → p.toBitVec = p.toBitVec from fun _ => rfl] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by simp [cs0]))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩)

example (z' : RegZmms) (f : StatusFlags) := runs 0 (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) := runs 31 (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) := runs 33 (by decide) z' f

end RejectLength

namespace RejectTooBig

def P : Program := [.label "ssz.ErrListTooBig"] ++ marshalSSZTo ++ RtCopy

theorem P_len : P.length = 145 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem prog_eq : Host.prog = P := rfl

theorem hk1 : marshalSSZTo.IsInfixAt Host.prog 1 :=
  infixAt_of [.label "ssz.ErrListTooBig"] RtCopy (by simp [prog_eq, P, List.append_assoc]) rfl
theorem hk119 : RtCopy.IsInfixAt Host.prog 119 :=
  infixAt_of ([.label "ssz.ErrListTooBig"] ++ marshalSSZTo) [] (by simp [prog_eq, P, List.append_assoc]) (by rfl)
theorem hf1 : LabelsFresh marshalSSZTo 1 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf119 : LabelsFresh RtCopy 119 := labelsFresh_of (by rw [prog_eq]; decide)

theorem label_etb : label "ssz.ErrListTooBig" = 0x10000 :=
  mk_label P _ 0 _ (by simp [P]) (by simp [labs])

/-- error words · guard · receiver window (state, BlockRoot ptr/len/cap, Columns ptr/len) · root · rslot · gap 72 ·
l64 · l56 · gap 8 · gap (l40) · l32 · gap (l24) · gap (l16) · fp · return address · spills rax, rbx · dst (36). -/
def block (root : List UInt8) (nb : BitVec 64) : List UInt8 :=
  bw 0x10e8 ++ (bw 0x2b ++ (bw 0 ++ (z 8 ++ (bw 0x10048 ++ (Int.toBytes 8 32 ++ (z 8 ++ (z 8 ++ (bw nb ++ (root
    ++ (z 8 ++ (z 72 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 8 ++ (bw 0 ++ (z 8 ++ (z 8
    ++ z 36))))))))))))))))))))))

def mem (root : List UInt8) (nb : BitVec 64) : DataMem := (block root nb).At (0x10000 : BitVec 64)

def cs0 (root : List UInt8) (nb : BitVec 64) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10018, 0x10110, 0, 0, 0, 36, 0x100f8, 0, 0, 0, 0, 0, 0, 0, 0x10000, 0⟩, zmms, flags, mem root nb⟩

-- Measured (three builds of `Prysm.DataColumnsByRootIdentifier.WitnessEncodeRejectLength`): 200000 and 1000000 fail (`whnf` timeout); 4000000 passes. Profile (the 4000000 build): `simp`
-- 2.49 s in the declaration; the `whnf` part that uses the heartbeats was not broken down further.
set_option maxHeartbeats 4000000 in
/-- **Non-vacuity of `Encode.reject_too_big`**, n = 129. -/
theorem runs (root : List UInt8) (hroot : root.length = 32) (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rcx = 0 ∧ st.data.regs.rdi = 0x10e8 ∧ st.data.regs.rsi = 0x2b)
      ⟨cs0 root 129 zmms flags, Host.addrOf 1⟩ :=
  eventually_mono (Encode.reject_too_big 1 hk1 hf1 (cs0 root 129 zmms flags) 0 0 0x10e8 0x2b 0x10048 129
    (by decide) (by decide) root [] (z 36) hroot rfl rfl (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8)
    rfl rfl rfl rfl rfl rfl rfl 0 [] rfl
    (Eq ((z 8).At (0x10018 : BitVec 64)) ⋆ Eq ((z 8).At (0x10030 : BitVec 64)) ⋆ Eq ((z 8).At (0x10038 : BitVec 64))
      ⋆ Eq ((z 72).At (0x10070 : BitVec 64)) ⋆ Eq ((z 8).At (0x100c8 : BitVec 64))
      ⋆ Eq ((z 8).At (0x100d0 : BitVec 64)) ⋆ Eq ((z 8).At (0x100e0 : BitVec 64))
      ⋆ Eq ((z 8).At (0x100e8 : BitVec 64)))
    (by
      have H : Eq ((block root 129).At (0x10000 : BitVec 64)) (mem root 129) := rfl
      wit_split [hroot]
      simp only [cs0, bw, label_etb, nil_At_emp, Std.ExtHashMap.sep_emp,
        UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, Int64.toBitVec_add,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, show (UInt64.ofNat 0).toBitVec = 0#64 from rfl,
        show (p : UInt64) → p.toBitVec = p.toBitVec from fun _ => rfl] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by simp [cs0]) (by simp [cs0]) (rt_memmove 119 hk119 hf119 0))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩)

example (z' : RegZmms) (f : StatusFlags) := runs (z 32) rfl z' f
example (z' : RegZmms) (f : StatusFlags) := runs (List.replicate 32 0xff) (by simp) z' f

end RejectTooBig

end Prysm.DataColumnsByRootIdentifier.Witness.EncodeRejectLength
