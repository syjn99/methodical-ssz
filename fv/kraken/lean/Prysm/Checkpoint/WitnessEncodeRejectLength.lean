import Prysm.Checkpoint.EncodeRejectLength
import Runtime.CopyModel
import Machine.WitnessHost

/-!
# Witness of `Encode.reject_length`

Host: the label `ssz.ErrBytesLength` (index 0) and the real Go 1.26.10
`(*v1alpha1.Checkpoint).MarshalSSZTo` (index 1). Memory at `0x10000`: the two
words of `ssz.ErrBytesLength` (stand-in values: the real ones are set by the
runtime's init), the guard word, the 72-byte receiver with `len(Root) = rl`,
the stack window from rsp − 64 to rsp + 24 (rsp = 0x100a0), and `dst` at
0x100b8 with `len = 0`, `cap = 48`. Frame `R`: the untouched 24-byte frame gap,
the rax spill slot and `dst[8:48]`. For every `rl ≠ 32` (instances 31, 33, 0)
the encoder returns the error words and a nil slice.
-/

open Machine Runtime Machine.Witness Prysm.Checkpoint.Code

namespace Prysm.Checkpoint.Witness.EncodeRejectLength

set_option maxRecDepth 100000

def P : Program := [.label "ssz.ErrBytesLength"] ++ marshalSSZTo

theorem P_len : P.length = 92 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem hk1 : marshalSSZTo.IsInfixAt Host.prog 1 := infixAt_of [.label "ssz.ErrBytesLength"] [] (by simp [Host.prog, mkHost, P]) rfl
theorem hf1 : LabelsFresh marshalSSZTo 1 := labelsFresh_of (by decide)

theorem label_ebl : label "ssz.ErrBytesLength" = 0x10000 :=
  mk_label P _ 0 _ (by simp [P]) (by simp [labs])

abbrev z (k : Nat) : List UInt8 := List.replicate k 0
abbrev w (v : UInt64) : List UInt8 := Int.toBytes 8 v.toBitVec.toInt

/-- ErrBytesLength words · guard · receiver (state, Epoch, Root ptr/len/cap, tail) · t40 · t30 · gap (24) · fp ·
return slot · spill rax · spill rbx · dst (48). -/
def block (e8 : List UInt8) (rl : UInt64) : List UInt8 :=
  w 0x10e8 ++ (w 0x2b ++ (w 0 ++ (z 8 ++ (e8 ++ (w 0x5000 ++ (w rl ++ (w 48 ++ (z 32 ++ (z 16 ++ (z 16 ++ (z 24
    ++ (z 8 ++ (w 0 ++ (z 8 ++ (z 8 ++ (z 8 ++ z 40))))))))))))))))

def mem (e8 : List UInt8) (rl : UInt64) : DataMem := (block e8 rl).At (0x10000 : BitVec 64)

def cs0 (e8 : List UInt8) (rl : UInt64) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10018, 0x100b8, 0, 0, 0, 48, 0x100a0, 0, 0, 0, 0, 0, 0, 0, 0x10000, 0⟩, zmms, flags, mem e8 rl⟩

set_option maxHeartbeats 16000000 in
/-- **Non-vacuity of `Encode.reject_length`.** -/
theorem runs (e8 : List UInt8) (he8 : e8.length = 8) (rl : UInt64) (hrl : rl ≠ 32)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rcx = 0 ∧ st.data.regs.rdi = 0x10e8 ∧ st.data.regs.rsi = 0x2b)
      ⟨cs0 e8 rl zmms flags, Host.addrOf 1⟩ :=
  eventually_mono (Encode.reject_length 1 hk1 hf1 (z 8) e8 (w 48) (z 32) [] (z 8) rfl he8 rfl rfl rfl 0x5000 rl hrl
    (cs0 e8 rl zmms flags) 0 0 0x10e8 0x2b rfl (z 8) (z 8) (z 16) (z 16) rfl rfl rfl rfl
    (Eq ((z 24).At (0x10080 : BitVec 64)) ⋆ Eq ((z 8).At (0x100a8 : BitVec 64)) ⋆ Eq ((z 40).At (0x100c0 : BitVec 64)))
    (by
      have H : Eq ((block e8 rl).At (0x10000 : BitVec 64)) (mem e8 rl) := rfl
      wit_split [he8]
      simp only [cs0, w, ElfData.PrysmTarget.sszErrBytesLength_addr, label_ebl, nil_At_emp, Std.ExtHashMap.sep_emp,
        Std.ExtHashMap.emp_sep, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, Int64.toBitVec_add,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, show (UInt64.ofNat 0).toBitVec = 0#64 from rfl,
        show (p : UInt64) → p.toBitVec = p.toBitVec from fun _ => rfl] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by simp [cs0]) (by simp [cs0]) (by simp [cs0]))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩)

example (z' : RegZmms) (f : StatusFlags) := runs (Int.toBytes 8 7) (by decide) 31 (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) := runs (Int.toBytes 8 (2 ^ 64 - 1)) (by decide) 33 (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) := runs (Int.toBytes 8 0) (by decide) 0 (by decide) z' f

/-! ## Non-empty prefix

Same Host and layout; `dst` at 0x100b8 has `len = 5` (prefix bytes 1..5), `cap = 48`; `d0` at 0x100bd,
frame `dst[13:48]`. -/
namespace NonEmptyPrefix

def pre5 : List UInt8 := [1, 2, 3, 4, 5]

def block (e8 : List UInt8) (rl : UInt64) : List UInt8 :=
  w 0x10e8 ++ (w 0x2b ++ (w 0 ++ (z 8 ++ (e8 ++ (w 0x5000 ++ (w rl ++ (w 48 ++ (z 32 ++ (z 16 ++ (z 16 ++ (z 24
    ++ (z 8 ++ (w 0 ++ (z 8 ++ (z 8 ++ (pre5 ++ (z 8 ++ z 35)))))))))))))))))

def mem (e8 : List UInt8) (rl : UInt64) : DataMem := (block e8 rl).At (0x10000 : BitVec 64)

def cs0 (e8 : List UInt8) (rl : UInt64) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10018, 0x100b8, 5, 0, 0, 48, 0x100a0, 0, 0, 0, 0, 0, 0, 0, 0x10000, 0⟩, zmms, flags, mem e8 rl⟩

set_option maxHeartbeats 16000000 in
/-- **Non-vacuity of `Encode.reject_length`** with a 5-byte prefix. -/
theorem runs (e8 : List UInt8) (he8 : e8.length = 8) (rl : UInt64) (hrl : rl ≠ 32)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rcx = 0 ∧ st.data.regs.rdi = 0x10e8 ∧ st.data.regs.rsi = 0x2b)
      ⟨cs0 e8 rl zmms flags, Host.addrOf 1⟩ :=
  eventually_mono (Encode.reject_length 1 hk1 hf1 (z 8) e8 (w 48) (z 32) pre5 (z 8) rfl he8 rfl rfl rfl 0x5000 rl
    hrl (cs0 e8 rl zmms flags) 0 0 0x10e8 0x2b rfl (z 8) (z 8) (z 16) (z 16) rfl rfl rfl rfl
    (Eq ((z 24).At (0x10080 : BitVec 64)) ⋆ Eq ((z 8).At (0x100a8 : BitVec 64)) ⋆ Eq ((z 35).At (0x100c5 : BitVec 64)))
    (by
      have H : Eq ((block e8 rl).At (0x10000 : BitVec 64)) (mem e8 rl) := rfl
      wit_split [he8, show pre5.length = 5 from rfl]
      simp only [cs0, w, ElfData.PrysmTarget.sszErrBytesLength_addr, label_ebl, nil_At_emp, Std.ExtHashMap.sep_emp,
        Std.ExtHashMap.emp_sep, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, Int64.toBitVec_add,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, show (UInt64.ofNat 0).toBitVec = 0#64 from rfl,
        show (p : UInt64) → p.toBitVec = p.toBitVec from fun _ => rfl] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by simp [cs0]) (by simp [cs0]) (by simp [cs0]))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩)

example (z' : RegZmms) (f : StatusFlags) := runs (Int.toBytes 8 7) (by decide) 31 (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) := runs (Int.toBytes 8 (2 ^ 64 - 1)) (by decide) 0 (by decide) z' f

end NonEmptyPrefix

end Prysm.Checkpoint.Witness.EncodeRejectLength
