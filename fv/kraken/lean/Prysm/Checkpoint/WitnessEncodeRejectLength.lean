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

def program : Program := [.label "ssz.ErrBytesLength"] ++ marshalSSZTo

theorem program_length : program.length = 92 := by rfl

instance host : Host := mkHost program (by rw [program_length]; decide)

theorem placed_at_1 : marshalSSZTo.IsInfixAt Host.prog 1 := infixAt_of [.label "ssz.ErrBytesLength"] [] (by simp [Host.prog, mkHost, program]) rfl
theorem labels_fresh_at_1 : LabelsFresh marshalSSZTo 1 := labelsFresh_of (by decide)

theorem label_err_bytes_length : label "ssz.ErrBytesLength" = 0x10000 :=
  mk_label program _ 0 _ (by simp [program]) (by simp [labs])

abbrev zeros (k : Nat) : List UInt8 := List.replicate k 0
abbrev word_bytes (v : UInt64) : List UInt8 := Int.toBytes 8 v.toBitVec.toInt

/-- ErrBytesLength words · guard · receiver (state, Epoch, Root ptr/len/cap, tail) · t40 · t30 · gap (24) · fp ·
return slot · spill rax · spill rbx · dst (48). -/
def block (e8 : List UInt8) (rl : UInt64) : List UInt8 :=
  word_bytes 0x10e8 ++ (word_bytes 0x2b ++ (word_bytes 0 ++ (zeros 8 ++ (e8 ++ (word_bytes 0x5000 ++ (word_bytes rl ++ (word_bytes 48 ++ (zeros 32 ++ (zeros 16 ++ (zeros 16 ++ (zeros 24
    ++ (zeros 8 ++ (word_bytes 0 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ zeros 40))))))))))))))))

def mem (e8 : List UInt8) (rl : UInt64) : DataMem := (block e8 rl).At (0x10000 : BitVec 64)

def initial_state (e8 : List UInt8) (rl : UInt64) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10018, 0x100b8, 0, 0, 0, 48, 0x100a0, 0, 0, 0, 0, 0, 0, 0, 0x10000, 0⟩, zmms, flags, mem e8 rl⟩

set_option maxHeartbeats 16000000 in
/-- **Non-vacuity of `Encode.reject_length`.** -/
theorem runs (e8 : List UInt8) (he8 : e8.length = 8) (rl : UInt64) (hrl : rl ≠ 32)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rcx = 0 ∧ st.data.regs.rdi = 0x10e8 ∧ st.data.regs.rsi = 0x2b)
      ⟨initial_state e8 rl zmms flags, Host.addrOf 1⟩ :=
  eventually_mono (Encode.reject_length 1 placed_at_1 labels_fresh_at_1 (zeros 8) e8 (word_bytes 48) (zeros 32) [] (zeros 8) rfl he8 rfl rfl rfl 0x5000 rl hrl
    (initial_state e8 rl zmms flags) 0 0 0x10e8 0x2b rfl (zeros 8) (zeros 8) (zeros 16) (zeros 16) rfl rfl rfl rfl
    (Eq ((zeros 24).At (0x10080 : BitVec 64)) ⋆ Eq ((zeros 8).At (0x100a8 : BitVec 64)) ⋆ Eq ((zeros 40).At (0x100c0 : BitVec 64)))
    (by
      have H : Eq ((block e8 rl).At (0x10000 : BitVec 64)) (mem e8 rl) := rfl
      witness_split [he8]
      simp only [initial_state, word_bytes, ElfData.PrysmTarget.sszErrBytesLength_addr, label_err_bytes_length, nil_At_emp, Std.ExtHashMap.sep_emp,
        Std.ExtHashMap.emp_sep, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, Int64.toBitVec_add,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, show (UInt64.ofNat 0).toBitVec = 0#64 from rfl,
        show (p : UInt64) → p.toBitVec = p.toBitVec from fun _ => rfl] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by simp [initial_state]) (by simp [initial_state]) (by simp [initial_state]))
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
  word_bytes 0x10e8 ++ (word_bytes 0x2b ++ (word_bytes 0 ++ (zeros 8 ++ (e8 ++ (word_bytes 0x5000 ++ (word_bytes rl ++ (word_bytes 48 ++ (zeros 32 ++ (zeros 16 ++ (zeros 16 ++ (zeros 24
    ++ (zeros 8 ++ (word_bytes 0 ++ (zeros 8 ++ (zeros 8 ++ (pre5 ++ (zeros 8 ++ zeros 35)))))))))))))))))

def mem (e8 : List UInt8) (rl : UInt64) : DataMem := (block e8 rl).At (0x10000 : BitVec 64)

def initial_state (e8 : List UInt8) (rl : UInt64) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10018, 0x100b8, 5, 0, 0, 48, 0x100a0, 0, 0, 0, 0, 0, 0, 0, 0x10000, 0⟩, zmms, flags, mem e8 rl⟩

set_option maxHeartbeats 16000000 in
/-- **Non-vacuity of `Encode.reject_length`** with a 5-byte prefix. -/
theorem runs (e8 : List UInt8) (he8 : e8.length = 8) (rl : UInt64) (hrl : rl ≠ 32)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rcx = 0 ∧ st.data.regs.rdi = 0x10e8 ∧ st.data.regs.rsi = 0x2b)
      ⟨initial_state e8 rl zmms flags, Host.addrOf 1⟩ :=
  eventually_mono (Encode.reject_length 1 placed_at_1 labels_fresh_at_1 (zeros 8) e8 (word_bytes 48) (zeros 32) pre5 (zeros 8) rfl he8 rfl rfl rfl 0x5000 rl
    hrl (initial_state e8 rl zmms flags) 0 0 0x10e8 0x2b rfl (zeros 8) (zeros 8) (zeros 16) (zeros 16) rfl rfl rfl rfl
    (Eq ((zeros 24).At (0x10080 : BitVec 64)) ⋆ Eq ((zeros 8).At (0x100a8 : BitVec 64)) ⋆ Eq ((zeros 35).At (0x100c5 : BitVec 64)))
    (by
      have H : Eq ((block e8 rl).At (0x10000 : BitVec 64)) (mem e8 rl) := rfl
      witness_split [he8, show pre5.length = 5 from rfl]
      simp only [initial_state, word_bytes, ElfData.PrysmTarget.sszErrBytesLength_addr, label_err_bytes_length, nil_At_emp, Std.ExtHashMap.sep_emp,
        Std.ExtHashMap.emp_sep, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, Int64.toBitVec_add,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, show (UInt64.ofNat 0).toBitVec = 0#64 from rfl,
        show (p : UInt64) → p.toBitVec = p.toBitVec from fun _ => rfl] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by simp [initial_state]) (by simp [initial_state]) (by simp [initial_state]))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩)

example (z' : RegZmms) (f : StatusFlags) := runs (Int.toBytes 8 7) (by decide) 31 (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) := runs (Int.toBytes 8 (2 ^ 64 - 1)) (by decide) 0 (by decide) z' f

end NonEmptyPrefix

end Prysm.Checkpoint.Witness.EncodeRejectLength
