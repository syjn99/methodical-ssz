import Prysm.Checkpoint.DecodeRejectSize
import Runtime.CopyModel
import Machine.WitnessHost

/-!
# Witness of `Decode.reject_size`

Host: the label `ssz.ErrSize` (index 0), then the real Go 1.26.10
`(*v1alpha1.Checkpoint).UnmarshalSSZ` (index 1). Memory at `0x10000`: the two
words of `ssz.ErrSize` after package init (a non-zero itab word `0x10e8` and a
data word `0x2a`, stand-ins: the real values are set by the runtime's init and
are not read from the ELF), the guard word, saved-rbp slot, return slot, the
unused rax spill slot (the frame `R`) and the rbx spill slot. For every length
`≠ 40` (instances 39, 41, 0) the decoder returns the two words.
-/

open Machine Runtime Machine.Witness Prysm.Checkpoint.Code

namespace Prysm.Checkpoint.Witness.DecodeRejectSize

set_option maxRecDepth 100000

def program : Program := [.label "ssz.ErrSize"] ++ unmarshalSSZ

theorem program_length : program.length = 109 := by rfl

instance host : Host := mkHost program (by rw [program_length]; decide)

theorem placed_at_1 : unmarshalSSZ.IsInfixAt Host.prog 1 := infixAt_of [.label "ssz.ErrSize"] [] (by simp [Host.prog, mkHost, program]) rfl

theorem labels_fresh_at_1 : LabelsFresh unmarshalSSZ 1 := labelsFresh_of (by decide)

theorem label_err_size : label "ssz.ErrSize" = 0x10000 :=
  mk_label program _ 0 _ (by simp [program]) (by simp [programLabels])

abbrev zeros (k : Nat) : List UInt8 := List.replicate k 0
abbrev word_bytes (v : UInt64) : List UInt8 := Int.toBytes 8 v.toBitVec.toInt

/-- ErrSize word 0 · word 1 · guard (r14 = 0x10000) · saved rbp · return slot (rsp = 0x10020) · spill rax · spill rbx. -/
def block : List UInt8 := word_bytes 0x10e8 ++ (word_bytes 0x2a ++ (word_bytes 0 ++ (zeros 8 ++ (word_bytes 0 ++ (zeros 8 ++ zeros 8)))))

def mem : DataMem := block.At (0x10000 : BitVec 64)

def initial_state (len : UInt64) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10100, 0x10200, len, 0, 0, 0, 0x10020, 0, 0, 0, 0, 0, 0, 0, 0x10000, 0⟩, zmms, flags, mem⟩

def frame_rest : DataMem → Prop := Eq ((zeros 8).At (0x10028 : BitVec 64))

set_option maxHeartbeats 4000000 in
/-- **Non-vacuity of `Decode.reject_size`.** -/
theorem runs (len : UInt64) (hlen : len ≠ 40) (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0x10e8
        ∧ st.data.regs.rbx = 0x2a)
      ⟨initial_state len zmms flags, Host.addrOf 1⟩ :=
  eventually_mono (Decode.reject_size 1 placed_at_1 labels_fresh_at_1 (initial_state len zmms flags) 0 0 0x10e8 0x2a (zeros 8) (zeros 8) rfl rfl frame_rest
    (by
      have H : Eq (block.At (0x10000 : BitVec 64)) mem := rfl
      witness_split []
      simp only [initial_state, frame_rest, word_bytes, ElfData.PrysmTarget.sszErrSize_addr, label_err_size, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat,
        Int64.toBitVec_add, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by simp [initial_state]) hlen)
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

example (z' : RegZmms) (f : StatusFlags) := runs 39 (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) := runs 41 (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) := runs 0 (by decide) z' f

end Prysm.Checkpoint.Witness.DecodeRejectSize
