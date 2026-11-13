import Prysm.DataColumnsByRootIdentifier.DecodeRejectSize
import Machine.WitnessHost
import Runtime.CopyModel

/-!
# Witnesses of the decoder size reject and offset reject

The text of `Prysm/Checkpoint/WitnessEncodeRejectLength.lean` with this host and layout. Host: the error label (index 0) and the real Go 1.26.10
`(*v1alpha1.DataColumnsByRootIdentifier).UnmarshalSSZ` (index 1). Memory at `0x10000`: the two error words (stand-in
values: the real ones are set by the runtime's init), the guard word (r14 = 0x10000), the stack window rsp − 8 …
rsp + 24 (rsp = 0x10020); the offset reject adds the 4 offset bytes at buf + 32 (0x10038). Frame `R`: the rax spill slot.
-/

open Machine Runtime TestTarget Machine.Witness Prysm.DataColumnsByRootIdentifier.Code

namespace Prysm.DataColumnsByRootIdentifier.Witness.DecodeRejectSize

abbrev z (k : Nat) : List UInt8 := List.replicate k 0
abbrev bw (v : BitVec 64) : List UInt8 := Int.toBytes 8 v.toInt

namespace RejectSize

def P : Program := [.label "ssz.ErrSize"] ++ unmarshalSSZ

theorem P_len : P.length = 230 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem hk1 : unmarshalSSZ.IsInfixAt Host.prog 1 := infixAt_of [.label "ssz.ErrSize"] [] (by simp [Host.prog, mkHost, P]) rfl
theorem hf1 : LabelsFresh unmarshalSSZ 1 := labelsFresh_of (by decide)

theorem label_es : label "ssz.ErrSize" = 0x10000 :=
  mk_label P _ 0 _ (by simp [P]) (by simp [labs])

/-- error words · guard · fp · return address · spill rax · spill rbx. -/
def block : List UInt8 := bw 0x10e8 ++ (bw 0x2b ++ (bw 0 ++ (z 8 ++ (bw 0 ++ (z 8 ++ z 8)))))

def cs0 (L : Nat) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10018, 0x20000, UInt64.ofNat L, 0, 0, 0, 0x10020, 0, 0, 0, 0, 0, 0, 0, 0x10000, 0⟩, zmms, flags,
    block.At (0x10000 : BitVec 64)⟩

/-- **Non-vacuity of `Decode.reject_size`** for every `len < 36`. -/
theorem runs (L : Nat) (hL : L < 36) (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0x10e8 ∧ st.data.regs.rbx = 0x2b)
      ⟨cs0 L zmms flags, Host.addrOf 1⟩ :=
  eventually_mono (Decode.reject_size 1 hk1 hf1 (cs0 L zmms flags) 0 0 0x10e8 0x2b (z 8) (z 8) rfl rfl
    (Eq ((z 8).At (0x10028 : BitVec 64)))
    (by
      have H : Eq (block.At (0x10000 : BitVec 64)) (block.At (0x10000 : BitVec 64)) := rfl
      wit_split
      simp only [cs0, bw, ElfData.CheckpointAndEpoch.e2eErrSize_addr, label_es, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat,
        Int64.toBitVec_add, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub,
        show (UInt64.ofNat 0).toBitVec = 0#64 from rfl] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by show (0 : UInt64).toNat + 16 < (0x10020 : UInt64).toNat; decide)
    (by show (UInt64.ofNat L).toNat < 36; rw [UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)]; exact hL))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

example (z' : RegZmms) (f : StatusFlags) := runs 0 (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) := runs 35 (by decide) z' f

end RejectSize

namespace RejectOffset

def P : Program := [.label "ssz.ErrInvalidVariableOffset"] ++ unmarshalSSZ

theorem P_len : P.length = 230 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem hk1 : unmarshalSSZ.IsInfixAt Host.prog 1 :=
  infixAt_of [.label "ssz.ErrInvalidVariableOffset"] [] (by simp [Host.prog, mkHost, P]) rfl
theorem hf1 : LabelsFresh unmarshalSSZ 1 := labelsFresh_of (by decide)

theorem label_eo : label "ssz.ErrInvalidVariableOffset" = 0x10000 :=
  mk_label P _ 0 _ (by simp [P]) (by simp [labs])

/-- error words · guard · fp · return address · spill rax · spill rbx · the offset bytes at buf + 32. -/
def block (off : List UInt8) : List UInt8 :=
  bw 0x10e8 ++ (bw 0x2b ++ (bw 0 ++ (z 8 ++ (bw 0 ++ (z 8 ++ (z 8 ++ off))))))

def cs0 (L : Nat) (off : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10018, 0x10018, UInt64.ofNat L, 0, 0, 0, 0x10020, 0, 0, 0, 0, 0, 0, 0, 0x10000, 0⟩, zmms, flags,
    (block off).At (0x10000 : BitVec 64)⟩

/-- **Non-vacuity of `Decode.reject_offset`** for every `len ≥ 36` below 2^63 and every 4-byte offset ≠ 36. -/
theorem runs (L : Nat) (hL : 36 ≤ L) (hL' : L < 2 ^ 63) (off : List UInt8) (hoff4 : off.length = 4)
    (hoff : off ≠ offsetBytes) (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0x10e8 ∧ st.data.regs.rbx = 0x2b)
      ⟨cs0 L off zmms flags, Host.addrOf 1⟩ :=
  eventually_mono (Decode.reject_offset 1 hk1 hf1 (cs0 L off zmms flags) 0 0 0x10e8 0x2b (z 8) (z 8) rfl rfl
    off hoff4 hoff (Eq ((z 8).At (0x10028 : BitVec 64)))
    (by
      have H : Eq ((block off).At (0x10000 : BitVec 64)) ((block off).At (0x10000 : BitVec 64)) := rfl
      wit_split [hoff4]
      simp only [cs0, bw, ElfData.IndexedAttestation.lvErrInvalidVariableOffset_addr, label_eo, UInt64.toBitVec_ofNat,
        Int64.toBitVec_ofNat, Int64.toBitVec_add, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub,
        show (UInt64.ofNat 0).toBitVec = 0#64 from rfl] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by show (0 : UInt64).toNat + 16 < (0x10020 : UInt64).toNat; decide)
    (by show 36 ≤ (UInt64.ofNat L).toNat; rw [UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)]; exact hL))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

example (z' : RegZmms) (f : StatusFlags) := runs 36 (by decide) (by decide) [0, 0, 0, 0] rfl (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) := runs 1060 (by decide) (by decide) [0x25, 0, 0, 0] rfl (by decide) z' f

end RejectOffset

end Prysm.DataColumnsByRootIdentifier.Witness.DecodeRejectSize
