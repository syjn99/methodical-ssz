import Prysm.IndexedAttestation.DecodeRejectSize
import Runtime.CopyModel
import Machine.WitnessHost

/-!
# Witnesses of `Decode.reject_size` (size reject) and `Decode.reject_offset` (offset reject)

The text of `Prysm/Checkpoint/WitnessDecodeRejectSize.lean`. The premises of the frozen statements `Decode.reject_size_statement` and
`Decode.reject_offset_statement` (`Prysm/IndexedAttestation/Statements.lean`) are satisfiable. Host: the labels `ssz.ErrSize` (index 0, 0x10000) and
`ssz.ErrInvalidVariableOffset` (index 16, 0x10010) with pad labels between, then the real Go 1.26.10
`(*v1alpha1.IndexedAttestation).UnmarshalSSZ` (index 17). (The host of the alignment and overflow rejects, `WitIaR` has neither label.)
Memory at 0x10000: the two words of `ssz.ErrSize` (stand-ins `0x10e8`, `0x2a`: the real values are set by the
runtime's package init), the two words of `ssz.ErrInvalidVariableOffset` (stand-ins `0x10f0`, `0x2b`), the guard
word (r14 = 0x10010), the saved-rbp slot, the return slot (rsp = 0x10030), the caller's word at rsp + 8, the rbx
spill slot and the 4 offset bytes of the input (rbx = 0x10048). The frame `R` holds the chunks that a statement does
not name. Size reject: every len < 228 (instances 0, 227). Offset reject: every len ≥ 228 with offset bytes `e5 00 00 00` ≠ 228
(instances 228, 228 + 8 · 2049).
-/

open Machine Runtime TestTarget Machine.Witness Prysm.IndexedAttestation.Code

namespace Prysm.IndexedAttestation.Witness.DecodeRejectSize

def dataLabels : Program :=
  [.label "ssz.ErrSize", .label "pad1", .label "pad2", .label "pad3", .label "pad4", .label "pad5", .label "pad6",
   .label "pad7", .label "pad8", .label "pad9", .label "pad10", .label "pad11", .label "pad12", .label "pad13",
   .label "pad14", .label "pad15", .label "ssz.ErrInvalidVariableOffset"]

def P : Program := dataLabels ++ unmarshalSSZ

-- Measured cause: `rfl` on the length of the 296-directive program stops with "maximum recursion depth"
-- at the default (512); 1024 passes. The other host facts need no option.
set_option maxRecDepth 1024 in
theorem P_len : P.length = 296 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem prog_eq : Host.prog = P := rfl

theorem hk17 : unmarshalSSZ.IsInfixAt Host.prog 17 :=
  infixAt_of dataLabels [] (by simp [prog_eq, P]) rfl

theorem hf17 : LabelsFresh unmarshalSSZ 17 := labelsFresh_of (by rw [prog_eq]; decide)

theorem label_err : label "ssz.ErrSize" = 0x10000 :=
  mk_label P _ 0 _ (by simp [P, dataLabels]) (by simp [labs])
theorem label_ivo : label "ssz.ErrInvalidVariableOffset" = 0x10010 :=
  mk_label P _ 16 _ (by simp [P, dataLabels]) (by decide)

abbrev z (k : Nat) : List UInt8 := List.replicate k 0
abbrev w (v : UInt64) : List UInt8 := Int.toBytes 8 v.toBitVec.toInt

/-- ErrSize word 0 · word 1 · ErrInvalidVariableOffset word 0 · word 1 · guard · saved rbp · return slot ·
caller word · spill rbx · offset bytes. -/
def block : List UInt8 :=
  w 0x10e8 ++ (w 0x2a ++ (w 0x10f0 ++ (w 0x2b ++ (w 0 ++ (z 8 ++ (w 0 ++ (z 8 ++ (z 8 ++ [0xe5, 0, 0, 0]))))))))

def mem : DataMem := block.At (0x10000 : BitVec 64)

def cs0 (len : UInt64) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10100, 0x10048, len, 0, 0, len, 0x10030, 0, 0, 0, 0, 0, 0, 0, 0x10010, 0⟩, zmms, flags, mem⟩

/-- Size reject frame: the ErrInvalidVariableOffset words, the caller's word and the offset bytes. -/
def R1 : DataMem → Prop :=
  Eq ((w 0x10f0).At (0x10010 : BitVec 64)) ⋆ Eq ((w 0x2b).At (0x10018 : BitVec 64))
    ⋆ Eq ((z 8).At (0x10038 : BitVec 64)) ⋆ Eq (([0xe5, 0, 0, 0] : List UInt8).At (0x10048 : BitVec 64))

/-- Offset reject frame: the ErrSize words and the caller's word. -/
def R2 : DataMem → Prop :=
  Eq ((w 0x10e8).At (0x10000 : BitVec 64)) ⋆ Eq ((w 0x2a).At (0x10008 : BitVec 64))
    ⋆ Eq ((z 8).At (0x10038 : BitVec 64))

/-- **Non-vacuity of `Decode.reject_size` (size reject)** for every len < 228. -/
theorem runs_size (len : UInt64) (hlen : len.toNat < 228) (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0x10e8
        ∧ st.data.regs.rbx = 0x2a)
      ⟨cs0 len zmms flags, Host.addrOf 17⟩ :=
  eventually_mono (Decode.reject_size 17 hk17 hf17 (cs0 len zmms flags) 0 0 0x10e8 0x2a (z 8) (z 8) rfl rfl R1
    (by
      have H : Eq (block.At (0x10000 : BitVec 64)) mem := rfl
      wit_split []
      simp only [cs0, R1, w, ElfData.CheckpointAndEpoch.e2eErrSize_addr, label_err, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat,
        Int64.toBitVec_add, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by show (0 : UInt64).toNat + 48 < (0x10030 : UInt64).toNat; decide) hlen)
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

example (z' : RegZmms) (f : StatusFlags) := runs_size 0 (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) := runs_size 227 (by decide) z' f

/-- **Non-vacuity of `Decode.reject_offset` (offset reject)** for every len ≥ 228 (offset bytes `e5 00 00 00`). -/
theorem runs_offset (len : UInt64) (hlen : 228 ≤ len.toNat) (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0x10f0
        ∧ st.data.regs.rbx = 0x2b)
      ⟨cs0 len zmms flags, Host.addrOf 17⟩ :=
  eventually_mono (Decode.reject_offset 17 hk17 hf17 (cs0 len zmms flags) 0 0 0x10f0 0x2b (z 8) (z 8) rfl rfl
    [0xe5, 0, 0, 0] rfl (by decide) R2
    (by
      have H : Eq (block.At (0x10000 : BitVec 64)) mem := rfl
      wit_split []
      simp only [cs0, R2, w, ElfData.IndexedAttestation.lvErrInvalidVariableOffset_addr, label_ivo, UInt64.toBitVec_ofNat,
        Int64.toBitVec_ofNat, Int64.toBitVec_add, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by show (0 : UInt64).toNat + 48 < (0x10030 : UInt64).toNat; decide) hlen)
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

example (z' : RegZmms) (f : StatusFlags) := runs_offset 228 (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) := runs_offset (228 + 8 * 2049) (by decide) z' f

end Prysm.IndexedAttestation.Witness.DecodeRejectSize
