import Prysm.BuilderDepositRequest.GeneratedDecodeAccept
import Runtime.CopyModel
import Machine.WitnessHost

/-!
# Witness of the generated `Decode.generated_reject` (FLAT24 / H7)

Host: the label `ssz.ErrSize` (index 0), then the real Go 1.26.10 `(*v1.BuilderDepositRequest).UnmarshalSSZ` (index 1).
Written by the FLAT24 evaluator with its evidence script `f24wit.py`: the text of the G5-C reject witnesses
(`WitSaGR.lean`) with the v1.BuilderDepositRequest decoder and the generated size-reject theorem of `Gen5F24BdrDec.lean`. Memory at
`0x10000`: the two words of `ssz.ErrSize` after package init (a non-zero itab word `0x10e8` and a data word `0x2a`,
stand-ins: the real values are set by the runtime's init and are not read from the ELF), the guard word, saved-rbp
slot, return slot, the unused rax spill slot (the frame `R`) and the rbx spill slot. For every length `≠ 184`
(instances 183, 185, 0) the decoder returns the two words.
-/

open Machine Runtime Machine.Witness Prysm.BuilderDepositRequest.Code

open Codec
namespace Prysm.BuilderDepositRequest.Witness.GeneratedDecodeRejectSize

set_option maxRecDepth 100000

def P : Program := [.label "ssz.ErrSize"] ++ unmarshalSSZ

theorem P_len : P.length = 144 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem hk1 : unmarshalSSZ.IsInfixAt Host.prog 1 := infixAt_of [.label "ssz.ErrSize"] [] (by simp [Host.prog, mkHost, P]) rfl

theorem hf1 : LabelsFresh unmarshalSSZ 1 := labelsFresh_of (by decide)

theorem label_err : label "ssz.ErrSize" = 0x10000 :=
  mk_label P _ 0 _ (by simp [P]) (by simp [labs])

abbrev z (k : Nat) : List UInt8 := List.replicate k 0
abbrev w (v : UInt64) : List UInt8 := Int.toBytes 8 v.toBitVec.toInt

/-- ErrSize word 0 · word 1 · guard (r14 = 0x10000) · saved rbp · return slot (rsp = 0x10020) · spill rax · spill rbx. -/
def block : List UInt8 := w 0x10e8 ++ (w 0x2a ++ (w 0 ++ (z 8 ++ (w 0 ++ (z 8 ++ z 8)))))

def mem : DataMem := block.At (0x10000 : BitVec 64)

def cs0 (len : UInt64) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10100, 0x10200, len, 0, 0, 0, 0x10020, 0, 0, 0, 0, 0, 0, 0, 0x10000, 0⟩, zmms, flags, mem⟩

def R0 : DataMem → Prop := Eq ((z 8).At (0x10028 : BitVec 64))

set_option maxHeartbeats 4000000 in
/-- **Non-vacuity of the generated `Decode.generated_reject`.** -/
theorem runs (len : UInt64) (hlen : len ≠ 184) (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0x10e8
        ∧ st.data.regs.rbx = 0x2a)
      ⟨cs0 len zmms flags, Host.addrOf 1⟩ :=
  eventually_mono (Prysm.BuilderDepositRequest.Decode.generated_reject 1 hk1 hf1 (cs0 len zmms flags) 0 0 0x10e8 0x2a (z 8) (z 8) rfl rfl R0
    (by
      have H : Eq (block.At (0x10000 : BitVec 64)) mem := rfl
      wit_split []
      simp only [cs0, R0, w, ElfData.CheckpointAndEpoch.e2eErrSize_addr, label_err, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat,
        Int64.toBitVec_add, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by simp [cs0]) hlen)
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

example (z' : RegZmms) (f : StatusFlags) := runs 183 (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) := runs 185 (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) := runs 0 (by decide) z' f

end Prysm.BuilderDepositRequest.Witness.GeneratedDecodeRejectSize
