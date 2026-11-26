module

public import Codec.FieldFrame
public import Machine.Labels
public import Machine.Bytes
public import Prysm.ElfData.PrysmTarget

@[expose] public section

/-!
# Size-reject statement kind of a container decoder

`decodeRejectKindAnyFrame C sz` is the statement of the theorems `Prysm.<Type>.Decode.reject_size` with the code
constant and the size as parameters (tie: `Prysm/Checkpoint/DecodeRejectSizeKindTie.lean`).
`decode_reject_segment` (`Codec/DecodeRejectSizeAnyFrame.lean`) is the lemma of the generated proofs.
-/

open Machine Runtime

open Codec
namespace Codec

variable [Host]

set_option linter.unusedVariables false in
/-- **Size-reject statement kind of a container decoder**: with `len(buf) ≠ sz` the decoder returns the two
words `e0`, `e1` of `ssz.ErrSize`; the receiver and the input are not read (they are in `R`). The text is the
statement of the hand theorems `Prysm.<Type>.Decode.reject_size` with the code constant and the size replaced. -/
abbrev decodeRejectKindAnyFrame (C : Program) (sz : UInt64) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp s2 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx ≠ sz),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrSize_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

end Codec
