import Prysm.ValidatorIndex.GeneratedDecodeAccept

/-!
# `Decode.accept_function_spec`: function specification of `(*primitives.ValidatorIndex).UnmarshalSSZ`, accept path

Hand-written (not generator output). The text of `Prysm.CommitteeIndex.Decode.accept_function_spec` with the
label `Prysm.CommitteeIndex.Code.unmarshalSSZLabel` replaced by `Prysm.ValidatorIndex.Code.unmarshalLabel`. `Decode.accept_function_spec_holds` proves it from the generated machine
theorem `Prysm.ValidatorIndex.Decode.generated_accept` (the proof text of `Prysm.CommitteeIndex.Decode.accept_function_spec_holds`). The
BeaconBlockHeader decoder uses the callee only through this specification (no contract).
-/

open Machine Runtime Prysm.ValidatorIndex.Code
variable [Host]

open Codec
namespace Prysm.ValidatorIndex

/-- **Function specification of `(*primitives.ValidatorIndex).UnmarshalSSZ`, accept path** (`len(buf) = 8`). -/
def Decode.accept_function_spec : Prop :=
  ∀ (st : MachineData) (ret : Int64) (e8 fp s2 c0 : List UInt8) (guard : UInt64) (F : DataMem → Prop),
    e8.length = 8 → fp.length = 8 → s2.length = 8 → c0.length = 8 →
    st.regs.rcx = 8 → guard.toNat < st.regs.rsp.toNat →
    (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (st.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (st.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (st.regs.r14.toBitVec + 16))
      ⋆ Eq (e8.At st.regs.rbx.toBitVec) ⋆ Eq (c0.At st.regs.rax.toBitVec) ⋆ F) st.dmem →
    Eventually (step1 Host.exe)
      (fun st' => st'.pc = ret ∧ st'.data.regs.rax = 0 ∧ st'.data.regs.rbx = 0
        ∧ st'.data.regs.rsp = st.regs.rsp + 8 ∧ st'.data.regs.rbp = st.regs.rbp
        ∧ st'.data.regs.r14 = st.regs.r14
        ∧ (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 st.regs.rbp.toBitVec.toInt).At (st.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 st.regs.rbx.toBitVec.toInt).At (st.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (st.regs.r14.toBitVec + 16))
          ⋆ Eq (e8.At st.regs.rbx.toBitVec) ⋆ Eq (e8.At st.regs.rax.toBitVec) ⋆ F) st'.data.dmem)
      ⟨st, label unmarshalLabel⟩

/-- The ValidatorIndex machine code satisfies its specification (no assumption beyond the code's place in
the host and its label freshness). -/
theorem Decode.accept_function_spec_holds (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh unmarshalSSZ k) : Decode.accept_function_spec := by
  intro st ret e8 fp s2 c0 guard F he8 hfp h2 hc0 hlen hguard hm
  rw [show label unmarshalLabel = Host.addrOf (k + 0) from label_at hk hf (j := 0) (by rfl) (by intro i hi; omega)]
  exact Prysm.ValidatorIndex.Decode.generated_accept k hk hf e8 he8 st (UInt64.ofBitVec ret.toBitVec) guard fp s2 c0
    hfp h2 hc0 F hm hguard hlen

end Prysm.ValidatorIndex
