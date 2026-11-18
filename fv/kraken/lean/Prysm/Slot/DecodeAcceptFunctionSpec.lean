import Prysm.Slot.GeneratedDecodeAccept
import Prysm.Slot.Code

/-!
# `Decode.accept_function_spec`: function specification of `(*primitives.Slot).UnmarshalSSZ`, accept path

Hand-written (not generator output).
`Decode.accept_function_spec_holds` proves it from the generated machine theorem `Prysm.Slot.Decode.generated_accept`.
-/

open Machine
variable [Host]

namespace Prysm.Slot

/-- **Function specification of `(*primitives.Slot).UnmarshalSSZ`, accept path**
(`len(buf) = 8`), in the shape of a runtime contract: a hypothesis-shaped statement
about the code at the Slot label, for every machine state, return address and
frame `F`. `Decode.accept_function_spec_holds` proves it from the machine code; the AttestationData
decoder uses the callee only through this specification (no contract). -/
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
      ⟨st, label Code.unmarshalSSZLabel⟩

/-- The Slot machine code satisfies its specification (no assumption beyond
the code's place in the host and its label freshness). -/
theorem Decode.accept_function_spec_holds (k : Nat) (hk : Code.unmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh Code.unmarshalSSZ k) : Decode.accept_function_spec := by
  intro st ret e8 fp s2 c0 guard F he8 hfp h2 hc0 hlen hguard hm
  rw [show label Code.unmarshalSSZLabel = Host.addrOf (k + 0) from label_at hk hf (j := 0) (by rfl) (by intro i hi; omega)]
  exact Decode.generated_accept k hk hf e8 he8 st (UInt64.ofBitVec ret.toBitVec) guard fp s2 c0 hfp h2 hc0 F hm
    hguard hlen

end Prysm.Slot
