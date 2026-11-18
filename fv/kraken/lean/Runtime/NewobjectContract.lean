import Runtime.Contracts
import Machine.Frame

/-!
# The contract form of `runtime.newobject`

`NewobjectContract Heap ty sz S` is the hypothesis about the code at the label `runtime.newobject`, in the form of
`MakesliceContract` (`Runtime/Contracts.lean`).
-/

open Machine Runtime
variable [Host]

/-- `runtime.newobject(typ *_type) unsafe.Pointer`: like `MakesliceContract` for one
object of `sz` bytes (zeroed, carved from the heap); the spill area is the
8-byte slot of its one register argument; r14 and rbp are kept. -/
def _root_.Runtime.NewobjectContract (Heap : Nat → DataMem → Prop) (ty : BitVec 64) (sz S : Nat) : Prop :=
  ∀ (st : MachineData) (ret : Int64) (avail : Nat) (stk spill : List UInt8) (F : DataMem → Prop),
    st.regs.rax.toBitVec = ty → sz ≤ avail → stk.length = S → spill.length = 8 →
    (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
      ⋆ Eq (stk.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (spill.At (st.regs.rsp.toBitVec + 8))
      ⋆ Heap avail ⋆ F) st.dmem →
    Eventually (step1 Host.exe)
      (fun st' => st'.pc = ret ∧ st'.data.regs.rsp = st.regs.rsp + 8 ∧ st'.data.regs.r14 = st.regs.r14
        ∧ st'.data.regs.rbp = st.regs.rbp ∧
        ∃ stk' spill' : List UInt8, stk'.length = S ∧ spill'.length = 8 ∧
        (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
          ⋆ Eq (stk'.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (spill'.At (st.regs.rsp.toBitVec + 8))
          ⋆ Eq ((List.replicate sz 0).At st'.data.regs.rax.toBitVec)
          ⋆ Heap (avail - sz) ⋆ F) st'.data.dmem)
      ⟨st, label "runtime.newobject"⟩
