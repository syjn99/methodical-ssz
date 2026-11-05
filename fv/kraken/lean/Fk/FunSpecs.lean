import Fk.ScSpec
import Fk.Contracts

/-!
# Function specifications for composition (C20)

A caller (Nested, ListC) uses each callee through a specification of the same
shape as a runtime contract: a hypothesis about the code at the callee's label,
for every machine state, return address and frame `F`. For our own callees the
specification is not assumed: it is derived from the machine theorem
(`sc_uacc_holds`). For runtime callees it is a contract (`NewobjectC`).

`ScUAccC`: Scalars.UnmarshalSSZ, accept path, on the Go encoding of `g`
(`scField g i` at the input), receiver chunks `c_i` of the widths it writes.
It returns nil with rsp + 8, the receiver = `scField g i`, the input, the
return slot and `F` kept, and the argument spill slot (rsp + 16) = rbx.
-/

open Fk Fk.Code Fv1
variable [Host]

namespace Fk

/-- `runtime.newobject(typ *_type) unsafe.Pointer`: like `MakesliceC` for one
object of `sz` bytes (zeroed, carved from the heap). -/
def NewobjectC (Heap : Nat → DataMem → Prop) (ty : BitVec 64) (sz S : Nat) : Prop :=
  ∀ (st : MachineData) (ret : Int64) (avail : Nat) (stk : List UInt8) (F : DataMem → Prop),
    st.regs.rax.toBitVec = ty → sz ≤ avail → stk.length = S →
    (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
      ⋆ Eq (stk.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Heap avail ⋆ F) st.dmem →
    Eventually (step1 Host.exe)
      (fun st' => st'.pc = ret ∧ st'.data.regs.rsp = st.regs.rsp + 8 ∧
        ∃ stk' : List UInt8, stk'.length = S ∧
        (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
          ⋆ Eq (stk'.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S))
          ⋆ Eq ((List.replicate sz 0).At st'.data.regs.rax.toBitVec)
          ⋆ Heap (avail - sz) ⋆ F) st'.data.dmem)
      ⟨st, label "runtime.newobject"⟩

def ScUAccC : Prop :=
  ∀ (st : MachineData) (ret : Int64) (g : Scalars) (slot c0 c1 c2 c3 c4 : List UInt8) (F : DataMem → Prop),
    slot.length = 8 → c0.length = 1 → c1.length = 2 → c2.length = 4 → c3.length = 8 → c4.length = 1 →
    st.regs.rcx = 16 →
    (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
      ⋆ Eq (slot.At (st.regs.rsp.toBitVec + 16))
      ⋆ Eq ((scField g 0).At st.regs.rbx.toBitVec) ⋆ Eq ((scField g 1).At (st.regs.rbx.toBitVec + 1))
      ⋆ Eq ((scField g 2).At (st.regs.rbx.toBitVec + 3)) ⋆ Eq ((scField g 3).At (st.regs.rbx.toBitVec + 7))
      ⋆ Eq ((scField g 4).At (st.regs.rbx.toBitVec + 15))
      ⋆ Eq (c0.At st.regs.rax.toBitVec) ⋆ Eq (c1.At (st.regs.rax.toBitVec + 2))
      ⋆ Eq (c2.At (st.regs.rax.toBitVec + 4)) ⋆ Eq (c3.At (st.regs.rax.toBitVec + 8))
      ⋆ Eq (c4.At (st.regs.rax.toBitVec + 16)) ⋆ F) st.dmem →
    Eventually (step1 Host.exe)
      (fun st' => st'.pc = ret ∧ st'.data.regs.rax = 0 ∧ st'.data.regs.rbx = 0
        ∧ st'.data.regs.rsp = st.regs.rsp + 8
        ∧ (Eq ((scField g 0).At st.regs.rax.toBitVec) ⋆ Eq ((scField g 1).At (st.regs.rax.toBitVec + 2))
          ⋆ Eq ((scField g 2).At (st.regs.rax.toBitVec + 4)) ⋆ Eq ((scField g 3).At (st.regs.rax.toBitVec + 8))
          ⋆ Eq ((scField g 4).At (st.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 st.regs.rbx.toBitVec.toInt).At (st.regs.rsp.toBitVec + 16))
          ⋆ Eq ((scField g 0).At st.regs.rbx.toBitVec) ⋆ Eq ((scField g 1).At (st.regs.rbx.toBitVec + 1))
          ⋆ Eq ((scField g 2).At (st.regs.rbx.toBitVec + 3)) ⋆ Eq ((scField g 3).At (st.regs.rbx.toBitVec + 7))
          ⋆ Eq ((scField g 4).At (st.regs.rbx.toBitVec + 15)) ⋆ F) st'.data.dmem)
      ⟨st, label "target.Scalars.UnmarshalSSZ"⟩

/-- The Scalars machine code satisfies its specification (no assumption). -/
theorem sc_uacc_holds (k : Nat) (hk : ScalarsUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh ScalarsUnmarshalSSZ k) : ScUAccC := by
  intro st ret g slot c0 c1 c2 c3 c4 F hsl g0 g1 g2 g3 g4 hlen hm
  rw [label_at hk hf (j := 0) (by rfl) (by intro i hi; omega)]
  have h := sc_accept_main k hk st (UInt64.ofBitVec ret.toBitVec) slot (scField g 0) (scField g 1) (scField g 2)
    (scField g 3) (scField g 4) c0 c1 c2 c3 c4 hsl (by simp [scField, Fv.uintBytes_size])
    (by simp [scField, Fv.uintBytes_size]) (by simp [scField, Fv.uintBytes_size])
    (by simp [scField, Fv.uintBytes_size]) rfl g0 g1 g2 g3 g4 F hm
    (fun i hi h => hf i hi _ h (by simp [ScalarsUnmarshalSSZ]))
    (fun i hi h => hf i hi _ h (by simp [ScalarsUnmarshalSSZ])) hlen (by cases g.e <;> simp [scField])
  simp only [Nat.add_zero] at h
  exact h

end Fk
