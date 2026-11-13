import Runtime.Contracts
import Machine.Frame
import Machine.Bytes
import Machine.Labels
import Prysm.ElfData.PrysmTarget
import Prysm.Checkpoint.Code
import Prysm.BeaconBlockHeader.Code
import Prysm.Deposit_Data.Code

/-!
# Independent hand STATEMENTS of the two accept theorems (hold-out; statements only, no proof): the `PendingPartialWithdrawal` part

The declarations of the other types of this group are in `Prysm/Deposit_Data/Statements.lean`.
-/

open Machine Runtime Prysm.Deposit_Data.Code
variable [Host]

namespace Prysm.PendingPartialWithdrawal

/-- Hand statement of the accept path of `(*v1alpha1.PendingPartialWithdrawal).UnmarshalSSZ`: on a 24-byte
input it returns nil and the receiver holds Index = buf[0:8], Amount = buf[8:16], WithdrawableEpoch =
buf[16:24]; input, `state`, the spills, the caller's frame `R` and the stack guard are unchanged. The two
delegated fields go through the callees' code (`Prysm.ValidatorIndex.Code.unmarshalSSZ`, `Prysm.Epoch.Code.unmarshalSSZ` placed in the host). -/
abbrev Decode.accept_statement : Prop :=
  ∀ (k : Nat) (hk : Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.PendingPartialWithdrawal.Code.unmarshalSSZ k)
    (kV : Nat) (hkV : Prysm.ValidatorIndex.Code.unmarshalSSZ.IsInfixAt Host.prog kV) (hfV : LabelsFresh Prysm.ValidatorIndex.Code.unmarshalSSZ kV)
    (kE : Nat) (hkE : Prysm.Epoch.Code.unmarshalSSZ.IsInfixAt Host.prog kE) (hfE : LabelsFresh Prysm.Epoch.Code.unmarshalSSZ kE)
    (in0 in1 in2 : List UInt8) (hin0 : in0.length = 8) (hin1 : in1.length = 8) (hin2 : in2.length = 8)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 sp1 rslot lo ast a8 a16 a24 : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h4 : s4.length = 8)
    (hsp1 : sp1.length = 8) (hrs : rslot.length = 8) (hlo : lo.length = 8)
    (hast : ast.length = 8) (ha8 : a8.length = 8) (ha16 : a16.length = 8) (ha24 : a24.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq (sp1.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (in0.At s.regs.rbx.toBitVec) ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 8))
      ⋆ Eq (in2.At (s.regs.rbx.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (a8.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (a16.At (s.regs.rax.toBitVec + 16)) ⋆ Eq (a24.At (s.regs.rax.toBitVec + 24)) ⋆ R)
    (hguard : guard.toNat + 88 < s.regs.rsp.toNat) (hlen : s.regs.rcx = 24),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (sp1' lo' : List UInt8), sp1'.length = 8 ∧ lo'.length = 8 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (sp1'.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 60)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (in0.At s.regs.rbx.toBitVec) ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq (in2.At (s.regs.rbx.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (in0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (in1.At (s.regs.rax.toBitVec + 16)) ⋆ Eq (in2.At (s.regs.rax.toBitVec + 24)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

end Prysm.PendingPartialWithdrawal
