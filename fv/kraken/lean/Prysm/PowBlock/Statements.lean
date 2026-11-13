import Runtime.Contracts
import Machine.Frame
import Machine.Bytes
import Machine.Labels
import Prysm.ElfData.PrysmTarget
import Prysm.Checkpoint.Code
import Prysm.AttestationData.Code
import Prysm.PendingDeposit.Code

/-!
# Independent hand STATEMENTS of the two accept theorems (hold-out; statements only, no proof): the `PowBlock` part

The declarations of the other types of this group are in `Prysm/PendingDeposit/Statements.lean`.
-/

open Machine Runtime Prysm.AttestationData.Code Prysm.PendingDeposit.Code
variable [Host]

namespace Prysm.PowBlock

/-- Hand statement of the accept path of `(*v1alpha1.PowBlock).UnmarshalSSZ`: on a 96-byte input it returns nil
and the receiver holds fresh BlockHash / ParentHash / TotalDifficulty slices equal to buf[0:32] / buf[32:64] /
buf[64:96] (len = cap = 32); input, the spills, the caller's frame `R` and the stack guard are unchanged; 96 heap
bytes are used. -/
abbrev Decode.accept_statement : Prop :=
  ∀ (k : Nat) (hk : Prysm.PowBlock.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.PowBlock.Code.unmarshalSSZ k)
    (bh ph td : List UInt8) (hbh : bh.length = 32) (hph : ph.length = 32) (htd : td.length = 32)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 spl l18 rslot lo aP1 aL1 aC1 aP2 aL2 aC2 aP3 aL3 aC3 : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8)
    (hspl : spl.length = 24) (hl18 : l18.length = 8) (hrs : rslot.length = 8)
    (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8)
    (haP2 : aP2.length = 8) (haL2 : aL2.length = 8) (haC2 : aC2.length = 8)
    (haP3 : aP3.length = 8) (haL3 : aL3.length = 8) (haC3 : aC3.length = 8)
    (R : DataMem → Prop) (S : Nat) (hlo : lo.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (l18.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 48 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (bh.At s.regs.rbx.toBitVec) ⋆ Eq (ph.At (s.regs.rbx.toBitVec + 32))
      ⋆ Eq (td.At (s.regs.rbx.toBitVec + 64))
      ⋆ Eq (aP1.At s.regs.rax.toBitVec) ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 16)) ⋆ Eq (aP2.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (aL2.At (s.regs.rax.toBitVec + 32)) ⋆ Eq (aC2.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (aP3.At (s.regs.rax.toBitVec + 48)) ⋆ Eq (aL3.At (s.regs.rax.toBitVec + 56))
      ⋆ Eq (aC3.At (s.regs.rax.toBitVec + 64))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx = 96) (hav : 96 ≤ avail)
    (hms : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 S) (hmm : MemmoveContract S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (p1 p2 p3 : BitVec 64) (spl' lo' : List UInt8), spl'.length = 24 ∧ lo'.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 104)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 48 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 96)
          ⋆ Eq (bh.At s.regs.rbx.toBitVec) ⋆ Eq (ph.At (s.regs.rbx.toBitVec + 32))
          ⋆ Eq (td.At (s.regs.rbx.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 8)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 56)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (bh.At p1) ⋆ Eq (ph.At p2) ⋆ Eq (td.At p3)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

end Prysm.PowBlock
