import Runtime.Contracts
import Machine.Frame
import Machine.Bytes
import Machine.Labels
import Prysm.ElfData.PrysmTarget
import Prysm.Checkpoint.Code
import Codec.Kind.EncodeFastPathAnyFrame
import Prysm.BuilderDepositRequest.Code

/-!
# Independent hand STATEMENTS of two decoder accept paths and two encoder fast paths with a: the `WithdrawalRequest` part

The declarations of the other types of this group are in `Prysm/BuilderExitRequest/Statements.lean`.
-/

open Machine Runtime Prysm.Checkpoint.Code Prysm.BuilderExitRequest.Code
variable [Host]

open Codec
namespace Prysm.WithdrawalRequest

/-- Hand statement of the accept path of `(*v1.WithdrawalRequest).UnmarshalSSZ`: on a 76-byte input it returns nil
and the receiver holds fresh SourceAddress (20) / ValidatorPubkey (48) slices equal to buf[0:20] / buf[20:68]
(len = cap) and Amount = buf[68:76]; input, `state`, the spills, the caller's frame `R` and the stack guard are
unchanged; 68 heap bytes are used. -/
abbrev Decode.accept_statement : Prop :=
  ∀ (k : Nat) (hk : Prysm.WithdrawalRequest.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.WithdrawalRequest.Code.unmarshalSSZ k)
    (sa pk amt : List UInt8) (hsa : sa.length = 20) (hpk : pk.length = 48) (hamt : amt.length = 8)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 spl l18 rslot lo ast aP1 aL1 aC1 aP2 aL2 aC2 aN : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8)
    (hspl : spl.length = 24) (hl18 : l18.length = 8) (hrs : rslot.length = 8)
    (hast : ast.length = 8)
    (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8)
    (haP2 : aP2.length = 8) (haL2 : aL2.length = 8) (haC2 : aC2.length = 8) (haN : aN.length = 8)
    (R : DataMem → Prop) (S : Nat) (hlo : lo.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (l18.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 48 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (sa.At s.regs.rbx.toBitVec) ⋆ Eq (pk.At (s.regs.rbx.toBitVec + 20))
      ⋆ Eq (amt.At (s.regs.rbx.toBitVec + 68))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 24)) ⋆ Eq (aP2.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (aL2.At (s.regs.rax.toBitVec + 40)) ⋆ Eq (aC2.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq (aN.At (s.regs.rax.toBitVec + 56))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx = 76) (hav : 68 ≤ avail)
    (hms : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 S) (hmm : MemmoveContract S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (p1 p2 : BitVec 64) (spl' lo' : List UInt8), spl'.length = 24 ∧ lo'.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 67)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 48 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 68)
          ⋆ Eq (sa.At s.regs.rbx.toBitVec) ⋆ Eq (pk.At (s.regs.rbx.toBitVec + 20))
          ⋆ Eq (amt.At (s.regs.rbx.toBitVec + 68))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 16)) ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 40)) ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (amt.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (sa.At p1) ⋆ Eq (pk.At p2)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

end Prysm.WithdrawalRequest
