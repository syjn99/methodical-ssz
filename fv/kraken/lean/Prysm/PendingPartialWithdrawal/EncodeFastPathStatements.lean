import Codec.Kind.EncodeFastPathAnyFrame
import Prysm.BlobIdentifier.EncoderCode

/-!
# Independent hand statements of four encoder fast paths: the `PendingPartialWithdrawal` part

The declarations of the other types of this group are in `Prysm/PowBlock/EncodeFastPathStatements.lean`.
-/

open Machine Runtime Codec Prysm.PowBlock.Code
variable [Host]

namespace Prysm.PendingPartialWithdrawal

/-- PendingPartialWithdrawal (`state`; Index `primitives.ValidatorIndex` at Go 8, Amount `uint64` at 16,
WithdrawableEpoch `primitives.Epoch` at 24). Frame `0x90`, guard `lea -0x18(%rsp)`, no call on the fast
path. Stack: saved rbp, home slots `rsp + 8`, `rsp + 16`, the zeroed temps at `rsp − 40` (Index) and
`rsp − 72` (WithdrawableEpoch), each two 16-byte halves. Amount is stored from a register. -/
abbrev Encode.fast_path_statement : Prop :=
  ∀ (k : Nat) (hk : Prysm.PendingPartialWithdrawal.Code.marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.PendingPartialWithdrawal.Code.marshalSSZTo k)
    (ast v0 v1 v2 pre d0 d1 d2 : List UInt8)
    (hast : ast.length = 8) (hv0 : v0.length = 8) (hv1 : v1.length = 8) (hv2 : v2.length = 8)
    (hd0 : d0.length = 8) (hd1 : d1.length = 8) (hd2 : d2.length = 8)
    (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 t40 t24 t72 t56 : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8)
    (ht40 : t40.length = 16) (ht24 : t24.length = 16) (ht72 : t72.length = 16) (ht56 : t56.length = 16)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (t24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (t72.At (s.regs.rsp.toBitVec - 72)) ⋆ Eq (t56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16)) ⋆ Eq (v2.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16)) ⋆ R)
    (hguard : guard.toNat + 24 < s.regs.rsp.toNat) (hsp : 160 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 24 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 24 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 x2 x3 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧ x2.length = 8 ∧ x3.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (v2.At (s.regs.rsp.toBitVec - 72)) ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16)) ⋆ Eq (v2.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (v2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

end Prysm.PendingPartialWithdrawal
