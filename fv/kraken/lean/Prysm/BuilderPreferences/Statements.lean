import Runtime.Contracts
import Machine.Frame
import Machine.Bytes
import Machine.Labels
import Prysm.ElfData.PrysmTarget
import Prysm.Checkpoint.Code
import Prysm.AttestationData.Code
import Prysm.BeaconBlockHeader.Code
import Codec.Kind.EncodeFastPathAnyFrame
import Prysm.BuilderDepositRequest.Code

/-!
# Independent hand STATEMENTS of four decoder accept paths and four encoder fast paths: the `BuilderPreferences` part

The declarations of the other types of this group are in `Prysm/DepositRequest/Statements.lean`.
-/

open Machine Runtime Prysm.Checkpoint.Code Prysm.AttestationData.Code Prysm.DepositRequest.Code
variable [Host]

open Codec
namespace Prysm.BuilderPreferences

/-- BuilderPreferences encoder fast path (`state`; MaxExecutionPayment `primitives.Gwei` at Go 8). Frame `0x48`,
small guard; stack: saved rbp, home slot `rsp + 16`, the zeroed temp at `rsp − 40` / `rsp − 24` (Gwei at − 40). -/
abbrev Encode.fast_path_statement : Prop :=
  ∀ (k : Nat) (hk : Prysm.BuilderPreferences.Code.marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.BuilderPreferences.Code.marshalSSZTo k)
    (ast v0 pre d0 : List UInt8)
    (hast : ast.length = 8) (hv0 : v0.length = 8) (hd0 : d0.length = 8)
    (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s2 t40 t24 : List UInt8)
    (hfp : fp.length = 8) (hs2 : s2.length = 8) (ht40 : t40.length = 16) (ht24 : t24.length = 16)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (t24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec)) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 88 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 8 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 8 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

end Prysm.BuilderPreferences
