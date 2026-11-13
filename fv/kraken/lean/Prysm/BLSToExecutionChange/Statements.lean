import Runtime.Contracts
import Machine.Frame
import Machine.Bytes
import Machine.Labels
import Prysm.ElfData.PrysmTarget
import Prysm.Checkpoint.Code
import Codec.Kind.EncodeFastPathAnyFrame
import Prysm.BuilderDepositRequest.Code

/-!
# Independent hand STATEMENTS of two decoder accept paths and two encoder fast paths with a: the `BLSToExecutionChange` part

The declarations of the other types of this group are in `Prysm/BuilderExitRequest/Statements.lean`.
-/

open Machine Runtime Prysm.Checkpoint.Code Prysm.BuilderExitRequest.Code
variable [Host]

open Codec
namespace Prysm.BLSToExecutionChange

/-- BLSToExecutionChange encoder fast path (`state`; ValidatorIndex `primitives.ValidatorIndex` at Go 8,
FromBlsPubkey `[]byte` 48 at 16, ToExecutionAddress `[]byte` 20 at 40). Frame `0x70`, small guard; stack: saved rbp,
home slots `rsp + 8`, `rsp + 16`; the zeroed temp `rsp − 72` / `rsp − 56` (ValidatorIndex at − 72); `rsp − 32`
(capacity, then len + 76), `rsp − 40` (len + 56, then capacity), `rsp − 16` (pointer); the `memmove` return slot
`rsp − 128` and the scratch. -/
abbrev Encode.fast_path_statement : Prop :=
  ∀ (k : Nat) (hk : Prysm.BLSToExecutionChange.Code.marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.BLSToExecutionChange.Code.marshalSSZTo k)
    (ast v0 c1 c2 b1 b2 pre d0 d1 d2 : List UInt8)
    (hast : ast.length = 8) (hv0 : v0.length = 8) (hc1 : c1.length = 8) (hc2 : c2.length = 8)
    (hb1 : b1.length = 48) (hb2 : b2.length = 20)
    (hd0 : d0.length = 8) (hd1 : d1.length = 48) (hd2 : d2.length = 20)
    (p1 p2 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 t72 t56 l32 l40 l16 rslot : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8)
    (ht72 : t72.length = 16) (ht56 : t56.length = 16) (hl32 : l32.length = 8) (hl40 : l40.length = 8)
    (hl16 : l16.length = 8) (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (t72.At (s.regs.rsp.toBitVec - 72)) ⋆ Eq (t56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32)) ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 128)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 128 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (c1.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 40))
      ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 48)) ⋆ Eq (c2.At (s.regs.rax.toBitVec + 56))
      ⋆ Eq (b1.At p1) ⋆ Eq (b2.At p2)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56)) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 128 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 76 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hmm : MemmoveContract S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 76 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 scr : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧ scr.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 72)) ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 76).toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 92)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 128 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (c1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 48)) ⋆ Eq (c2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (b1.At p1) ⋆ Eq (b2.At p2)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (b2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

end Prysm.BLSToExecutionChange
