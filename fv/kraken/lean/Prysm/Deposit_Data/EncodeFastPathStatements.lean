import Codec.Kind.EncodeFastPathAnyFrame
import Prysm.BlobIdentifier.EncoderCode

/-!
# Independent hand statements of four encoder fast paths: the `Deposit_Data` part

The declarations of the other types of this group are in `Prysm/PowBlock/EncodeFastPathStatements.lean`.
-/

open Machine Runtime Codec Prysm.PowBlock.Code
variable [Host]

namespace Prysm.Deposit_Data

/-- Deposit_Data (`state`; PublicKey `[]byte` 48 at Go 8, WithdrawalCredentials `[]byte` 32 at 32, Amount
`uint64` at 56, Signature `[]byte` 96 at 64). Frame `0x88`, guard `lea -0x10(%rsp)`. Stack: saved rbp, home
slots `rsp + 8`, `rsp + 16`; `rsp − 16` (pointer), `rsp − 40` (len + 48, then len + 184), `rsp − 48`
(capacity), `rsp − 32` (pointer), `rsp − 64` (len + 80), `rsp − 56` (capacity), the `memmove` return slot
`rsp − 152` and the scratch. Amount is stored from a register. -/
abbrev Encode.fast_path_statement : Prop :=
  ∀ (k : Nat) (hk : Prysm.Deposit_Data.Code.marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.Deposit_Data.Code.marshalSSZTo k)
    (ast v2 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 : List UInt8)
    (hast : ast.length = 8) (hv2 : v2.length = 8) (hc0 : c0.length = 8) (hc1 : c1.length = 8)
    (hc3 : c3.length = 8) (hb0 : b0.length = 48) (hb1 : b1.length = 32) (hb3 : b3.length = 96)
    (hd0 : d0.length = 48) (hd1 : d1.length = 32) (hd2 : d2.length = 8) (hd3 : d3.length = 96)
    (p0 p1 p3 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l40 l48 l32 l64 l56 rslot : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8)
    (hl40 : l40.length = 8) (hl48 : l48.length = 8) (hl32 : l32.length = 8) (hl64 : l64.length = 8)
    (hl56 : l56.length = 8) (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16)) ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (l64.At (s.regs.rsp.toBitVec - 64)) ⋆ Eq (l56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 152)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 152 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16)) ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40)) ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq (v2.At (s.regs.rax.toBitVec + 56))
      ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
      ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 72)) ⋆ Eq (c3.At (s.regs.rax.toBitVec + 80))
      ⋆ Eq (b0.At p0) ⋆ Eq (b1.At p1) ⋆ Eq (b3.At p3)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
      ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88)) ⋆ R)
    (hguard : guard.toNat + 16 < s.regs.rsp.toNat) (hsp : 152 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 184 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hmm : MemmoveContract S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 184 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (scr : List UInt8), scr.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 184).toInt).At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 80).toInt).At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 110)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 152))
          ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 152 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16)) ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40)) ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 72)) ⋆ Eq (c3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (b0.At p0) ⋆ Eq (b1.At p1) ⋆ Eq (b3.At p3)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
          ⋆ Eq (b3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

end Prysm.Deposit_Data
