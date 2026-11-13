import Codec.Kind.EncodeFastPathAnyFrame
import Prysm.BlobIdentifier.EncoderCode

/-!
# Independent hand statements of four encoder fast paths: the `SyncCommitteeMessage` part

The declarations of the other types of this group are in `Prysm/PowBlock/EncodeFastPathStatements.lean`.
-/

open Machine Runtime Codec Prysm.PowBlock.Code
variable [Host]

namespace Prysm.SyncCommitteeMessage

/-- SyncCommitteeMessage (`state`; Slot `primitives.Slot` at Go 8; BlockRoot `[]byte` 32 at 16; ValidatorIndex
`primitives.ValidatorIndex` at 40; Signature `[]byte` 96 at 48). Frame `0xa8`, guard `lea -0x30(%rsp)`.
Stack: saved rbp, home slots `rsp + 8`, `rsp + 16`; the zeroed 32-byte temp at `rsp − 56` (two 16-byte
halves; Slot stored at `rsp − 56`), `rsp − 112` (capacity), `rsp − 120` (len + 40), `rsp − 24` (pointer), the
temp at `rsp − 88` (ValidatorIndex at `rsp − 88`), `rsp − 16` (pointer), `rsp − 96` (capacity), `rsp − 104`
(len + 144), the `memmove` return slot `rsp − 184` and the scratch. -/
abbrev Encode.fast_path_statement : Prop :=
  ∀ (k : Nat) (hk : Prysm.SyncCommitteeMessage.Code.marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.SyncCommitteeMessage.Code.marshalSSZTo k)
    (ast v0 v2 c1 c3 b1 b3 pre d0 d1 d2 d3 : List UInt8)
    (hast : ast.length = 8) (hv0 : v0.length = 8) (hv2 : v2.length = 8) (hc1 : c1.length = 8)
    (hc3 : c3.length = 8) (hb1 : b1.length = 32) (hb3 : b3.length = 96)
    (hd0 : d0.length = 8) (hd1 : d1.length = 32) (hd2 : d2.length = 8) (hd3 : d3.length = 96)
    (p1 p3 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 t56 t40 l112 l120 l24 t88 t72 l16 l96 l104 rslot : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8)
    (ht56 : t56.length = 16) (ht40 : t40.length = 16) (hl112 : l112.length = 8) (hl120 : l120.length = 8)
    (hl24 : l24.length = 8) (ht88 : t88.length = 16) (ht72 : t72.length = 16) (hl16 : l16.length = 8)
    (hl96 : l96.length = 8) (hl104 : l104.length = 8) (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (t56.At (s.regs.rsp.toBitVec - 56)) ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (l112.At (s.regs.rsp.toBitVec - 112)) ⋆ Eq (l120.At (s.regs.rsp.toBitVec - 120))
      ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (t88.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (t72.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16)) ⋆ Eq (l96.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (l104.At (s.regs.rsp.toBitVec - 104))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 184)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (c1.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (v2.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
      ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 56)) ⋆ Eq (c3.At (s.regs.rax.toBitVec + 64))
      ⋆ Eq (b1.At p1) ⋆ Eq (b3.At p3)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 40))
      ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48)) ⋆ R)
    (hguard : guard.toNat + 48 < s.regs.rsp.toNat) (hsp : 184 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 144 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hmm : MemmoveC S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 144 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 scr x3 x4 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧ scr.length = S
          ∧ x3.length = 8 ∧ x4.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 56)) ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 40).toInt).At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (v2.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x4.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 144).toInt).At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 115)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 184))
          ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (c1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 56)) ⋆ Eq (c3.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (b1.At p1) ⋆ Eq (b3.At p3)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (v2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 40))
          ⋆ Eq (b3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

end Prysm.SyncCommitteeMessage
