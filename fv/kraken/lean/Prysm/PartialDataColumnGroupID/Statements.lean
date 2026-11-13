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
# Independent hand STATEMENTS of four decoder accept paths and four encoder fast paths: the `PartialDataColumnGroupID` part

The declarations of the other types of this group are in `Prysm/DepositRequest/Statements.lean`.
-/

open Machine Runtime Prysm.Checkpoint.Code Prysm.AttestationData.Code Prysm.DepositRequest.Code
variable [Host]

open Codec
namespace Prysm.PartialDataColumnGroupID

/-- Hand statement of the accept path of `(*v1alpha1.PartialDataColumnGroupID).UnmarshalSSZ`: on a 40-byte input it
returns nil and the receiver holds a fresh BeaconBlockRoot slice equal to buf[0:32] (len = cap = 32) and Slot =
buf[32:40] (through the callee `Prysm.Slot.Code.unmarshalSSZ`); input, `state`, the spills, the caller's frame `R` and the stack guard
are unchanged; 32 heap bytes are used. -/
abbrev Decode.accept_statement : Prop :=
  ∀ (k : Nat) (hk : Prysm.PartialDataColumnGroupID.Code.unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.PartialDataColumnGroupID.Code.unmarshalSSZ k)
    (kS : Nat) (hkS : Prysm.Slot.Code.unmarshalSSZ.IsInfixAt Host.prog kS) (hfS : LabelsFresh Prysm.Slot.Code.unmarshalSSZ kS)
    (rt sl : List UInt8) (hrt : rt.length = 32) (hsl : sl.length = 8)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 sp0 sp1 sp2 l28 rslot lo ast aP1 aL1 aC1 aS : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h4 : s4.length = 8)
    (hsp0 : sp0.length = 8) (hsp1 : sp1.length = 8) (hsp2 : sp2.length = 8)
    (hl28 : l28.length = 8) (hrs : rslot.length = 8) (hast : ast.length = 8)
    (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8) (haS : aS.length = 8)
    (R : DataMem → Prop) (S : Nat) (hS : S < 2 ^ 60) (hlo : lo.length = S + 8)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq (sp0.At (s.regs.rsp.toBitVec - 72)) ⋆ Eq (sp1.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (sp2.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (l28.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 80)) ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (rt.At s.regs.rbx.toBitVec) ⋆ Eq (sl.At (s.regs.rbx.toBitVec + 32))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 24)) ⋆ Eq (aS.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat + 80 < s.regs.rsp.toNat) (hlen : s.regs.rcx = 40) (hav : 32 ≤ avail)
    (hms : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 (S + 8)) (hmm : MemmoveContract (S + 8)),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (p1 : BitVec 64) (spl lo' : List UInt8), spl.length = 24 ∧ lo'.length = S + 8 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 56)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 32)
          ⋆ Eq (rt.At s.regs.rbx.toBitVec) ⋆ Eq (sl.At (s.regs.rbx.toBitVec + 32))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (sl.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (rt.At p1)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- PartialDataColumnGroupID encoder fast path (`state`; BeaconBlockRoot `[]byte` 32 at Go 8, Slot `primitives.Slot`
at 32). Frame `0x68`, small guard; stack: saved rbp, home slots `rsp + 8`, `rsp + 16`; `rsp − 24` (pointer),
`rsp − 64` (capacity), `rsp − 72` (len + 32), the zeroed temp `rsp − 56` / `rsp − 40` (Slot at − 56, written after the
`memmove`), the `memmove` return slot `rsp − 120` and the scratch. -/
abbrev Encode.fast_path_statement : Prop :=
  ∀ (k : Nat) (hk : Prysm.PartialDataColumnGroupID.Code.marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh Prysm.PartialDataColumnGroupID.Code.marshalSSZTo k)
    (ast v1 c0 b0 pre d0 d1 : List UInt8)
    (hast : ast.length = 8) (hv1 : v1.length = 8) (hc0 : c0.length = 8) (hb0 : b0.length = 32)
    (hd0 : d0.length = 32) (hd1 : d1.length = 8)
    (p0 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l24 l64 l72 t56 t40 rslot : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl24 : l24.length = 8)
    (hl64 : l64.length = 8) (hl72 : l72.length = 8) (ht56 : t56.length = 16) (ht40 : t40.length = 16)
    (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24)) ⋆ Eq (l64.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (l72.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (t56.At (s.regs.rsp.toBitVec - 56)) ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 120)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16)) ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (v1.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (b0.At p0)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 32)) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 120 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 40 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hmm : MemmoveContract S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 40 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (scr x1 x2 : List UInt8), scr.length = S ∧ x1.length = 8 ∧ x2.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 32).toInt).At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (v1.At (s.regs.rsp.toBitVec - 56)) ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 36)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16)) ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 32)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

end Prysm.PartialDataColumnGroupID
