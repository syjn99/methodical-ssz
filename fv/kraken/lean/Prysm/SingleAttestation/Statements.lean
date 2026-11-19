module

public import Runtime.Contracts
public import Runtime.NewobjectContract
public import Machine.Frame
public import Machine.Bytes
public import Machine.Labels
public import Prysm.ElfData.PrysmTarget
public import Prysm.Checkpoint.Code
public import Prysm.Epoch.Code
public import Prysm.AttestationData.Code
public import Prysm.CommitteeIndex.Code
public import Prysm.ValidatorIndex.Code
public import Prysm.Slot.Code
public import Prysm.SingleAttestation.Code
public import Prysm.SingleAttestation.Spec

@[expose] public section

/-!
# Hand statements of `(*v1alpha1.SingleAttestation).UnmarshalSSZ`

This module holds the statements of the size reject, the accept path and their specification corollaries.
Statement shape: `Prysm/IndexedAttestation/Statements.lean` (exact frame, contracts as hypotheses, input and receiver kept).

    func (c *SingleAttestation) UnmarshalSSZ(buf []byte) error {        // electra.ssz.go:4914
        if size != 240 { return ssz.ErrSize }                                                       // size reject
        if err = c.CommitteeId.UnmarshalSSZ(buf[0:8]); err != nil { return fmt.Errorf("CommitteeId: %w", err) }
        if err = c.AttesterIndex.UnmarshalSSZ(buf[8:16]); err != nil { return fmt.Errorf("AttesterIndex: %w", err) }
        c.Data = new(AttestationData); if err = c.Data.UnmarshalSSZ(buf[16:144]); err != nil { return fmt.Errorf("Data: %w", err) }
        c.Signature = append(make([]byte, 0, 96), buf[144:240]...); return err }                   // accept

Receiver: protoc struct, IR `go_fields` (`prysm/ir/ir-mainnet.json`, size 88): `state` 0, `CommitteeId` 8,
`AttesterIndex` 16, `Data` 24 (pointer), `Signature` 32 (ptr, len, cap), `unknownFields` 56 (24), `sizeCache` 80 (4)
(the last two and the padding are in `R`).

Frame (`.S`, x = entry rsp): guard `cmp 0x10(%r14),%rsp; jbe` (so `guard < x`); `sub $0x70`; spills `0x80` = x + 8 (rax),
`0x88` = x + 16 (rbx, written at directive 7 before the size check), `0x98` = x + 32 (rdi); locals `0x28` = x − 80 (the nil
error word 0), `0x30` = x − 72 (the nil error word 1), `0x38` = x − 64 (Signature pointer); the `fmt.errorf` argument
arrays `0x40` … `0x6f` = x − 56 … x − 9 are not written on the accept path (in `R`); callee spill area `0x0…0x27` =
x − 120 (40 bytes; makeslice 24, newobject 8, the uint64 callees write x − 112, the AttestationData callee x − 120, x − 112,
x − 96); runtime and callee return slot x − 128; scratch below it.
On the accept path the AttestationData callee's whole stack (its entry rsp = x − 128, `Prysm.AttestationData.Decode.accept`
with scratch `Sd`) lies in our scratch: `S = Sd + 224`.
The last runtime call is the memmove at directive 159, so the return slot holds directive 160 at the end.
-/

open Machine Runtime EthLib.Serialization.Ssz Prysm.SingleAttestation.Code
variable [Host]

namespace Prysm.SingleAttestation

/-- **Size reject (machine).** `len(buf) ≠ 240`: the decoder returns the two words `e0`, `e1` of `ssz.ErrSize`; the rbx
spill slot holds rbx; the input, the receiver and the caller's frame (all in `R`) and the global are unchanged. -/
def Decode.reject_size_statement : Prop :=
  ∀ (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp s2 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx ≠ 240),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrSize_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- **Accept (machine).** On a 240-byte input `ci ‖ ai ‖ data (128) ‖ sig (96)` the decoder returns nil; the receiver holds
CommitteeId = `ci`, AttesterIndex = `ai`, Data = a fresh 96-byte AttestationData object `pd` decoded by
`AttestationData.UnmarshalSSZ` (placed in the host, discharged by `Prysm.AttestationData.Decode.accept`; its Source / Target
objects as in that theorem), Signature = (psig, 96, 96) = sig. The callees CommitteeIndex and ValidatorIndex are discharged
by their proved function specifications. Exact frame, input, `state` and `R` unchanged; heap 432 bytes. -/
def Decode.accept_statement : Prop :=
  ∀ (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (kA : Nat) (hkA : Prysm.AttestationData.Code.unmarshalSSZ.IsInfixAt Host.prog kA) (hfA : LabelsFresh Prysm.AttestationData.Code.unmarshalSSZ kA)
    (kS : Nat) (hkS : Prysm.Slot.Code.unmarshalSSZ.IsInfixAt Host.prog kS) (hfS : LabelsFresh Prysm.Slot.Code.unmarshalSSZ kS)
    (kI : Nat) (hkI : Prysm.CommitteeIndex.Code.unmarshalSSZ.IsInfixAt Host.prog kI) (hfI : LabelsFresh Prysm.CommitteeIndex.Code.unmarshalSSZ kI)
    (kV : Nat) (hkV : Prysm.ValidatorIndex.Code.unmarshalSSZ.IsInfixAt Host.prog kV) (hfV : LabelsFresh Prysm.ValidatorIndex.Code.unmarshalSSZ kV)
    (kC : Nat) (hkC : Prysm.Checkpoint.Code.unmarshalSSZ.IsInfixAt Host.prog kC) (hfC : LabelsFresh Prysm.Checkpoint.Code.unmarshalSSZ kC)
    (kE : Nat) (hkE : Prysm.Epoch.Code.unmarshalSSZ.IsInfixAt Host.prog kE) (hfE : LabelsFresh Prysm.Epoch.Code.unmarshalSSZ kE)
    (ci ai ds di root se sroot te troot sig : List UInt8)
    (hci : ci.length = 8) (hai : ai.length = 8) (hds : ds.length = 8) (hdi : di.length = 8) (hroot : root.length = 32)
    (hse : se.length = 8) (hsroot : sroot.length = 32) (hte : te.length = 8) (htroot : troot.length = 32)
    (hsig : sig.length = 96)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 l28 l30 l38 spl rslot lo ast aCI aAI aD aP aL aC : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h4 : s4.length = 8)
    (hl28 : l28.length = 8) (hl30 : l30.length = 8) (hl38 : l38.length = 8) (hspl : spl.length = 40)
    (hrs : rslot.length = 8) (hast : ast.length = 8) (haCI : aCI.length = 8) (haAI : aAI.length = 8)
    (haD : aD.length = 8) (haP : aP.length = 8) (haL : aL.length = 8) (haC : aC.length = 8)
    (R : DataMem → Prop) (Sd : Nat) (hSd8 : 8 ≤ Sd) (hSd : Sd < 2 ^ 60) (hlo : lo.length = Sd + 224)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (s4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq (l28.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (l30.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (l38.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 120))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 128))
      ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 128 - BitVec.ofNat 64 (Sd + 224)))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (ci.At s.regs.rbx.toBitVec)
      ⋆ Eq (ai.At (s.regs.rbx.toBitVec + 8))
      ⋆ Eq (ds.At (s.regs.rbx.toBitVec + 16))
      ⋆ Eq (di.At (s.regs.rbx.toBitVec + 24))
      ⋆ Eq (root.At (s.regs.rbx.toBitVec + 32))
      ⋆ Eq (se.At (s.regs.rbx.toBitVec + 64))
      ⋆ Eq (sroot.At (s.regs.rbx.toBitVec + 72))
      ⋆ Eq (te.At (s.regs.rbx.toBitVec + 104))
      ⋆ Eq (troot.At (s.regs.rbx.toBitVec + 112))
      ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 144))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (aCI.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (aAI.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (aD.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (aP.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (aL.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (aC.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
      ⋆ R)
    (hguard : guard.toNat + 352 < s.regs.rsp.toNat) (hlen : s.regs.rcx = 240) (hav : 432 ≤ avail)
    (hno : NewobjectContract Heap ElfData.PrysmTarget.typeAttestationData_addr 96 (Sd + 224))
    (hms : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 (Sd + 224)) (hmm : MemmoveContract (Sd + 224))
    (hmsD : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 Sd) (hmmD : MemmoveContract Sd)
    (hmsD' : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 (Sd + 96)) (hmmD' : MemmoveContract (Sd + 96))
    (hnoD : NewobjectContract Heap ElfData.PrysmTarget.typeCheckpoint_addr 72 (Sd + 96)),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (pd p ps pt p1 p2 psig : BitVec 64) (spl' lo' : List UInt8), spl'.length = 40 ∧ lo'.length = Sd + 224 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 0).At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq ((Int.toBytes 8 0).At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 psig.toInt).At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 160)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 128 - BitVec.ofNat 64 (Sd + 224)))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 432)
          ⋆ Eq (ci.At s.regs.rbx.toBitVec)
          ⋆ Eq (ai.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq (ds.At (s.regs.rbx.toBitVec + 16))
          ⋆ Eq (di.At (s.regs.rbx.toBitVec + 24))
          ⋆ Eq (root.At (s.regs.rbx.toBitVec + 32))
          ⋆ Eq (se.At (s.regs.rbx.toBitVec + 64))
          ⋆ Eq (sroot.At (s.regs.rbx.toBitVec + 72))
          ⋆ Eq (te.At (s.regs.rbx.toBitVec + 104))
          ⋆ Eq (troot.At (s.regs.rbx.toBitVec + 112))
          ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 144))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (ci.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (ai.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 pd.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 psig.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((List.replicate 8 0).At pd)
          ⋆ Eq (ds.At (pd + 8))
          ⋆ Eq (di.At (pd + 16))
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (pd + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (pd + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (pd + 40))
          ⋆ Eq ((Int.toBytes 8 ps.toInt).At (pd + 48))
          ⋆ Eq ((Int.toBytes 8 pt.toInt).At (pd + 56))
          ⋆ Eq ((List.replicate 32 0).At (pd + 64))
          ⋆ Eq (root.At p)
          ⋆ Eq ((List.replicate 8 0).At ps)
          ⋆ Eq (se.At (ps + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (ps + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (ps + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (ps + 32))
          ⋆ Eq ((List.replicate 32 0).At (ps + 40))
          ⋆ Eq (sroot.At p1)
          ⋆ Eq ((List.replicate 8 0).At pt)
          ⋆ Eq (te.At (pt + 8))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (pt + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (pt + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (pt + 32))
          ⋆ Eq ((List.replicate 32 0).At (pt + 40))
          ⋆ Eq (troot.At p2)
          ⋆ Eq (sig.At psig)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- **Accept (spec).** If EthLib accepts `bsA` against `desc` as `v`, there is `g : SszValue` with `g.toValue = v` and
`bsA = SszValue.encode g`; with the input chunks of that `g` the machine code returns nil and the receiver holds `g`
(postcondition of `Decode.accept_statement`). -/
def Decode.accept_spec_statement : Prop :=
  ∀ (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (kA : Nat) (hkA : Prysm.AttestationData.Code.unmarshalSSZ.IsInfixAt Host.prog kA) (hfA : LabelsFresh Prysm.AttestationData.Code.unmarshalSSZ kA)
    (kS : Nat) (hkS : Prysm.Slot.Code.unmarshalSSZ.IsInfixAt Host.prog kS) (hfS : LabelsFresh Prysm.Slot.Code.unmarshalSSZ kS)
    (kI : Nat) (hkI : Prysm.CommitteeIndex.Code.unmarshalSSZ.IsInfixAt Host.prog kI) (hfI : LabelsFresh Prysm.CommitteeIndex.Code.unmarshalSSZ kI)
    (kV : Nat) (hkV : Prysm.ValidatorIndex.Code.unmarshalSSZ.IsInfixAt Host.prog kV) (hfV : LabelsFresh Prysm.ValidatorIndex.Code.unmarshalSSZ kV)
    (kC : Nat) (hkC : Prysm.Checkpoint.Code.unmarshalSSZ.IsInfixAt Host.prog kC) (hfC : LabelsFresh Prysm.Checkpoint.Code.unmarshalSSZ kC)
    (kE : Nat) (hkE : Prysm.Epoch.Code.unmarshalSSZ.IsInfixAt Host.prog kE) (hfE : LabelsFresh Prysm.Epoch.Code.unmarshalSSZ kE)
    (bsA : Array UInt8) (v : Value) (hd : deserialize desc bsA = .ok v)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 l28 l30 l38 spl rslot lo ast aCI aAI aD aP aL aC : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h4 : s4.length = 8)
    (hl28 : l28.length = 8) (hl30 : l30.length = 8) (hl38 : l38.length = 8) (hspl : spl.length = 40)
    (hrs : rslot.length = 8) (hast : ast.length = 8) (haCI : aCI.length = 8) (haAI : aAI.length = 8)
    (haD : aD.length = 8) (haP : aP.length = 8) (haL : aL.length = 8) (haC : aC.length = 8)
    (R : DataMem → Prop) (Sd : Nat) (hSd8 : 8 ≤ Sd) (hSd : Sd < 2 ^ 60) (hlo : lo.length = Sd + 224)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (Pm : ∀ g : SszValue, bsA = SszValue.encode g →
      s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (s4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq (l28.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (l30.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (l38.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 120))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 128))
      ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 128 - BitVec.ofNat 64 (Sd + 224)))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq ((uintBytes 8 g.committeeIndex.toNat).toList.At s.regs.rbx.toBitVec)
      ⋆ Eq ((uintBytes 8 g.attesterIndex.toNat).toList.At (s.regs.rbx.toBitVec + 8))
      ⋆ Eq ((uintBytes 8 g.data.slot.toNat).toList.At (s.regs.rbx.toBitVec + 16))
      ⋆ Eq ((uintBytes 8 g.data.index.toNat).toList.At (s.regs.rbx.toBitVec + 24))
      ⋆ Eq (g.data.root.toList.At (s.regs.rbx.toBitVec + 32))
      ⋆ Eq ((uintBytes 8 g.data.source.epoch.toNat).toList.At (s.regs.rbx.toBitVec + 64))
      ⋆ Eq (g.data.source.root.toList.At (s.regs.rbx.toBitVec + 72))
      ⋆ Eq ((uintBytes 8 g.data.target.epoch.toNat).toList.At (s.regs.rbx.toBitVec + 104))
      ⋆ Eq (g.data.target.root.toList.At (s.regs.rbx.toBitVec + 112))
      ⋆ Eq (g.signature.toList.At (s.regs.rbx.toBitVec + 144))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (aCI.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (aAI.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (aD.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (aP.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (aL.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (aC.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
      ⋆ R)
    (hguard : guard.toNat + 352 < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bsA.size) (hav : 432 ≤ avail)
    (hno : NewobjectContract Heap ElfData.PrysmTarget.typeAttestationData_addr 96 (Sd + 224))
    (hms : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 (Sd + 224)) (hmm : MemmoveContract (Sd + 224))
    (hmsD : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 Sd) (hmmD : MemmoveContract Sd)
    (hmsD' : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 (Sd + 96)) (hmmD' : MemmoveContract (Sd + 96))
    (hnoD : NewobjectContract Heap ElfData.PrysmTarget.typeCheckpoint_addr 72 (Sd + 96)),
    ∃ g : SszValue, g.toValue = v ∧ bsA = SszValue.encode g ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (pd p ps pt p1 p2 psig : BitVec 64) (spl' lo' : List UInt8), spl'.length = 40 ∧ lo'.length = Sd + 224 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 0).At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq ((Int.toBytes 8 0).At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 psig.toInt).At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 160)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 128 - BitVec.ofNat 64 (Sd + 224)))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 432)
          ⋆ Eq ((uintBytes 8 g.committeeIndex.toNat).toList.At s.regs.rbx.toBitVec)
          ⋆ Eq ((uintBytes 8 g.attesterIndex.toNat).toList.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq ((uintBytes 8 g.data.slot.toNat).toList.At (s.regs.rbx.toBitVec + 16))
          ⋆ Eq ((uintBytes 8 g.data.index.toNat).toList.At (s.regs.rbx.toBitVec + 24))
          ⋆ Eq (g.data.root.toList.At (s.regs.rbx.toBitVec + 32))
          ⋆ Eq ((uintBytes 8 g.data.source.epoch.toNat).toList.At (s.regs.rbx.toBitVec + 64))
          ⋆ Eq (g.data.source.root.toList.At (s.regs.rbx.toBitVec + 72))
          ⋆ Eq ((uintBytes 8 g.data.target.epoch.toNat).toList.At (s.regs.rbx.toBitVec + 104))
          ⋆ Eq (g.data.target.root.toList.At (s.regs.rbx.toBitVec + 112))
          ⋆ Eq (g.signature.toList.At (s.regs.rbx.toBitVec + 144))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((uintBytes 8 g.committeeIndex.toNat).toList.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((uintBytes 8 g.attesterIndex.toNat).toList.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 pd.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 psig.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((List.replicate 8 0).At pd)
          ⋆ Eq ((uintBytes 8 g.data.slot.toNat).toList.At (pd + 8))
          ⋆ Eq ((uintBytes 8 g.data.index.toNat).toList.At (pd + 16))
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (pd + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (pd + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (pd + 40))
          ⋆ Eq ((Int.toBytes 8 ps.toInt).At (pd + 48))
          ⋆ Eq ((Int.toBytes 8 pt.toInt).At (pd + 56))
          ⋆ Eq ((List.replicate 32 0).At (pd + 64))
          ⋆ Eq (g.data.root.toList.At p)
          ⋆ Eq ((List.replicate 8 0).At ps)
          ⋆ Eq ((uintBytes 8 g.data.source.epoch.toNat).toList.At (ps + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (ps + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (ps + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (ps + 32))
          ⋆ Eq ((List.replicate 32 0).At (ps + 40))
          ⋆ Eq (g.data.source.root.toList.At p1)
          ⋆ Eq ((List.replicate 8 0).At pt)
          ⋆ Eq ((uintBytes 8 g.data.target.epoch.toNat).toList.At (pt + 8))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (pt + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (pt + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (pt + 32))
          ⋆ Eq ((List.replicate 32 0).At (pt + 40))
          ⋆ Eq (g.data.target.root.toList.At p2)
          ⋆ Eq (g.signature.toList.At psig)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- **Size reject (spec).** `bs.size ≠ 240`: EthLib rejects, and the machine code returns the two words of
`ssz.ErrSize` (postcondition of `Decode.reject_size_statement`). -/
def Decode.reject_size_spec_statement : Prop :=
  ∀ (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (bs : Array UInt8) (hbs : bs.size ≠ 240)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp s2 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bs.size),
    (∃ e, deserialize desc bs = .error e) ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrSize_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- **Reject completeness (spec).** Every input that EthLib rejects has `size ≠ 240`: the path condition of the
decoder's size reject. The three `fmt.Errorf` wraps after the callees are not a disjunct: EthLib accepts every 240-byte
input, and `Prysm/SingleAttestation/DecodeErrorUnreachable.lean` shows that each wrap is skipped when its callee returns nil. -/
def Decode.reject_complete_statement : Prop :=
  ∀ bs : Array UInt8, (¬ ∃ v, deserialize desc bs = .ok v) → bs.size ≠ 240

end Prysm.SingleAttestation
