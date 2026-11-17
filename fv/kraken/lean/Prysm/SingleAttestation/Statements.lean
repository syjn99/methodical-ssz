import Runtime.Contracts
import Runtime.NewobjectContract
import Machine.Frame
import Machine.Bytes
import Machine.Labels
import Prysm.ElfData.PrysmTarget
import Prysm.Checkpoint.Code
import Prysm.Epoch.Code
import Prysm.AttestationData.Code
import Prysm.CommitteeIndex.Code
import Prysm.ValidatorIndex.Code
import Prysm.Slot.Code
import Prysm.SingleAttestation.Code
import Prysm.SingleAttestation.Spec

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
