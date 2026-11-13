import Runtime.Contracts
import Runtime.NewobjectContract
import Machine.Frame
import Machine.Bytes
import Machine.Labels
import Prysm.ElfData.PrysmTarget
import Prysm.Checkpoint.Code
import Prysm.AttestationData.Code
import Prysm.IndexedAttestation.Code
import Prysm.IndexedAttestation.SpecDefinitions

/-!
# Hand STATEMENTS of the target `(*v1alpha1.IndexedAttestation).UnmarshalSSZ` (statements only, no proof)

Frozen at their commit. A later change needs a new name and a reason; these definitions stay.
Statement shape: `Prysm/SyncAggregate/Statements.lean` / `Prysm/SyncCommittee/Statements.lean` (exact frame, contracts as hypotheses, input and receiver kept) and, for
the two `fmt.errorf` rejects, the contract forms `ConvT64C` and `FmtErrorfDWC` (`Runtime/Contracts.lean`).

    func (c *IndexedAttestation) UnmarshalSSZ(buf []byte) error {        // phase0.ssz.go:2819
        if size < 228 { return ssz.ErrSize }                                                  // size reject
        sszVarOffset0 := ssz.ReadOffset(buf[0:4]); if sszVarOffset0 != 228 { return ssz.ErrInvalidVariableOffset } // offset reject
        if len(sszSlice0)%8 != 0 { return fmt.Errorf("misaligned bytes: … %d … %w", …, ssz.ErrIncorrectListSize) } // alignment reject
        numElem := len(sszSlice0) / 8
        if numElem > 2048 { return fmt.Errorf("ssz-max exceeded: … %d … %w", numElem, ssz.ErrListTooBig) }         // overflow reject
        c.AttestingIndices = make([]uint64, numElem); for i … { c.AttestingIndices[i] = LE64(sszSlice0[i*8:(1+i)*8]) }
        c.Data = new(AttestationData); if err = c.Data.UnmarshalSSZ(buf[4:132]); err != nil { return fmt.Errorf("Data: %w", err) } // delegate error
        c.Signature = append(make([]byte, 0, 96), buf[132:228]...); return err }                              // accept

Receiver: protoc struct, IR `go_fields` (`prysm/ir/ir-mainnet.json`, size 96): `state` 0, `AttestingIndices` 8 (ptr, len,
cap), `Data` 32 (pointer), `Signature` 40 (ptr, len, cap), `unknownFields` 64 (24), `sizeCache` 88 (4) (the last two and
the padding in `R`).

Frame (`.S`, x = entry rsp): guard `lea -0x30(%rsp),%r12; cmp 0x10(%r14),%r12; jbe` (so `guard + 48 < x`); `sub $0xa8`;
spills `0xb8` = x + 8 (rax), `0xc0` = x + 16 (rbx, written at directive 8 before the size check), `0xd0` = x + 32 (rdi);
locals `0x28` = x − 136 (numElem), `0x30` = x − 128, `0x38` = x − 120 (cap − 228), `0x40` = x − 112 (buf[228:] pointer),
`0x48` = x − 104, `0xa0` = x − 16 (Signature pointer); errorf argument arrays `0x50` = x − 96 (16 bytes, delegate error), `0x60` = x − 80
(32 bytes, overflow reject), `0x80` = x − 48 (32 bytes, alignment reject); callee spill area `0x0…0x27` = x − 176 (40 bytes; errorf spills 40, makeslice 24,
newobject / convT64 8; the AttestationData callee spills its rax, rbx, rdi at x − 176, x − 168, x − 152); runtime call
return slot x − 184; scratch `S` below it. On the accept path the AttestationData callee's whole stack (its entry rsp = x − 184,
`Prysm.AttestationData.Decode.accept` with scratch `Sd`) lies in our scratch: `S = Sd + 224`.
Return addresses at the end: alignment reject errorf call 116 → `k + 117`; overflow reject errorf call 79 → `k + 80`; accept last memmove 240 → `k + 241`.
-/

open Machine Runtime EthLib.Serialization.Ssz Prysm.IndexedAttestation.Code
variable [Host]

namespace Prysm.IndexedAttestation

/-- **Size reject (machine).** `len(buf) < 228`: the decoder returns the two words `e0`, `e1` of `ssz.ErrSize`; the rbx spill slot holds rbx; the input, the receiver and the caller's frame (all in `R`) and the global are unchanged. -/
def Decode.reject_size_statement : Prop :=
  ∀ (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp s2 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec)
      ⋆ R)
    (hguard : guard.toNat + 48 < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat < 228),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrSize_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec)
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- **Offset reject (machine).** `len(buf) ≥ 228` and the first offset (the 4 bytes `off` at buf[0:4]) is not 228: the decoder returns the two words of `ssz.ErrInvalidVariableOffset`; `off` and `R` are unchanged. -/
def Decode.reject_offset_statement : Prop :=
  ∀ (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp s2 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)
    (off : List UInt8) (hoff4 : off.length = 4) (hoff : off ≠ offsetBytes)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (off.At s.regs.rbx.toBitVec)
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrInvalidVariableOffset_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrInvalidVariableOffset" + 8).toBitVec)
      ⋆ R)
    (hguard : guard.toNat + 48 < s.regs.rsp.toNat) (hlen : 228 ≤ s.regs.rcx.toNat),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (off.At s.regs.rbx.toBitVec)
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrInvalidVariableOffset_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrInvalidVariableOffset" + 8).toBitVec)
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- **Alignment reject (machine).** `len(buf) ≥ 228`, offset 228, `(len − 228) mod 8 ≠ 0`: `convT64(len − 228)` and `fmt.errorf("misaligned bytes: … %d … %w", len − 228, ssz.ErrIncorrectListSize)`; the decoder returns that error (rax ≠ 0). The 32-byte argument array at rsp − 48 holds `type:int`, the box, the error's type word and data word. Exact frame; the heap shrinks by at most the box and the errorf allocation. -/
def Decode.reject_alignment_statement : Prop :=
  ∀ (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (s : MachineData) (ra guard e0 e1 : UInt64) (esp : BitVec 64) (msg ity : List UInt8)
    (he0 : e0.toBitVec = (label "go_itab._errors.errorString_error").toBitVec) (hity : ity.length = 8)
    (fp s2 aw spl rslot lo : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8) (haw : aw.length = 32)
    (hspl : spl.length = 40) (hrs : rslot.length = 8) (S : Nat) (hlo : lo.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (aw.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 176))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 184))
      ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 (S)))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (ElfData.PrysmTarget.formatAttestingIndicesMisaligned.At ElfData.PrysmTarget.formatAttestingIndicesMisaligned_addr)
      ⋆ Eq (offsetBytes.At s.regs.rbx.toBitVec)
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrIncorrectListSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrIncorrectListSize" + 8).toBitVec)
      ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8))
      ⋆ ErrStr e1.toBitVec esp msg
      ⋆ StaticBox (s.regs.rcx.toBitVec - 228)
      ⋆ R)
    (hguard : guard.toNat + 48 < s.regs.rsp.toNat) (hlen : 228 ≤ s.regs.rcx.toNat) (hmis : (s.regs.rcx.toNat - 228) % 8 ≠ 0)
    (hav : ElfData.PrysmTarget.formatAttestingIndicesMisaligned.length + msg.length + 8220 ≤ avail)
    (hcv : ConvT64C Heap S) (hfe : FmtErrorfDWC Heap ElfData.PrysmTarget.formatAttestingIndicesMisaligned ElfData.PrysmTarget.typeInt_addr S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax ≠ 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (bx : BitVec 64) (hb spl' lo' : List UInt8) (avail' : Nat), spl'.length = 40 ∧ lo'.length = S
          ∧ BoxIn bx (s.regs.rcx.toBitVec - 228) hb ∧ avail' + hb.length ≤ avail ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 ElfData.PrysmTarget.typeInt_addr.toInt ++ Int.toBytes 8 bx.toInt ++ ity ++ Int.toBytes 8 e1.toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 176))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 117)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 184))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 (S)))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap avail'
          ⋆ Eq (ElfData.PrysmTarget.formatAttestingIndicesMisaligned.At ElfData.PrysmTarget.formatAttestingIndicesMisaligned_addr)
          ⋆ Eq (offsetBytes.At s.regs.rbx.toBitVec)
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrIncorrectListSize_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrIncorrectListSize" + 8).toBitVec)
          ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8))
          ⋆ ErrStr e1.toBitVec esp msg
          ⋆ StaticBox (s.regs.rcx.toBitVec - 228)
          ⋆ Eq (hb.At bx)
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- **Overflow reject (machine).** `len(buf) ≥ 228`, offset 228, `(len − 228) mod 8 = 0`, `numElem = (len − 228)/8 > 2048`: `convT64(numElem)` and `fmt.errorf("ssz-max exceeded: … %d … %w", numElem, ssz.ErrListTooBig)`; the decoder returns that error (rax ≠ 0). Argument array at rsp − 80. -/
def Decode.reject_overflow_statement : Prop :=
  ∀ (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (s : MachineData) (ra guard e0 e1 : UInt64) (esp : BitVec 64) (msg ity : List UInt8)
    (he0 : e0.toBitVec = (label "go_itab._errors.errorString_error").toBitVec) (hity : ity.length = 8)
    (fp s2 aw spl rslot lo : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8) (haw : aw.length = 32)
    (hspl : spl.length = 40) (hrs : rslot.length = 8) (S : Nat) (hlo : lo.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (aw.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 176))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 184))
      ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 (S)))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (ElfData.PrysmTarget.formatAttestingIndicesTooBig.At ElfData.PrysmTarget.formatAttestingIndicesTooBig_addr)
      ⋆ Eq (offsetBytes.At s.regs.rbx.toBitVec)
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrListTooBig_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrListTooBig" + 8).toBitVec)
      ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8))
      ⋆ ErrStr e1.toBitVec esp msg
      ⋆ StaticBox (BitVec.ofNat 64 ((s.regs.rcx.toNat - 228) / 8))
      ⋆ R)
    (hguard : guard.toNat + 48 < s.regs.rsp.toNat) (hlen : 228 ≤ s.regs.rcx.toNat) (hal : (s.regs.rcx.toNat - 228) % 8 = 0) (hbig : 2048 < (s.regs.rcx.toNat - 228) / 8)
    (hav : ElfData.PrysmTarget.formatAttestingIndicesTooBig.length + msg.length + 8220 ≤ avail)
    (hcv : ConvT64C Heap S) (hfe : FmtErrorfDWC Heap ElfData.PrysmTarget.formatAttestingIndicesTooBig ElfData.PrysmTarget.typeInt_addr S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax ≠ 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (bx : BitVec 64) (hb spl' lo' : List UInt8) (avail' : Nat), spl'.length = 40 ∧ lo'.length = S
          ∧ BoxIn bx (BitVec.ofNat 64 ((s.regs.rcx.toNat - 228) / 8)) hb ∧ avail' + hb.length ≤ avail ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 ElfData.PrysmTarget.typeInt_addr.toInt ++ Int.toBytes 8 bx.toInt ++ ity ++ Int.toBytes 8 e1.toBitVec.toInt).At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 176))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 80)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 184))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 (S)))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap avail'
          ⋆ Eq (ElfData.PrysmTarget.formatAttestingIndicesTooBig.At ElfData.PrysmTarget.formatAttestingIndicesTooBig_addr)
          ⋆ Eq (offsetBytes.At s.regs.rbx.toBitVec)
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrListTooBig_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrListTooBig" + 8).toBitVec)
          ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8))
          ⋆ ErrStr e1.toBitVec esp msg
          ⋆ StaticBox (BitVec.ofNat 64 ((s.regs.rcx.toNat - 228) / 8))
          ⋆ Eq (hb.At bx)
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- **Accept (machine).** For every `n ≤ 2048`, on the input `off(228) ‖ data(128) ‖ sig(96) ‖ ib(8n)` the decoder returns nil; the receiver holds AttestingIndices = (A, n, n) with `ib` at A, Data = a fresh 96-byte AttestationData object `pd` decoded by the real `AttestationData.UnmarshalSSZ` (placed in the host, discharged by `Prysm.AttestationData.Decode.accept`; its Source / Target objects as in that theorem), Signature = (psig, 96, 96) = sig. The three panicBounds branches of the element loop are not on the path (to be proved, not assumed). Exact frame, input, `state` and `R` unchanged; heap `8n + 432` bytes. -/
def Decode.accept_statement : Prop :=
  ∀ (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (kA : Nat) (hkA : Prysm.AttestationData.Code.unmarshalSSZ.IsInfixAt Host.prog kA) (hfA : LabelsFresh Prysm.AttestationData.Code.unmarshalSSZ kA)
    (kS : Nat) (hkS : Prysm.Slot.Code.unmarshalSSZ.IsInfixAt Host.prog kS) (hfS : LabelsFresh Prysm.Slot.Code.unmarshalSSZ kS)
    (kI : Nat) (hkI : Prysm.CommitteeIndex.Code.unmarshalSSZ.IsInfixAt Host.prog kI) (hfI : LabelsFresh Prysm.CommitteeIndex.Code.unmarshalSSZ kI)
    (kC : Nat) (hkC : Prysm.Checkpoint.Code.unmarshalSSZ.IsInfixAt Host.prog kC) (hfC : LabelsFresh Prysm.Checkpoint.Code.unmarshalSSZ kC)
    (kE : Nat) (hkE : Prysm.Epoch.Code.unmarshalSSZ.IsInfixAt Host.prog kE) (hfE : LabelsFresh Prysm.Epoch.Code.unmarshalSSZ kE)
    (n : Nat) (hn : n ≤ 2048) (in0 in1 root se sroot te troot sig ib : List UInt8)
    (hin0 : in0.length = 8) (hin1 : in1.length = 8) (hroot : root.length = 32) (hse : se.length = 8)
    (hsroot : sroot.length = 32) (hte : te.length = 8) (htroot : troot.length = 32) (hsig : sig.length = 96)
    (hib : ib.length = 8 * n)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 l28 l30 l38 l40 l48 la0 spl rslot lo ast aP1 aL1 aC1 aD aP2 aL2 aC2 : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h4 : s4.length = 8)
    (hl28 : l28.length = 8) (hl30 : l30.length = 8) (hl38 : l38.length = 8) (hl40 : l40.length = 8)
    (hl48 : l48.length = 8) (hla0 : la0.length = 8) (hspl : spl.length = 40) (hrs : rslot.length = 8)
    (hast : ast.length = 8) (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8)
    (haD : aD.length = 8) (haP2 : aP2.length = 8) (haL2 : aL2.length = 8) (haC2 : aC2.length = 8)
    (R : DataMem → Prop) (Sd : Nat) (hSd8 : 8 ≤ Sd) (hSd : Sd < 2 ^ 60) (hlo : lo.length = Sd + 224)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (s4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq (l28.At (s.regs.rsp.toBitVec - 136))
      ⋆ Eq (l30.At (s.regs.rsp.toBitVec - 128))
      ⋆ Eq (l38.At (s.regs.rsp.toBitVec - 120))
      ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 112))
      ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 104))
      ⋆ Eq (la0.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 176))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 184))
      ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 (Sd + 224)))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (offsetBytes.At s.regs.rbx.toBitVec)
      ⋆ Eq (in0.At (s.regs.rbx.toBitVec + 4))
      ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 12))
      ⋆ Eq (root.At (s.regs.rbx.toBitVec + 20))
      ⋆ Eq (se.At (s.regs.rbx.toBitVec + 52))
      ⋆ Eq (sroot.At (s.regs.rbx.toBitVec + 60))
      ⋆ Eq (te.At (s.regs.rbx.toBitVec + 92))
      ⋆ Eq (troot.At (s.regs.rbx.toBitVec + 100))
      ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 132))
      ⋆ Eq (ib.At (s.regs.rbx.toBitVec + 228))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (aD.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (aP2.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (aL2.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq (aC2.At (s.regs.rax.toBitVec + 56))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
      ⋆ R)
    (hguard : guard.toNat + 408 < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = 228 + 8 * n)
    (hcap : s.regs.rcx.toNat ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hav : 8 * n + 432 ≤ avail)
    (hmsU : MakesliceC Heap ElfData.PrysmTarget.typeUint64_addr 8 (Sd + 224))
    (hms : MakesliceC Heap ElfData.PrysmTarget.typeUint8_addr 1 (Sd + 224)) (hmm : MemmoveC (Sd + 224))
    (hno : NewobjectC Heap ElfData.PrysmTarget.typeAttestationData_addr 96 (Sd + 224))
    (hmsD : MakesliceC Heap ElfData.PrysmTarget.typeUint8_addr 1 Sd) (hmmD : MemmoveC Sd)
    (hmsD' : MakesliceC Heap ElfData.PrysmTarget.typeUint8_addr 1 (Sd + 96)) (hmmD' : MemmoveC (Sd + 96))
    (hnoD : NewobjectC Heap ElfData.PrysmTarget.typeCheckpoint_addr 72 (Sd + 96)),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (A pd p ps pt p1 p2 psig : BitVec 64) (l28' l30' l38' l40' l48' spl' lo' : List UInt8),
          l28'.length = 8 ∧ l30'.length = 8 ∧ l38'.length = 8 ∧ l40'.length = 8 ∧ l48'.length = 8
          ∧ spl'.length = 40 ∧ lo'.length = Sd + 224 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (l28'.At (s.regs.rsp.toBitVec - 136))
          ⋆ Eq (l30'.At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq (l38'.At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq (l40'.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq (l48'.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq ((Int.toBytes 8 psig.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 176))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 241)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 184))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 (Sd + 224)))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - (8 * n + 432))
          ⋆ Eq (offsetBytes.At s.regs.rbx.toBitVec)
          ⋆ Eq (in0.At (s.regs.rbx.toBitVec + 4))
          ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 12))
          ⋆ Eq (root.At (s.regs.rbx.toBitVec + 20))
          ⋆ Eq (se.At (s.regs.rbx.toBitVec + 52))
          ⋆ Eq (sroot.At (s.regs.rbx.toBitVec + 60))
          ⋆ Eq (te.At (s.regs.rbx.toBitVec + 92))
          ⋆ Eq (troot.At (s.regs.rbx.toBitVec + 100))
          ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 132))
          ⋆ Eq (ib.At (s.regs.rbx.toBitVec + 228))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 A.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 (n : Int)).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 (n : Int)).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 pd.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 psig.toInt).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (ib.At A)
          ⋆ Eq ((List.replicate 8 0).At pd)
          ⋆ Eq (in0.At (pd + 8))
          ⋆ Eq (in1.At (pd + 16))
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

/-- **Size reject (spec).** `bs.size < 228`: EthLib rejects, and the machine code returns `ssz.ErrSize` (postcondition of `Decode.reject_size_statement`). -/
def Decode.reject_size_spec_statement : Prop :=
  ∀ (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (bs : Array UInt8) (hbs : bs.size < 228)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp s2 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec)
      ⋆ R)
    (hguard : guard.toNat + 48 < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bs.size),
    (∃ e, deserialize desc bs = .error e) ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrSize_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec)
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- **Offset reject (spec).** `bs.size ≥ 228` and `bs[0:4] ≠ offsetBytes`: EthLib rejects, and the machine code returns `ssz.ErrInvalidVariableOffset`. -/
def Decode.reject_offset_spec_statement : Prop :=
  ∀ (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (bs : Array UInt8) (hbs : 228 ≤ bs.size) (hoff : bs.toList.take 4 ≠ offsetBytes)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp s2 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((bs.toList.take 4).At s.regs.rbx.toBitVec)
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrInvalidVariableOffset_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrInvalidVariableOffset" + 8).toBitVec)
      ⋆ R)
    (hguard : guard.toNat + 48 < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bs.size),
    (∃ e, deserialize desc bs = .error e) ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((bs.toList.take 4).At s.regs.rbx.toBitVec)
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrInvalidVariableOffset_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrInvalidVariableOffset" + 8).toBitVec)
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- **Alignment reject (spec).** `bs.size ≥ 228`, `bs[0:4] = offsetBytes`, `(bs.size − 228) mod 8 ≠ 0`: EthLib rejects, and the machine code returns the `fmt.errorf` error (postcondition of `Decode.reject_alignment_statement`). -/
def Decode.reject_alignment_spec_statement : Prop :=
  ∀ (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (bs : Array UInt8) (hbs : 228 ≤ bs.size) (hoff : bs.toList.take 4 = offsetBytes) (hmis : (bs.size - 228) % 8 ≠ 0)
    (s : MachineData) (ra guard e0 e1 : UInt64) (esp : BitVec 64) (msg ity : List UInt8)
    (he0 : e0.toBitVec = (label "go_itab._errors.errorString_error").toBitVec) (hity : ity.length = 8)
    (fp s2 aw spl rslot lo : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8) (haw : aw.length = 32)
    (hspl : spl.length = 40) (hrs : rslot.length = 8) (S : Nat) (hlo : lo.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (aw.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 176))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 184))
      ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 (S)))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (ElfData.PrysmTarget.formatAttestingIndicesMisaligned.At ElfData.PrysmTarget.formatAttestingIndicesMisaligned_addr)
      ⋆ Eq (offsetBytes.At s.regs.rbx.toBitVec)
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrIncorrectListSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrIncorrectListSize" + 8).toBitVec)
      ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8))
      ⋆ ErrStr e1.toBitVec esp msg
      ⋆ StaticBox (s.regs.rcx.toBitVec - 228)
      ⋆ R)
    (hguard : guard.toNat + 48 < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bs.size)
    (hav : ElfData.PrysmTarget.formatAttestingIndicesMisaligned.length + msg.length + 8220 ≤ avail)
    (hcv : ConvT64C Heap S) (hfe : FmtErrorfDWC Heap ElfData.PrysmTarget.formatAttestingIndicesMisaligned ElfData.PrysmTarget.typeInt_addr S),
    (∃ e, deserialize desc bs = .error e) ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax ≠ 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (bx : BitVec 64) (hb spl' lo' : List UInt8) (avail' : Nat), spl'.length = 40 ∧ lo'.length = S
          ∧ BoxIn bx (s.regs.rcx.toBitVec - 228) hb ∧ avail' + hb.length ≤ avail ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 ElfData.PrysmTarget.typeInt_addr.toInt ++ Int.toBytes 8 bx.toInt ++ ity ++ Int.toBytes 8 e1.toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 176))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 117)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 184))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 (S)))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap avail'
          ⋆ Eq (ElfData.PrysmTarget.formatAttestingIndicesMisaligned.At ElfData.PrysmTarget.formatAttestingIndicesMisaligned_addr)
          ⋆ Eq (offsetBytes.At s.regs.rbx.toBitVec)
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrIncorrectListSize_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrIncorrectListSize" + 8).toBitVec)
          ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8))
          ⋆ ErrStr e1.toBitVec esp msg
          ⋆ StaticBox (s.regs.rcx.toBitVec - 228)
          ⋆ Eq (hb.At bx)
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- **Overflow reject (spec).** `bs.size ≥ 228`, `bs[0:4] = offsetBytes`, `(bs.size − 228) mod 8 = 0`, `(bs.size − 228)/8 > 2048`: EthLib rejects, and the machine code returns the `fmt.errorf` error (postcondition of `Decode.reject_overflow_statement`). -/
def Decode.reject_overflow_spec_statement : Prop :=
  ∀ (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (bs : Array UInt8) (hbs : 228 ≤ bs.size) (hoff : bs.toList.take 4 = offsetBytes) (hal : (bs.size - 228) % 8 = 0) (hbig : 2048 < (bs.size - 228) / 8)
    (s : MachineData) (ra guard e0 e1 : UInt64) (esp : BitVec 64) (msg ity : List UInt8)
    (he0 : e0.toBitVec = (label "go_itab._errors.errorString_error").toBitVec) (hity : ity.length = 8)
    (fp s2 aw spl rslot lo : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8) (haw : aw.length = 32)
    (hspl : spl.length = 40) (hrs : rslot.length = 8) (S : Nat) (hlo : lo.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (aw.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 176))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 184))
      ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 (S)))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (ElfData.PrysmTarget.formatAttestingIndicesTooBig.At ElfData.PrysmTarget.formatAttestingIndicesTooBig_addr)
      ⋆ Eq (offsetBytes.At s.regs.rbx.toBitVec)
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrListTooBig_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrListTooBig" + 8).toBitVec)
      ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8))
      ⋆ ErrStr e1.toBitVec esp msg
      ⋆ StaticBox (BitVec.ofNat 64 ((s.regs.rcx.toNat - 228) / 8))
      ⋆ R)
    (hguard : guard.toNat + 48 < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bs.size)
    (hav : ElfData.PrysmTarget.formatAttestingIndicesTooBig.length + msg.length + 8220 ≤ avail)
    (hcv : ConvT64C Heap S) (hfe : FmtErrorfDWC Heap ElfData.PrysmTarget.formatAttestingIndicesTooBig ElfData.PrysmTarget.typeInt_addr S),
    (∃ e, deserialize desc bs = .error e) ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax ≠ 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (bx : BitVec 64) (hb spl' lo' : List UInt8) (avail' : Nat), spl'.length = 40 ∧ lo'.length = S
          ∧ BoxIn bx (BitVec.ofNat 64 ((s.regs.rcx.toNat - 228) / 8)) hb ∧ avail' + hb.length ≤ avail ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 ElfData.PrysmTarget.typeInt_addr.toInt ++ Int.toBytes 8 bx.toInt ++ ity ++ Int.toBytes 8 e1.toBitVec.toInt).At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 176))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 80)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 184))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 (S)))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap avail'
          ⋆ Eq (ElfData.PrysmTarget.formatAttestingIndicesTooBig.At ElfData.PrysmTarget.formatAttestingIndicesTooBig_addr)
          ⋆ Eq (offsetBytes.At s.regs.rbx.toBitVec)
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrListTooBig_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrListTooBig" + 8).toBitVec)
          ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8))
          ⋆ ErrStr e1.toBitVec esp msg
          ⋆ StaticBox (BitVec.ofNat 64 ((s.regs.rcx.toNat - 228) / 8))
          ⋆ Eq (hb.At bx)
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- **Accept (spec).** If EthLib accepts `bsA` against `desc` as `v`, there is `g : SszValue` with `g.toValue = v` and `bsA = SszValue.encode g`; with the input chunks of that `g` the machine code returns nil and the receiver holds `g` (postcondition of `Decode.accept_statement` with `n = g.idx.length`). -/
def Decode.accept_spec_statement : Prop :=
  ∀ (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (kA : Nat) (hkA : Prysm.AttestationData.Code.unmarshalSSZ.IsInfixAt Host.prog kA) (hfA : LabelsFresh Prysm.AttestationData.Code.unmarshalSSZ kA)
    (kS : Nat) (hkS : Prysm.Slot.Code.unmarshalSSZ.IsInfixAt Host.prog kS) (hfS : LabelsFresh Prysm.Slot.Code.unmarshalSSZ kS)
    (kI : Nat) (hkI : Prysm.CommitteeIndex.Code.unmarshalSSZ.IsInfixAt Host.prog kI) (hfI : LabelsFresh Prysm.CommitteeIndex.Code.unmarshalSSZ kI)
    (kC : Nat) (hkC : Prysm.Checkpoint.Code.unmarshalSSZ.IsInfixAt Host.prog kC) (hfC : LabelsFresh Prysm.Checkpoint.Code.unmarshalSSZ kC)
    (kE : Nat) (hkE : Prysm.Epoch.Code.unmarshalSSZ.IsInfixAt Host.prog kE) (hfE : LabelsFresh Prysm.Epoch.Code.unmarshalSSZ kE)
    (bsA : Array UInt8) (v : Value) (hd : deserialize desc bsA = .ok v)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 l28 l30 l38 l40 l48 la0 spl rslot lo ast aP1 aL1 aC1 aD aP2 aL2 aC2 : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h4 : s4.length = 8)
    (hl28 : l28.length = 8) (hl30 : l30.length = 8) (hl38 : l38.length = 8) (hl40 : l40.length = 8)
    (hl48 : l48.length = 8) (hla0 : la0.length = 8) (hspl : spl.length = 40) (hrs : rslot.length = 8)
    (hast : ast.length = 8) (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8)
    (haD : aD.length = 8) (haP2 : aP2.length = 8) (haL2 : aL2.length = 8) (haC2 : aC2.length = 8)
    (R : DataMem → Prop) (Sd : Nat) (hSd8 : 8 ≤ Sd) (hSd : Sd < 2 ^ 60) (hlo : lo.length = Sd + 224)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (Pm : ∀ g : SszValue, bsA = SszValue.encode g →
      s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (s4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq (l28.At (s.regs.rsp.toBitVec - 136))
      ⋆ Eq (l30.At (s.regs.rsp.toBitVec - 128))
      ⋆ Eq (l38.At (s.regs.rsp.toBitVec - 120))
      ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 112))
      ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 104))
      ⋆ Eq (la0.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 176))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 184))
      ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 (Sd + 224)))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (offsetBytes.At s.regs.rbx.toBitVec)
      ⋆ Eq ((uintBytes 8 g.data.slot.toNat).toList.At (s.regs.rbx.toBitVec + 4))
      ⋆ Eq ((uintBytes 8 g.data.index.toNat).toList.At (s.regs.rbx.toBitVec + 12))
      ⋆ Eq (g.data.root.toList.At (s.regs.rbx.toBitVec + 20))
      ⋆ Eq ((uintBytes 8 g.data.source.epoch.toNat).toList.At (s.regs.rbx.toBitVec + 52))
      ⋆ Eq (g.data.source.root.toList.At (s.regs.rbx.toBitVec + 60))
      ⋆ Eq ((uintBytes 8 g.data.target.epoch.toNat).toList.At (s.regs.rbx.toBitVec + 92))
      ⋆ Eq (g.data.target.root.toList.At (s.regs.rbx.toBitVec + 100))
      ⋆ Eq (g.signature.toList.At (s.regs.rbx.toBitVec + 132))
      ⋆ Eq ((Spec.u64Bytes g.idx).toList.At (s.regs.rbx.toBitVec + 228))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (aD.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (aP2.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (aL2.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq (aC2.At (s.regs.rax.toBitVec + 56))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
      ⋆ R)
    (hguard : guard.toNat + 408 < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bsA.size)
    (hcap : s.regs.rcx.toNat ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hav : bsA.size - 228 + 432 ≤ avail)
    (hmsU : MakesliceC Heap ElfData.PrysmTarget.typeUint64_addr 8 (Sd + 224))
    (hms : MakesliceC Heap ElfData.PrysmTarget.typeUint8_addr 1 (Sd + 224)) (hmm : MemmoveC (Sd + 224))
    (hno : NewobjectC Heap ElfData.PrysmTarget.typeAttestationData_addr 96 (Sd + 224))
    (hmsD : MakesliceC Heap ElfData.PrysmTarget.typeUint8_addr 1 Sd) (hmmD : MemmoveC Sd)
    (hmsD' : MakesliceC Heap ElfData.PrysmTarget.typeUint8_addr 1 (Sd + 96)) (hmmD' : MemmoveC (Sd + 96))
    (hnoD : NewobjectC Heap ElfData.PrysmTarget.typeCheckpoint_addr 72 (Sd + 96)),
    ∃ g : SszValue, g.toValue = v ∧ bsA = SszValue.encode g ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (A pd p ps pt p1 p2 psig : BitVec 64) (l28' l30' l38' l40' l48' spl' lo' : List UInt8),
          l28'.length = 8 ∧ l30'.length = 8 ∧ l38'.length = 8 ∧ l40'.length = 8 ∧ l48'.length = 8
          ∧ spl'.length = 40 ∧ lo'.length = Sd + 224 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (l28'.At (s.regs.rsp.toBitVec - 136))
          ⋆ Eq (l30'.At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq (l38'.At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq (l40'.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq (l48'.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq ((Int.toBytes 8 psig.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 176))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 241)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 184))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 (Sd + 224)))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - (8 * g.idx.length + 432))
          ⋆ Eq (offsetBytes.At s.regs.rbx.toBitVec)
          ⋆ Eq ((uintBytes 8 g.data.slot.toNat).toList.At (s.regs.rbx.toBitVec + 4))
          ⋆ Eq ((uintBytes 8 g.data.index.toNat).toList.At (s.regs.rbx.toBitVec + 12))
          ⋆ Eq (g.data.root.toList.At (s.regs.rbx.toBitVec + 20))
          ⋆ Eq ((uintBytes 8 g.data.source.epoch.toNat).toList.At (s.regs.rbx.toBitVec + 52))
          ⋆ Eq (g.data.source.root.toList.At (s.regs.rbx.toBitVec + 60))
          ⋆ Eq ((uintBytes 8 g.data.target.epoch.toNat).toList.At (s.regs.rbx.toBitVec + 92))
          ⋆ Eq (g.data.target.root.toList.At (s.regs.rbx.toBitVec + 100))
          ⋆ Eq (g.signature.toList.At (s.regs.rbx.toBitVec + 132))
          ⋆ Eq ((Spec.u64Bytes g.idx).toList.At (s.regs.rbx.toBitVec + 228))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 A.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 (g.idx.length : Int)).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 (g.idx.length : Int)).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 pd.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 psig.toInt).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Spec.u64Bytes g.idx).toList.At A)
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

/-- **Reject cases (spec, pure).** Every input that EthLib rejects meets one of the four reject conditions of the
decoder: size < 228 (size reject), offset ≠ 228 (offset reject), misaligned (alignment reject), more than 2048 elements (overflow reject). This is a statement about
EthLib only. It is a reject-completeness statement for the machine code only for those disjuncts whose machine path is
proved (the alignment and overflow rejects only under `e0 ≠ 0`, `Prysm/IndexedAttestation/StatementsErrorWordNonzero.lean`). The delegate's error is not a disjunct: EthLib accepts every 128-byte `data`. -/
def Decode.reject_cases_statement : Prop :=
  ∀ bs : Array UInt8, (¬ ∃ v, deserialize desc bs = .ok v) →
    bs.size < 228 ∨ (228 ≤ bs.size ∧ bs.toList.take 4 ≠ offsetBytes)
    ∨ (228 ≤ bs.size ∧ bs.toList.take 4 = offsetBytes ∧ (bs.size - 228) % 8 ≠ 0)
    ∨ (228 ≤ bs.size ∧ bs.toList.take 4 = offsetBytes ∧ (bs.size - 228) % 8 = 0 ∧ 2048 < (bs.size - 228) / 8)

end Prysm.IndexedAttestation
