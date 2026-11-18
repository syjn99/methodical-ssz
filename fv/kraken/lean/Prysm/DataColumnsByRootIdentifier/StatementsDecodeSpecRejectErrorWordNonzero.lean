import Runtime.Contracts
import Machine.Frame
import Machine.Bytes
import Machine.Labels
import Prysm.ElfData.PrysmTarget
import Prysm.DataColumnsByRootIdentifier.SpecDefinitions
import Prysm.DataColumnsByRootIdentifier.SpecDescription
import Prysm.DataColumnsByRootIdentifier.Code

/-!
# Hand STATEMENTS of the spec forms of the decoder's alignment and overflow rejects

Statements only.
Statement shape: `Decode.reject_alignment_spec_error_word_nonzero_statement` and `Decode.reject_overflow_spec_error_word_nonzero_statement` of `Prysm/IndexedAttestation/StatementsErrorWordNonzero.lean`.
Each statement adds the input `bs` to the machine statement of `Prysm/DataColumnsByRootIdentifier/StatementsDecodeErrorWordNonzero.lean`.
It adds the premise `rcx = bs.size` and the conclusion that EthLib `deserialize` returns an error.
The 32 root bytes and the 4 offset bytes in memory are `bs[0:32]` and `bs[32:36]`.
Both statements have the premise `e0 ≠ 0` of the machine statements.
This module is separate from `StatementsDecodeErrorWordNonzero.lean`.
So a negative case of a spec statement needs no copy of the machine proofs.
-/

open Machine Runtime EthLib.Serialization.Ssz Prysm.DataColumnsByRootIdentifier.Code
variable [Host]

namespace Prysm.DataColumnsByRootIdentifier

/-- **Alignment reject (spec).** `bs.size ≥ 36`, `bs[32:36] = offsetBytes`, `(bs.size − 36) mod 8 ≠ 0`: EthLib rejects, and the machine code returns the `fmt.errorf` error (postcondition of `Decode.reject_alignment_error_word_nonzero_statement`). The 32 bytes at rbx are `bs[0:32]`. -/
def Decode.reject_alignment_spec_error_word_nonzero_statement : Prop :=
  ∀ (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (bs : Array UInt8) (hbs : 36 ≤ bs.size) (hoff : (bs.toList.drop 32).take 4 = offsetBytes) (hmis : (bs.size - 36) % 8 ≠ 0)
    (s : MachineData) (ra guard e0 e1 : UInt64) (esp : BitVec 64) (msg ity : List UInt8)
    (he0 : e0.toBitVec = (label "go_itab._errors.errorString_error").toBitVec) (he0nz : e0 ≠ 0) (hity : ity.length = 8)
    (fp s1 s2 s3 s4 l28 l38 l40 aw spl rslot lo aP1 aL1 aC1 : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h3 : s3.length = 8) (h4 : s4.length = 8)
    (hl28 : l28.length = 8) (hl38 : l38.length = 8) (hl40 : l40.length = 8) (haw : aw.length = 32)
    (hspl : spl.length = 40) (hrs : rslot.length = 8)
    (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8)
    (S : Nat) (hlo : lo.length = S) (Heap : Nat → DataMem → Prop) (avail : Nat) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s3.At (s.regs.rsp.toBitVec + 24)) ⋆ Eq (s4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq (l28.At (s.regs.rsp.toBitVec - 104)) ⋆ Eq (l38.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (aw.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 144)) ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 152))
      ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 152 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq ((bs.toList.take 32).At s.regs.rbx.toBitVec) ⋆ Eq (((bs.toList.drop 32).take 4).At (s.regs.rbx.toBitVec + 32))
      ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 16)) ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
      ⋆ Eq (ElfData.PrysmTarget.formatColumnsMisaligned.At ElfData.PrysmTarget.formatColumnsMisaligned_addr)
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrIncorrectListSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrIncorrectListSize" + 8).toBitVec)
      ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8))
      ⋆ ErrStr e1.toBitVec esp msg
      ⋆ StaticBox (s.regs.rcx.toBitVec - 36)
      ⋆ R)
    (hguard : guard.toNat + 16 < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bs.size)
    (hav : 32 + ElfData.PrysmTarget.formatColumnsMisaligned.length + msg.length + 8220 ≤ avail)
    (hms : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 S) (hmm : MemmoveContract S)
    (hcv : ConvT64Contract Heap S) (hfe : FmtErrorfDecimalWrapContract Heap ElfData.PrysmTarget.formatColumnsMisaligned ElfData.PrysmTarget.typeInt_addr S),
    (∃ e, deserialize desc bs = .error e) ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax ≠ 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (pb bx : BitVec 64) (hb l28' l38' l40' spl' lo' : List UInt8) (avail' : Nat),
          l28'.length = 8 ∧ l38'.length = 8 ∧ l40'.length = 8 ∧ spl'.length = 40 ∧ lo'.length = S
          ∧ BoxIn bx (s.regs.rcx.toBitVec - 36) hb ∧ avail' + 32 + hb.length ≤ avail ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rcx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (l28'.At (s.regs.rsp.toBitVec - 104)) ⋆ Eq (l38'.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (l40'.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq ((Int.toBytes 8 ElfData.PrysmTarget.typeInt_addr.toInt ++ Int.toBytes 8 bx.toInt ++ ity ++ Int.toBytes 8 e1.toBitVec.toInt).At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 154)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 152))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 152 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap avail'
          ⋆ Eq ((bs.toList.take 32).At s.regs.rbx.toBitVec) ⋆ Eq (((bs.toList.drop 32).take 4).At (s.regs.rbx.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 pb.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((bs.toList.take 32).At pb)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ Eq (ElfData.PrysmTarget.formatColumnsMisaligned.At ElfData.PrysmTarget.formatColumnsMisaligned_addr)
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrIncorrectListSize_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrIncorrectListSize" + 8).toBitVec)
          ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8))
          ⋆ ErrStr e1.toBitVec esp msg
          ⋆ StaticBox (s.regs.rcx.toBitVec - 36)
          ⋆ Eq (hb.At bx)
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- **Overflow reject (spec).** `bs.size ≥ 36`, `bs[32:36] = offsetBytes`, `(bs.size − 36) mod 8 = 0`, `(bs.size − 36)/8 > 128`: EthLib rejects, and the machine code returns the `fmt.errorf` error (postcondition of `Decode.reject_overflow_error_word_nonzero_statement`). The 32 bytes at rbx are `bs[0:32]`. -/
def Decode.reject_overflow_spec_error_word_nonzero_statement : Prop :=
  ∀ (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (bs : Array UInt8) (hbs : 36 ≤ bs.size) (hoff : (bs.toList.drop 32).take 4 = offsetBytes) (hal : (bs.size - 36) % 8 = 0)
    (hbig : 128 < (bs.size - 36) / 8)
    (s : MachineData) (ra guard e0 e1 : UInt64) (esp : BitVec 64) (msg ity : List UInt8)
    (he0 : e0.toBitVec = (label "go_itab._errors.errorString_error").toBitVec) (he0nz : e0 ≠ 0) (hity : ity.length = 8)
    (fp s1 s2 s3 s4 l28 l38 l40 aw spl rslot lo aP1 aL1 aC1 : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h3 : s3.length = 8) (h4 : s4.length = 8)
    (hl28 : l28.length = 8) (hl38 : l38.length = 8) (hl40 : l40.length = 8) (haw : aw.length = 32)
    (hspl : spl.length = 40) (hrs : rslot.length = 8)
    (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8)
    (S : Nat) (hlo : lo.length = S) (Heap : Nat → DataMem → Prop) (avail : Nat) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s3.At (s.regs.rsp.toBitVec + 24)) ⋆ Eq (s4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq (l28.At (s.regs.rsp.toBitVec - 104)) ⋆ Eq (l38.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (aw.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 144)) ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 152))
      ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 152 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq ((bs.toList.take 32).At s.regs.rbx.toBitVec) ⋆ Eq (((bs.toList.drop 32).take 4).At (s.regs.rbx.toBitVec + 32))
      ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 16)) ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
      ⋆ Eq (ElfData.PrysmTarget.formatColumnsTooBig.At ElfData.PrysmTarget.formatColumnsTooBig_addr)
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrListTooBig_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrListTooBig" + 8).toBitVec)
      ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8))
      ⋆ ErrStr e1.toBitVec esp msg
      ⋆ StaticBox (BitVec.ofNat 64 ((s.regs.rcx.toNat - 36) / 8))
      ⋆ R)
    (hguard : guard.toNat + 16 < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bs.size)
    (hav : 32 + ElfData.PrysmTarget.formatColumnsTooBig.length + msg.length + 8220 ≤ avail)
    (hms : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 S) (hmm : MemmoveContract S)
    (hcv : ConvT64Contract Heap S) (hfe : FmtErrorfDecimalWrapContract Heap ElfData.PrysmTarget.formatColumnsTooBig ElfData.PrysmTarget.typeInt_addr S),
    (∃ e, deserialize desc bs = .error e) ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax ≠ 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (pb bx : BitVec 64) (hb l28' l38' l40' spl' lo' : List UInt8) (avail' : Nat),
          l28'.length = 8 ∧ l38'.length = 8 ∧ l40'.length = 8 ∧ spl'.length = 40 ∧ lo'.length = S
          ∧ BoxIn bx (BitVec.ofNat 64 ((s.regs.rcx.toNat - 36) / 8)) hb ∧ avail' + 32 + hb.length ≤ avail ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rcx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (l28'.At (s.regs.rsp.toBitVec - 104)) ⋆ Eq (l38'.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (l40'.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq ((Int.toBytes 8 ElfData.PrysmTarget.typeInt_addr.toInt ++ Int.toBytes 8 bx.toInt ++ ity ++ Int.toBytes 8 e1.toBitVec.toInt).At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 117)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 152))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 152 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap avail'
          ⋆ Eq ((bs.toList.take 32).At s.regs.rbx.toBitVec) ⋆ Eq (((bs.toList.drop 32).take 4).At (s.regs.rbx.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 pb.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((bs.toList.take 32).At pb)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ Eq (ElfData.PrysmTarget.formatColumnsTooBig.At ElfData.PrysmTarget.formatColumnsTooBig_addr)
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrListTooBig_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrListTooBig" + 8).toBitVec)
          ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8))
          ⋆ ErrStr e1.toBitVec esp msg
          ⋆ StaticBox (BitVec.ofNat 64 ((s.regs.rcx.toNat - 36) / 8))
          ⋆ Eq (hb.At bx)
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

end Prysm.DataColumnsByRootIdentifier
