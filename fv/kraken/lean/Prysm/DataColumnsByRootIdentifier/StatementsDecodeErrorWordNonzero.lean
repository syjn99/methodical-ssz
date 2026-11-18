import Runtime.Contracts
import Machine.Frame
import Machine.Bytes
import Machine.Labels
import Prysm.ElfData.PrysmTarget
import Prysm.DataColumnsByRootIdentifier.SpecDefinitions
import Prysm.DataColumnsByRootIdentifier.SpecDescription
import Prysm.DataColumnsByRootIdentifier.Code

/-!
# DataColumnsByRootIdentifier statements of the alignment reject and the overflow reject

Statements only.
Statement shape: `Prysm/IndexedAttestation/StatementsErrorWordNonzero.lean`.
These two statements have the premise `(he0nz : e0 ≠ 0)`.
This premise says that the first word of the error value is not zero.
The suffix `_error_word_nonzero` of each name gives this premise.
Reason: directives 140–143 (alignment reject) and 103–106 (overflow reject) are
`mov ssz.Err…(%rip),%rcx; test %rcx,%rcx; je …; mov 0x8(%rcx),%rcx`.
When the itab word of the error is 0, the code skips the type-word load.
Then it passes 0 where `FmtErrorfDecimalWrapContract` needs `ity`.
The Kraken Host places labels anywhere, so without the premise the itab label can be 0.
In the pinned ELF `e0` is the itab address of `go_itab._errors.errorString_error`.
The global label check of `link/check.py` binds that label to its address.
The spec forms of the two statements are in `Prysm/DataColumnsByRootIdentifier/StatementsDecodeSpecRejectErrorWordNonzero.lean`.

Both rejects run after the BlockRoot allocation, the copy of the root and the BlockRoot header stores.
So the statements also have the premises of these calls, in the form of `Decode.accept_statement`.
These are `MakesliceContract Heap typeUint8_addr 1 S`, `MemmoveContract S` and `writeBarrier = 0`.
The input in memory is the 32 root bytes at rbx and the 4 offset bytes at rbx + 32.
The code reads no other input byte on these paths.

Frame (x = entry rsp), as in `Prysm/DataColumnsByRootIdentifier/StatementsDecode.lean`.
Spills: x + 8 … x + 39.
Locals: x − 104 (cap − 36), x − 88 (buf[36:] pointer), x − 80 (BlockRoot pointer).
The errorf argument array is 32 bytes: x − 40 (alignment reject, `0x68(%rsp)`) or x − 72 (overflow reject, `0x48(%rsp)`).
Callee spill area x − 144 (40 bytes), runtime call return slot x − 152, scratch `S` below it.
Return address at the end of the alignment reject: errorf call 153 → `k + 154`.
Return address at the end of the overflow reject: errorf call 116 → `k + 117`.
-/

open Machine Runtime EthLib.Serialization.Ssz Prysm.DataColumnsByRootIdentifier.Code
variable [Host]

namespace Prysm.DataColumnsByRootIdentifier

/-- **Alignment reject (machine).** `len(buf) ≥ 36`, offset 36, `(len − 36) mod 8 ≠ 0`: the BlockRoot allocation and copy, then `convT64(len − 36)` and `fmt.errorf("misaligned bytes: … %d … %w", len − 36, ssz.ErrIncorrectListSize)`; the decoder returns that error (rax ≠ 0). The receiver holds BlockRoot = (pb, 32, 32) with the root bytes at pb. The 32-byte argument array at rsp − 40 holds `type:int`, the box, the error's type word and data word. Exact frame; the heap shrinks by the 32 root bytes, the box and the errorf allocation. -/
def Decode.reject_alignment_error_word_nonzero_statement : Prop :=
  ∀ (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (root : List UInt8) (hroot : root.length = 32)
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
      ⋆ Eq (root.At s.regs.rbx.toBitVec) ⋆ Eq (offsetBytes.At (s.regs.rbx.toBitVec + 32))
      ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 16)) ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
      ⋆ Eq (ElfData.PrysmTarget.formatColumnsMisaligned.At ElfData.PrysmTarget.formatColumnsMisaligned_addr)
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrIncorrectListSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrIncorrectListSize" + 8).toBitVec)
      ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8))
      ⋆ ErrStr e1.toBitVec esp msg
      ⋆ StaticBox (s.regs.rcx.toBitVec - 36)
      ⋆ R)
    (hguard : guard.toNat + 16 < s.regs.rsp.toNat) (hlen : 36 ≤ s.regs.rcx.toNat) (hmis : (s.regs.rcx.toNat - 36) % 8 ≠ 0)
    (hav : 32 + ElfData.PrysmTarget.formatColumnsMisaligned.length + msg.length + 8220 ≤ avail)
    (hms : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 S) (hmm : MemmoveContract S)
    (hcv : ConvT64Contract Heap S) (hfe : FmtErrorfDecimalWrapContract Heap ElfData.PrysmTarget.formatColumnsMisaligned ElfData.PrysmTarget.typeInt_addr S),
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
          ⋆ Eq (root.At s.regs.rbx.toBitVec) ⋆ Eq (offsetBytes.At (s.regs.rbx.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 pb.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (root.At pb)
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

/-- **Overflow reject (machine).** `len(buf) ≥ 36`, offset 36, `(len − 36) mod 8 = 0`, `numElem = (len − 36)/8 > 128`: the BlockRoot allocation and copy, then `convT64(numElem)` and `fmt.errorf("ssz-max exceeded: … %d … %w", numElem, ssz.ErrListTooBig)`; the decoder returns that error (rax ≠ 0). The receiver holds BlockRoot = (pb, 32, 32) with the root bytes at pb. Argument array at rsp − 72. -/
def Decode.reject_overflow_error_word_nonzero_statement : Prop :=
  ∀ (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (root : List UInt8) (hroot : root.length = 32)
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
      ⋆ Eq (root.At s.regs.rbx.toBitVec) ⋆ Eq (offsetBytes.At (s.regs.rbx.toBitVec + 32))
      ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 16)) ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
      ⋆ Eq (ElfData.PrysmTarget.formatColumnsTooBig.At ElfData.PrysmTarget.formatColumnsTooBig_addr)
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrListTooBig_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrListTooBig" + 8).toBitVec)
      ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8))
      ⋆ ErrStr e1.toBitVec esp msg
      ⋆ StaticBox (BitVec.ofNat 64 ((s.regs.rcx.toNat - 36) / 8))
      ⋆ R)
    (hguard : guard.toNat + 16 < s.regs.rsp.toNat) (hlen : 36 ≤ s.regs.rcx.toNat) (hal : (s.regs.rcx.toNat - 36) % 8 = 0)
    (hbig : 128 < (s.regs.rcx.toNat - 36) / 8)
    (hav : 32 + ElfData.PrysmTarget.formatColumnsTooBig.length + msg.length + 8220 ≤ avail)
    (hms : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 S) (hmm : MemmoveContract S)
    (hcv : ConvT64Contract Heap S) (hfe : FmtErrorfDecimalWrapContract Heap ElfData.PrysmTarget.formatColumnsTooBig ElfData.PrysmTarget.typeInt_addr S),
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
          ⋆ Eq (root.At s.regs.rbx.toBitVec) ⋆ Eq (offsetBytes.At (s.regs.rbx.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 pb.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (root.At pb)
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
