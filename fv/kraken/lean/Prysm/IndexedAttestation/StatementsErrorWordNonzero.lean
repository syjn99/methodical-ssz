import Runtime.Contracts
import Runtime.NewobjectContract
import Machine.Frame
import Machine.Bytes
import Machine.Labels
import Prysm.ElfData.CheckpointAndEpoch
import Prysm.Checkpoint.Code
import Prysm.AttestationData.Code
import Prysm.ElfData.AttestationData
import Prysm.IndexedAttestation.Code
import Prysm.ElfData.IndexedAttestation
import Prysm.IndexedAttestation.SpecDefinitions

/-!
# Corrected IndexedAttestation statements for the alignment reject and the overflow reject: the itab word is non-zero (user-approved correction after the freeze)

The four defs below are the frozen texts of `Prysm/IndexedAttestation/Statements.lean` with one added premise `(he0nz : e0 ≠ 0)` and the suffix
`_nz` in the name; nothing else differs. Reason: directives 103–106 (alignment reject) and 66–69 (overflow reject) are
`mov ssz.Err…(%rip),%rcx; test %rcx,%rcx; je …; mov 0x8(%rcx),%rcx`; when the error's itab word is 0 the code skips the
type-word load and passes 0 where `FmtErrorfDWC` needs `ity`. The Kraken Host places labels anywhere, so the itab label
may be 0 and the frozen statements cannot refute that branch. The precondition is stronger than the frozen one (not
equivalent). The originals in `Prysm/IndexedAttestation/Statements.lean` stay unchanged and unproved. Precedent: the misaligned reject of the Go 1.26.3 test type ListU64
(a proof that is no longer in the tree) had the same two premises `e0 = itab` and `e0 ≠ 0`. In the real ELF `e0` is the
itab address `0xd28520` (check (b) of `lv/link-t3/RESULT` binds `go_itab._errors.errorString_error` to it).
-/

open Machine Runtime EthLib.Serialization.Ssz Prysm.IndexedAttestation.Code
variable [Host]

namespace Prysm.IndexedAttestation

/-- **Alignment reject (machine).** `len(buf) ≥ 228`, offset 228, `(len − 228) mod 8 ≠ 0`: `convT64(len − 228)` and `fmt.errorf("misaligned bytes: … %d … %w", len − 228, ssz.ErrIncorrectListSize)`; the decoder returns that error (rax ≠ 0). The 32-byte argument array at rsp − 48 holds `type:int`, the box, the error's type word and data word. Exact frame; the heap shrinks by at most the box and the errorf allocation. -/
def Decode.reject_alignment_error_word_nonzero_statement : Prop :=
  ∀ (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (s : MachineData) (ra guard e0 e1 : UInt64) (esp : BitVec 64) (msg ity : List UInt8)
    (he0 : e0.toBitVec = (label "go_itab._errors.errorString_error").toBitVec) (he0nz : e0 ≠ 0) (hity : ity.length = 8)
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
      ⋆ Eq (ElfData.IndexedAttestation.lvFmtMis.At ElfData.IndexedAttestation.lvFmtMis_addr)
      ⋆ Eq (offsetBytes.At s.regs.rbx.toBitVec)
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.IndexedAttestation.lvErrIncorrectListSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrIncorrectListSize" + 8).toBitVec)
      ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8))
      ⋆ ErrStr e1.toBitVec esp msg
      ⋆ StaticBox (s.regs.rcx.toBitVec - 228)
      ⋆ R)
    (hguard : guard.toNat + 48 < s.regs.rsp.toNat) (hlen : 228 ≤ s.regs.rcx.toNat) (hmis : (s.regs.rcx.toNat - 228) % 8 ≠ 0)
    (hav : ElfData.IndexedAttestation.lvFmtMis.length + msg.length + 8220 ≤ avail)
    (hcv : ConvT64C Heap S) (hfe : FmtErrorfDWC Heap ElfData.IndexedAttestation.lvFmtMis ElfData.CheckpointAndEpoch.e2eIntType_addr S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax ≠ 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (bx : BitVec 64) (hb spl' lo' : List UInt8) (avail' : Nat), spl'.length = 40 ∧ lo'.length = S
          ∧ BoxIn bx (s.regs.rcx.toBitVec - 228) hb ∧ avail' + hb.length ≤ avail ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 ElfData.CheckpointAndEpoch.e2eIntType_addr.toInt ++ Int.toBytes 8 bx.toInt ++ ity ++ Int.toBytes 8 e1.toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 176))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 117)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 184))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 (S)))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap avail'
          ⋆ Eq (ElfData.IndexedAttestation.lvFmtMis.At ElfData.IndexedAttestation.lvFmtMis_addr)
          ⋆ Eq (offsetBytes.At s.regs.rbx.toBitVec)
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.IndexedAttestation.lvErrIncorrectListSize_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrIncorrectListSize" + 8).toBitVec)
          ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8))
          ⋆ ErrStr e1.toBitVec esp msg
          ⋆ StaticBox (s.regs.rcx.toBitVec - 228)
          ⋆ Eq (hb.At bx)
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩


/-- **Overflow reject (machine).** `len(buf) ≥ 228`, offset 228, `(len − 228) mod 8 = 0`, `numElem = (len − 228)/8 > 2048`: `convT64(numElem)` and `fmt.errorf("ssz-max exceeded: … %d … %w", numElem, ssz.ErrListTooBig)`; the decoder returns that error (rax ≠ 0). Argument array at rsp − 80. -/
def Decode.reject_overflow_error_word_nonzero_statement : Prop :=
  ∀ (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (s : MachineData) (ra guard e0 e1 : UInt64) (esp : BitVec 64) (msg ity : List UInt8)
    (he0 : e0.toBitVec = (label "go_itab._errors.errorString_error").toBitVec) (he0nz : e0 ≠ 0) (hity : ity.length = 8)
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
      ⋆ Eq (ElfData.IndexedAttestation.lvFmtTooBig.At ElfData.IndexedAttestation.lvFmtTooBig_addr)
      ⋆ Eq (offsetBytes.At s.regs.rbx.toBitVec)
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.IndexedAttestation.lvErrListTooBig_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrListTooBig" + 8).toBitVec)
      ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8))
      ⋆ ErrStr e1.toBitVec esp msg
      ⋆ StaticBox (BitVec.ofNat 64 ((s.regs.rcx.toNat - 228) / 8))
      ⋆ R)
    (hguard : guard.toNat + 48 < s.regs.rsp.toNat) (hlen : 228 ≤ s.regs.rcx.toNat) (hal : (s.regs.rcx.toNat - 228) % 8 = 0) (hbig : 2048 < (s.regs.rcx.toNat - 228) / 8)
    (hav : ElfData.IndexedAttestation.lvFmtTooBig.length + msg.length + 8220 ≤ avail)
    (hcv : ConvT64C Heap S) (hfe : FmtErrorfDWC Heap ElfData.IndexedAttestation.lvFmtTooBig ElfData.CheckpointAndEpoch.e2eIntType_addr S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax ≠ 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (bx : BitVec 64) (hb spl' lo' : List UInt8) (avail' : Nat), spl'.length = 40 ∧ lo'.length = S
          ∧ BoxIn bx (BitVec.ofNat 64 ((s.regs.rcx.toNat - 228) / 8)) hb ∧ avail' + hb.length ≤ avail ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 ElfData.CheckpointAndEpoch.e2eIntType_addr.toInt ++ Int.toBytes 8 bx.toInt ++ ity ++ Int.toBytes 8 e1.toBitVec.toInt).At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 176))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 80)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 184))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 (S)))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap avail'
          ⋆ Eq (ElfData.IndexedAttestation.lvFmtTooBig.At ElfData.IndexedAttestation.lvFmtTooBig_addr)
          ⋆ Eq (offsetBytes.At s.regs.rbx.toBitVec)
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.IndexedAttestation.lvErrListTooBig_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrListTooBig" + 8).toBitVec)
          ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8))
          ⋆ ErrStr e1.toBitVec esp msg
          ⋆ StaticBox (BitVec.ofNat 64 ((s.regs.rcx.toNat - 228) / 8))
          ⋆ Eq (hb.At bx)
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩


/-- **Alignment reject (spec).** `bs.size ≥ 228`, `bs[0:4] = offsetBytes`, `(bs.size − 228) mod 8 ≠ 0`: EthLib rejects, and the machine code returns the `fmt.errorf` error (postcondition of `Decode.reject_alignment_statement`). -/
def Decode.reject_alignment_spec_error_word_nonzero_statement : Prop :=
  ∀ (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (bs : Array UInt8) (hbs : 228 ≤ bs.size) (hoff : bs.toList.take 4 = offsetBytes) (hmis : (bs.size - 228) % 8 ≠ 0)
    (s : MachineData) (ra guard e0 e1 : UInt64) (esp : BitVec 64) (msg ity : List UInt8)
    (he0 : e0.toBitVec = (label "go_itab._errors.errorString_error").toBitVec) (he0nz : e0 ≠ 0) (hity : ity.length = 8)
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
      ⋆ Eq (ElfData.IndexedAttestation.lvFmtMis.At ElfData.IndexedAttestation.lvFmtMis_addr)
      ⋆ Eq (offsetBytes.At s.regs.rbx.toBitVec)
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.IndexedAttestation.lvErrIncorrectListSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrIncorrectListSize" + 8).toBitVec)
      ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8))
      ⋆ ErrStr e1.toBitVec esp msg
      ⋆ StaticBox (s.regs.rcx.toBitVec - 228)
      ⋆ R)
    (hguard : guard.toNat + 48 < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bs.size)
    (hav : ElfData.IndexedAttestation.lvFmtMis.length + msg.length + 8220 ≤ avail)
    (hcv : ConvT64C Heap S) (hfe : FmtErrorfDWC Heap ElfData.IndexedAttestation.lvFmtMis ElfData.CheckpointAndEpoch.e2eIntType_addr S),
    (∃ e, deserialize desc bs = .error e) ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax ≠ 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (bx : BitVec 64) (hb spl' lo' : List UInt8) (avail' : Nat), spl'.length = 40 ∧ lo'.length = S
          ∧ BoxIn bx (s.regs.rcx.toBitVec - 228) hb ∧ avail' + hb.length ≤ avail ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 ElfData.CheckpointAndEpoch.e2eIntType_addr.toInt ++ Int.toBytes 8 bx.toInt ++ ity ++ Int.toBytes 8 e1.toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 176))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 117)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 184))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 (S)))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap avail'
          ⋆ Eq (ElfData.IndexedAttestation.lvFmtMis.At ElfData.IndexedAttestation.lvFmtMis_addr)
          ⋆ Eq (offsetBytes.At s.regs.rbx.toBitVec)
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.IndexedAttestation.lvErrIncorrectListSize_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrIncorrectListSize" + 8).toBitVec)
          ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8))
          ⋆ ErrStr e1.toBitVec esp msg
          ⋆ StaticBox (s.regs.rcx.toBitVec - 228)
          ⋆ Eq (hb.At bx)
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩


/-- **Overflow reject (spec).** `bs.size ≥ 228`, `bs[0:4] = offsetBytes`, `(bs.size − 228) mod 8 = 0`, `(bs.size − 228)/8 > 2048`: EthLib rejects, and the machine code returns the `fmt.errorf` error (postcondition of `Decode.reject_overflow_statement`). -/
def Decode.reject_overflow_spec_error_word_nonzero_statement : Prop :=
  ∀ (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (bs : Array UInt8) (hbs : 228 ≤ bs.size) (hoff : bs.toList.take 4 = offsetBytes) (hal : (bs.size - 228) % 8 = 0) (hbig : 2048 < (bs.size - 228) / 8)
    (s : MachineData) (ra guard e0 e1 : UInt64) (esp : BitVec 64) (msg ity : List UInt8)
    (he0 : e0.toBitVec = (label "go_itab._errors.errorString_error").toBitVec) (he0nz : e0 ≠ 0) (hity : ity.length = 8)
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
      ⋆ Eq (ElfData.IndexedAttestation.lvFmtTooBig.At ElfData.IndexedAttestation.lvFmtTooBig_addr)
      ⋆ Eq (offsetBytes.At s.regs.rbx.toBitVec)
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.IndexedAttestation.lvErrListTooBig_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrListTooBig" + 8).toBitVec)
      ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8))
      ⋆ ErrStr e1.toBitVec esp msg
      ⋆ StaticBox (BitVec.ofNat 64 ((s.regs.rcx.toNat - 228) / 8))
      ⋆ R)
    (hguard : guard.toNat + 48 < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bs.size)
    (hav : ElfData.IndexedAttestation.lvFmtTooBig.length + msg.length + 8220 ≤ avail)
    (hcv : ConvT64C Heap S) (hfe : FmtErrorfDWC Heap ElfData.IndexedAttestation.lvFmtTooBig ElfData.CheckpointAndEpoch.e2eIntType_addr S),
    (∃ e, deserialize desc bs = .error e) ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax ≠ 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (bx : BitVec 64) (hb spl' lo' : List UInt8) (avail' : Nat), spl'.length = 40 ∧ lo'.length = S
          ∧ BoxIn bx (BitVec.ofNat 64 ((s.regs.rcx.toNat - 228) / 8)) hb ∧ avail' + hb.length ≤ avail ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 ElfData.CheckpointAndEpoch.e2eIntType_addr.toInt ++ Int.toBytes 8 bx.toInt ++ ity ++ Int.toBytes 8 e1.toBitVec.toInt).At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 176))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 80)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 184))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 (S)))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap avail'
          ⋆ Eq (ElfData.IndexedAttestation.lvFmtTooBig.At ElfData.IndexedAttestation.lvFmtTooBig_addr)
          ⋆ Eq (offsetBytes.At s.regs.rbx.toBitVec)
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.IndexedAttestation.lvErrListTooBig_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrListTooBig" + 8).toBitVec)
          ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8))
          ⋆ ErrStr e1.toBitVec esp msg
          ⋆ StaticBox (BitVec.ofNat 64 ((s.regs.rcx.toNat - 228) / 8))
          ⋆ Eq (hb.At bx)
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩


end Prysm.IndexedAttestation
