import Fk.Contracts
import Fk.FunSpecs
import Fk.Frame
import Fk.Bytes
import Fk.Labels
import E2e.Data
import E2e.Code
import E2eAd.Code
import E2eAd.Data
import E2eList.CodeIa
import E2eList.DataIa
import E2eList.DefsIa

/-!
# Corrected T3 statements for P4 and P5: the itab word is non-zero (LV, user-approved correction after the freeze)

The four defs below are the frozen texts of `StmtIa.lean` with one added premise `(he0nz : e0 ≠ 0)` and the suffix
`_nz` in the name; nothing else differs. Reason: directives 103–106 (P4) and 66–69 (P5) are
`mov ssz.Err…(%rip),%rcx; test %rcx,%rcx; je …; mov 0x8(%rcx),%rcx`; when the error's itab word is 0 the code skips the
type-word load and passes 0 where `FmtErrorfDWC` needs `ity`. The Kraken Host places labels anywhere, so the itab label
may be 0 and the frozen statements cannot refute that branch. The precondition is stronger than the frozen one (not
equivalent). The originals in `StmtIa.lean` stay unchanged and unproved. Precedent: `Fk.lu_reject_misaligned_main`
(`Fk/LuRejectCall.lean`, Go 1.26.3) has the same two premises `e0 = itab` and `e0 ≠ 0`. In the real ELF `e0` is the
itab address (`STATEMENTS-T3.md`).
-/

open Fk E2e EthLib.Serialization.Ssz E2eList.Code
variable [Host]

namespace E2eList

/-- **P4 misaligned reject (machine).** `len(buf) ≥ 228`, offset 228, `(len − 228) mod 8 ≠ 0`: `convT64(len − 228)` and `fmt.errorf("misaligned bytes: … %d … %w", len − 228, ssz.ErrIncorrectListSize)`; the decoder returns that error (rax ≠ 0). The 32-byte argument array at rsp − 48 holds `type:int`, the box, the error's type word and data word. Exact frame; the heap shrinks by at most the box and the errorf allocation. -/
def ia_reject_misaligned_nz_stmt : Prop :=
  ∀ (k : Nat) (hk : IaUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh IaUnmarshal k)
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
      ⋆ Eq (E2eList.Data.lvFmtMis.At E2eList.Data.lvFmtMis_addr)
      ⋆ Eq (iaOff.At s.regs.rbx.toBitVec)
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At E2eList.Data.lvErrIncorrectListSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrIncorrectListSize" + 8).toBitVec)
      ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8))
      ⋆ ErrStr e1.toBitVec esp msg
      ⋆ StaticBox (s.regs.rcx.toBitVec - 228)
      ⋆ R)
    (hguard : guard.toNat + 48 < s.regs.rsp.toNat) (hlen : 228 ≤ s.regs.rcx.toNat) (hmis : (s.regs.rcx.toNat - 228) % 8 ≠ 0)
    (hav : E2eList.Data.lvFmtMis.length + msg.length + 8220 ≤ avail)
    (hcv : ConvT64C Heap S) (hfe : FmtErrorfDWC Heap E2eList.Data.lvFmtMis E2e.Data.e2eIntType_addr S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax ≠ 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (bx : BitVec 64) (hb spl' lo' : List UInt8) (avail' : Nat), spl'.length = 40 ∧ lo'.length = S
          ∧ BoxIn bx (s.regs.rcx.toBitVec - 228) hb ∧ avail' + hb.length ≤ avail ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 E2e.Data.e2eIntType_addr.toInt ++ Int.toBytes 8 bx.toInt ++ ity ++ Int.toBytes 8 e1.toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 176))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 117)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 184))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 (S)))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap avail'
          ⋆ Eq (E2eList.Data.lvFmtMis.At E2eList.Data.lvFmtMis_addr)
          ⋆ Eq (iaOff.At s.regs.rbx.toBitVec)
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At E2eList.Data.lvErrIncorrectListSize_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrIncorrectListSize" + 8).toBitVec)
          ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8))
          ⋆ ErrStr e1.toBitVec esp msg
          ⋆ StaticBox (s.regs.rcx.toBitVec - 228)
          ⋆ Eq (hb.At bx)
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩


/-- **P5 too-big reject (machine).** `len(buf) ≥ 228`, offset 228, `(len − 228) mod 8 = 0`, `numElem = (len − 228)/8 > 2048`: `convT64(numElem)` and `fmt.errorf("ssz-max exceeded: … %d … %w", numElem, ssz.ErrListTooBig)`; the decoder returns that error (rax ≠ 0). Argument array at rsp − 80. -/
def ia_reject_toobig_nz_stmt : Prop :=
  ∀ (k : Nat) (hk : IaUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh IaUnmarshal k)
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
      ⋆ Eq (E2eList.Data.lvFmtTooBig.At E2eList.Data.lvFmtTooBig_addr)
      ⋆ Eq (iaOff.At s.regs.rbx.toBitVec)
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At E2eList.Data.lvErrListTooBig_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrListTooBig" + 8).toBitVec)
      ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8))
      ⋆ ErrStr e1.toBitVec esp msg
      ⋆ StaticBox (BitVec.ofNat 64 ((s.regs.rcx.toNat - 228) / 8))
      ⋆ R)
    (hguard : guard.toNat + 48 < s.regs.rsp.toNat) (hlen : 228 ≤ s.regs.rcx.toNat) (hal : (s.regs.rcx.toNat - 228) % 8 = 0) (hbig : 2048 < (s.regs.rcx.toNat - 228) / 8)
    (hav : E2eList.Data.lvFmtTooBig.length + msg.length + 8220 ≤ avail)
    (hcv : ConvT64C Heap S) (hfe : FmtErrorfDWC Heap E2eList.Data.lvFmtTooBig E2e.Data.e2eIntType_addr S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax ≠ 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (bx : BitVec 64) (hb spl' lo' : List UInt8) (avail' : Nat), spl'.length = 40 ∧ lo'.length = S
          ∧ BoxIn bx (BitVec.ofNat 64 ((s.regs.rcx.toNat - 228) / 8)) hb ∧ avail' + hb.length ≤ avail ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 E2e.Data.e2eIntType_addr.toInt ++ Int.toBytes 8 bx.toInt ++ ity ++ Int.toBytes 8 e1.toBitVec.toInt).At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 176))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 80)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 184))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 (S)))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap avail'
          ⋆ Eq (E2eList.Data.lvFmtTooBig.At E2eList.Data.lvFmtTooBig_addr)
          ⋆ Eq (iaOff.At s.regs.rbx.toBitVec)
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At E2eList.Data.lvErrListTooBig_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrListTooBig" + 8).toBitVec)
          ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8))
          ⋆ ErrStr e1.toBitVec esp msg
          ⋆ StaticBox (BitVec.ofNat 64 ((s.regs.rcx.toNat - 228) / 8))
          ⋆ Eq (hb.At bx)
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩


/-- **P4 (spec).** `bs.size ≥ 228`, `bs[0:4] = iaOff`, `(bs.size − 228) mod 8 ≠ 0`: EthLib rejects, and the machine code returns the `fmt.errorf` error (postcondition of `ia_reject_misaligned_stmt`). -/
def ia_reject_misaligned_spec_nz_stmt : Prop :=
  ∀ (k : Nat) (hk : IaUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh IaUnmarshal k)
    (bs : Array UInt8) (hbs : 228 ≤ bs.size) (hoff : bs.toList.take 4 = iaOff) (hmis : (bs.size - 228) % 8 ≠ 0)
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
      ⋆ Eq (E2eList.Data.lvFmtMis.At E2eList.Data.lvFmtMis_addr)
      ⋆ Eq (iaOff.At s.regs.rbx.toBitVec)
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At E2eList.Data.lvErrIncorrectListSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrIncorrectListSize" + 8).toBitVec)
      ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8))
      ⋆ ErrStr e1.toBitVec esp msg
      ⋆ StaticBox (s.regs.rcx.toBitVec - 228)
      ⋆ R)
    (hguard : guard.toNat + 48 < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bs.size)
    (hav : E2eList.Data.lvFmtMis.length + msg.length + 8220 ≤ avail)
    (hcv : ConvT64C Heap S) (hfe : FmtErrorfDWC Heap E2eList.Data.lvFmtMis E2e.Data.e2eIntType_addr S),
    (∃ e, deserialize prysmIaDesc bs = .error e) ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax ≠ 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (bx : BitVec 64) (hb spl' lo' : List UInt8) (avail' : Nat), spl'.length = 40 ∧ lo'.length = S
          ∧ BoxIn bx (s.regs.rcx.toBitVec - 228) hb ∧ avail' + hb.length ≤ avail ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 E2e.Data.e2eIntType_addr.toInt ++ Int.toBytes 8 bx.toInt ++ ity ++ Int.toBytes 8 e1.toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 176))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 117)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 184))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 (S)))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap avail'
          ⋆ Eq (E2eList.Data.lvFmtMis.At E2eList.Data.lvFmtMis_addr)
          ⋆ Eq (iaOff.At s.regs.rbx.toBitVec)
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At E2eList.Data.lvErrIncorrectListSize_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrIncorrectListSize" + 8).toBitVec)
          ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8))
          ⋆ ErrStr e1.toBitVec esp msg
          ⋆ StaticBox (s.regs.rcx.toBitVec - 228)
          ⋆ Eq (hb.At bx)
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩


/-- **P5 (spec).** `bs.size ≥ 228`, `bs[0:4] = iaOff`, `(bs.size − 228) mod 8 = 0`, `(bs.size − 228)/8 > 2048`: EthLib rejects, and the machine code returns the `fmt.errorf` error (postcondition of `ia_reject_toobig_stmt`). -/
def ia_reject_toobig_spec_nz_stmt : Prop :=
  ∀ (k : Nat) (hk : IaUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh IaUnmarshal k)
    (bs : Array UInt8) (hbs : 228 ≤ bs.size) (hoff : bs.toList.take 4 = iaOff) (hal : (bs.size - 228) % 8 = 0) (hbig : 2048 < (bs.size - 228) / 8)
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
      ⋆ Eq (E2eList.Data.lvFmtTooBig.At E2eList.Data.lvFmtTooBig_addr)
      ⋆ Eq (iaOff.At s.regs.rbx.toBitVec)
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At E2eList.Data.lvErrListTooBig_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrListTooBig" + 8).toBitVec)
      ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8))
      ⋆ ErrStr e1.toBitVec esp msg
      ⋆ StaticBox (BitVec.ofNat 64 ((s.regs.rcx.toNat - 228) / 8))
      ⋆ R)
    (hguard : guard.toNat + 48 < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bs.size)
    (hav : E2eList.Data.lvFmtTooBig.length + msg.length + 8220 ≤ avail)
    (hcv : ConvT64C Heap S) (hfe : FmtErrorfDWC Heap E2eList.Data.lvFmtTooBig E2e.Data.e2eIntType_addr S),
    (∃ e, deserialize prysmIaDesc bs = .error e) ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax ≠ 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (bx : BitVec 64) (hb spl' lo' : List UInt8) (avail' : Nat), spl'.length = 40 ∧ lo'.length = S
          ∧ BoxIn bx (BitVec.ofNat 64 ((s.regs.rcx.toNat - 228) / 8)) hb ∧ avail' + hb.length ≤ avail ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 E2e.Data.e2eIntType_addr.toInt ++ Int.toBytes 8 bx.toInt ++ ity ++ Int.toBytes 8 e1.toBitVec.toInt).At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 176))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 80)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 184))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 (S)))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap avail'
          ⋆ Eq (E2eList.Data.lvFmtTooBig.At E2eList.Data.lvFmtTooBig_addr)
          ⋆ Eq (iaOff.At s.regs.rbx.toBitVec)
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At E2eList.Data.lvErrListTooBig_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrListTooBig" + 8).toBitVec)
          ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8))
          ⋆ ErrStr e1.toBitVec esp msg
          ⋆ StaticBox (BitVec.ofNat 64 ((s.regs.rcx.toNat - 228) / 8))
          ⋆ Eq (hb.At bx)
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩


end E2eList
