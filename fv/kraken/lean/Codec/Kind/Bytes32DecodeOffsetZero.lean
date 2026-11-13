import Codec.Bytes32DecodeOffsetZero

/-!
# Statement kind of the generated offset-0 decode segments

Added after the frozen generator ran on the hold-out types, so no hold-out type tests it. `Codec/Kind/FieldPatterns.lean` is not
changed. `rootDecSegOffsetZeroKind` is the text of `rootDecSegKind` with the
`add`-form parts removed: no `src`, no `aSrc` / `hSrc`, the source bytes at `bf`, end pc `k + j2 + 11`,
memmove return address `k + j2 + 5 + 1`. `rootDecSegOffsetZeroKind_of` proves the kind from the lemma
`rootdec_seg_offset_zero` (kernel check that the kind body is the lemma conclusion). `gen/generator/kindcheck.py` accepts
it only with this file at its pinned blob.
-/

open Machine Runtime

namespace Codec

variable [Host]

set_option linter.unusedVariables false in
/-- P2 decode statement kind, offset-0 form: the decode segment of one 32-byte field at SSZ offset 0 of the
decoder `C`, head block at `k + j1`, second block (`rootDecMidOffsetZero`) at `k + j2`, with the stack displacements
`dR dB dS` and the Go field offsets `fP fL fC`. The text is the conclusion of `rootdec_seg_offset_zero` with
`j1 := k + j1`, `j2 := k + j2`, after the binders `k hk hf`. -/
abbrev rootDecSegOffsetZeroKind (C : Program) (j1 j2 : Nat) (dR dB dS fP fL fC : Int64) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k)
    (sp rcv bf aR aB aS aRet aLo aP aL aC : BitVec 64) (St : Nat)
    (hR : sp + dR.toBitVec = aR) (hB' : sp + dB.toBitVec = aB) (hS : sp + dS.toBitVec = aS)
    (hRet : sp - 8 = aRet) (hLo : sp - 8 - BitVec.ofNat 64 St = aLo)
    (hP : rcv + fP.toBitVec = aP) (hL : rcv + fL.toBitVec = aL) (hC : rcv + fC.toBitVec = aC)
    (rbp0 r140 : UInt64) (root : List UInt8) (hroot : root.length = 32)
    (spl rslot lo lS vP vL vC : List UInt8)
    (hspl : spl.length = 24) (hrs : rslot.length = 8) (hlo : lo.length = St) (hlS : lS.length = 8)
    (hvP : vP.length = 8) (hvL : vL.length = 8) (hvC : vC.length = 8)
    (R : DataMem → Prop) (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 32 ≤ avail)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
      ⋆ Eq (spl.At sp) ⋆ Eq (rslot.At aRet) ⋆ Eq (lo.At aLo) ⋆ Eq (lS.At aS)
      ⋆ Heap avail
      ⋆ Eq (vP.At aP) ⋆ Eq (vL.At aL) ⋆ Eq (vC.At aC)
      ⋆ Eq (root.At bf)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hms : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 St) (hmm : MemmoveContract St),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + j2 + 11) ∧ st.data.regs.rsp = { toBitVec := sp }
        ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        ∃ (p : BitVec 64) (spl' lo' : List UInt8), spl'.length = 24 ∧ lo'.length = St
          ∧ st.data.regs.rdx.toBitVec = rcv ∧
        (Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
          ⋆ Eq (spl'.At sp)
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + j2 + 5 + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq (lo'.At aLo)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aS)
          ⋆ Heap (avail - 32)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aP) ⋆ Eq ((Int.toBytes 8 32).At aL)
          ⋆ Eq ((Int.toBytes 8 32).At aC) ⋆ Eq (root.At p)
          ⋆ Eq (root.At bf)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + j1)⟩

/-- The offset-0 kind follows from `rootdec_seg_offset_zero` and the code facts of an instance (kernel check that the
kind body is the lemma conclusion at `j1 := k + j1`, `j2 := k + j2`). -/
theorem rootDecSegOffsetZeroKind_of (C : Program) (lff lwb : String) (dR dB dS fP fL fC : Int64) (j1 j2 : Nat)
    (hA : ∀ k, C.IsInfixAt Host.prog k → (rootDecHead lff dR fL fC).IsInfixAt Host.prog (k + j1))
    (hB : ∀ k, C.IsInfixAt Host.prog k → (rootDecMidOffsetZero lff lwb dR dB dS fP fL fC).IsInfixAt Host.prog (k + j2))
    (hl : ∀ k, C.IsInfixAt Host.prog k → LabelsFresh C k → label lff = Host.addrOf (k + j2)) :
    rootDecSegOffsetZeroKind C j1 j2 dR dB dS fP fL fC :=
  fun k hk hf => rootdec_seg_offset_zero lff lwb dR dB dS fP fL fC (k + j1) (k + j2) (hA k hk) (hB k hk) (hl k hk hf)

end Codec
