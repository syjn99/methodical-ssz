import Codec.FixedBytesDecode

/-!
# Statement kinds of the size-parametric fixed-bytes decode segments

`bytesDecodeSegmentKind n` / `bytesDecodeSegmentOffsetZeroKind n` are the texts of `rootDecodeSegmentKind` (`Codec/Kind/FieldPatterns.lean`) and
`rootDecodeSegmentOffsetZeroKind` (`Codec/Kind/Bytes32DecodeOffsetZero.lean`) with the size `32` replaced by the parameter `n : Nat` (four places:
`root.length = n`, `n ≤ avail`, `Heap (avail - n)`, `Int.toBytes 8 (OfNat.ofNat n)` twice). `Codec/Kind/FieldPatterns.lean` and `Codec/Kind/Bytes32DecodeOffsetZero.lean`
are unchanged. `bytesDecodeSegmentKind_of` / `bytesDecodeSegmentOffsetZeroKind_of` prove a kind from the lemma (`bytes_decode_segment`,
`bytes_decode_segment_offset_zero`) and the code facts of an instance, so the kind body is kernel-checked against the lemma
conclusion. The kind has no size hypothesis: for a size outside 32 / 48 / 96 it is a proposition without a
proof here. `Codec/FixedBytesDecodeSizeInstances.lean` shows `rootDecodeSegmentKind = bytesDecodeSegmentKind 32` and
`rootDecodeSegmentOffsetZeroKind = bytesDecodeSegmentOffsetZeroKind 32` (`rfl`).
-/

open Machine Runtime

namespace Codec

variable [Host]

set_option linter.unusedVariables false in
/-- Fixed-bytes decode statement kind, add form: the decode segment of one `n`-byte field of the decoder `C`,
head block at `k + j1`, second block at `k + j2`, stack displacements `dR dB dS`, Go field offsets
`fP fL fC`, SSZ source offset `src`. The text is the conclusion of `bytes_decode_segment` with `j1 := k + j1`,
`j2 := k + j2`, after the binders `k hk hf`. -/
abbrev bytesDecodeSegmentKind (n : Nat) (C : Program) (j1 j2 : Nat) (dR dB dS fP fL fC src : Int64) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k)
    (sp rcv bf aR aB aS aRet aLo aP aL aC aSrc : BitVec 64) (St : Nat)
    (hR : sp + dR.toBitVec = aR) (hB' : sp + dB.toBitVec = aB) (hS : sp + dS.toBitVec = aS)
    (hRet : sp - 8 = aRet) (hLo : sp - 8 - BitVec.ofNat 64 St = aLo)
    (hP : rcv + fP.toBitVec = aP) (hL : rcv + fL.toBitVec = aL) (hC : rcv + fC.toBitVec = aC)
    (hSrc : bf + src.toBitVec = aSrc)
    (rbp0 r140 : UInt64) (root : List UInt8) (hroot : root.length = n)
    (spl rslot lo lS vP vL vC : List UInt8)
    (hspl : spl.length = 24) (hrs : rslot.length = 8) (hlo : lo.length = St) (hlS : lS.length = 8)
    (hvP : vP.length = 8) (hvL : vL.length = 8) (hvC : vC.length = 8)
    (R : DataMem → Prop) (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : n ≤ avail)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
      ⋆ Eq (spl.At sp) ⋆ Eq (rslot.At aRet) ⋆ Eq (lo.At aLo) ⋆ Eq (lS.At aS)
      ⋆ Heap avail
      ⋆ Eq (vP.At aP) ⋆ Eq (vL.At aL) ⋆ Eq (vC.At aC)
      ⋆ Eq (root.At aSrc)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hms : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 St) (hmm : MemmoveContract St),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + j2 + 12) ∧ st.data.regs.rsp = { toBitVec := sp }
        ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        ∃ (p : BitVec 64) (spl' lo' : List UInt8), spl'.length = 24 ∧ lo'.length = St
          ∧ st.data.regs.rdx.toBitVec = rcv ∧
        (Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
          ⋆ Eq (spl'.At sp)
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + j2 + 6 + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq (lo'.At aLo)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aS)
          ⋆ Heap (avail - n)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aP) ⋆ Eq ((Int.toBytes 8 (OfNat.ofNat n)).At aL)
          ⋆ Eq ((Int.toBytes 8 (OfNat.ofNat n)).At aC) ⋆ Eq (root.At p)
          ⋆ Eq (root.At aSrc)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + j1)⟩

/-- The add-form kind follows from `bytes_decode_segment` and the code facts of an instance. -/
theorem bytesDecodeSegmentKind_of (n : Nat) (hn : n = 32 ∨ n = 48 ∨ n = 96) (C : Program) (lff lwb : String)
    (dR dB dS fP fL fC src : Int64) (j1 j2 : Nat)
    (hA : ∀ k, C.IsInfixAt Host.prog k → (bytesDecodeHead (OfNat.ofNat n) lff dR fL fC).IsInfixAt Host.prog (k + j1))
    (hB : ∀ k, C.IsInfixAt Host.prog k →
      (bytesDecodeMiddle (OfNat.ofNat n) lff lwb dR dB dS fP fL fC src).IsInfixAt Host.prog (k + j2))
    (hl : ∀ k, C.IsInfixAt Host.prog k → LabelsFresh C k → label lff = Host.addrOf (k + j2)) :
    bytesDecodeSegmentKind n C j1 j2 dR dB dS fP fL fC src :=
  fun k hk hf => bytes_decode_segment n hn lff lwb dR dB dS fP fL fC src (k + j1) (k + j2) (hA k hk) (hB k hk) (hl k hk hf)

set_option linter.unusedVariables false in
/-- Fixed-bytes decode statement kind, offset-0 form: as `bytesDecodeSegmentKind` without `src`, source bytes at
`bf`, second block `bytesDecodeMiddleOffsetZero` (11 directives). The text is the conclusion of `bytes_decode_segment_offset_zero`. -/
abbrev bytesDecodeSegmentOffsetZeroKind (n : Nat) (C : Program) (j1 j2 : Nat) (dR dB dS fP fL fC : Int64) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k)
    (sp rcv bf aR aB aS aRet aLo aP aL aC : BitVec 64) (St : Nat)
    (hR : sp + dR.toBitVec = aR) (hB' : sp + dB.toBitVec = aB) (hS : sp + dS.toBitVec = aS)
    (hRet : sp - 8 = aRet) (hLo : sp - 8 - BitVec.ofNat 64 St = aLo)
    (hP : rcv + fP.toBitVec = aP) (hL : rcv + fL.toBitVec = aL) (hC : rcv + fC.toBitVec = aC)
    (rbp0 r140 : UInt64) (root : List UInt8) (hroot : root.length = n)
    (spl rslot lo lS vP vL vC : List UInt8)
    (hspl : spl.length = 24) (hrs : rslot.length = 8) (hlo : lo.length = St) (hlS : lS.length = 8)
    (hvP : vP.length = 8) (hvL : vL.length = 8) (hvC : vC.length = 8)
    (R : DataMem → Prop) (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : n ≤ avail)
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
          ⋆ Heap (avail - n)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aP) ⋆ Eq ((Int.toBytes 8 (OfNat.ofNat n)).At aL)
          ⋆ Eq ((Int.toBytes 8 (OfNat.ofNat n)).At aC) ⋆ Eq (root.At p)
          ⋆ Eq (root.At bf)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + j1)⟩

/-- The offset-0 kind follows from `bytes_decode_segment_offset_zero` and the code facts of an instance. -/
theorem bytesDecodeSegmentOffsetZeroKind_of (n : Nat) (hn : n = 32 ∨ n = 48 ∨ n = 96) (C : Program) (lff lwb : String)
    (dR dB dS fP fL fC : Int64) (j1 j2 : Nat)
    (hA : ∀ k, C.IsInfixAt Host.prog k → (bytesDecodeHead (OfNat.ofNat n) lff dR fL fC).IsInfixAt Host.prog (k + j1))
    (hB : ∀ k, C.IsInfixAt Host.prog k →
      (bytesDecodeMiddleOffsetZero (OfNat.ofNat n) lff lwb dR dB dS fP fL fC).IsInfixAt Host.prog (k + j2))
    (hl : ∀ k, C.IsInfixAt Host.prog k → LabelsFresh C k → label lff = Host.addrOf (k + j2)) :
    bytesDecodeSegmentOffsetZeroKind n C j1 j2 dR dB dS fP fL fC :=
  fun k hk hf => bytes_decode_segment_offset_zero n hn lff lwb dR dB dS fP fL fC (k + j1) (k + j2) (hA k hk) (hB k hk) (hl k hk hf)

end Codec
