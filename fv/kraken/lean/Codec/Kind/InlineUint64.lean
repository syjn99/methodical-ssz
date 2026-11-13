import Codec.InlineUint64

/-!
# Statement kind of the inline uint64 decode segments

`uint64DecodeInlineSegmentKind C j dB src f` is the conclusion of `uint64_decode_inline_segment` with `j := k + j`, after the
binders `k hk hf` (the idiom of `Codec/Kind/FieldPatterns.lean`). The scratch register is not in the kind, because it is not in
the statement. `uint64DecodeInlineSegmentKind_of` proves the kind from the lemma and the code fact of an instance, so
the kind body is kernel-checked against the lemma conclusion.
-/

open Machine Runtime

namespace Codec

variable [Host]

set_option linter.unusedVariables false in
/-- Inline uint64 decode statement kind: the segment of one inline uint64 field of the decoder `C`, three
directives at `k + j`, buffer spill displacement `dB`, SSZ source offset `src`, Go field offset `f`. -/
abbrev uint64DecodeInlineSegmentKind (C : Program) (j : Nat) (dB src f : Int64) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k)
    (sp rcv bf aB aSrc aF : BitVec 64)
    (hB' : sp + dB.toBitVec = aB) (hSrc : bf + src.toBitVec = aSrc) (hF : rcv + f.toBitVec = aF)
    (rbp0 r140 : UInt64) (v vF : List UInt8) (hv : v.length = 8) (hvF : vF.length = 8)
    (R : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140) (hrdx : s.regs.rdx.toBitVec = rcv)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 bf.toInt).At aB) ⋆ Eq (v.At aSrc) ⋆ Eq (vF.At aF) ⋆ R),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + j + 3) ∧ st.data.regs.rsp = { toBitVec := sp }
        ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧ st.data.regs.rdx.toBitVec = rcv ∧
        (Eq ((Int.toBytes 8 bf.toInt).At aB) ⋆ Eq (v.At aSrc) ⋆ Eq (v.At aF) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + j)⟩

/-- The inline uint64 kind follows from `uint64_decode_inline_segment` and the code fact of an instance. -/
theorem uint64DecodeInlineSegmentKind_of (C : Program) (rX : Reg64) (hX : Uint64InlineReg rX) (dB src f : Int64) (j : Nat)
    (hA : ∀ k, C.IsInfixAt Host.prog k → (uint64DecodeInline rX dB src f).IsInfixAt Host.prog (k + j)) :
    uint64DecodeInlineSegmentKind C j dB src f :=
  fun k hk _ => uint64_decode_inline_segment rX hX dB src f (k + j) (hA k hk)

end Codec
