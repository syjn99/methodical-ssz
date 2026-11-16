import Codec.CalleeDecode
import Codec.InlineUint64RegisterBase

/-!
# Statement kind of the callee-decoder call block

The kind is the conclusion of its lemma `call_decode_segment` (`Codec/CalleeDecode.lean`) with `j := k + j`, `j2 := k + j2`,
after the binders `k hk hf` (the idiom of `Codec/Kind/FieldPatterns.lean`). The `_of` theorem proves the kind from the lemma and
the code facts of an instance, so the kind body is kernel-checked against the lemma conclusion. The callee
specification `Uint64CalleeAccept fn` is a hypothesis of `callDecodeSegmentKind` (discharged at the composition by the
proved `Prysm.<Type>.Decode.accept_function_spec_holds` theorems).
`Codec/CalleeDecodeWindow.lean` states the window form `callDecodeSegmentKindWindow`.
-/

open Machine Runtime

open Codec
namespace Codec

variable [Host]

set_option linter.unusedVariables false in
/-- Call-block statement kind: `callq fn; test; je lok` at `k + j`, `lok:` at `k + j2` of the decoder `C`, callee specification `Uint64CalleeAccept fn` as a hypothesis. -/
abbrev callDecodeSegmentKind (C : Program) (fn lok : String) (j j2 : Nat) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k) (hC : Uint64CalleeAccept fn)
    (sp dst src aRet aFp aS2 : BitVec 64)
    (hRet : sp - 8 = aRet) (hFp : sp - 16 = aFp) (hS2 : sp + 8 = aS2)
    (rbp0 r140 guard : UInt64) (e8 rslot fp s2 c0 : List UInt8)
    (he8 : e8.length = 8) (hrs : rslot.length = 8) (hfp : fp.length = 8) (hs2 : s2.length = 8)
    (hc0 : c0.length = 8) (hguard : guard.toNat < aRet.toNat)
    (F : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140) (hrax : s.regs.rax.toBitVec = dst) (hrbx : s.regs.rbx.toBitVec = src)
    (hrcx : s.regs.rcx = 8)
    (h_mem : s.dmem =⋆ Eq (rslot.At aRet) ⋆ Eq (fp.At aFp) ⋆ Eq (s2.At aS2)
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
      ⋆ Eq (e8.At src) ⋆ Eq (c0.At dst) ⋆ F),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + j2 + 1) ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = { toBitVec := sp } ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        (Eq ((Int.toBytes 8 (Host.addrOf (k + j + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At aFp) ⋆ Eq ((Int.toBytes 8 src.toInt).At aS2)
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
          ⋆ Eq (e8.At src) ⋆ Eq (e8.At dst) ⋆ F) st.data.dmem)
      ⟨s, Host.addrOf (k + j)⟩

/-- `callDecodeSegmentKind` follows from `call_decode_segment` and the code facts of an instance. -/
theorem callDecodeSegmentKind_of (C : Program) (fn lok : String) (j j2 : Nat)
    (hA : ∀ k, C.IsInfixAt Host.prog k → (callDecode fn lok).IsInfixAt Host.prog (k + j))
    (hB : ∀ k, C.IsInfixAt Host.prog k → (callDecodeContinuationLabel lok).IsInfixAt Host.prog (k + j2))
    (hl : ∀ k, C.IsInfixAt Host.prog k → LabelsFresh C k → label lok = Host.addrOf (k + j2)) :
    callDecodeSegmentKind C fn lok j j2 :=
  fun k hk hf hC => call_decode_segment fn lok (k + j) (k + j2) (hA k hk) (hB k hk) (hl k hk hf) hC

end Codec
