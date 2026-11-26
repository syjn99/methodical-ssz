module

public import Codec.CalleeDecodeWindow

@[expose] public section

/-!
# Statement kind of the callee-decoder call block over a window

`callDecodeSegmentKindWindow C fn lok j jc j2` is the conclusion of `call_decode_segment_window` (`Codec/CalleeDecodeWindow.lean`)
for the decoder `C`: the block starts at `k + j`, the `callq` is at `k + jc`, and the label `lok:` is at `k + j2`.
`callDecodeSegmentKindWindow_of` proves the kind from the lemma and the window facts of an instance.
-/

open Machine Runtime

open Codec
namespace Codec

variable [Host]

set_option linter.unusedVariables false in
/-- Call-block statement kind over a window: start `k + j`, `callq` at `k + jc`, `lok:` at `k + j2`. -/
abbrev callDecodeSegmentKindWindow (C : Program) (fn lok : String) (j jc j2 : Nat) : Prop :=
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
        (Eq ((Int.toBytes 8 (Host.addrOf (k + jc + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At aFp) ⋆ Eq ((Int.toBytes 8 src.toInt).At aS2)
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
          ⋆ Eq (e8.At src) ⋆ Eq (e8.At dst) ⋆ F) st.data.dmem)
      ⟨s, Host.addrOf (k + j)⟩

/-- `callDecodeSegmentKindWindow` follows from `call_decode_segment_window` and the window facts of an instance. -/
theorem callDecodeSegmentKindWindow_of (C : Program) (fn lok : String) (j jc j2 : Nat) (q : Program)
    (hq : ∀ k, C.IsInfixAt Host.prog k → q.IsInfixAt Host.prog (k + j)) (he : eraseNop q = callDecode fn lok)
    (hjc : j + nonNopIndex q 0 = jc)
    (hB : ∀ k, C.IsInfixAt Host.prog k → (callDecodeContinuationLabel lok).IsInfixAt Host.prog (k + j2))
    (hl : ∀ k, C.IsInfixAt Host.prog k → LabelsFresh C k → label lok = Host.addrOf (k + j2)) :
    callDecodeSegmentKindWindow C fn lok j jc j2 :=
  fun k hk hf hC => call_decode_segment_window fn lok q (k + j) (k + jc) (k + j2) (hq k hk) he (by omega) (hB k hk)
    (hl k hk hf) hC

end Codec
