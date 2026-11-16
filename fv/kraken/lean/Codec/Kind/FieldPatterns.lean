import Codec.Uint64Decoder
import Codec.SegmentTemplate
import Runtime.Contracts

/-!
# Frozen statement kinds of the generated theorems

A generated theorem `t` is followed by `t_kind : ∀ (h : Host), type_of% (@t h) = <kind> …` (`rfl`).
`@t h` is the whole declared type, binders before the colon included. So an added, removed or changed
hypothesis anywhere in the statement makes `t_kind` fail. A theorem that only has an `exact` against the
lemma instance does not have this property: `theorem t (hx : 1 = 2) : P := p` compiles when `p` does not use `hx`.

The kinds are hand text and do not depend on a hand theorem of the instance type.
`uint64DecodeAcceptKind_of` proves the kind of this module from the code facts of its lemma, so the kind
body is kernel-checked against the lemma conclusion. The kinds are `abbrev`s: `with_reducible rfl` unfolds
them, but not `Int.toBytes` or other semireducible definitions. A wrong literal fails fast and does not run
into a long unfolding.
The anchors in `Prysm/Slot/Uint64DecoderKindSameAsHand.lean` show that the uint64 decoder kind is the statement of the reviewed hand
theorems `Prysm.Slot.Decode.accept` and `Prysm.CommitteeIndex.Decode.accept`.
-/

open Machine Runtime

namespace Codec

variable [Host]

set_option linter.unusedVariables false in
/-- Statement kind of the uint64 decoder pattern: the accept path of a uint64 primitive `UnmarshalSSZ` whose code constant is `C`.
The text is the statement of `Prysm.Slot.Decode.accept` with `Prysm.Slot.Code.unmarshalSSZ` replaced by `C` and
every binder after the colon. -/
abbrev uint64DecodeAcceptKind (C : Program) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k)
    (e8 : List UInt8) (he8 : e8.length = 8)
    (s : MachineData) (ra guard : UInt64) (fp s2 c0 : List UInt8)
    (hfp : fp.length = 8) (h2 : s2.length = 8) (hc0 : c0.length = 8) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (e8.At s.regs.rbx.toBitVec) ⋆ Eq (c0.At s.regs.rax.toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx = 8),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (e8.At s.regs.rbx.toBitVec) ⋆ Eq (e8.At s.regs.rax.toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- The uint64 decoder kind follows from `uint64_decode_accept` and the code facts of an instance (kernel check that the
kind body is the lemma conclusion at `j := k`). -/
theorem uint64DecodeAcceptKind_of (C : Program) (fn l0 lcc lbb : String) (fs dsp : Int64)
    (hdsp : dsp.toBitVec = fs.toBitVec + 24) (jb : Nat)
    (hA : ∀ k, C.IsInfixAt Host.prog k → (uint64DecodeHead fn l0 lcc lbb fs dsp).IsInfixAt Host.prog k)
    (hB : ∀ k, C.IsInfixAt Host.prog k → (uint64DecodeTail lbb fs).IsInfixAt Host.prog (k + jb))
    (hl : ∀ k, C.IsInfixAt Host.prog k → LabelsFresh C k → label lbb = Host.addrOf (k + jb)) :
    uint64DecodeAcceptKind C :=
  fun k hk hf => uint64_decode_accept fn l0 lcc lbb fs dsp hdsp k (k + jb) (hA k hk) (hB k hk) (hl k hk hf)

end Codec
