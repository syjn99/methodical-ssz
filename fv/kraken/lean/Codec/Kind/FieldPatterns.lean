import Codec.Uint64Decoder
import Codec.Bytes32Decode

/-!
# Frozen statement kinds of the generated theorems (review fix-r1 M2, S1)

A generated theorem `t` is followed by `t_kind : ∀ (h : Host), type_of% (@t h) = <kind> …` (`rfl`).
`@t h` is the whole declared type, binders before the colon included. So an added, removed or changed
hypothesis anywhere in the statement makes `t_kind` fail. A theorem that only has an `exact` against the
lemma instance does not have this property: `theorem t (hx : 1 = 2) : P := p` compiles when `p` does not use `hx`.

The kinds are hand text, written once, and do not depend on a hand theorem of the instance type.
`u64DecAcceptKind_of` and `rootDecSegKind_of` prove each kind from the code facts of its lemma, so the kind
body is kernel-checked against the lemma conclusion. They are `abbrev`s: `with_reducible rfl` unfolds
them, but not `Int.toBytes` or other semireducible definitions. A wrong literal fails fast and does not run
into a long unfolding.
The anchors in `Prysm/Slot/Uint64DecoderKindAnchors.lean` show that the uint64 decoder kind is the statement of the reviewed hand
theorems `Prysm.Slot.Decode.accept` and `Prysm.CommitteeIndex.Decode.accept`.
-/

open Machine Runtime

namespace Codec

variable [Host]

set_option linter.unusedVariables false in
/-- Statement kind of the uint64 decoder pattern: the accept path of a uint64 primitive `UnmarshalSSZ` whose code constant is `C`.
The text is the statement of `Prysm.Slot.Decode.accept` with `SlUnmarshal` replaced by `C` and
every binder after the colon. -/
abbrev u64DecAcceptKind (C : Program) : Prop :=
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

/-- The uint64 decoder kind follows from `u64dec_accept` and the code facts of an instance (kernel check that the
kind body is the lemma conclusion at `j := k`). -/
theorem u64DecAcceptKind_of (C : Program) (fn l0 lcc lbb : String) (fs dsp : Int64)
    (hdsp : dsp.toBitVec = fs.toBitVec + 24) (jb : Nat)
    (hA : ∀ k, C.IsInfixAt Host.prog k → (u64DecHead fn l0 lcc lbb fs dsp).IsInfixAt Host.prog k)
    (hB : ∀ k, C.IsInfixAt Host.prog k → (u64DecTail lbb fs).IsInfixAt Host.prog (k + jb))
    (hl : ∀ k, C.IsInfixAt Host.prog k → LabelsFresh C k → label lbb = Host.addrOf (k + jb)) :
    u64DecAcceptKind C :=
  fun k hk hf => u64dec_accept fn l0 lcc lbb fs dsp hdsp k (k + jb) (hA k hk) (hB k hk) (hl k hk hf)

set_option linter.unusedVariables false in
/-- P2 decode statement kind: the decode segment of one 32-byte field of the decoder `C`, head block at
`k + j1`, second block at `k + j2`, with the stack displacements `dR dB dS`, the Go field offsets
`fP fL fC` and the SSZ source offset `src`. The text is the conclusion of `rootdec_seg` with
`j1 := k + j1`, `j2 := k + j2`, after the binders `k hk hf`. -/
abbrev rootDecSegKind (C : Program) (j1 j2 : Nat) (dR dB dS fP fL fC src : Int64) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k)
    (sp rcv bf aR aB aS aRet aLo aP aL aC aSrc : BitVec 64) (St : Nat)
    (hR : sp + dR.toBitVec = aR) (hB' : sp + dB.toBitVec = aB) (hS : sp + dS.toBitVec = aS)
    (hRet : sp - 8 = aRet) (hLo : sp - 8 - BitVec.ofNat 64 St = aLo)
    (hP : rcv + fP.toBitVec = aP) (hL : rcv + fL.toBitVec = aL) (hC : rcv + fC.toBitVec = aC)
    (hSrc : bf + src.toBitVec = aSrc)
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
      ⋆ Eq (root.At aSrc)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hms : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 St) (hmm : MemmoveC St),
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
          ⋆ Heap (avail - 32)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aP) ⋆ Eq ((Int.toBytes 8 32).At aL)
          ⋆ Eq ((Int.toBytes 8 32).At aC) ⋆ Eq (root.At p)
          ⋆ Eq (root.At aSrc)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + j1)⟩

/-- The P2 decode kind follows from `rootdec_seg` and the code facts of an instance (kernel check that the
kind body is the lemma conclusion at `j1 := k + j1`, `j2 := k + j2`). -/
theorem rootDecSegKind_of (C : Program) (lff lwb : String) (dR dB dS fP fL fC src : Int64) (j1 j2 : Nat)
    (hA : ∀ k, C.IsInfixAt Host.prog k → (rootDecHead lff dR fL fC).IsInfixAt Host.prog (k + j1))
    (hB : ∀ k, C.IsInfixAt Host.prog k → (rootDecMid lff lwb dR dB dS fP fL fC src).IsInfixAt Host.prog (k + j2))
    (hl : ∀ k, C.IsInfixAt Host.prog k → LabelsFresh C k → label lff = Host.addrOf (k + j2)) :
    rootDecSegKind C j1 j2 dR dB dS fP fL fC src :=
  fun k hk hf => rootdec_seg lff lwb dR dB dS fP fL fC src (k + j1) (k + j2) (hA k hk) (hB k hk) (hl k hk hf)

end Codec
