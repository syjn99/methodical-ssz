import Codec.FixedBytesDecodeInline
import Machine.Labels

/-!
# Statement kind of the 4-byte fixed-bytes decode segment with an inline copy, over windows

`bytesDecodeInlineSegmentKindWindow C rX rB j1 jc e dR dB fP fL fC src` is the conclusion of
`bytes_decode_inline_segment_window` (`Codec/FixedBytesDecodeInline.lean`) for the decoder `C`.
The segment starts at `k + j1`, the `callq runtime.makeslice` is at `k + jc`, and the segment ends at `k + e`.
At the end the register `rX` holds the receiver and the register `rB` holds the buffer.
The temporary register, the label indices and the positions of nops are not in the statement.
So they are not kind parameters.
`bytesDecodeInlineSegmentKindWindow_of` proves the kind from the lemma and the window facts of an instance.
-/

open Machine Runtime

namespace Codec

variable [Host]

set_option linter.unusedVariables false in
/-- 4-byte inline-copy decode segment statement kind over windows. -/
abbrev bytesDecodeInlineSegmentKindWindow (C : Program) (rX rB : Reg64) (j1 jc e : Nat) (dR dB fP fL fC src : Int64) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k)
    (sp rcv bf aR aB aRet aLo aP aL aC aSrc : BitVec 64) (St : Nat)
    (hR : sp + dR.toBitVec = aR) (hB' : sp + dB.toBitVec = aB)
    (hRet : sp - 8 = aRet) (hLo : sp - 8 - BitVec.ofNat 64 St = aLo)
    (hP : rcv + fP.toBitVec = aP) (hL : rcv + fL.toBitVec = aL) (hC : rcv + fC.toBitVec = aC)
    (hSrc : bf + src.toBitVec = aSrc)
    (rbp0 r140 : UInt64) (root : List UInt8) (hroot : root.length = 4)
    (spl rslot lo vP vL vC : List UInt8)
    (hspl : spl.length = 24) (hrs : rslot.length = 8) (hlo : lo.length = St)
    (hvP : vP.length = 8) (hvL : vL.length = 8) (hvC : vC.length = 8)
    (R : DataMem → Prop) (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 4 ≤ avail)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
      ⋆ Eq (spl.At sp) ⋆ Eq (rslot.At aRet) ⋆ Eq (lo.At aLo)
      ⋆ Heap avail
      ⋆ Eq (vP.At aP) ⋆ Eq (vL.At aL) ⋆ Eq (vC.At aC)
      ⋆ Eq (root.At aSrc)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hms : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 St),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + e) ∧ st.data.regs.rsp = { toBitVec := sp }
        ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        ∃ (p : BitVec 64) (spl' lo' : List UInt8), spl'.length = 24 ∧ lo'.length = St
          ∧ st.data.regs.get64 rX = rcv ∧ st.data.regs.get64 rB = bf ∧
        (Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
          ⋆ Eq (spl'.At sp)
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + jc + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq (lo'.At aLo)
          ⋆ Heap (avail - 4)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aP) ⋆ Eq ((Int.toBytes 8 4).At aL)
          ⋆ Eq ((Int.toBytes 8 4).At aC) ⋆ Eq (root.At p)
          ⋆ Eq (root.At aSrc)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + j1)⟩

/-- `bytesDecodeInlineSegmentKindWindow` follows from `bytes_decode_inline_segment_window` and the window facts of an instance. -/
theorem bytesDecodeInlineSegmentKindWindow_of (C : Program) (rX rB rT : Reg64) (hX : rX = Reg64.rdx)
    (hBT : (rB = Reg64.rsi ∧ rT = Reg64.rdi) ∨ (rB = Reg64.rbx ∧ rT = Reg64.rsi))
    (j1 j2 j3 jl jw jc e : Nat) (lff lwb : String) (dR dB fP fL fC src : Int64) (qA qB qC : Program)
    (hqA : ∀ k, C.IsInfixAt Host.prog k → qA.IsInfixAt Host.prog (k + j1))
    (heA : eraseNop qA = bytesDecodeHeadRegister rX 4 lff dR fL fC)
    (hqB : ∀ k, C.IsInfixAt Host.prog k → qB.IsInfixAt Host.prog (k + j2))
    (heB : eraseNop qB = bytesDecodeInlineMiddle rX rB rT lff lwb dB fP fL fC src)
    (hqC : ∀ k, C.IsInfixAt Host.prog k → qC.IsInfixAt Host.prog (k + j3))
    (heC : eraseNop qC = bytesDecodeInlineTail rX lwb fP)
    (hjl : j2 + nonNopIndex qB 0 = jl)
    (hl : ∀ k, C.IsInfixAt Host.prog k → LabelsFresh C k → label lff = Host.addrOf (k + jl))
    (hjw : j3 + nonNopIndex qC 0 = jw)
    (hw : ∀ k, C.IsInfixAt Host.prog k → LabelsFresh C k → label lwb = Host.addrOf (k + jw))
    (hjc : j1 + nonNopIndex qA 3 = jc) (hend : j3 + qC.length = e) :
    bytesDecodeInlineSegmentKindWindow C rX rB j1 jc e dR dB fP fL fC src :=
  fun k hk hf => bytes_decode_inline_segment_window rX rB rT hX hBT lff lwb dR dB fP fL fC src qA qB qC
    (k + j1) (k + j2) (k + j3) (k + jl) (k + jw) (k + jc) (k + e) (hqA k hk) heA (hqB k hk) heB (hqC k hk) heC
    (by omega) (hl k hk hf) (by omega) (hw k hk hf) (by omega) (by omega)

end Codec
