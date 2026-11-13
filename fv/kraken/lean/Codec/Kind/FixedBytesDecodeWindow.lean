import Codec.FixedBytesDecodeWindow
import Machine.Labels

/-!
# Statement kind of the fixed-bytes decode segment over windows

`bytesDecSegKindWindow n C rY j1 jm e dR dB dS fP fL fC src` is the conclusion of `bytesdec_seg_window` (`Codec/FixedBytesDecodeWindow.lean`)
for the decoder `C`: the segment starts at `k + j1`, the `callq runtime.memmove` is at `k + jm`, the segment
ends at `k + e`, and the register `rY` holds the receiver at the end. The register `rX`, the label index and
the positions of nops are not in the statement, so they are not kind parameters. `bytesDecSegKindWindow_of`
proves the kind from the lemma and the window facts of an instance.
-/

open Machine Runtime

namespace Codec

variable [Host]

set_option linter.unusedVariables false in
/-- Fixed-bytes decode segment statement kind over windows (add form). -/
abbrev bytesDecSegKindWindow (n : Nat) (C : Program) (rY : Reg64) (j1 jm e : Nat) (dR dB dS fP fL fC src : Int64) : Prop :=
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
      (fun st => st.pc = Host.addrOf (k + e) ∧ st.data.regs.rsp = { toBitVec := sp }
        ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        ∃ (p : BitVec 64) (spl' lo' : List UInt8), spl'.length = 24 ∧ lo'.length = St
          ∧ st.data.regs.get64 rY = rcv ∧
        (Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
          ⋆ Eq (spl'.At sp)
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + jm + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq (lo'.At aLo)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aS)
          ⋆ Heap (avail - n)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At aP) ⋆ Eq ((Int.toBytes 8 (OfNat.ofNat n)).At aL)
          ⋆ Eq ((Int.toBytes 8 (OfNat.ofNat n)).At aC) ⋆ Eq (root.At p)
          ⋆ Eq (root.At aSrc)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + j1)⟩

/-- `bytesDecSegKindWindow` follows from `bytesdec_seg_window` and the window facts of an instance. -/
theorem bytesDecSegKindWindow_of (n : Nat) (hn : n = 32 ∨ n = 48 ∨ n = 96) (C : Program) (rX rY : Reg64)
    (hX : rX = Reg64.rdx ∨ rX = Reg64.rsi)
    (hY : rY = Reg64.rax ∨ rY = Reg64.rcx ∨ rY = Reg64.rdx ∨ rY = Reg64.rsi ∨ rY = Reg64.rdi)
    (j1 j2 jl jm e : Nat) (lff lwb : String) (dR dB dS fP fL fC src : Int64) (qA qB : Program)
    (hqA : ∀ k, C.IsInfixAt Host.prog k → qA.IsInfixAt Host.prog (k + j1))
    (heA : eraseNop qA = bytesDecHeadRegister rX (OfNat.ofNat n) lff dR fL fC)
    (hqB : ∀ k, C.IsInfixAt Host.prog k → qB.IsInfixAt Host.prog (k + j2))
    (heB : eraseNop qB = bytesDecMidRegisters rX rY (OfNat.ofNat n) lff lwb dR dB dS fP fL fC src)
    (hjl : j2 + nonNopIndex qB 0 = jl)
    (hl : ∀ k, C.IsInfixAt Host.prog k → LabelsFresh C k → label lff = Host.addrOf (k + jl))
    (hjm : j2 + nonNopIndex qB 6 = jm) (hend : j2 + qB.length = e) :
    bytesDecSegKindWindow n C rY j1 jm e dR dB dS fP fL fC src :=
  fun k hk hf => bytesdec_seg_window n hn rX rY hX hY lff lwb dR dB dS fP fL fC src qA qB (k + j1) (k + j2) (k + jl)
    (k + jm) (k + e) (hqA k hk) heA (hqB k hk) heB (by omega) (hl k hk hf) (by omega) (by omega)

end Codec
