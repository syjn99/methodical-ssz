import Codec.NestedCheckpointDecode
import Machine.Labels

/-!
# Statement kind of the nested Checkpoint field block over windows

`nestedCheckpointDecodeKindWindow C fn j1 jc j3 dR fP dB src dC` is the conclusion of `nested_checkpoint_decode_window`
(`Codec/NestedCheckpointDecode.lean`) for the decoder `C`: the block starts at `k + j1`, the `callq fn` is at `k + jc`,
and the label `lok:` is at `k + j3`.
The labels, the second window start, the `add $rest,%rdi` immediate and the positions of nops are not in the statement,
so they are not kind parameters.
`nestedCheckpointDecodeKindWindow_of` proves the kind from the lemma and the window facts of an instance.
-/

open Machine Runtime

namespace Codec

variable [Host]

set_option linter.unusedVariables false in
/-- Nested Checkpoint field block statement kind over windows. -/
abbrev nestedCheckpointDecodeKindWindow (C : Program) (fn : String) (j1 jc j3 : Nat) (dR fP dB src dC : Int64) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k)
    (S : Nat) (hS8 : 8 ≤ S) (hS : S < 2 ^ 60) (Heap : Nat → DataMem → Prop)
    (hC : NestedCheckpointCalleeAccept fn Heap S)
    (hno : NewobjectContract Heap ElfData.PrysmTarget.typeCheckpoint_addr 72 (S + 96))
    (sp rcv bf aR aB aC aW1 aRet aLo aP aSrc aRoot : BitVec 64)
    (hR : sp + dR.toBitVec = aR) (hB' : sp + dB.toBitVec = aB) (hC' : sp + dC.toBitVec = aC)
    (hW1 : sp + 8 = aW1) (hRet : sp - 8 = aRet) (hLo : sp - 8 - BitVec.ofNat 64 (S + 96) = aLo)
    (hP : rcv + fP.toBitVec = aP) (hSrc : bf + src.toBitVec = aSrc) (hRoot : aSrc + 8 = aRoot)
    (rbp0 r140 guard : UInt64) (hguard : guard.toNat + 96 < aRet.toNat)
    (e8 root : List UInt8) (he8 : e8.length = 8) (hroot : root.length = 32)
    (w0 w1 rslot lo cap vP : List UInt8) (hw0 : w0.length = 8) (hw1 : w1.length = 8) (hrs : rslot.length = 8)
    (hlo : lo.length = S + 96) (hcap : cap.length = 8) (hvP : vP.length = 8)
    (avail : Nat) (hav : 104 ≤ avail) (R : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
      ⋆ Eq (cap.At aC) ⋆ Eq (w0.At sp) ⋆ Eq (w1.At aW1) ⋆ Eq (rslot.At aRet) ⋆ Eq (lo.At aLo)
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (vP.At aP) ⋆ Eq (e8.At aSrc) ⋆ Eq (root.At aRoot)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + j3 + 1) ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = { toBitVec := sp } ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        ∃ (po pr : BitVec 64) (lo' : List UInt8), lo'.length = S + 96 ∧
        (Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
          ⋆ Eq (cap.At aC) ⋆ Eq ((Int.toBytes 8 po.toInt).At sp) ⋆ Eq ((Int.toBytes 8 aSrc.toInt).At aW1)
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + jc + 1)).toBitVec.toInt).At aRet) ⋆ Eq (lo'.At aLo)
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
          ⋆ Heap (avail - 104)
          ⋆ Eq ((Int.toBytes 8 po.toInt).At aP)
          ⋆ Eq ((List.replicate 8 0).At po) ⋆ Eq (e8.At (po + 8))
          ⋆ Eq ((Int.toBytes 8 pr.toInt).At (po + 16)) ⋆ Eq ((Int.toBytes 8 32).At (po + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (po + 32)) ⋆ Eq ((List.replicate 32 0).At (po + 40))
          ⋆ Eq (root.At pr)
          ⋆ Eq (e8.At aSrc) ⋆ Eq (root.At aRoot)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + j1)⟩

/-- `nestedCheckpointDecodeKindWindow` follows from `nested_checkpoint_decode_window` and the window facts of an instance. -/
theorem nestedCheckpointDecodeKindWindow_of (C : Program) (fn lwb lst lok : String) (dR fP dB src dC rest : Int64)
    (qA qB : Program) (j1 j2 j3 jl jc : Nat)
    (hqA : ∀ k, C.IsInfixAt Host.prog k → qA.IsInfixAt Host.prog (k + j1))
    (heA : eraseNop qA = nestedCheckpointAllocate lwb lst dR)
    (hqB : ∀ k, C.IsInfixAt Host.prog k → qB.IsInfixAt Host.prog (k + j2))
    (heB : eraseNop qB = nestedCheckpointCall lst fn lok fP dB src dC rest)
    (hjl : j2 + nonNopIndex qB 0 = jl)
    (hls : ∀ k, C.IsInfixAt Host.prog k → LabelsFresh C k → label lst = Host.addrOf (k + jl))
    (hjc : j2 + nonNopIndex qB 7 = jc)
    (hB : ∀ k, C.IsInfixAt Host.prog k → (callDecodeContinuationLabel lok).IsInfixAt Host.prog (k + j3))
    (hl : ∀ k, C.IsInfixAt Host.prog k → LabelsFresh C k → label lok = Host.addrOf (k + j3)) :
    nestedCheckpointDecodeKindWindow C fn j1 jc j3 dR fP dB src dC :=
  fun k hk hf => nested_checkpoint_decode_window fn lwb lst lok dR fP dB src dC rest qA qB (k + j1) (k + j2) (k + j3)
    (k + jl) (k + jc) (hqA k hk) heA (hqB k hk) heB (by omega) (hls k hk hf) (by omega) (hB k hk) (hl k hk hf)

end Codec
