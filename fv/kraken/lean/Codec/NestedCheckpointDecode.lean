import Codec.CalleeDecode
import Codec.NopWindow
import Codec.SegmentAddress
import Runtime.NewobjectContract
import Prysm.ElfData.PrysmTarget

/-!
# The nested Checkpoint field block over windows

A field of type `*Checkpoint` in a fixed-size container decoder.
The Go source allocates the object when the pointer is nil.
The compiled code (Go 1.26.10, `AttestationData.Source` and `.Target`) has no nil test.
It always allocates a new object and overwrites the old pointer:

    lea type__+1289312(%rip),%rax; callq runtime.newobject
    cmpl $0x0,runtime.writeBarrier(%rip); jne lwb; mov dR(%rsp),%rdx; jmp lst      -- first window
    lst: mov %rax,fP(%rdx); mov dB(%rsp),%rbx; add $src,%rbx; mov dC(%rsp),%rdi
    add $rest,%rdi; mov $0x28,%ecx; callq fn; test %rax,%rax; je lok                -- second window
    lok:

The block uses the callee only through `NestedCheckpointCalleeAccept fn Heap S`.
This is the text of `Prysm.Checkpoint.Decode.accept_function_spec Heap S` with the callee label as a parameter.
`Prysm.Checkpoint.Decode.accept_function_spec_holds` proves it from the machine code.
The allocation uses the contract `NewobjectContract Heap typeCheckpoint 72 (S + 96)`.
The callee frame lives in the `S + 96` stack bytes below the return slot.
The write-barrier path (`jne lwb` taken) is not covered: the statement assumes that `runtime.writeBarrier` is 0.
-/

open Machine Runtime

namespace Codec

/-- Function specification form of a nested Checkpoint decoder at the label `fn`.
It is the text of `Prysm.Checkpoint.Decode.accept_function_spec Heap S` with the label `fn`. -/
def NestedCheckpointCalleeAccept [Host] (fn : String) (Heap : Nat → DataMem → Prop) (S : Nat) : Prop :=
  ∀ (st : MachineData) (ret : Int64) (guard : UInt64) (avail : Nat)
    (e8 root fp s1 s2 l20 l28 l30 m0 m1 m2 rslot cst c0 cP cL cC ctl scratch : List UInt8)
    (F : DataMem → Prop),
    e8.length = 8 → root.length = 32 → fp.length = 8 → s1.length = 8 → s2.length = 8 → l20.length = 8 →
    l28.length = 8 → l30.length = 8 → m0.length = 8 → m1.length = 8 → m2.length = 8 → rslot.length = 8 →
    cst.length = 8 → c0.length = 8 → cP.length = 8 → cL.length = 8 → cC.length = 8 → ctl.length = 32 →
    8 ≤ S → S < 2 ^ 60 → scratch.length = S →
    guard.toNat + 96 < st.regs.rsp.toNat → st.regs.rcx = 40 → 32 ≤ avail →
    (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (st.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (st.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (st.regs.rsp.toBitVec + 16))
      ⋆ Eq (l20.At (st.regs.rsp.toBitVec - 32)) ⋆ Eq (l28.At (st.regs.rsp.toBitVec - 40))
      ⋆ Eq (l30.At (st.regs.rsp.toBitVec - 48))
      ⋆ Eq (m2.At (st.regs.rsp.toBitVec - 72)) ⋆ Eq (m1.At (st.regs.rsp.toBitVec - 80))
      ⋆ Eq (m0.At (st.regs.rsp.toBitVec - 88)) ⋆ Eq (rslot.At (st.regs.rsp.toBitVec - 96))
      ⋆ Eq (scratch.At (st.regs.rsp.toBitVec - 96 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (st.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (e8.At st.regs.rbx.toBitVec) ⋆ Eq (root.At (st.regs.rbx.toBitVec + 8))
      ⋆ Eq (cst.At st.regs.rax.toBitVec) ⋆ Eq (c0.At (st.regs.rax.toBitVec + 8))
      ⋆ Eq (cP.At (st.regs.rax.toBitVec + 16)) ⋆ Eq (cL.At (st.regs.rax.toBitVec + 24))
      ⋆ Eq (cC.At (st.regs.rax.toBitVec + 32)) ⋆ Eq (ctl.At (st.regs.rax.toBitVec + 40))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ F) st.dmem →
    Eventually (step1 Host.exe)
      (fun st' => st'.pc = ret ∧ st'.data.regs.rax = 0 ∧ st'.data.regs.rbx = 0
        ∧ st'.data.regs.rsp = st.regs.rsp + 8 ∧ st'.data.regs.rbp = st.regs.rbp ∧ st'.data.regs.r14 = st.regs.r14 ∧
        ∃ (p : BitVec 64) (scr mm rs' : List UInt8), scr.length = S ∧ mm.length = 24 ∧ rs'.length = 8 ∧
        (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 st.regs.rbp.toBitVec.toInt).At (st.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 st.regs.rax.toBitVec.toInt).At (st.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 st.regs.rbx.toBitVec.toInt).At (st.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (st.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 0).At (st.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 0).At (st.regs.rsp.toBitVec - 48))
          ⋆ Eq (mm.At (st.regs.rsp.toBitVec - 88))
          ⋆ Eq (rs'.At (st.regs.rsp.toBitVec - 96))
          ⋆ Eq (scr.At (st.regs.rsp.toBitVec - 96 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (st.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 32)
          ⋆ Eq (e8.At st.regs.rbx.toBitVec) ⋆ Eq (root.At (st.regs.rbx.toBitVec + 8))
          ⋆ Eq (cst.At st.regs.rax.toBitVec) ⋆ Eq (e8.At (st.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (st.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (st.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (st.regs.rax.toBitVec + 32))
          ⋆ Eq (ctl.At (st.regs.rax.toBitVec + 40)) ⋆ Eq (root.At p)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ F) st'.data.dmem)
      ⟨st, label fn⟩

/-- First window: `lea type__+1289312(%rip),%rax; callq runtime.newobject; cmpl $0x0,runtime.writeBarrier(%rip);
jne lwb; mov dR(%rsp),%rdx; jmp lst`. The type word is the `abi.Type` of `Checkpoint` (`typeCheckpoint`). -/
def nestedCheckpointAllocate (lwb lst : String) (dR : Int64) : Program :=
  [Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.lea (Reg.low Reg64.rax Width.W64)
       (AddrExpr.mk (some RegOrRip.rip) none (((ConstExpr.label "type__").add (ConstExpr.int64 1289312)).sub ConstExpr.after_current_instruction)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.call (RelRegOrMem.rel ((ConstExpr.label "runtime.newobject").sub ConstExpr.after_current_instruction)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W32
     (Operation.cmp (RegOrMem.mem (AddrExpr.mk (some RegOrRip.rip) none ((ConstExpr.label "runtime.writeBarrier").sub ConstExpr.after_current_instruction)))
       (Operand.imm (ConstExpr.int64 0)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64 (Operation.jcc CondCode.nz lwb)),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.reg (Reg.low Reg64.rdx Width.W64))
       (Operand.regOrMem (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rsp)) none (ConstExpr.int64 dR)))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.jmp (RelRegOrMem.rel ((ConstExpr.label lst).sub ConstExpr.after_current_instruction))))]

/-- Second window: `lst: mov %rax,fP(%rdx); mov dB(%rsp),%rbx; add $src,%rbx; mov dC(%rsp),%rdi; add $rest,%rdi;
mov $0x28,%ecx; callq fn; test %rax,%rax; je lok`. -/
def nestedCheckpointCall (lst fn lok : String) (fP dB src dC rest : Int64) : Program :=
  [Kraken.Directive.label lst,
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rdx)) none (ConstExpr.int64 fP)))
       (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rax Width.W64))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.reg (Reg.low Reg64.rbx Width.W64))
       (Operand.regOrMem (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rsp)) none (ConstExpr.int64 dB)))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.add (RegOrMem.reg (Reg.low Reg64.rbx Width.W64)) (Operand.imm (ConstExpr.int64 src)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.reg (Reg.low Reg64.rdi Width.W64))
       (Operand.regOrMem (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rsp)) none (ConstExpr.int64 dC)))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.add (RegOrMem.reg (Reg.low Reg64.rdi Width.W64)) (Operand.imm (ConstExpr.int64 rest)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W32
     (Operation.mov (RegOrMem.reg (Reg.low Reg64.rcx Width.W32)) (Operand.imm (ConstExpr.int64 40)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.call (RelRegOrMem.rel ((ConstExpr.label fn).sub ConstExpr.after_current_instruction)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.test (RegOrMem.reg (Reg.low Reg64.rax Width.W64))
       (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rax Width.W64))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64 (Operation.jcc CondCode.z lok))]

/-- The `S + 96` stack bytes below the return slot, in the slots of the Checkpoint decoder frame:
scratch (S), return slot, argument area (24), a 16-byte gap, three locals, a 16-byte gap, saved rbp. -/
def nestedCheckpointFrame (scratch rslot mm gA l30 l28 l20 gB fp : List UInt8) : List UInt8 :=
  scratch ++ (rslot ++ (mm ++ (gA ++ (l30 ++ (l28 ++ (l20 ++ (gB ++ fp)))))))

theorem nestedCheckpointFrame_length (scratch rslot mm gA l30 l28 l20 gB fp : List UInt8) (S : Nat)
    (h0 : scratch.length = S) (h1 : rslot.length = 8) (h2 : mm.length = 24) (h3 : gA.length = 16)
    (h4 : l30.length = 8) (h5 : l28.length = 8) (h6 : l20.length = 8) (h7 : gB.length = 16) (h8 : fp.length = 8) :
    (nestedCheckpointFrame scratch rslot mm gA l30 l28 l20 gB fp).length = S + 96 := by
  simp only [nestedCheckpointFrame, List.length_append, *]; try omega

/-- The frame as its chunks; `c` is the callee rsp (the address of the return slot). -/
theorem nestedCheckpointFrame_sep (c : BitVec 64) (S : Nat) (hS : S < 2 ^ 60)
    (scratch rslot mm gA l30 l28 l20 gB fp : List UInt8)
    (h0 : scratch.length = S) (h1 : rslot.length = 8) (h2 : mm.length = 24) (h3 : gA.length = 16)
    (h4 : l30.length = 8) (h5 : l28.length = 8) (h6 : l20.length = 8) (h7 : gB.length = 16) (h8 : fp.length = 8) :
    Eq ((nestedCheckpointFrame scratch rslot mm gA l30 l28 l20 gB fp).At (c - 96 - BitVec.ofNat 64 S)) =
      Eq (scratch.At (c - 96 - BitVec.ofNat 64 S)) ⋆ Eq (rslot.At (c - 96)) ⋆ Eq (mm.At (c - 88))
      ⋆ Eq (gA.At (c - 64)) ⋆ Eq (l30.At (c - 48)) ⋆ Eq (l28.At (c - 40)) ⋆ Eq (l20.At (c - 32))
      ⋆ Eq (gB.At (c - 24)) ⋆ Eq (fp.At (c - 8)) := by
  simp only [nestedCheckpointFrame]
  rw [at_app _ _ (b := c - 96) (by rw [h0]; bv_omega) (by simp [*]; omega),
    at_app _ _ (b := c - 88) (by rw [h1]; bv_omega) (by simp [*]),
    at_app _ _ (b := c - 64) (by rw [h2]; bv_omega) (by simp [*]),
    at_app _ _ (b := c - 48) (by rw [h3]; bv_omega) (by simp [*]),
    at_app _ _ (b := c - 40) (by rw [h4]; bv_omega) (by simp [*]),
    at_app _ _ (b := c - 32) (by rw [h5]; bv_omega) (by simp [*]),
    at_app _ _ (b := c - 24) (by rw [h6]; bv_omega) (by simp [*]),
    at_app _ _ (b := c - 8) (by rw [h7]; bv_omega) (by simp [*])]
  simp only [Std.ExtHashMap.sep_assoc]

/-- Any block of `S + 96` bytes is a `nestedCheckpointFrame` (slices by nested `drop`). -/
theorem nestedCheckpointFrame_slices (stk : List UInt8) (S : Nat) :
    let t0 := stk.drop S; let t1 := t0.drop 8; let t2 := t1.drop 24; let t3 := t2.drop 16
    let t4 := t3.drop 8; let t5 := t4.drop 8; let t6 := t5.drop 8; let t7 := t6.drop 16
    stk = nestedCheckpointFrame (stk.take S) (t0.take 8) (t1.take 24) (t2.take 16) (t3.take 8) (t4.take 8) (t5.take 8)
      (t6.take 16) t7 := by
  intro t0 t1 t2 t3 t4 t5 t6 t7
  simp only [nestedCheckpointFrame, t0, t1, t2, t3, t4, t5, t6, t7, List.take_append_drop]

theorem nestedCheckpointFrame_lengths (stk : List UInt8) (S : Nat) (h : stk.length = S + 96) :
    (stk.take S).length = S ∧ ((stk.drop S).take 8).length = 8 ∧ (((stk.drop S).drop 8).take 24).length = 24
      ∧ ((((stk.drop S).drop 8).drop 24).take 16).length = 16
      ∧ (((((stk.drop S).drop 8).drop 24).drop 16).take 8).length = 8
      ∧ ((((((stk.drop S).drop 8).drop 24).drop 16).drop 8).take 8).length = 8
      ∧ (((((((stk.drop S).drop 8).drop 24).drop 16).drop 8).drop 8).take 8).length = 8
      ∧ ((((((((stk.drop S).drop 8).drop 24).drop 16).drop 8).drop 8).drop 8).take 16).length = 16
      ∧ ((((((((stk.drop S).drop 8).drop 24).drop 16).drop 8).drop 8).drop 8).drop 16).length = 8 := by
  simp only [List.length_take, List.length_drop, h]; omega

/-- The 24-byte argument area of the callee as its three words. -/
theorem nestedCheckpointFrame_argument_words (c : BitVec 64) (mm : List UInt8) (h : mm.length = 24) :
    Eq (mm.At (c - 88)) = Eq ((mm.take 8).At (c - 88)) ⋆ Eq (((mm.drop 8).take 8).At (c - 80))
      ⋆ Eq ((mm.drop 16).At (c - 72)) := by
  have e : mm = mm.take 8 ++ (((mm.drop 8).take 8) ++ mm.drop 16) := by
    conv => lhs; rw [← List.take_append_drop 8 mm, ← List.take_append_drop 8 (mm.drop 8)]
    simp only [List.drop_drop]
  conv => lhs; rw [e]
  rw [at_app _ _ (b := c - 80) (by simp [h]; bv_omega) (by simp [h]),
    at_app _ _ (b := c - 72) (by simp [h]; bv_omega) (by simp [h])]
  simp only [Std.ExtHashMap.sep_assoc]

/-- A fresh 72-byte Checkpoint object as the receiver chunks of the callee specification. -/
theorem nestedCheckpointFreshObject (p : BitVec 64) :
    Eq ((List.replicate 72 (0 : UInt8)).At p) = Eq ((List.replicate 8 0).At p) ⋆ Eq ((List.replicate 8 0).At (p + 8))
      ⋆ Eq ((List.replicate 8 0).At (p + 16)) ⋆ Eq ((List.replicate 8 0).At (p + 24))
      ⋆ Eq ((List.replicate 8 0).At (p + 32)) ⋆ Eq ((List.replicate 32 0).At (p + 40)) := by
  rw [show List.replicate 72 (0 : UInt8) = List.replicate 8 0 ++ (List.replicate 8 0 ++ (List.replicate 8 0
    ++ (List.replicate 8 0 ++ (List.replicate 8 0 ++ List.replicate 32 0)))) by rfl]
  rw [at_app _ _ (b := p + 8) (by simp) (by simp), at_app _ _ (b := p + 16) (by simp; bv_omega) (by simp),
    at_app _ _ (b := p + 24) (by simp; bv_omega) (by simp), at_app _ _ (b := p + 32) (by simp; bv_omega) (by simp),
    at_app _ _ (b := p + 40) (by simp; bv_omega) (by simp)]
  simp only [Std.ExtHashMap.sep_assoc]

/-- The low address of the `S + 96` bytes below the callee rsp `c`. -/
theorem nestedCheckpointFrame_low_address (c : BitVec 64) (S : Nat) :
    c - BitVec.ofNat 64 (S + 96) = c - 96 - BitVec.ofNat 64 S := by
  have : BitVec.ofNat 64 (S + 96) = BitVec.ofNat 64 S + 96 := by
    apply BitVec.eq_of_toNat_eq; simp
  rw [this]; bv_omega

variable [Host]

/-- **Nested Checkpoint field block over windows.** The first window `qA` at `j1` allocates the object
(`runtime.newobject`), tests the write barrier and jumps to `lst` (index `jl`).
The second window `qB` at `j2` stores the new pointer at `rcv + fP` and calls the Checkpoint decoder `fn` on
`buf[src:src+40]` (`callq` at `jc`). The label `lok` is at `j3`.
The object holds `state` = 0, the epoch, a new 32-byte root slice and zero `unknownFields` / `sizeCache`.
The words at `sp` and `sp + 8` hold the callee's spills of the object pointer and of `bf + src`. -/
theorem nested_checkpoint_decode_window (fn lwb lst lok : String) (dR fP dB src dC rest : Int64)
    (qA qB : Program) (j1 j2 j3 jl jc : Nat)
    (hqA : qA.IsInfixAt Host.prog j1) (heA : eraseNop qA = nestedCheckpointAllocate lwb lst dR)
    (hqB : qB.IsInfixAt Host.prog j2) (heB : eraseNop qB = nestedCheckpointCall lst fn lok fP dB src dC rest)
    (hjl : j2 + nonNopIndex qB 0 = jl) (hls : label lst = Host.addrOf jl)
    (hjc : j2 + nonNopIndex qB 7 = jc)
    (hB : (callDecodeContinuationLabel lok).IsInfixAt Host.prog j3) (hl : label lok = Host.addrOf j3)
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
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (j3 + 1) ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = { toBitVec := sp } ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        ∃ (po pr : BitVec 64) (lo' : List UInt8), lo'.length = S + 96 ∧
        (Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ Eq ((Int.toBytes 8 bf.toInt).At aB)
          ⋆ Eq (cap.At aC) ⋆ Eq ((Int.toBytes 8 po.toInt).At sp) ⋆ Eq ((Int.toBytes 8 aSrc.toInt).At aW1)
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (jc + 1)).toBitVec.toInt).At aRet) ⋆ Eq (lo'.At aLo)
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
          ⋆ Heap (avail - 104)
          ⋆ Eq ((Int.toBytes 8 po.toInt).At aP)
          ⋆ Eq ((List.replicate 8 0).At po) ⋆ Eq (e8.At (po + 8))
          ⋆ Eq ((Int.toBytes 8 pr.toInt).At (po + 16)) ⋆ Eq ((Int.toBytes 8 32).At (po + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (po + 32)) ⋆ Eq ((List.replicate 32 0).At (po + 40))
          ⋆ Eq (root.At pr)
          ⋆ Eq (e8.At aSrc) ⋆ Eq (root.At aRoot)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf j1⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp hrbp hr14 h_mem ⊢
  subst rsp rbp r14 hRet hLo hjl hjc hW1 hRoot
  have := guard.toNat_lt_size; simp only [UInt64.size] at *
  -- first window: allocate
  window_skip_leading_nops hqA
  window_step_directive hqA heA nestedCheckpointAllocate 0
  window_skip_nops hqA heA 0
  window_step_directive hqA heA nestedCheckpointAllocate 1
  apply store_step_at _ _ (sp - 8) _ _ _ rslot _ _ (by segment_addr) (by ecancel) (by exact hrs)
  intro m1' H1
  simp only [Width.bytes, Width.bits] at H1
  unfold_step
  try rw [show sp - 8#64 = sp - 8 from rfl] at *
  refine eventually_trans _ _ _ _ (hno _ (Host.addrOf (j1 + nonNopIndex qA 1 + 1)) avail lo w0 _ rfl (by omega) hlo hw0
    (by dsimp only; rw [show sp - 8 + 8 = sp by bv_omega]; ecancel)) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrsp3, hr143, hrbp3, stk3, sp3, hstk3, hsp3, Hm3⟩
  dsimp only at hpc3 hrsp3 hr143 hrbp3 Hm3
  subst hpc3
  obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,
    zmms3, flags3, mem3⟩ := d3
  simp only at hrsp3 hr143 hrbp3 Hm3
  rw [show ({ toBitVec := sp - 8 } + 8 : UInt64) = { toBitVec := sp } by
    apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega] at hrsp3
  subst hrsp3 hr143 hrbp3
  rw [show sp - 8 + 8 = sp by bv_omega, nestedCheckpointFreshObject] at Hm3
  window_skip_nops hqA heA 1
  window_step_directive hqA heA nestedCheckpointAllocate 2
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  unfold_step
  window_skip_nops hqA heA 2
  window_step_directive hqA heA nestedCheckpointAllocate 3
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  window_skip_nops hqA heA 3
  window_step_directive hqA heA nestedCheckpointAllocate 4
  apply load_step_at _ _ aR _ _ (Int.toBytes 8 rcv.toInt) _ _ (by rw [← hR]) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  window_skip_nops hqA heA 4
  window_step_directive hqA heA nestedCheckpointAllocate 5
  rw [hls]
  -- second window: store the pointer, set up the arguments, call the Checkpoint decoder
  window_step_directive hqB heB nestedCheckpointCall 0
  window_skip_nops hqB heB 0
  window_step_directive hqB heB nestedCheckpointCall 1
  apply store_step_at _ _ aP _ _ _ vP _ _ (by rw [← hP]) (by ecancel) (by exact hvP)
  intro m4' H4
  simp only [Width.bytes, Width.bits] at H4
  unfold_step
  window_skip_nops hqB heB 1
  window_step_directive hqB heB nestedCheckpointCall 2
  apply load_step_at _ _ aB _ _ (Int.toBytes 8 bf.toInt) _ _ (by rw [← hB']) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  window_skip_nops hqB heB 2
  window_step_directive hqB heB nestedCheckpointCall 3
  window_skip_nops hqB heB 3
  window_step_directive hqB heB nestedCheckpointCall 4
  apply load_step_at _ _ aC _ _ cap _ _ (by rw [← hC']) (by ecancel) (by exact hcap)
  unfold_step
  window_skip_nops hqB heB 4
  window_step_directive hqB heB nestedCheckpointCall 5
  window_skip_nops hqB heB 5
  window_step_directive hqB heB nestedCheckpointCall 6
  window_skip_nops hqB heB 6
  window_step_directive hqB heB nestedCheckpointCall 7
  apply store_step_at _ _ (sp - 8) _ _ _ (Int.toBytes 8 (Host.addrOf (j1 + nonNopIndex qA 1 + 1)).toBitVec.toInt) _ _
    (by segment_addr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m5' H5
  simp only [Width.bytes, Width.bits] at H5
  unfold_step
  try rw [show sp - 8#64 = sp - 8 from rfl] at *
  -- the callee frame in the S + 96 stack bytes
  obtain ⟨l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := nestedCheckpointFrame_lengths stk3 S hstk3
  rw [nestedCheckpointFrame_slices stk3 S] at H5
  try dsimp only at H5
  rw [nestedCheckpointFrame_low_address _ S,
    nestedCheckpointFrame_sep _ S hS _ _ _ _ _ _ _ _ _ l0 l1 l2 l3 l4 l5 l6 l7 l8,
    nestedCheckpointFrame_argument_words _ _ l2] at H5
  rw [show src.toBitVec + bf = aSrc by rw [← hSrc]; exact BitVec.add_comm _ _]
  refine eventually_trans _ _ _ _ (hC _ (Host.addrOf (j2 + nonNopIndex qB 7 + 1)) guard (avail - 72) e8 root _ sp3 w1 _ _ _
    ((((stk3.drop S).drop 8).take 24).take 8) (((((stk3.drop S).drop 8).take 24).drop 8).take 8)
    ((((stk3.drop S).drop 8).take 24).drop 16) _
    (List.replicate 8 0) (List.replicate 8 0) (List.replicate 8 0) (List.replicate 8 0) (List.replicate 8 0)
    (List.replicate 32 0) _ _
    he8 hroot l8 hsp3 hw1 l6 l5 l4 (by simp [hstk3]) (by simp [hstk3]) (by simp [hstk3]) l1
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) hS8 hS l0
    hguard rfl (by omega)
    (by dsimp only
        rw [show sp - 8 + 8 = sp by bv_omega, show sp - 8 + 16 = sp + 8 by bv_omega]
        ecancel)) ?_
  rintro ⟨d5, pc5⟩ ⟨hpc5, hrax5, hrbx5, hrsp5, hrbp5, hr145, pr, scr, mm, rs', hscr, hmm, hrs', Hm5⟩
  dsimp only at hpc5 hrax5 hrbx5 hrsp5 hrbp5 hr145 Hm5
  subst hpc5
  obtain ⟨⟨rax5, rbx5, rcx5, rdx5, rsi5, rdi5, rsp5, rbp5, r85, r95, r105, r115, r125, r135, r145, r155⟩,
    zmms5, flags5, mem5⟩ := d5
  simp only at hrax5 hrbx5 hrsp5 hrbp5 hr145 Hm5
  rw [show ({ toBitVec := sp - 8 } + 8 : UInt64) = { toBitVec := sp } by
    apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega] at hrsp5
  subst rax5 rbx5 rsp5 rbp5 r145
  try dsimp only at Hm5
  rw [show sp - 8 + 8 = sp by bv_omega, show sp - 8 + 16 = sp + 8 by bv_omega] at Hm5
  rw [show avail - 72 - 32 = avail - 104 by omega] at Hm5
  window_skip_nops hqB heB 7
  window_step_directive hqB heB nestedCheckpointCall 8
  intro _
  window_skip_nops hqB heB 8
  window_step_directive hqB heB nestedCheckpointCall 9
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  rw [hl]
  step_directive hB callDecodeContinuationLabel 0
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rax3.toBitVec, pr,
    nestedCheckpointFrame scr rs' mm _ (Int.toBytes 8 0) (Int.toBytes 8 0) (Int.toBytes 8 pr.toInt) _
      (Int.toBytes 8 rbp3.toBitVec.toInt),
    nestedCheckpointFrame_length _ _ _ _ _ _ _ _ _ S hscr hrs' hmm l3 (Int.toBytes_length 8 _)
      (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) l7 (Int.toBytes_length 8 _), ?_⟩
  rw [nestedCheckpointFrame_low_address _ S,
    nestedCheckpointFrame_sep _ S hS _ _ _ _ _ _ _ _ _ hscr hrs' hmm l3 (Int.toBytes_length 8 _)
      (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) l7 (Int.toBytes_length 8 _)]
  ecancel

end Codec
