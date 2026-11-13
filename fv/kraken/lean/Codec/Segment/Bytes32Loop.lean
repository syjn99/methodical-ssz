import Runtime.Contracts
import Machine.Step
import Machine.Labels
import Prysm.ElfData.PrysmTarget
import Prysm.HistoricalBatch.DecodeLoopBlockRoots
import Codec.Segment.ByteSliceList

/-!
# The `[][]byte` element loop with 32-byte elements, for ANY count `n < 2^31` and any frame (generalized once)

Go 1.26.10 compiles `c.F = make([][]byte, n); for i := 0; i < n; i++ { tmp := make([]byte, 0, 32);
tmp = append(tmp, buf[src+i*32 : src+(1+i)*32]...); c.F[i] = tmp }` to the same instruction sequence for
HistoricalBatch (two loops, n = 8192) and Deposit (n = 33). Only these vary between the instances:
the count `n`, the five stack slots, the two receiver field offsets, the labels, the source offset `src`
(an extra `lea src(%rbx),%rbx`, HistoricalBatch.StateRoots), and `nop` padding at four places.
The loop body is cut into six blocks at those places (`bytes32LoopHead` … `bytes32LoopBack`); `Glue a b` says that the gap between
two blocks is empty or one `nop`, `GlueSrc` that it is empty (src = 0) or the `lea`.
The element size is fixed at 32: other sizes compile to other sequences (48: `lea (x,x,2)` then `shl $4`), and
`shl $5` is stepped with `shift_left64 5` (a literal count).
The templates are the Kraken terms of HistoricalBatch directives 36–77 (link set `prysm/go1.26.10/link-set`) (printed with `repr`) with the varying
operands replaced by parameters; each use shows the equality with the real program by `infix_sub` and
`rfl`/`decide` (`Codec/Segment/Bytes32LoopHistoricalBatch.lean`, `Prysm/Deposit/DecodeAccept.lean`).
-/

open Machine Runtime Prysm.HistoricalBatch

namespace Codec.Segment

def bytes32LoopHead (n : Int64) (lhead lexit : String) : Program :=
  [Kraken.Directive.label lhead,
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.cmp (RegOrMem.reg (Reg.low (Reg64.rax) (Width.W64))) (Operand.imm (ConstExpr.int64 n)))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.jcc (CondCode.ge) lexit)),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.mov (RegOrMem.reg (Reg.low (Reg64.rsi) (Width.W64))) (Operand.regOrMem (RegOrMem.reg (Reg.low (Reg64.rax) (Width.W64)))))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.shl (RegOrMem.reg (Reg.low (Reg64.rax) (Width.W64))) (ShiftCountExpr.imm8 (ConstExpr.int64 5)))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.lea (Reg.low (Reg64.rdi) (Width.W64)) { base := some (RegOrRip.reg (Reg64.rsi)), idx := none, disp := ConstExpr.int64 1 })),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.mov (RegOrMem.reg (Reg.low (Reg64.r8) (Width.W64))) (Operand.regOrMem (RegOrMem.reg (Reg.low (Reg64.rdi) (Width.W64)))))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.shl (RegOrMem.reg (Reg.low (Reg64.rdi) (Width.W64))) (ShiftCountExpr.imm8 (ConstExpr.int64 5))))]

def bytes32LoopMiddle (lp1 : String) (dI dD dI1 dP dB : Int64) : Program :=
  [Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.cmp (RegOrMem.reg (Reg.low (Reg64.rdi) (Width.W64))) (Operand.regOrMem (RegOrMem.reg (Reg.low (Reg64.rax) (Width.W64)))))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.jcc (CondCode.c) lp1)),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.mov (RegOrMem.mem { base := some (RegOrRip.reg (Reg64.rsp)), idx := none, disp := ConstExpr.int64 dI }) (Operand.regOrMem (RegOrMem.reg (Reg.low (Reg64.rsi) (Width.W64)))))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.mov (RegOrMem.mem { base := some (RegOrRip.reg (Reg64.rsp)), idx := none, disp := ConstExpr.int64 dD }) (Operand.regOrMem (RegOrMem.reg (Reg.low (Reg64.rax) (Width.W64)))))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.mov (RegOrMem.mem { base := some (RegOrRip.reg (Reg64.rsp)), idx := none, disp := ConstExpr.int64 dI1 }) (Operand.regOrMem (RegOrMem.reg (Reg.low (Reg64.r8) (Width.W64)))))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.lea (Reg.low (Reg64.rax) (Width.W64)) { base := some (RegOrRip.rip), idx := none, disp := ConstExpr.sub (ConstExpr.add (ConstExpr.label "type__") (ConstExpr.int64 387072)) (ConstExpr.after_current_instruction) })),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W32) (Operation.xor (RegOrMem.reg (Reg.low (Reg64.rbx) (Width.W32))) (Operand.regOrMem (RegOrMem.reg (Reg.low (Reg64.rbx) (Width.W32)))))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W32) (Operation.mov (RegOrMem.reg (Reg.low (Reg64.rcx) (Width.W32))) (Operand.imm (ConstExpr.int64 32)))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.call (RelRegOrMem.rel (ConstExpr.sub (ConstExpr.label "runtime.makeslice") (ConstExpr.after_current_instruction))))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.mov (RegOrMem.mem { base := some (RegOrRip.reg (Reg64.rsp)), idx := none, disp := ConstExpr.int64 dP }) (Operand.regOrMem (RegOrMem.reg (Reg.low (Reg64.rax) (Width.W64)))))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.mov (RegOrMem.reg (Reg.low (Reg64.rdx) (Width.W64))) (Operand.regOrMem (RegOrMem.mem { base := some (RegOrRip.reg (Reg64.rsp)), idx := none, disp := ConstExpr.int64 dD })))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.mov (RegOrMem.reg (Reg.low (Reg64.rsi) (Width.W64))) (Operand.regOrMem (RegOrMem.mem { base := some (RegOrRip.reg (Reg64.rsp)), idx := none, disp := ConstExpr.int64 dB })))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.lea (Reg.low (Reg64.rbx) (Width.W64)) { base := some (RegOrRip.reg (Reg64.rsi)), idx := some { reg := Reg64.rdx, scale := Width.W8 }, disp := ConstExpr.int64 0 }))]

def bytes32LoopMemmove (dR fL dI : Int64) : Program :=
  [Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W32) (Operation.mov (RegOrMem.reg (Reg.low (Reg64.rcx) (Width.W32))) (Operand.imm (ConstExpr.int64 32)))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.call (RelRegOrMem.rel (ConstExpr.sub (ConstExpr.label "runtime.memmove") (ConstExpr.after_current_instruction))))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.mov (RegOrMem.reg (Reg.low (Reg64.rdx) (Width.W64))) (Operand.regOrMem (RegOrMem.mem { base := some (RegOrRip.reg (Reg64.rsp)), idx := none, disp := ConstExpr.int64 dR })))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.mov (RegOrMem.reg (Reg.low (Reg64.rsi) (Width.W64))) (Operand.regOrMem (RegOrMem.mem { base := some (RegOrRip.reg (Reg64.rdx)), idx := none, disp := ConstExpr.int64 fL })))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.mov (RegOrMem.reg (Reg.low (Reg64.rdi) (Width.W64))) (Operand.regOrMem (RegOrMem.mem { base := some (RegOrRip.reg (Reg64.rsp)), idx := none, disp := ConstExpr.int64 dI }))))]

def bytes32LoopHeader (lp2 : String) (fP : Int64) : Program :=
  [Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.cmp (RegOrMem.reg (Reg.low (Reg64.rdi) (Width.W64))) (Operand.regOrMem (RegOrMem.reg (Reg.low (Reg64.rsi) (Width.W64)))))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.jcc (CondCode.nc) lp2)),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.lea (Reg.low (Reg64.rsi) (Width.W64)) { base := some (RegOrRip.reg (Reg64.rdi)), idx := some { reg := Reg64.rdi, scale := Width.W16 }, disp := ConstExpr.int64 0 })),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.mov (RegOrMem.reg (Reg.low (Reg64.rdi) (Width.W64))) (Operand.regOrMem (RegOrMem.mem { base := some (RegOrRip.reg (Reg64.rdx)), idx := none, disp := ConstExpr.int64 fP })))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.mov (RegOrMem.mem { base := some (RegOrRip.reg (Reg64.rdi)), idx := some { reg := Reg64.rsi, scale := Width.W64 }, disp := ConstExpr.int64 8 }) (Operand.imm (ConstExpr.int64 32)))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.mov (RegOrMem.mem { base := some (RegOrRip.reg (Reg64.rdi)), idx := some { reg := Reg64.rsi, scale := Width.W64 }, disp := ConstExpr.int64 16 }) (Operand.imm (ConstExpr.int64 32)))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W32) (Operation.cmp (RegOrMem.mem { base := some (RegOrRip.rip), idx := none, disp := ConstExpr.sub (ConstExpr.label "runtime.writeBarrier") (ConstExpr.after_current_instruction) }) (Operand.imm (ConstExpr.int64 0))))]

def bytes32LoopTail (lwb lback : String) (dP : Int64) : Program :=
  [Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.jcc (CondCode.nz) lwb)),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.mov (RegOrMem.reg (Reg.low (Reg64.r9) (Width.W64))) (Operand.regOrMem (RegOrMem.mem { base := some (RegOrRip.reg (Reg64.rsp)), idx := none, disp := ConstExpr.int64 dP })))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.jmp (RelRegOrMem.rel (ConstExpr.sub (ConstExpr.label lback) (ConstExpr.after_current_instruction)))))]

def bytes32LoopBack (lback : String) (dI1 : Int64) : Program :=
  [Kraken.Directive.label lback,
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.mov (RegOrMem.mem { base := some (RegOrRip.reg (Reg64.rdi)), idx := some { reg := Reg64.rsi, scale := Width.W64 }, disp := ConstExpr.int64 0 }) (Operand.regOrMem (RegOrMem.reg (Reg.low (Reg64.r9) (Width.W64)))))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.mov (RegOrMem.reg (Reg.low (Reg64.rax) (Width.W64))) (Operand.regOrMem (RegOrMem.mem { base := some (RegOrRip.reg (Reg64.rsp)), idx := none, disp := ConstExpr.int64 dI1 }))))]

/-- The `nop` that Go inserts as padding. -/
def bytes32LoopNop : Directive :=
  Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.nop 1))

/-- `lea src(%rbx),%rbx`: the field offset added to the source pointer (HistoricalBatch.StateRoots). -/
def bytes32LoopLeaSource (src : Int64) : Directive :=
  Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.lea (Reg.low (Reg64.rbx) (Width.W64)) { base := some (RegOrRip.reg (Reg64.rbx)), idx := none, disp := ConstExpr.int64 src }))

def bytes32LoopNopProgram : Program := [Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.nop 1))]
def bytes32LoopLeaProgram (src : Int64) : Program := [Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.lea (Reg.low (Reg64.rbx) (Width.W64)) { base := some (RegOrRip.reg (Reg64.rbx)), idx := none, disp := ConstExpr.int64 src }))]

variable [Host]

/-- The gap between two blocks: nothing, or one `nop` at `a`. -/
def Glue (a b : Nat) : Prop := b = a ∨ (b = a + 1 ∧ Host.prog[a]? = some bytes32LoopNop)

/-- The gap before the `memmove` count: nothing (src = 0), or `lea src(%rbx),%rbx` at `a`. -/
def GlueSrc (a b : Nat) (src : Int64) : Prop :=
  (src = 0 ∧ b = a) ∨ (b = a + 1 ∧ Host.prog[a]? = some (bytes32LoopLeaSource src))

theorem infix_one {d : Directive} {a : Nat} (h : Host.prog[a]? = some d) : [d].IsInfixAt Host.prog a := by
  rw [List.isInfixAt_iff_getElem?]; intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  have : i = 0 := by omega
  subst this; simpa using h

theorem glue_nop {a b : Nat} (g : Glue a b) {P : MachineState → Prop} {s : MachineData}
    (h : Eventually (step1 Host.exe) P ⟨s, Host.addrOf b⟩) : Eventually (step1 Host.exe) P ⟨s, Host.addrOf a⟩ := by
  rcases g with rfl | ⟨rfl, hp⟩
  · exact h
  · have hk : bytes32LoopNopProgram.IsInfixAt Host.prog a := infix_one hp
    step_directive hk bytes32LoopNopProgram 0
    exact h

theorem glue_src {a b : Nat} {src : Int64} (g : GlueSrc a b src) {P : MachineState → Prop} {s : MachineData}
    (h : Eventually (step1 Host.exe) P
      ⟨{ s with regs := { s.regs with rbx := { toBitVec := s.regs.rbx.toBitVec + src.toBitVec } } }, Host.addrOf b⟩) :
    Eventually (step1 Host.exe) P ⟨s, Host.addrOf a⟩ := by
  rcases g with ⟨rfl, rfl⟩ | ⟨rfl, hp⟩
  · obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
    simpa using h
  · have hk : (bytes32LoopLeaProgram src).IsInfixAt Host.prog a := infix_one hp
    obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
    step_directive hk bytes32LoopLeaProgram 0
    exact h

end Codec.Segment
