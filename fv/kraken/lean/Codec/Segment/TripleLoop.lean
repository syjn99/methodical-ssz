import Codec.Segment.Bytes32Loop

/-!
# The second `[][]byte` element-loop code shape: element size `w = 3·2^k` (generalized once)

Go 1.26.10 compiles the element loop of `SyncCommittee` (`Vector[Bytes48, 512]`) to a different instruction sequence
from the 32-byte one of `Codec.Segment.Bytes32Loop`: no overflow check, the index is computed as `3i` (`lea (x,x,2)`), saved, and
shifted by `k` (`shl $k`), so the element size is `3·2^k`. One statement cannot cover both sequences (the templates
differ in length and in the registers), so this is a second general loop. The blocks are the Kraken terms of
SyncCommittee directives 36–71 (link set `prysm/go1.26.10/link-set`) with the count, the stack slots, the receiver offsets, the labels, the shift
`k` and the element size `w` as parameters; the gaps (`Glue`, `GlueSrc`) and the `nop` are those of `Codec.Segment.Bytes32Loop`.
-/

open Machine Runtime

namespace Codec.Segment

def tripleLoopHead (n : Int64) (lhead lexit : String) (dI w : Int64) : Program :=
  [Kraken.Directive.label lhead,
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.cmp (RegOrMem.reg (Reg.low (Reg64.rax) (Width.W64))) (Operand.imm (ConstExpr.int64 n)))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.jcc (CondCode.ge) lexit)),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.mov (RegOrMem.mem { base := some (RegOrRip.reg (Reg64.rsp)), idx := none, disp := ConstExpr.int64 dI }) (Operand.regOrMem (RegOrMem.reg (Reg.low (Reg64.rax) (Width.W64)))))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.lea (Reg.low (Reg64.rax) (Width.W64)) { base := some (RegOrRip.rip), idx := none, disp := ConstExpr.sub (ConstExpr.add (ConstExpr.label "type__") (ConstExpr.int64 387072)) (ConstExpr.after_current_instruction) })),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W32) (Operation.xor (RegOrMem.reg (Reg.low (Reg64.rbx) (Width.W32))) (Operand.regOrMem (RegOrMem.reg (Reg.low (Reg64.rbx) (Width.W32)))))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W32) (Operation.mov (RegOrMem.reg (Reg.low (Reg64.rcx) (Width.W32))) (Operand.imm (ConstExpr.int64 w))))]

def tripleLoopMiddle (k dP dI d3 dB : Int64) : Program :=
  [Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.call (RelRegOrMem.rel (ConstExpr.sub (ConstExpr.label "runtime.makeslice") (ConstExpr.after_current_instruction))))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.mov (RegOrMem.mem { base := some (RegOrRip.reg (Reg64.rsp)), idx := none, disp := ConstExpr.int64 dP }) (Operand.regOrMem (RegOrMem.reg (Reg.low (Reg64.rax) (Width.W64)))))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.mov (RegOrMem.reg (Reg.low (Reg64.rdx) (Width.W64))) (Operand.regOrMem (RegOrMem.mem { base := some (RegOrRip.reg (Reg64.rsp)), idx := none, disp := ConstExpr.int64 dI })))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.lea (Reg.low (Reg64.rdx) (Width.W64)) { base := some (RegOrRip.reg (Reg64.rdx)), idx := some { reg := Reg64.rdx, scale := Width.W16 }, disp := ConstExpr.int64 0 })),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.mov (RegOrMem.mem { base := some (RegOrRip.reg (Reg64.rsp)), idx := none, disp := ConstExpr.int64 d3 }) (Operand.regOrMem (RegOrMem.reg (Reg.low (Reg64.rdx) (Width.W64)))))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.shl (RegOrMem.reg (Reg.low (Reg64.rdx) (Width.W64))) (ShiftCountExpr.imm8 (ConstExpr.int64 k)))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.mov (RegOrMem.reg (Reg.low (Reg64.rsi) (Width.W64))) (Operand.regOrMem (RegOrMem.mem { base := some (RegOrRip.reg (Reg64.rsp)), idx := none, disp := ConstExpr.int64 dB })))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.lea (Reg.low (Reg64.rbx) (Width.W64)) { base := some (RegOrRip.reg (Reg64.rsi)), idx := some { reg := Reg64.rdx, scale := Width.W8 }, disp := ConstExpr.int64 0 }))]

def tripleLoopMemmove (w dR fL dI : Int64) : Program :=
  [Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W32) (Operation.mov (RegOrMem.reg (Reg.low (Reg64.rcx) (Width.W32))) (Operand.imm (ConstExpr.int64 w)))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.call (RelRegOrMem.rel (ConstExpr.sub (ConstExpr.label "runtime.memmove") (ConstExpr.after_current_instruction))))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.mov (RegOrMem.reg (Reg.low (Reg64.rdx) (Width.W64))) (Operand.regOrMem (RegOrMem.mem { base := some (RegOrRip.reg (Reg64.rsp)), idx := none, disp := ConstExpr.int64 dR })))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.mov (RegOrMem.reg (Reg.low (Reg64.rsi) (Width.W64))) (Operand.regOrMem (RegOrMem.mem { base := some (RegOrRip.reg (Reg64.rdx)), idx := none, disp := ConstExpr.int64 fL })))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.mov (RegOrMem.reg (Reg.low (Reg64.rdi) (Width.W64))) (Operand.regOrMem (RegOrMem.mem { base := some (RegOrRip.reg (Reg64.rsp)), idx := none, disp := ConstExpr.int64 dI }))))]

def tripleLoopHeader (lp : String) (fP d3 w : Int64) : Program :=
  [Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.cmp (RegOrMem.reg (Reg.low (Reg64.rdi) (Width.W64))) (Operand.regOrMem (RegOrMem.reg (Reg.low (Reg64.rsi) (Width.W64)))))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.jcc (CondCode.nc) lp)),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.mov (RegOrMem.reg (Reg.low (Reg64.rsi) (Width.W64))) (Operand.regOrMem (RegOrMem.mem { base := some (RegOrRip.reg (Reg64.rdx)), idx := none, disp := ConstExpr.int64 fP })))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.mov (RegOrMem.reg (Reg.low (Reg64.r8) (Width.W64))) (Operand.regOrMem (RegOrMem.mem { base := some (RegOrRip.reg (Reg64.rsp)), idx := none, disp := ConstExpr.int64 d3 })))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.mov (RegOrMem.mem { base := some (RegOrRip.reg (Reg64.rsi)), idx := some { reg := Reg64.r8, scale := Width.W64 }, disp := ConstExpr.int64 8 }) (Operand.imm (ConstExpr.int64 w)))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.mov (RegOrMem.mem { base := some (RegOrRip.reg (Reg64.rsi)), idx := some { reg := Reg64.r8, scale := Width.W64 }, disp := ConstExpr.int64 16 }) (Operand.imm (ConstExpr.int64 w)))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W32) (Operation.cmp (RegOrMem.mem { base := some (RegOrRip.rip), idx := none, disp := ConstExpr.sub (ConstExpr.label "runtime.writeBarrier") (ConstExpr.after_current_instruction) }) (Operand.imm (ConstExpr.int64 0))))]

def tripleLoopTail (lwb lback : String) (dP : Int64) : Program :=
  [Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.jcc (CondCode.nz) lwb)),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.mov (RegOrMem.reg (Reg.low (Reg64.r10) (Width.W64))) (Operand.regOrMem (RegOrMem.mem { base := some (RegOrRip.reg (Reg64.rsp)), idx := none, disp := ConstExpr.int64 dP })))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.jmp (RelRegOrMem.rel (ConstExpr.sub (ConstExpr.label lback) (ConstExpr.after_current_instruction)))))]

def tripleLoopBack (lback : String) : Program :=
  [Kraken.Directive.label lback,
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.mov (RegOrMem.mem { base := some (RegOrRip.reg (Reg64.rsi)), idx := some { reg := Reg64.r8, scale := Width.W64 }, disp := ConstExpr.int64 0 }) (Operand.regOrMem (RegOrMem.reg (Reg.low (Reg64.r10) (Width.W64)))))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.lea (Reg.low (Reg64.rax) (Width.W64)) { base := some (RegOrRip.reg (Reg64.rdi)), idx := none, disp := ConstExpr.int64 1 }))]

end Codec.Segment
