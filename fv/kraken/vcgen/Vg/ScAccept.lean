import Kraken.StateCfg
import Kraken.SeparationMem
import Kraken.FunSpec
import Kraken.X64.Parser
import Vg.Specs

/-! B0: `sc_accept_main` (Scalars.UnmarshalSSZ accept path) as a vcgen `funspec`.

1b-fix X8: the 1b postcondition compared 16 SSZ bytes with the first 16 bytes
of the Go receiver. That is false: the SSZ fields sit at 0, 1, 3, 7, 15 and the
Go fields at 0, 2, 4, 8, 16 (padding between). The spill slot the code writes
is rsp + 16, not rsp + 8 (`Fk/ScAccept.lean`). Both are fixed here.

Re-proof R9 (astra 1b-fix finding 1): `s` in `funspec … at s` is the state
before the call; the callee's entry state is `s.push64 ra`, whose rsp is
`s.rsp − 8`. The spill slot entry-rsp + 16 is therefore pre-call `rsp + 8`, not
`rsp + 16` (1b-fix used + 16, following the earlier review). The return slot is
pre-call `rsp − 8`. The input is now also disjoint from the stack blocks (an
input at the spill slot would be overwritten by the first store).

Re-proof fix X7 (astra 1b-fix 1, reprove 7): the reachable labels `L_37` (bool
byte 0) and `L_3b` (join) have the invariant `ScInv` instead of `False`. VCs:
20; `kfinish` closes 3; 17 stay open (memory mapping `isSome` after stores,
the label VCs with `Mem.WritesOnly`). Record: `../b0x7-scaccept.txt`. -/

open Kraken.X64.Parser
open Std.WP
open Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace Vg

def ScU : Program := parseFile("../link/out/norm/target.Scalars.UnmarshalSSZ.S")

/-- Go ABIInternal on amd64: no callee-saved general register except rsp
(rbp is the frame pointer, r14 = g, X15 = 0 are fixed, not saved/restored). -/
def GoABI : CallingConvention := ⟨[.rsp, .r14], fun k => 8 * k⟩

/-- Label invariant of the accept path (re-proof fix X7). `done = false` at
`L_37` (the bool byte is 0, field 4 not yet written), `true` at `L_3b`. `s` is
the state before the call, `s₀ = s.push64 ra` the entry state. -/
def ScInv (s s₀ t : MachineData) (done : Bool) : Prop :=
  t.regs.rsp = s₀.regs.rsp ∧ t.regs.rax = s.regs.rax ∧ t.regs.rbp = s.regs.rbp ∧ t.regs.r14 = s.regs.r14
  ∧ t.dmem.loadBytes s₀.regs.rsp.toBitVec 8 = s₀.dmem.loadBytes s₀.regs.rsp.toBitVec 8
  ∧ Mem.Mapped [(s.regs.rbx.toBitVec, 16), (s.regs.rax.toBitVec, 17),
      (s.regs.rsp.toBitVec - 8#64, 8), (s.regs.rsp.toBitVec + 8#64, 8)] t.dmem
  ∧ Mem.WritesOnly [(s.regs.rax.toBitVec, 17), (s.regs.rsp.toBitVec - 8#64, 8), (s.regs.rsp.toBitVec + 8#64, 8)]
      s.dmem t.dmem
  ∧ t.dmem.loadBytes s.regs.rax.toBitVec 1 = s.dmem.loadBytes s.regs.rbx.toBitVec 1
  ∧ t.dmem.loadBytes (s.regs.rax.toBitVec + 2#64) 2 = s.dmem.loadBytes (s.regs.rbx.toBitVec + 1#64) 2
  ∧ t.dmem.loadBytes (s.regs.rax.toBitVec + 4#64) 4 = s.dmem.loadBytes (s.regs.rbx.toBitVec + 3#64) 4
  ∧ t.dmem.loadBytes (s.regs.rax.toBitVec + 8#64) 8 = s.dmem.loadBytes (s.regs.rbx.toBitVec + 7#64) 8
  ∧ (if done then t.dmem.loadBytes (s.regs.rax.toBitVec + 16#64) 1 = s.dmem.loadBytes (s.regs.rbx.toBitVec + 15#64) 1
     else (s.dmem.loadInt (s.regs.rbx.toBitVec + 15#64) 1).get! = 0)

set_option maxHeartbeats 4000000 in
funspec sc_accept_vg "target.Scalars.UnmarshalSSZ" [Host] [FunDecls] [Embeds ScU]
    (hs : FunDecls.at (label "target.Scalars.UnmarshalSSZ") = some ⟨ScU⟩) at s
    requires s.regs.rcx = 16
      ∧ s.regs.rbx.toNat + 16 < 2 ^ 64 ∧ s.regs.rax.toNat + 17 < 2 ^ 64
      ∧ Mem.Mapped [(s.regs.rbx.toBitVec, 16), (s.regs.rax.toBitVec, 17),
          (s.regs.rsp.toBitVec - 8#64, 8), (s.regs.rsp.toBitVec + 8#64, 8)] s.dmem
      ∧ Mem.Blocks.Disjoint [(s.regs.rax.toBitVec, 17)]
          [(s.regs.rbx.toBitVec, 16), (s.regs.rsp.toBitVec - 8#64, 8), (s.regs.rsp.toBitVec + 8#64, 8)]
      ∧ Mem.Blocks.Disjoint [(s.regs.rbx.toBitVec, 16)]
          [(s.regs.rsp.toBitVec - 8#64, 8), (s.regs.rsp.toBitVec + 8#64, 8)]
      ∧ (s.dmem.loadInt (s.regs.rbx.toBitVec + 15#64) 1).get! ≤ 1
    ensures s' => s'.regs.rax = 0 ∧ s'.regs.rbx = 0
      ∧ s'.dmem.loadBytes s.regs.rax.toBitVec 1 = s.dmem.loadBytes s.regs.rbx.toBitVec 1
      ∧ s'.dmem.loadBytes (s.regs.rax.toBitVec + 2#64) 2 = s.dmem.loadBytes (s.regs.rbx.toBitVec + 1#64) 2
      ∧ s'.dmem.loadBytes (s.regs.rax.toBitVec + 4#64) 4 = s.dmem.loadBytes (s.regs.rbx.toBitVec + 3#64) 4
      ∧ s'.dmem.loadBytes (s.regs.rax.toBitVec + 8#64) 8 = s.dmem.loadBytes (s.regs.rbx.toBitVec + 7#64) 8
      ∧ s'.dmem.loadBytes (s.regs.rax.toBitVec + 16#64) 1 = s.dmem.loadBytes (s.regs.rbx.toBitVec + 15#64) 1
    autoframes calling_conv GoABI preserves rbp
      writes s.regs.rax.toBitVec[*...<17], (s.regs.rsp.toBitVec + 8#64)[*...<8] := by
  refine Program.Triple.cfg
    (fun s₀ => fun
      | "target.Scalars.UnmarshalSSZ", s' => s' = s₀
      | "L_target.Scalars.UnmarshalSSZ_37", t => ScInv s s₀ t false
      | "L_target.Scalars.UnmarshalSSZ_3b", t => ScInv s s₀ t true
      | _, _ => False)
    (fun _ _ _ => 0) fun s₀ ⟨h₀, _⟩ => ?_
  cfg_cases
  all_goals vcgen with kfinish

end Vg
