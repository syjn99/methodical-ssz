import Kraken.StateCfg
import Kraken.SeparationMem
import Kraken.FunSpec
import Kraken.X64.Parser
import Vg.Specs

/-! B0: `sc_accept_main` (Scalars.UnmarshalSSZ accept path) as a vcgen `funspec`. -/

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

set_option maxHeartbeats 4000000 in
funspec sc_accept_vg "target.Scalars.UnmarshalSSZ" [Host] [FunDecls] [Embeds ScU]
    (hs : FunDecls.at (label "target.Scalars.UnmarshalSSZ") = some ⟨ScU⟩) at s
    requires s.regs.rcx = 16
      ∧ s.regs.rbx.toNat + 16 < 2 ^ 64 ∧ s.regs.rax.toNat + 17 < 2 ^ 64
      ∧ Mem.Mapped [(s.regs.rbx.toBitVec, 16), (s.regs.rax.toBitVec, 17),
          (s.regs.rsp.toBitVec - 8#64, 8), (s.regs.rsp.toBitVec + 8#64, 8)] s.dmem
      ∧ Mem.Blocks.Disjoint [(s.regs.rax.toBitVec, 17)]
          [(s.regs.rbx.toBitVec, 16), (s.regs.rsp.toBitVec - 8#64, 8), (s.regs.rsp.toBitVec + 8#64, 8)]
      ∧ (s.dmem.loadInt (s.regs.rbx.toBitVec + 15#64) 1).get! ≤ 1
    ensures s' => s'.regs.rax = 0 ∧ s'.regs.rbx = 0
      ∧ s'.dmem.loadBytes s.regs.rax.toBitVec 16 = s.dmem.loadBytes s.regs.rbx.toBitVec 16
    autoframes calling_conv GoABI preserves rbp
      writes s.regs.rax.toBitVec[*...<17], (s.regs.rsp.toBitVec + 8#64)[*...<8] := by
  refine Program.Triple.cfg
    (fun s₀ => fun
      | "target.Scalars.UnmarshalSSZ", s' => s' = s₀
      | _, _ => False)
    (fun _ _ _ => 0) fun s₀ ⟨h₀, _⟩ => ?_
  cfg_cases
  all_goals vcgen with kfinish

end Vg
