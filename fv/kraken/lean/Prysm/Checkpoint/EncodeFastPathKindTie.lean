import Codec.Kind.EncodeFastPathAnyFrame
import Prysm.Checkpoint.EncodeFastPath
import Prysm.Checkpoint.Code
import Prysm.Checkpoint.EncodeLayout

/-!
# Tie of `encodeFastPathKindAnyFrame` to the hand encoder fast-path statement of `Checkpoint`

This theorem shows that the kind `Codec.encodeFastPathKindAnyFrame` implies the statement of the hand theorem `Prysm.Checkpoint.Encode.fast_path`.
`encodeLayout` (`Prysm/Checkpoint/EncodeLayout.lean`) is the layout of the hand statement `Encode.fast_path`, with the stack chunks in its order.
The converse does not hold as stated.
-/

open Machine Runtime

open Codec
namespace Prysm.Checkpoint

variable [Host]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Checkpoint: the kind instance implies the hand theorem's statement.** Not `rfl`: the hand statement
names a 32-byte chunk `ctl` at `rax + 40` (in the kind it is part of `R`). The kind instance is the stronger
statement; the converse does not hold as stated. -/
theorem Encode.fast_path_kind_tie
    (H : encodeFastPathKindAnyFrame Prysm.Checkpoint.Code.marshalSSZTo Prysm.Checkpoint.encodeLayout [.uint64, .bytes 32]) :
    type_of% (@Prysm.Checkpoint.Encode.fast_path ‹Host›) := by
  intro k hk hf cst e8 cC ctl root pre d0 d1 hcst he8 hcC hctl hroot hd0 hd1 p s ra guard hpre
    fp s2 l16 l24 l32 t40 t30 rslot hfp h2 hl16 hl24 hl32 ht40 ht30 hrs R S scratch hsc
    h_mem hguard hsp hcap hcap63 hmm
  have hm : (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16)) ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32)) ⋆ Eq (t30.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 120)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq (e8.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (root.At p)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
      ⋆ (Eq (ctl.At (s.regs.rax.toBitVec + 40)) ⋆ R)) s.dmem := by
    ecancel
  have H' := H k hk hf cst e8 cC root pre d0 d1 hcst he8 hcC hroot hd0 hd1 p s ra guard hpre
    fp s2 l16 l24 l32 t40 t30 rslot hfp h2 hl16 hl24 hl32 ht40 ht30 hrs
    (Eq (ctl.At (s.regs.rax.toBitVec + 40)) ⋆ R) S scratch hsc hm hguard hsp hcap hcap63 hmm
  refine eventually_trans _ _ _ _ H' ?_
  rintro ⟨d, pc⟩ ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, hrsp, hrbp, hr14, t, u, scr, ht, hu, hscr, Hm⟩
  apply Eventually.done
  have Hm' : (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 40).toInt).At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (u.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (e8.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (t.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 63)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 120))
      ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq (e8.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (root.At p)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (e8.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (root.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
      ⋆ (Eq (ctl.At (s.regs.rax.toBitVec + 40)) ⋆ R)) d.dmem := Hm
  exact ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, hrsp, hrbp, hr14, t, u, scr, ht, hu, hscr, by ecancel⟩

end Prysm.Checkpoint
