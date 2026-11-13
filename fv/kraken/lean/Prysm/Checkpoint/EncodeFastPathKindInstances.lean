import Codec.Kind.EncodeFastPathAnyFrame
import Prysm.Checkpoint.EncodeFastPath

/-!
# Tie of `encodeFastPathKindAnyFrame` to the hand-written encoder fast-path statement of Checkpoint

`encodeLayout` is the layout of the hand statement `Encode.fast_path`, with the stack chunks in its order.
`Encode.fast_path_of_kind`: the kind instance implies the hand statement; the converse does not hold as stated.
-/

open Machine Runtime

open Codec
namespace Prysm.Checkpoint

/-- Checkpoint `MarshalSSZTo`: frame `0x68`, small guard. Stack chunks `fp s2 l16 l24 l32 t40 t30 rslot` (the
order of the hand statement). -/
def encodeLayout : EncoderFrameLayout where
  stateWord := true
  frame := 104
  guardAddend := 0
  callsMemmove := true
  stackChunkCount := 8
  stackChunkLengths := [(0, 8), (1, 8), (2, 8), (3, 8), (4, 8), (5, 16), (6, 16), (7, 8)]
  pre := [.at (.below 8) (.original 0), .at (.above 16) (.original 1), .at (.below 16) (.original 2), .at (.below 24) (.original 3),
    .at (.below 32) (.original 4), .at (.below 48) (.original 6), .at (.below 64) (.original 5), .at (.below 120) (.original 7), .low .scratch]
  existentials := [.fixed 8, .fixed 16, .low]
  post := [.at (.below 8) (.reg .rbp), .at (.above 16) (.reg .rbx), .at (.below 16) (.reg .rbx), .at (.below 24) (.reg .rdi),
    .at (.below 32) (.len 40), .at (.below 48) (.existential 1), .at (.below 64) (.field 0), .at (.below 56) (.existential 0),
    .at (.below 120) (.ret 63), .low (.existential 2)]

variable [Host]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Checkpoint: the kind instance implies the hand theorem's statement.** Not `rfl`: the hand statement
names a 32-byte chunk `ctl` at `rax + 40` (in the kind it is part of `R`). The kind instance is the stronger
statement; the converse does not hold as stated. -/
theorem Encode.fast_path_of_kind
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
