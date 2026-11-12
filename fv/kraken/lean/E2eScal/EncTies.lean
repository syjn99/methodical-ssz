import E2eScal.KindEncN
import E2eScal.BhEncMain
import E2eScal.E1EncMain
import Prysm.Checkpoint.EncodeFastPath

/-!
# ENC2 L1: ties of `encFastKindN` to the three hand-written encoder fast-path statements

- BeaconBlockHeader (`Bh.bh_e2e_marshal_main`) and Eth1Data (`E1.e1_e2e_marshal_main`): the declared type of
  the committed theorem is the kind instance, `rfl` at default transparency (the recursive definitions of
  the kind unfold on the literal layout and field list).
- Checkpoint (`Prysm.Checkpoint.Encode.fast_path`): not `rfl`. The hand statement names a 32-byte chunk `ctl` at
  `rax + 40` (after the capacity word of `Root`; not part of the Go layout of the receiver). In the kind that
  memory is part of `R`. `cp_marshal_of_kind`: the kind instance implies the hand statement. The converse
  does not hold as stated (`R` need not contain such a chunk). No other difference: with the binder `ctl`,
  its length hypothesis and its chunk removed, the two statements have the same text.

The hand statements and theorems are used as committed.
-/

open Machine Runtime TestTarget

open Codec
namespace E2eScal

/-- BeaconBlockHeader `MarshalSSZTo`: frame `0x98`, large-frame guard (`lea -0x20(%rsp),%r12`). Stack chunks
`fp s1 s2 l16 l96 l104 t1a t1b t2a t2b rslot`. -/
def layEncBh : EncLayout where
  st := true
  frame := 152
  gd := 32
  rt := true
  nstk := 11
  lens := [(0, 8), (1, 8), (2, 8), (3, 8), (4, 8), (5, 8), (6, 16), (7, 16), (8, 16), (9, 16), (10, 8)]
  pre := [.at (.dn 8) (.orig 0), .at (.up 8) (.orig 1), .at (.up 16) (.orig 2), .at (.dn 16) (.orig 3),
    .at (.dn 96) (.orig 4), .at (.dn 104) (.orig 5), .at (.dn 56) (.orig 6), .at (.dn 40) (.orig 7),
    .at (.dn 88) (.orig 8), .at (.dn 72) (.orig 9), .at (.dn 168) (.orig 10), .lo .scr]
  exs := [.n 8, .n 16, .n 8, .n 16, .lo]
  post := [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 16) (.reg .rbx),
    .at (.dn 96) (.reg .rdi), .at (.dn 104) (.len 112), .at (.dn 56) (.fld 0), .at (.dn 48) (.ex 0),
    .at (.dn 40) (.ex 1), .at (.dn 88) (.fld 1), .at (.dn 80) (.ex 2), .at (.dn 72) (.ex 3),
    .at (.dn 168) (.ret 148), .lo (.ex 4)]

/-- Eth1Data `MarshalSSZTo`: frame `0x80` (`add $-0x80,%rsp`), large-frame guard (`lea -0x8(%rsp),%r12`).
Stack chunks `fp s1 s2 l16 l24 l32 l40 l48 l56 rslot`. -/
def layEncE1 : EncLayout where
  st := true
  frame := 128
  gd := 8
  rt := true
  nstk := 10
  lens := [(0, 8), (1, 8), (2, 8), (3, 8), (4, 8), (5, 8), (6, 8), (7, 8), (8, 8), (9, 8)]
  pre := [.at (.dn 8) (.orig 0), .at (.up 8) (.orig 1), .at (.up 16) (.orig 2), .at (.dn 16) (.orig 3),
    .at (.dn 24) (.orig 4), .at (.dn 32) (.orig 5), .at (.dn 40) (.orig 6), .at (.dn 48) (.orig 7),
    .at (.dn 56) (.orig 8), .at (.dn 144) (.orig 9), .lo .scr]
  exs := [.lo]
  post := [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 16) (.reg .rbx),
    .at (.dn 24) (.reg .rbx), .at (.dn 32) (.len 72), .at (.dn 40) (.reg .rdi), .at (.dn 48) (.reg .rdi),
    .at (.dn 56) (.len 32), .at (.dn 144) (.ret 81), .lo (.ex 0)]

/-- Checkpoint `MarshalSSZTo`: frame `0x68`, small guard. Stack chunks `fp s2 l16 l24 l32 t40 t30 rslot` (the
order of the hand statement). -/
def layEncCp : EncLayout where
  st := true
  frame := 104
  gd := 0
  rt := true
  nstk := 8
  lens := [(0, 8), (1, 8), (2, 8), (3, 8), (4, 8), (5, 16), (6, 16), (7, 8)]
  pre := [.at (.dn 8) (.orig 0), .at (.up 16) (.orig 1), .at (.dn 16) (.orig 2), .at (.dn 24) (.orig 3),
    .at (.dn 32) (.orig 4), .at (.dn 48) (.orig 6), .at (.dn 64) (.orig 5), .at (.dn 120) (.orig 7), .lo .scr]
  exs := [.n 8, .n 16, .lo]
  post := [.at (.dn 8) (.reg .rbp), .at (.up 16) (.reg .rbx), .at (.dn 16) (.reg .rbx), .at (.dn 24) (.reg .rdi),
    .at (.dn 32) (.len 40), .at (.dn 48) (.ex 1), .at (.dn 64) (.fld 0), .at (.dn 56) (.ex 0),
    .at (.dn 120) (.ret 63), .lo (.ex 2)]

variable [Host]

/-- BeaconBlockHeader: the declared type of the hand theorem is the kind instance. -/
theorem bh_marshal_is_kindN : ∀ (h : Host), type_of% (@E2eScal.Bh.bh_e2e_marshal_main h)
    = @encFastKindN h E2eScal.BhCode.BhMarshal layEncBh [.u64, .u64, .bytes 32, .bytes 32, .bytes 32] := by
  intro h; rfl

/-- Eth1Data: the declared type of the hand theorem is the kind instance. -/
theorem e1_marshal_is_kindN : ∀ (h : Host), type_of% (@E2eScal.E1.e1_e2e_marshal_main h)
    = @encFastKindN h E2eScal.E1Code.E1Marshal layEncE1 [.bytes 32, .u64, .bytes 32] := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Checkpoint: the kind instance implies the hand theorem's statement.** Not `rfl`: the hand statement
names a 32-byte chunk `ctl` at `rax + 40` (in the kind it is part of `R`). The kind instance is the stronger
statement; the converse does not hold as stated. -/
theorem cp_marshal_of_kind
    (H : encFastKindN Prysm.Checkpoint.Code.marshalSSZTo layEncCp [.u64, .bytes 32]) :
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

end E2eScal
