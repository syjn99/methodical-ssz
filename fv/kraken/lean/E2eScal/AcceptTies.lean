import E2eScal.KindAcceptN
import E2eScal.BhAccept
import E2eScal.PwAccept
import E2eScal.H5Stmt
import E2eScal.H6Stmt
import Prysm.Checkpoint.DecodeAccept

/-!
# GEN5 L1: ties of `decAcceptKindN` to the hand accept statements

For every flat development type with a hand-written accept statement, the kind instance is that statement.
`rfl` at default transparency (the recursive definitions of the kind unfold on the literal layout and field
list), as the GEN3 ties of `decAcceptKind`. The hand statements and theorems are used as committed.

Layouts: three frame classes.
- `layRt st jret nb` (frame `0x20`, `makeslice` / `memmove` only): BlobIdentifier, DepositMessage, Eth1Data,
  Deposit_Data, PowBlock.
- `layCal callees jret` (frame `0x48`, callee decoders only): PendingPartialWithdrawal, PendingConsolidation.
- `layMix40`, `layMix60` (frames `0x40`, `0x60`, both): PendingDeposit; SyncCommitteeMessage,
  BeaconBlockHeader.

Checkpoint (`Prysm.Checkpoint.Decode.accept`) is not `rfl`: see `cp_accept_of_kind` (the kind instance implies the
hand statement; the converse does not hold).
-/

open Machine Runtime TestTarget

open Codec
namespace E2eScal

/-- Frame `0x20`, runtime calls only. `nb` = number of byte fields (the pointer save slot holds the last
pointer), `jret` = the directive after the last `callq runtime.memmove`. -/
def layRt (st : Bool) (jret nb : Nat) : DecLayout where
  callees := []
  nstk := 7
  lens := [(0, 8), (1, 8), (2, 8), (3, 24), (4, 8), (5, 8)]
  pre := [.at (.dn 8) (.orig 0), .at (.up 8) (.orig 1), .at (.up 16) (.orig 2), .at (.dn 40) (.orig 3),
    .at (.dn 16) (.orig 4), .at (.dn 48) (.orig 5), .lo (.orig 6)]
  rt := some ⟨false, 0, 6, 48⟩
  gd := 0
  st := st
  exs := [.n 24, .lo]
  post := [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 40) (.ex 0),
    .at (.dn 16) (.ptr (nb - 1)), .at (.dn 48) (.ret jret), .lo (.ex 1)]
  frame := 40

/-- Frame `0x48`, callee decoders only. `jret` = the directive after the last callee `callq`. -/
def layCal (callees : List Program) (jret : Nat) : DecLayout where
  callees := callees
  nstk := 7
  lens := [(0, 8), (1, 8), (2, 8), (3, 8), (4, 8), (5, 8), (6, 8)]
  pre := [.at (.dn 8) (.orig 0), .at (.up 8) (.orig 1), .at (.up 16) (.orig 2), .at (.up 32) (.orig 3),
    .at (.dn 72) (.orig 4), .at (.dn 88) (.orig 5), .at (.dn 96) (.orig 6)]
  rt := none
  gd := 88
  st := true
  exs := [.n 8, .n 8]
  post := [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.up 32) (.reg .rdi),
    .at (.dn 72) (.ex 0), .at (.dn 88) (.ret jret), .at (.dn 96) (.ex 1)]
  frame := 80

/-- Frame `0x40`, callee decoders and runtime calls (PendingDeposit). `ip` = index of the byte field whose
pointer is in the save slot at the end. -/
def layMix40 (callees : List Program) (jret ip : Nat) : DecLayout where
  callees := callees
  nstk := 10
  lens := [(0, 8), (1, 8), (2, 8), (3, 8), (4, 8), (5, 8), (6, 8), (7, 8), (8, 8)]
  pre := [.at (.dn 8) (.orig 0), .at (.up 8) (.orig 1), .at (.up 16) (.orig 2), .at (.up 32) (.orig 3),
    .at (.dn 72) (.orig 4), .at (.dn 64) (.orig 5), .at (.dn 56) (.orig 6), .at (.dn 32) (.orig 7),
    .at (.dn 80) (.orig 8), .lo (.orig 9)]
  rt := some ⟨true, 8, 9, 88⟩
  gd := 80
  st := true
  exs := [.n 24, .lo]
  post := [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.up 32) (.reg .rdi),
    .at (.dn 72) (.ex 0), .at (.dn 32) (.ptr ip), .at (.dn 80) (.ret jret), .lo (.ex 1)]
  frame := 72

/-- Frame `0x60`, callee decoders and runtime calls (SyncCommitteeMessage, BeaconBlockHeader). -/
def layMix60 (callees : List Program) (jret ip : Nat) : DecLayout where
  callees := callees
  nstk := 12
  lens := [(0, 8), (1, 8), (2, 8), (3, 8), (4, 8), (5, 8), (6, 8), (7, 8), (8, 8), (9, 8), (10, 8)]
  pre := [.at (.dn 8) (.orig 0), .at (.up 8) (.orig 1), .at (.up 16) (.orig 2), .at (.up 32) (.orig 3),
    .at (.dn 104) (.orig 4), .at (.dn 96) (.orig 5), .at (.dn 88) (.orig 6), .at (.dn 64) (.orig 7),
    .at (.dn 56) (.orig 8), .at (.dn 48) (.orig 9), .at (.dn 112) (.orig 10), .lo (.orig 11)]
  rt := some ⟨true, 8, 11, 120⟩
  gd := 112
  st := true
  exs := [.n 24, .lo]
  post := [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.up 32) (.reg .rdi),
    .at (.dn 104) (.ex 0), .at (.dn 64) .zero, .at (.dn 56) .zero, .at (.dn 48) (.ptr ip),
    .at (.dn 112) (.ret jret), .lo (.ex 1)]
  frame := 104

/-! ## Class A: frame `0x20` -/

theorem bi_accept_is_kindN : ∀ (h : Host), type_of% (@E2eScal.Bi.bi_e2e_accept_main h)
    = @decAcceptKindN h E2eScal.H3Code.BiUnmarshal (layRt true 32 1) [.bytes 32, .u64] := by
  intro h; rfl

theorem dm_accept_is_kindN : ∀ (h : Host), type_of% (@E2eScal.Dm.dm_e2e_accept_main h)
    = @decAcceptKindN h E2eScal.H3Code.DmUnmarshal (layRt false 68 2) [.bytes 48, .bytes 32, .u64] := by
  intro h; rfl

theorem e1_accept_is_kindN : ∀ (h : Host), type_of% (@E2eScal.E1.e1_e2e_accept_main h)
    = @decAcceptKindN h E2eScal.E1Code.E1Unmarshal (layRt true 70 2) [.bytes 32, .u64, .bytes 32] := by
  intro h; rfl

theorem dd_accept_is_kindN : ∀ (h : Host), @E2eScal.H4.dd_accept_stmt h
    = @decAcceptKindN h E2eScal.H4Code.DdUnmarshal (layRt true 106 3) [.bytes 48, .bytes 32, .u64, .bytes 96] := by
  intro h; rfl

theorem pb_accept_is_kindN : ∀ (h : Host), @E2eScal.H6.pb_accept_stmt h
    = @decAcceptKindN h E2eScal.H6Code.PbUnmarshal (layRt false 104 3) [.bytes 32, .bytes 32, .bytes 32] := by
  intro h; rfl

/-! ## Class B: frame `0x48` -/

theorem pw_accept_is_kindN : ∀ (h : Host), @E2eScal.H4.pw_accept_stmt h
    = @decAcceptKindN h E2eScal.H4Code.PwUnmarshal
        (layCal [E2eScal.BhCode.ViUnmarshal, Prysm.Epoch.Code.unmarshalSSZ] 60) [.u64, .u64, .u64] := by
  intro h; rfl

theorem pc_accept_is_kindN : ∀ (h : Host), @E2eScal.H5.pc_accept_stmt h
    = @decAcceptKindN h E2eScal.H5Code.PcUnmarshal (layCal [E2eScal.BhCode.ViUnmarshal] 56) [.u64, .u64] := by
  intro h; rfl

/-! ## Class C: frames `0x40`, `0x60` -/

theorem pd_accept_is_kindN : ∀ (h : Host), @E2eScal.H6.pd_accept_stmt h
    = @decAcceptKindN h E2eScal.H6Code.PdUnmarshal (layMix40 [E2eAd.Code.SlUnmarshal] 131 2)
        [.bytes 48, .bytes 32, .u64, .bytes 96, .u64] := by
  intro h; rfl

theorem sm_accept_is_kindN : ∀ (h : Host), @E2eScal.H5.sm_accept_stmt h
    = @decAcceptKindN h E2eScal.H5Code.SmUnmarshal
        (layMix60 [E2eAd.Code.SlUnmarshal, E2eScal.BhCode.ViUnmarshal] 141 1)
        [.u64, .bytes 32, .u64, .bytes 96] := by
  intro h; rfl

theorem bh_accept_is_kindN : ∀ (h : Host), type_of% (@E2eScal.Bh.bh_e2e_accept_main h)
    = @decAcceptKindN h E2eScal.BhCode.BhUnmarshal
        (layMix60 [E2eAd.Code.SlUnmarshal, E2eScal.BhCode.ViUnmarshal] 179 2)
        [.u64, .u64, .bytes 32, .bytes 32, .bytes 32] := by
  intro h; rfl

/-! ## Relation to the GEN3 kind `decAcceptKind` (the four types it is tied to) -/

theorem bi_kindN_is_kind : ∀ (h : Host),
    @decAcceptKindN h E2eScal.H3Code.BiUnmarshal (layRt true 32 1) [.bytes 32, .u64]
    = @decAcceptKind h E2eScal.H3Code.BiUnmarshal true [.bytes 32, .u64] 32 :=
  fun h => (bi_accept_is_kindN h).symm.trans (bi_accept_is_kind h)

theorem dm_kindN_is_kind : ∀ (h : Host),
    @decAcceptKindN h E2eScal.H3Code.DmUnmarshal (layRt false 68 2) [.bytes 48, .bytes 32, .u64]
    = @decAcceptKind h E2eScal.H3Code.DmUnmarshal false [.bytes 48, .bytes 32, .u64] 68 :=
  fun h => (dm_accept_is_kindN h).symm.trans (dm_accept_is_kind h)

theorem e1_kindN_is_kind : ∀ (h : Host),
    @decAcceptKindN h E2eScal.E1Code.E1Unmarshal (layRt true 70 2) [.bytes 32, .u64, .bytes 32]
    = @decAcceptKind h E2eScal.E1Code.E1Unmarshal true [.bytes 32, .u64, .bytes 32] 70 :=
  fun h => (e1_accept_is_kindN h).symm.trans (e1_accept_is_kind h)

theorem dd_kindN_is_kind : ∀ (h : Host),
    @decAcceptKindN h E2eScal.H4Code.DdUnmarshal (layRt true 106 3) [.bytes 48, .bytes 32, .u64, .bytes 96]
    = @decAcceptKind h E2eScal.H4Code.DdUnmarshal true [.bytes 48, .bytes 32, .u64, .bytes 96] 106 :=
  fun h => (dd_accept_is_kindN h).symm.trans (dd_accept_is_kind h)

/-! ## Checkpoint: implication, not `rfl` -/

variable [Host]

/-- Checkpoint layout for the kind (frame `0x50`; callee `Epoch`, one byte field). -/
def layCp : DecLayout where
  callees := [Prysm.Epoch.Code.unmarshalSSZ]
  nstk := 11
  lens := [(0, 8), (1, 8), (2, 8), (3, 8), (4, 8), (5, 8), (6, 8), (7, 8), (8, 8), (9, 8)]
  pre := [.at (.dn 8) (.orig 0), .at (.up 8) (.orig 1), .at (.up 16) (.orig 2), .at (.dn 32) (.orig 3),
    .at (.dn 40) (.orig 4), .at (.dn 48) (.orig 5), .at (.dn 88) (.orig 6), .at (.dn 80) (.orig 7),
    .at (.dn 72) (.orig 8), .at (.dn 96) (.orig 9), .lo (.orig 10)]
  rt := some ⟨true, 8, 10, 104⟩
  gd := 96
  st := true
  exs := [.n 24, .lo]
  post := [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 32) (.ptr 0),
    .at (.dn 40) .zero, .at (.dn 48) .zero, .at (.dn 88) (.ex 0), .at (.dn 96) (.ret 70), .lo (.ex 1)]
  frame := 88

theorem cp_lo_addr (x : BitVec 64) (S : Nat) (h8 : 8 ≤ S) (hS : S < 2 ^ 60) :
    x - 96 - BitVec.ofNat 64 S = x - 104 - BitVec.ofNat 64 (S - 8) := by
  rw [Prysm.Checkpoint.Decode.accept_ofNat S h8 hS]; bv_omega

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Checkpoint: the kind instance implies the hand theorem's statement.** Not `rfl`: the hand statement
has the premise `8 ≤ S` with a low stack of `S` bytes (the kind: `S + 8` bytes, any `S`), binds the low stack
after `R S`, orders three stack chunks and the two existential chunks differently, writes the zero slots as
`Int.toBytes 8 0`, and names a 32-byte receiver tail chunk `ctl` (in the kind it is part of `R`). The kind
instance is the stronger statement; the converse does not hold (`R` need not contain a tail chunk). -/
theorem cp_accept_of_kind
    (H : decAcceptKindN Prysm.Checkpoint.Code.unmarshalSSZ layCp [.u64, .bytes 32]) :
    type_of% (@Prysm.Checkpoint.Decode.accept ‹Host›) := by
  intro k hk hf kE hkE hfE e8 root he8 hroot s ra guard fp s1 s2 l20 l28 l30 m0 m1 m2 rslot cst c0 cP cL cC ctl
    hfp h1 h2 hl20 hl28 hl30 hm0 hm1 hm2 hrs hcst hc0 hcP hcL hcC hctl R S hS8 hS scratch hsc Heap avail
    h_mem hguard hlen hav hms hmm
  have hS' : S - 8 + 8 = S := by omega
  rw [cp_lo_addr _ S hS8 hS] at h_mem ⊢
  have hm : (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l20.At (s.regs.rsp.toBitVec - 32)) ⋆ Eq (l28.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (l30.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (m0.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (m1.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (m2.At (s.regs.rsp.toBitVec - 72)) ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 104 - BitVec.ofNat 64 (S - 8)))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (e8.At s.regs.rbx.toBitVec) ⋆ Eq (root.At (s.regs.rbx.toBitVec + 8))
      ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq (c0.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (cP.At (s.regs.rax.toBitVec + 16)) ⋆ Eq (cL.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
      ⋆ (Eq (ctl.At (s.regs.rax.toBitVec + 40)) ⋆ R)) s.dmem := by
    ecancel
  have H' := H k hk hf kE hkE hfE e8 root he8 hroot s ra guard fp s1 s2 l20 l28 l30 m0 m1 m2 rslot scratch
    cst c0 cP cL cC hfp h1 h2 hl20 hl28 hl30 hm0 hm1 hm2 hrs hcst hc0 hcP hcL hcC
    (Eq (ctl.At (s.regs.rax.toBitVec + 40)) ⋆ R) (S - 8) (by omega) (hsc.trans hS'.symm)
    Heap avail hm hguard hlen hav (by rw [show addX (S - 8) 8 = S from hS']; exact hms)
    (by rw [show addX (S - 8) 8 = S from hS']; exact hmm)
  refine eventually_trans _ _ _ _ H' ?_
  rintro ⟨d, pc⟩ ⟨hpc, hrax, hrbx, hrsp, hrbp, hr14, p, mm, scr, hmml, hscr, Hm⟩
  apply Eventually.done
  have Hm' : (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq ((Int.toBytes 8 0).At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq ((Int.toBytes 8 0).At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (mm.At (s.regs.rsp.toBitVec - 88))
      ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 70)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 104 - BitVec.ofNat 64 (S - 8)))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap (avail - 32)
      ⋆ Eq (e8.At s.regs.rbx.toBitVec) ⋆ Eq (root.At (s.regs.rbx.toBitVec + 8))
      ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq (e8.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (root.At p)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
      ⋆ (Eq (ctl.At (s.regs.rax.toBitVec + 40)) ⋆ R)) d.dmem := Hm
  refine ⟨hpc, hrax, hrbx, hrsp, hrbp, hr14, p, scr, mm, hscr.trans hS', hmml, ?_⟩
  dsimp only
  ecancel

end E2eScal
