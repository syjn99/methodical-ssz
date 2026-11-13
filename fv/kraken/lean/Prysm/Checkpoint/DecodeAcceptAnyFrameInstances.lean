import Codec.Kind.DecodeAcceptAnyFrame
import Prysm.BeaconBlockHeader.DecodeAccept
import Prysm.PendingPartialWithdrawal.DecodeAccept
import Prysm.SyncCommitteeMessage.Statements
import Prysm.PendingDeposit.Statements
import Prysm.Checkpoint.DecodeAccept
import Codec.Kind.DecodeAcceptAnyFrameInstances

/-!
# Ties of `decAcceptKindN` to the hand accept statements: the `Checkpoint` part

The declarations of the other types of this group are in `Codec/Kind/DecodeAcceptAnyFrameInstances.lean`.
-/

open Machine Runtime

open Codec
namespace Prysm.Checkpoint

variable [Host]

/-- Checkpoint layout for the kind (frame `0x50`; callee `Epoch`, one byte field). -/
def decodeLayout : DecLayout where
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

theorem Decode.lo_addr (x : BitVec 64) (S : Nat) (h8 : 8 ≤ S) (hS : S < 2 ^ 60) :
    x - 96 - BitVec.ofNat 64 S = x - 104 - BitVec.ofNat 64 (S - 8) := by
  rw [Prysm.Checkpoint.Decode.accept_ofNat S h8 hS]; bv_omega

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Checkpoint: the kind instance implies the hand theorem's statement.** Not `rfl`: the hand statement
has the premise `8 ≤ S` with a low stack of `S` bytes (the kind: `S + 8` bytes, any `S`), binds the low stack
after `R S`, orders three stack chunks and the two existential chunks differently, writes the zero slots as
`Int.toBytes 8 0`, and names a 32-byte receiver tail chunk `ctl` (in the kind it is part of `R`). The kind
instance is the stronger statement; the converse does not hold (`R` need not contain a tail chunk). -/
theorem Decode.accept_of_kind
    (H : decAcceptKindN Prysm.Checkpoint.Code.unmarshalSSZ Prysm.Checkpoint.decodeLayout [.u64, .bytes 32]) :
    type_of% (@Prysm.Checkpoint.Decode.accept ‹Host›) := by
  intro k hk hf kE hkE hfE e8 root he8 hroot s ra guard fp s1 s2 l20 l28 l30 m0 m1 m2 rslot cst c0 cP cL cC ctl
    hfp h1 h2 hl20 hl28 hl30 hm0 hm1 hm2 hrs hcst hc0 hcP hcL hcC hctl R S hS8 hS scratch hsc Heap avail
    h_mem hguard hlen hav hms hmm
  have hS' : S - 8 + 8 = S := by omega
  rw [Prysm.Checkpoint.Decode.lo_addr _ S hS8 hS] at h_mem ⊢
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

end Prysm.Checkpoint
