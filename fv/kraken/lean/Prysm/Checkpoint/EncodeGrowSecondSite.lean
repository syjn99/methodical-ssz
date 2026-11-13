import Prysm.Checkpoint.EncodeHead
import Runtime.CopyModel

/-!
# `(*v1alpha1.Checkpoint).MarshalSSZTo`: the remaining capacity cases and the reject after growth

Each theorem is a prefix of `Prysm.Checkpoint.EncodeHead` followed by a tail of `Prysm.Checkpoint.EncodeTail` / `Prysm.Checkpoint.EncodeTailGrow`
(directive indices of the Go 1.26.10 `.S`, `Prysm.Checkpoint.Code.marshalSSZTo`):

- `Encode.grow_second_site` — first append fits, second needs growth (`len + 8 ≤ cap <
  len + 40`, `len(Root) = 32`): `Encode.head_fit` + `Encode.tail_grow`.
- `Encode.grow_any_site` (`Prysm/Checkpoint/EncodeGrowAnySite.lean`) — first append needs growth (`cap < len + 8`,
  every such case, including `cap = 0` / nil `dst`; no premise on `nextSliceCap`): `Encode.head_grow`,
  then the code's own branch on the capacity `C1` that `growslice` returned: `len + 40 ≤ C1` →
  `Encode.tail_fit` (left disjunct, full return); `C1 < len + 40` → `Encode.tail_grow_call` (right
  disjunct: the exact state at the entry of the second growslice call; the rest of that run is NOT
  proved, see `Prysm/Checkpoint/EncodeGrowAnySite.lean`).
- `Encode.reject_length_grow_first_site` — `cap < len + 8` and `len(Root) ≠ 32`: `Encode.head_grow` +
  `Encode.tail_rej`. The result is `(nil, ssz.ErrBytesLength words)`; the epoch bytes are at
  `new[len..len+8]` of the block that growslice returned (written before the root length test, here in the new block); the old
  block is unchanged; the new block is not returned (its pointer is in the dead frame slot only).

The error words `e0`, `e1` are the global's value as it is; that they are non-nil is not proved here
(no premise gives it): differential only.
-/

open Machine Runtime Prysm.Checkpoint.Code
variable [Host]

namespace Prysm.Checkpoint

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem Encode.grow_second_site (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (cst e8 cC ctl root pre d0 : List UInt8) (hcst : cst.length = 8) (he8 : e8.length = 8) (hcC : cC.length = 8)
    (hctl : ctl.length = 32) (hroot : root.length = 32) (hd0 : d0.length = 8)
    (p : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s2 l16 l24 l32 t40 t30 l72 spl rslot : List UInt8)
    (hfp : fp.length = 8) (h2 : s2.length = 8) (hl16 : l16.length = 8) (hl24 : l24.length = 8)
    (hl32 : l32.length = 8) (ht40 : t40.length = 16) (ht30 : t30.length = 16) (hl72 : l72.length = 8)
    (hspl : spl.length = 40) (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16)) ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32)) ⋆ Eq (t30.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 64)) ⋆ Eq (l72.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 112))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 120)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq (e8.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (ctl.At (s.regs.rax.toBitVec + 40)) ⋆ Eq (root.At p)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec)) ⋆ Heap avail ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 120 ≤ s.regs.rsp.toNat)
    (hlo : s.regs.rcx.toNat + 8 ≤ s.regs.rdi.toNat) (hhi : s.regs.rdi.toNat < s.regs.rcx.toNat + 40)
    (hbud : 2 * nextSliceCap (s.regs.rcx.toNat + 40) s.regs.rdi.toNat + 8192 ≤ avail) (hmax : avail ≤ maxAlloc)
    (hgs : GrowsliceC Heap ElfData.PrysmTarget.e2eU8Type_addr 1 S) (hmm : MemmoveC S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 40
        ∧ nextSliceCap (s.regs.rcx.toNat + 40) s.regs.rdi.toNat ≤ st.data.regs.rcx.toNat
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (t u scr spl' rest : List UInt8) (av' : Nat), t.length = 8 ∧ u.length = 16 ∧ scr.length = S
          ∧ spl'.length = 40 ∧ s.regs.rcx.toNat + 40 + rest.length = st.data.regs.rcx.toNat
          ∧ av' + st.data.regs.rcx.toNat ≤ avail ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 st.data.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 st.data.regs.rcx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 40).toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (u.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (e8.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (t.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 8).toInt).At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 63)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq (e8.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (ctl.At (s.regs.rax.toBitVec + 40)) ⋆ Eq (root.At p)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (e8.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (pre.At st.data.regs.rax.toBitVec) ⋆ Eq (e8.At (st.data.regs.rax.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (root.At (st.data.regs.rax.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (rest.At (st.data.regs.rax.toBitVec + s.regs.rcx.toBitVec + 40))
          ⋆ Heap av' ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hlo hhi hbud hpre ⊢
  refine eventually_trans _ _ _ _ (Encode.head_fit k hk hf e8 he8 _ ra guard fp s2 t40 t30 hfp h2 ht40 ht30 _
    (by dsimp only; ecancel) hguard hsp (by dsimp only; omega)) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, hrax1, hrbx1, hrcx1, hrdx1, hrdi1, t, u, ht, hu, Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 hrax1 hrbx1 hrcx1 hrdx1 hrdi1 Hm1
  subst hpc1
  refine eventually_mono (Encode.tail_grow k hk hf rsp r14 rbp ra rcx rdi rax.toBitVec rbx.toBitVec p e8 root pre d0
    l16 l24 l32 l72 spl rslot scratch he8 hroot hpre hd0 hl16 hl24 hl32 hl72 hspl hrs S hsc _ Heap avail d1
    hrsp1 hrbp1 hr141 (by rw [hrax1]) (by rw [hrbx1]) hrcx1 hrdx1 hrdi1 (by ecancel) hlo hhi hbud hmax hgs hmm) ?_
  rintro st ⟨e1, e2, e3, e4, e5, e6, e7, e8', scr, spl', rest, av', hscr, hspl', hrest, hav', Hm⟩
  exact ⟨e1, e2, e3, e4, e5, e6, e7, e8', t, u, scr, spl', rest, av', ht, hu, hscr, hspl', hrest, hav', by ecancel⟩

end Prysm.Checkpoint
