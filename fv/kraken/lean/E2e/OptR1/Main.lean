import E2e.OptR1.HeadG
import E2e.OptR1.TailR
import Runtime.CopyModel

/-!
# OPT-R1 reserve encoder `(*v1alpha1.Checkpoint).MarshalSSZTo`: the four main theorems

Contract of the pilot for the new ELF `3ef7ac89…f602`
(`L = len(dst)`, `C = cap(dst)`, `spare = C − L`):

| theorem                        | range              | result (exact frame)                                        |
| `cpo_marshal_main`             | `L + 40 ≤ C`       | `(dst.ptr, L + 40, C, nil)`; writes `dst[L..L+40]` only; no heap |
| `cpo_marshal_reject_main`      | `L + 40 ≤ C`, root length ≠ 32 | `(nil, ErrBytesLength)`; writes `dst[L..L+8]` (epoch written before the root test)  |
| `cpo_marshal_grow_main`        | `L ≤ C < L + 40`   | `(new, L + 40, newCap, nil)`; one heap block of `newCap ≥ nextSliceCap (L+40) C` bytes; the caller's `pre ++ spare` unchanged |
| `cpo_marshal_reject_grow_main` | `L ≤ C < L + 40`, root length ≠ 32 | `(nil, ErrBytesLength)`; one heap block (not returned); the caller's array unchanged |

The new block on the grow path is `pre ++ epoch ++ root ++ tail` (resp. `pre ++ epoch ++ z' ++ tail` on the
reject path, `z'` = bytes 8–39 of the zeroed `z`, existential because X15 is not assumed zero). Neither path
reaches the two `growslice` calls of the original appends (directives 66 and 88).
-/

open Machine Runtime TestTarget E2e.OptR1.Code
variable [Host]

namespace E2e.OptR1

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem cpo_marshal_main (k : Nat) (hk : CpMarshalO.IsInfixAt Host.prog k) (hf : LabelsFresh CpMarshalO k)
    (cst e8 cC ctl root pre d0 d1 : List UInt8) (hcst : cst.length = 8) (he8 : e8.length = 8) (hcC : cC.length = 8)
    (hctl : ctl.length = 32) (hroot : root.length = 32) (hd0 : d0.length = 8) (hd1 : d1.length = 32)
    (p : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 s3 l16 l24 l32 t40 t30 rslot : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h3 : s3.length = 8) (hl16 : l16.length = 8)
    (hl24 : l24.length = 8) (hl32 : l32.length = 8) (ht40 : t40.length = 16) (ht30 : t30.length = 16)
    (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s3.At (s.regs.rsp.toBitVec + 24))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16)) ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32)) ⋆ Eq (t30.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 160)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 160 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq (e8.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (ctl.At (s.regs.rax.toBitVec + 40)) ⋆ Eq (root.At p)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8)) ⋆ R)
    (hguard : guard.toNat + 24 < s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 40 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hmm : MemmoveC S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 40 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (t u scr : List UInt8), t.length = 8 ∧ u.length = 16 ∧ scr.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rcx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 40).toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (u.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (e8.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (t.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 103)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 160 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq (e8.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (ctl.At (s.regs.rax.toBitVec + 40)) ⋆ Eq (root.At p)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (e8.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (root.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hcap hcap63 hpre ⊢
  refine eventually_trans _ _ _ _ (head_fast k hk hf _ ra guard fp s1 s2 s3 hfp h1 h2 h3 _
    (by dsimp only; ecancel) hguard hcap hcap63) ?_
  rintro ⟨d, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, hrax1, hrbx1, hrcx1, hrdx1, Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 hrax1 hrbx1 hrcx1 hrdx1 Hm1
  subst hpc1
  refine eventually_mono (tail_fit k hk hf rsp r14 rbp ra rcx rdi rax.toBitVec rbx.toBitVec p e8 root pre d0 d1
    l16 l24 l32 t40 t30 rslot scratch he8 hroot hpre hd0 hd1 hl16 hl24 hl32 ht40 ht30 hrs S hsc _ d hrsp1 hrbp1
    hr141 (by rw [hrax1]) (by rw [hrbx1]) hrcx1 hrdx1 (by ecancel) hcap hmm) ?_
  rintro st ⟨e1, e2, e3, e4, e5, e6, e7, e8', e9, t, u, scr, ht, hu, hscr, Hm⟩
  exact ⟨e1, UInt64.toBitVec_inj.mp e2, e3, e4, e5, e6, e7, e8', e9, t, u, scr, ht, hu, hscr, by ecancel⟩

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem cpo_marshal_reject_main (k : Nat) (hk : CpMarshalO.IsInfixAt Host.prog k) (hf : LabelsFresh CpMarshalO k)
    (cst e8 cC ctl pre d0 : List UInt8) (hcst : cst.length = 8) (he8 : e8.length = 8) (hcC : cC.length = 8)
    (hctl : ctl.length = 32) (hd0 : d0.length = 8)
    (p : BitVec 64) (rl e0 e1 : UInt64) (hrl : rl ≠ 32) (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s3 t40 t30 : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h3 : s3.length = 8)
    (ht40 : t40.length = 16) (ht30 : t30.length = 16) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s3.At (s.regs.rsp.toBitVec + 24))
      ⋆ Eq (t30.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq (e8.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 rl.toBitVec.toInt).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (ctl.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At E2e.Data.e2eErrBytesLength_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrBytesLength" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat + 24 < s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 40 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rcx = 0 ∧ st.data.regs.rdi = e0 ∧ st.data.regs.rsi = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (t u : List UInt8), t.length = 8 ∧ u.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rcx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 24))
          ⋆ Eq (u.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (e8.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (t.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq (e8.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 rl.toBitVec.toInt).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (ctl.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (e8.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At E2e.Data.e2eErrBytesLength_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrBytesLength" + 8).toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hcap hcap63 ⊢
  refine eventually_trans _ _ _ _ (head_fast k hk hf _ ra guard fp s1 s2 s3 hfp h1 h2 h3 _
    (by dsimp only; ecancel) hguard hcap hcap63) ?_
  rintro ⟨d, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, hrax1, hrbx1, hrcx1, hrdx1, Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 hrax1 hrbx1 hrcx1 hrdx1 Hm1
  subst hpc1
  refine eventually_mono (tail_rej k hk hf rsp r14 rbp ra rcx rdi e0 e1 rl hrl rax.toBitVec rbx.toBitVec p
    e8 pre d0 t40 t30 he8 hd0 ht40 ht30 _ d hrsp1 hrbp1 hr141 (by rw [hrax1]) (by rw [hrbx1]) hrcx1 hrdx1
    (by ecancel) (by omega)) ?_
  rintro st ⟨e1', e2, e3, e4, e5, e6, e7, e8', e9, t, u, ht, hu, Hm⟩
  exact ⟨e1', e2, e3, e4, e5, e6, e7, e8', e9, t, u, ht, hu, by ecancel⟩

end E2e.OptR1
