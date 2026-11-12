import E2eScal.BhEncHead
import E2eScal.BhEncRoots

/-!
# Real Prysm `(*v1alpha1.BeaconBlockHeader).MarshalSSZTo`, fast path, Go 1.26.10 machine code (hold-out)

Hand proof by composition of the segments of `E2eScal.BhEncHead` (`bh_enc_a1`, `bh_enc_a2`) and
`E2eScal.BhEncRoots` (`bh_enc_b`, `bh_enc_c`, `bh_enc_d`, `bh_enc_e`). Statement shape of
`E2e.cp_e2e_marshal_main`. **Fast path only**: `len(dst) + 112 ≤ cap(dst)` and all three roots of length 32.
The `runtime.growslice` branches and the three length rejects are not covered by this theorem.

Receiver (gc amd64 layout, `prysm/ir/ir-mainnet.json`): `state` 0 (`ast`), `Slot` 8, `ProposerIndex` 16,
`ParentRoot` 24 (ptr, len, cap), `StateRoot` 48, `BodyRoot` 72. The capacity words `c1 c2 c3` are not read.

Stack (rsp = s.regs.rsp at entry): return slot; saved rbp at rsp − 8; argument spills at rsp + 8 (receiver)
and rsp + 16 (slice pointer); frame rsp − 160 … rsp − 9: slice pointer rsp − 16, the Slot temp rsp − 56 …
rsp − 25, the ProposerIndex temp rsp − 88 … rsp − 57, capacity rsp − 96, length rsp − 104; the rest of the
frame is not touched on this path (in `R`); `memmove` return slot rsp − 168 and `S` bytes below it.
The stack guard is the large-frame form (`lea -0x20(%rsp),%r12`): premise `guard + 32 < rsp`.
-/

open Fk E2eScal.BhCode
variable [Host]

namespace E2eScal.Bh

theorem bhm_o16 (x y : BitVec 64) : x + y + 16 = x + (y + 8 + 8) := by bv_omega
theorem bhm_o48 (x y : BitVec 64) : x + y + 48 = x + (y + 8 + 8 + 32) := by bv_omega
theorem bhm_o80 (x y : BitVec 64) : x + y + 80 = x + (y + 8 + 8 + 32 + 32) := by bv_omega
theorem bhm_v112 (y : BitVec 64) : y + 112 = y + 8 + 8 + 32 + 32 + 32 := by bv_omega

theorem bhm_cap (a b : BitVec 64) (h : a.toNat + 112 ≤ b.toNat) (h63 : b.toNat < 2 ^ 63) :
    (a + 8 + 8).toNat + 32 ≤ b.toNat ∧ (a + 8 + 8 + 32).toNat + 32 ≤ b.toNat
      ∧ (a + 8 + 8 + 32 + 32).toNat + 32 ≤ b.toNat := by
  refine ⟨?_, ?_, ?_⟩ <;> bv_omega

theorem bhm_len112 (x : UInt64) (h : x.toNat + 112 < 2 ^ 64) :
    ({ toBitVec := x.toBitVec + 8 + 8 + 32 + 32 + 32 } : UInt64).toNat = x.toNat + 112 := by
  have h' : x.toBitVec.toNat + 112 < 2 ^ 64 := h
  show (x.toBitVec + 8 + 8 + 32 + 32 + 32).toNat = x.toBitVec.toNat + 112
  bv_omega

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Fast path of the real `(*v1alpha1.BeaconBlockHeader).MarshalSSZTo` (Go 1.26.10)**: with
`len(dst) + 112 ≤ cap(dst)` and three roots of length 32 it returns `(dst, len + 112, cap, nil)` and the
112 bytes after the prefix are Slot ‖ ProposerIndex ‖ ParentRoot ‖ StateRoot ‖ BodyRoot; the receiver, the
roots, the prefix, the caller's frame `R` and the stack guard are unchanged. Fast path only. -/
theorem bh_e2e_marshal_main (k : Nat) (hk : BhMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh BhMarshal k)
    (ast sl pi c1 c2 c3 r1 r2 r3 pre d0 d1 d2 d3 d4 : List UInt8)
    (hast : ast.length = 8) (hsl : sl.length = 8) (hpi : pi.length = 8)
    (hc1 : c1.length = 8) (hc2 : c2.length = 8) (hc3 : c3.length = 8)
    (hr1 : r1.length = 32) (hr2 : r2.length = 32) (hr3 : r3.length = 32)
    (hd0 : d0.length = 8) (hd1 : d1.length = 8) (hd2 : d2.length = 32) (hd3 : d3.length = 32) (hd4 : d4.length = 32)
    (p1 p2 p3 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l96 l104 t1a t1b t2a t2b rslot : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (hl16 : l16.length = 8)
    (hl96 : l96.length = 8) (hl104 : l104.length = 8)
    (ht1a : t1a.length = 16) (ht1b : t1b.length = 16) (ht2a : t2a.length = 16) (ht2b : t2b.length = 16)
    (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16)) ⋆ Eq (l96.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (l104.At (s.regs.rsp.toBitVec - 104))
      ⋆ Eq (t1a.At (s.regs.rsp.toBitVec - 56)) ⋆ Eq (t1b.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (t2a.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (t2b.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 168)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 168 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (sl.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (pi.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32)) ⋆ Eq (c1.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 48))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 56)) ⋆ Eq (c2.At (s.regs.rax.toBitVec + 64))
      ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 72))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 80)) ⋆ Eq (c3.At (s.regs.rax.toBitVec + 88))
      ⋆ Eq (r1.At p1) ⋆ Eq (r2.At p2) ⋆ Eq (r3.At p3)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
      ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
      ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80)) ⋆ R)
    (hguard : guard.toNat + 32 < s.regs.rsp.toNat) (hsp : 168 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 112 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hmm : MemmoveC S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 112 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (t1 u1 t2 u2 scr : List UInt8), t1.length = 8 ∧ u1.length = 16 ∧ t2.length = 8 ∧ u2.length = 16
          ∧ scr.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 112).toInt).At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (sl.At (s.regs.rsp.toBitVec - 56)) ⋆ Eq (t1.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (u1.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (pi.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (t2.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (u2.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 148)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 168))
          ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 168 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (sl.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (pi.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32)) ⋆ Eq (c1.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 56)) ⋆ Eq (c2.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 80)) ⋆ Eq (c3.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (r1.At p1) ⋆ Eq (r2.At p2) ⋆ Eq (r3.At p3)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (sl.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (pi.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (r1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
          ⋆ Eq (r2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (r3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  have hC := s.regs.rdi.toNat_lt_size
  simp only [UInt64.size] at hC
  obtain ⟨hcB, hcC, hcD⟩ := bhm_cap s.regs.rcx.toBitVec s.regs.rdi.toBitVec hcap hcap63
  have hc63 : s.regs.rdi.toBitVec.toNat < 2 ^ 63 := hcap63
  rw [bhm_o16 s.regs.rbx.toBitVec s.regs.rcx.toBitVec, bhm_o48 s.regs.rbx.toBitVec s.regs.rcx.toBitVec,
    bhm_o80 s.regs.rbx.toBitVec s.regs.rcx.toBitVec] at h_mem
  -- Slot segment, directives 0–35
  refine eventually_trans _ _ _ _ (bh_enc_a1 k hk hf sl d0 hsl hd0 s guard fp s1 s2 t1a t1b hfp h1 h2 ht1a ht1b _
    (by ecancel) hguard hsp hcap hcap63) ?_
  rintro ⟨e1, pc1⟩ ⟨hpc1, hrax1, hrbx1, hrcx1, hrdx1, hrdi1, hrsp1, hrbp1, hr141, t1, u1, ht1, hu1, Hm1⟩
  dsimp only at hpc1 hrax1 hrbx1 hrcx1 hrdx1 hrdi1 hrsp1 hrbp1 hr141 Hm1
  subst hpc1
  -- ProposerIndex segment, directives 36–61
  refine eventually_trans _ _ _ _ (bh_enc_a2 k hk hf pi d1 hpi hd1 e1 s.regs.rsp t2a t2b ht2a ht2b _
    hrsp1 (by rw [hrdx1, hrcx1]) (by rw [hrax1, hrbx1, hrcx1]; ecancel)
    (by rw [hrcx1, hrdi1]; exact hcap) (by rw [hrdi1]; exact hcap63)) ?_
  rintro ⟨e2, pc2⟩ ⟨hpc2, hrax2, hrbx2, hr82, hrdi2, hrsp2, hrbp2, hr142, t2, u2, ht2, hu2, Hm2⟩
  dsimp only at hpc2 hrax2 hrbx2 hr82 hrdi2 hrsp2 hrbp2 hr142 Hm2
  subst hpc2
  rw [hrax1, hrbx1, hrcx1] at Hm2
  have hr8' : e2.regs.r8 = { toBitVec := s.regs.rcx.toBitVec + 8 + 8 } := by
    apply UInt64.toBitVec_inj.mp; rw [hr82, hrcx1]
  -- ParentRoot segment, directives 62–89, memmove
  refine eventually_trans _ _ _ _ (bh_enc_b k hk hf r1 d2 hr1 hd2 e2 s.regs.rsp s.regs.rax.toBitVec
    s.regs.rbx.toBitVec (s.regs.rcx.toBitVec + 8 + 8) s.regs.rdi.toBitVec p1 l16 l96 l104 rslot scratch
    hl16 hl96 hl104 hrs S hsc _ (hrsp2.trans hrsp1) (hrax2.trans hrax1) (hrbx2.trans hrbx1) hr8'
    (hrdi2.trans hrdi1) (by ecancel) hcB hc63 hmm) ?_
  rintro ⟨e3, pc3⟩ ⟨hpc3, hrsp3, hrbp3, hr143, scr1, hscr1, Hm3⟩
  dsimp only at hpc3 hrsp3 hrbp3 hr143 Hm3
  subst hpc3
  -- StateRoot segment, directives 90–117, memmove
  refine eventually_trans _ _ _ _ (bh_enc_c k hk hf r2 d3 hr2 hd3 e3 s.regs.rsp s.regs.rax.toBitVec
    s.regs.rbx.toBitVec (s.regs.rcx.toBitVec + 8 + 8 + 32) s.regs.rdi.toBitVec p2
    (Int.toBytes 8 (Host.addrOf (k + 90)).toBitVec.toInt) scr1 (Int.toBytes_length 8 _) S hscr1 _
    (hrsp3.trans (hrsp2.trans hrsp1)) (by ecancel) hcC hc63 hmm) ?_
  rintro ⟨e4, pc4⟩ ⟨hpc4, hrsp4, hrbp4, hr144, scr2, hscr2, Hm4⟩
  dsimp only at hpc4 hrsp4 hrbp4 hr144 Hm4
  subst hpc4
  -- BodyRoot segment, directives 118–147, memmove
  refine eventually_trans _ _ _ _ (bh_enc_d k hk hf r3 d4 hr3 hd4 e4 s.regs.rsp s.regs.rax.toBitVec
    s.regs.rbx.toBitVec (s.regs.rcx.toBitVec + 8 + 8 + 32 + 32) s.regs.rdi.toBitVec p3
    (Int.toBytes 8 (Host.addrOf (k + 118)).toBitVec.toInt) scr2 (Int.toBytes_length 8 _) S hscr2 _
    (hrsp4.trans (hrsp3.trans (hrsp2.trans hrsp1))) (by ecancel) hcD hc63 hmm) ?_
  rintro ⟨e5, pc5⟩ ⟨hpc5, hrsp5, hrbp5, hr145, scr3, hscr3, Hm5⟩
  dsimp only at hpc5 hrsp5 hrbp5 hr145 Hm5
  subst hpc5
  -- Return segment, directives 148–155
  refine eventually_trans _ _ _ _ (bh_enc_e k hk e5 s.regs.rsp ra s.regs.rbp s.regs.rbx.toBitVec
    (s.regs.rcx.toBitVec + 8 + 8 + 32 + 32 + 32) s.regs.rdi.toBitVec _
    (hrsp5.trans (hrsp4.trans (hrsp3.trans (hrsp2.trans hrsp1)))) (by ecancel)) ?_
  rintro ⟨e6, pc6⟩ ⟨hpc6, hrax6, hrbx6, hrcx6, hrdi6, hrsi6, hrsp6, hrbp6, hr146, Hm6⟩
  dsimp only at hpc6 hrax6 hrbx6 hrcx6 hrdi6 hrsi6 hrsp6 hrbp6 hr146 Hm6
  apply Eventually.done
  refine ⟨hpc6, hrax6, ?grbx, hrcx6, hrdi6, hrsi6, hrsp6, hrbp6, ?gr14, t1, u1, t2, u2, scr3, ht1, hu1, ht2, hu2,
    hscr3, ?hmem⟩
  case grbx => exact (congrArg UInt64.toNat hrbx6).trans (bhm_len112 s.regs.rcx (by omega))
  case gr14 => exact hr146.trans (hr145.trans (hr144.trans (hr143.trans (hr142.trans hr141))))
  case hmem =>
    rw [bhm_o16 s.regs.rbx.toBitVec s.regs.rcx.toBitVec, bhm_o48 s.regs.rbx.toBitVec s.regs.rcx.toBitVec,
      bhm_o80 s.regs.rbx.toBitVec s.regs.rcx.toBitVec, bhm_v112 s.regs.rcx.toBitVec]
    first | ecancel | (simp only [Std.ExtHashMap.sep_emp] at Hm6; ecancel)

end E2eScal.Bh
