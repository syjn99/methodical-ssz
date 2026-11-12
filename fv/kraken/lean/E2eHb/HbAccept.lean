import E2eHb.HbLoop2
import E2eHb.StmtHb

/-!
# `(*v1alpha1.HistoricalBatch).UnmarshalSSZ`, accept path, Go 1.26.10 machine code

* head 0–29 (hand steps): guard, prologue (`sub $0x38`), size check, spills, `makeslice` of the BlockRoots backing
  array (`MakesliceC Heap lvSliceType_addr 24 S`, cnt 8192), len = cap = 8192, writeBarrier = 0, ptr, rax = 0,
  `jmp L_a0`;
* BlockRoots loop 40–84, 36–39: `hb_loop1`;
* middle 86–103 (hand steps): `makeslice` of the StateRoots backing array, len = cap = 8192, writeBarrier = 0, ptr,
  rax = 0, `jmp L_1c0`;
* StateRoots loop 108–153, 104–107: `hb_loop2`;
* epilogue 155–159 (hand steps, `add $0x38`).
Proof text: `Prysm.SyncCommittee.Decode.accept` (`ScAccept.lean`): its head and epilogue steps with the frame size and the
receiver offsets changed; the middle is a second copy of the head steps; there is no tail field segment.
Statement: the frozen `E2eHb.hb_accept_stmt`.
-/

open Machine Runtime TestTarget E2eHb.Code
variable [Host]

namespace E2eHb

/-- **Accept path of the real `(*v1alpha1.HistoricalBatch).UnmarshalSSZ` (Go 1.26.10)**; statement = the frozen
`hb_accept_stmt`. -/
theorem hb_e2e_accept_main : hb_accept_stmt := by
  intro k hk hf brs srs hbrs hbr hsrs hsr s ra guard
    fp s1 s2 l18 l20 l28 l30 spl rslot lo aP1 aL1 aC1 aP2 aL2 aC2
    hfp h1 h2 hl18 hl20 hl28 hl30 hspl hrs haP1 haL1 haC1 haP2 haL2 haC2
    R S hlo Heap avail h_mem hguard hlen hav hms hmsA hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  subst hlen
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; simp only [UInt64.size] at *
  kat hk HbUnmarshal 0
  kat hk HbUnmarshal 1
  kat hk HbUnmarshal 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk HbUnmarshal 3
  split
  · rename_i h; exfalso
    simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk HbUnmarshal 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk HbUnmarshal 5
  kat hk HbUnmarshal 6
  kat hk HbUnmarshal 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by bv_omega) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk HbUnmarshal 8
  kat hk HbUnmarshal 9
  kat hk HbUnmarshal 10
  split
  case isTrue h => exact absurd h (by decide)
  simp only [Effects.All]
  kat hk HbUnmarshal 11
  apply store_step_at _ _ (rsp.toBitVec + 8) _ _ _ s1 _ _ (by bv_omega) (by ecancel) (by exact h1)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk HbUnmarshal 12
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by bv_omega) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  kat hk HbUnmarshal 13
  kat hk HbUnmarshal 14
  kat hk HbUnmarshal 15
  kat hk HbUnmarshal 16
  apply store_step_at _ _ (rsp.toBitVec - 72) _ _ _ rslot _ _ (by laddr) (by ecancel) (by exact hrs)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  rw [show rsp.toBitVec - 8#64 - 56 - 8#64 = rsp.toBitVec - 72 by bv_omega]
  refine eventually_trans _ _ _ _ (hmsA _ (Host.addrOf (k + 16 + 1)) 8192 avail lo spl _
    rfl (Nat.le_refl _) (by rfl) (by omega) (by unfold maxAlloc; omega) (by omega) hlo hspl
    (by dsimp only; rw [show rsp.toBitVec - 72 + 8 = rsp.toBitVec - 64 by bv_omega]; ecancel)) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrsp3, hr143, hrbp3, stk3, spm3, hstk3, hspm3, Hm3⟩
  dsimp only at hpc3 hrsp3 hr143 hrbp3 Hm3
  subst hpc3
  obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,
    zmms3, flags3, mem3⟩ := d3
  simp only at hrsp3 hr143 hrbp3 Hm3
  rw [show ({ toBitVec := rsp.toBitVec - 72 } + 8 : UInt64) = { toBitVec := rsp.toBitVec - 64 } by
    apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega] at hrsp3
  subst hrsp3 hr143 hrbp3
  rw [show rsp.toBitVec - 72 + 8 = rsp.toBitVec - 64 by bv_omega] at Hm3
  -- 17 load recv; 18–19 BlockRoots len = cap = 8192; 20–21 writeBarrier; 26–27 ptr; 28 rax = 0; 29 jmp L_a0
  kat hk HbUnmarshal 17
  apply load_step_at _ _ (rsp.toBitVec + 8) _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by kaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk HbUnmarshal 18
  apply store_step_at _ _ (rax.toBitVec + 8) _ _ _ aL1 _ _ (by kaddr) (by ecancel) (by exact haL1)
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  kat hk HbUnmarshal 19
  apply store_step_at _ _ (rax.toBitVec + 16) _ _ _ aC1 _ _ (by kaddr) (by ecancel) (by exact haC1)
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  kat hk HbUnmarshal 20
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk HbUnmarshal 21
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf HbUnmarshal 26
  kat hk HbUnmarshal 26
  kat hk HbUnmarshal 27
  apply store_step_at _ _ rax.toBitVec _ _ _ aP1 _ _ (by kaddr) (by ecancel) (by exact haP1)
  intro m8 H8
  simp only [Width.bytes, Width.bits] at H8
  kunfold
  kat hk HbUnmarshal 28
  intro _
  kat hk HbUnmarshal 29
  klabel hk hf HbUnmarshal 40
  have e8192 : Int.toBytes 8 (BitVec.toInt (8192 : BitVec 64)) = Int.toBytes 8 8192 := by decide
  simp only [e8192] at H8
  -- BlockRoots loop: L_a0 (40) → directive 86
  refine eventually_trans _ _ _ _ (hb_loop1 k hk hf (rsp.toBitVec - 64) rax.toBitVec rbx.toBitVec rax3.toBitVec brs
    hbrs hbr _ _ S Heap _ hms hmm 8192 0 [] l18 l20 l28 l30 spm3
    (Int.toBytes 8 (Host.addrOf (k + 16 + 1)).toBitVec.toInt) stk3 (avail - 24 * 8192) _ (by omega) rfl hl18 hl20
    hl28 hl30 hspm3 (Int.toBytes_length 8 _) hstk3 (by omega) (by simp) rfl rfl rfl
    (by
      dsimp only
      rw [show rsp.toBitVec - 64 + 72 = rsp.toBitVec + 8 by laddr, show rsp.toBitVec - 64 + 80 = rsp.toBitVec + 16 by laddr,
        show rsp.toBitVec - 64 + 24 = rsp.toBitVec - 40 by laddr, show rsp.toBitVec - 64 + 32 = rsp.toBitVec - 32 by laddr,
        show rsp.toBitVec - 64 + 40 = rsp.toBitVec - 24 by laddr, show rsp.toBitVec - 64 + 48 = rsp.toBitVec - 16 by laddr,
        show rsp.toBitVec - 64 - 8 = rsp.toBitVec - 72 by laddr]
      simp only [show Prysm.SyncCommittee.sliceHeaders 32 [] ++ Prysm.SyncCommittee.zz (24 * (8192 - 0)) = List.replicate (24 * 8192) 0 from rfl, List.take_zero,
        show Prysm.SyncCommittee.elementBlocks [] ([] : List (List UInt8)) = Std.ExtHashMap.emp from rfl, Std.ExtHashMap.sep_emp]
      ecancel)) ?_
  rintro ⟨d4, pc4⟩ ⟨hpc4, hrsp4, hrbp4, hr144, ps1, l18', l20', l28', l30', spl', rslot', lo', hps1, g18, g20, g28,
    g30, gspl, grs, glo, Hm4⟩
  dsimp only at hpc4 hrsp4 hrbp4 hr144 Hm4
  subst hpc4
  obtain ⟨⟨rax4, rbx4, rcx4, rdx4, rsi4, rdi4, rsp4, rbp4, r84, r94, r104, r114, r124, r134, r144', r154⟩,
    zmms4, flags4, mem4⟩ := d4
  simp only at hrsp4 hrbp4 hr144 Hm4
  subst hrsp4 hrbp4 hr144
  -- 86–89 makeslice of the StateRoots backing array
  kat hk HbUnmarshal 86
  kat hk HbUnmarshal 87
  kat hk HbUnmarshal 88
  kat hk HbUnmarshal 89
  apply store_step_at _ _ (rsp.toBitVec - 64 - 8) _ _ _ rslot' _ _ (by laddr) (by ecancel) (by exact grs)
  intro m9 H9
  simp only [Width.bytes, Width.bits] at H9
  kunfold
  try rw [show rsp.toBitVec - 64 - 8#64 = rsp.toBitVec - 64 - 8 from rfl] at *
  refine eventually_trans _ _ _ _ (hmsA _ (Host.addrOf (k + 89 + 1)) 8192 (avail - 24 * 8192 - 32 * 8192) lo' spl' _
    rfl (Nat.le_refl _) (by rfl) (by omega) (by unfold maxAlloc; omega) (by omega) glo gspl
    (by dsimp only; rw [show rsp.toBitVec - 64 - 8 + 8 = rsp.toBitVec - 64 by bv_omega]; ecancel)) ?_
  rintro ⟨d5, pc5⟩ ⟨hpc5, hrsp5, hr145, hrbp5, stk5, spm5, hstk5, hspm5, Hm5⟩
  dsimp only at hpc5 hrsp5 hr145 hrbp5 Hm5
  subst hpc5
  obtain ⟨⟨rax5, rbx5, rcx5, rdx5, rsi5, rdi5, rsp5, rbp5, r85, r95, r105, r115, r125, r135, r145', r155⟩,
    zmms5, flags5, mem5⟩ := d5
  simp only at hrsp5 hr145 hrbp5 Hm5
  rw [show ({ toBitVec := rsp.toBitVec - 64 - 8 } + 8 : UInt64) = { toBitVec := rsp.toBitVec - 64 } by
    apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega] at hrsp5
  subst hrsp5 hr145 hrbp5
  rw [show rsp.toBitVec - 64 - 8 + 8 = rsp.toBitVec - 64 by bv_omega] at Hm5
  -- 90 load recv; 91–92 StateRoots len = cap = 8192; 93–94 writeBarrier; 100–101 ptr; 102 rax = 0; 103 jmp L_1c0
  kat hk HbUnmarshal 90
  apply load_step_at _ _ (rsp.toBitVec - 64 + 72) _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by kaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk HbUnmarshal 91
  apply store_step_at _ _ (rax.toBitVec + 32) _ _ _ aL2 _ _ (by kaddr) (by ecancel) (by exact haL2)
  intro m10 H10
  simp only [Width.bytes, Width.bits] at H10
  kunfold
  kat hk HbUnmarshal 92
  apply store_step_at _ _ (rax.toBitVec + 40) _ _ _ aC2 _ _ (by kaddr) (by ecancel) (by exact haC2)
  intro m11 H11
  simp only [Width.bytes, Width.bits] at H11
  kunfold
  kat hk HbUnmarshal 93
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk HbUnmarshal 94
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf HbUnmarshal 100
  kat hk HbUnmarshal 100
  kat hk HbUnmarshal 101
  apply store_step_at _ _ (rax.toBitVec + 24) _ _ _ aP2 _ _ (by kaddr) (by ecancel) (by exact haP2)
  intro m12 H12
  simp only [Width.bytes, Width.bits] at H12
  kunfold
  kat hk HbUnmarshal 102
  intro _
  kat hk HbUnmarshal 103
  klabel hk hf HbUnmarshal 108
  simp only [e8192] at H12
  -- StateRoots loop: L_1c0 (108) → directive 155
  refine eventually_trans _ _ _ _ (hb_loop2 k hk hf (rsp.toBitVec - 64) rax.toBitVec rbx.toBitVec rax5.toBitVec srs
    hsrs hsr _ _ S Heap _ hms hmm 8192 0 [] l18' l20' l28' l30' spm5
    (Int.toBytes 8 (Host.addrOf (k + 89 + 1)).toBitVec.toInt) stk5 (avail - 24 * 8192 - 32 * 8192 - 24 * 8192) _
    (by omega) rfl g18 g20 g28 g30 hspm5 (Int.toBytes_length 8 _) hstk5 (by omega) (Or.inl (by decide)) (by simp)
    rfl rfl rfl
    (by
      dsimp only
      simp only [show Prysm.SyncCommittee.sliceHeaders 32 [] ++ Prysm.SyncCommittee.zz (24 * (8192 - 0)) = List.replicate (24 * 8192) 0 from rfl, List.take_zero,
        show Prysm.SyncCommittee.elementBlocks [] ([] : List (List UInt8)) = Std.ExtHashMap.emp from rfl, Std.ExtHashMap.sep_emp]
      ecancel)) ?_
  rintro ⟨d6, pc6⟩ ⟨hpc6, hrsp6, hrbp6, hr146, ps2, m18, m20, m28, m30, mspl, mlo, hps2, q18, q20, q28, q30, qspl,
    qlo, Hm6⟩
  dsimp only at hpc6 hrsp6 hrbp6 hr146 Hm6
  subst hpc6
  obtain ⟨⟨rax6, rbx6, rcx6, rdx6, rsi6, rdi6, rsp6, rbp6, r86, r96, r106, r116, r126, r136, r146', r156⟩,
    zmms6, flags6, mem6⟩ := d6
  simp only at hrsp6 hrbp6 hr146 Hm6
  subst hrsp6 hrbp6 hr146
  -- epilogue 155–159
  kat hk HbUnmarshal 155
  intro _
  kat hk HbUnmarshal 156
  intro _
  kat hk HbUnmarshal 157
  kat hk HbUnmarshal 158
  apply load_step_at _ _ (rsp.toBitVec - 8) _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by laddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk HbUnmarshal 159
  apply load_step_at _ _ rsp.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by laddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  rw [show rsp.toBitVec - 64 + 72 = rsp.toBitVec + 8 by laddr, show rsp.toBitVec - 64 + 80 = rsp.toBitVec + 16 by laddr,
    show rsp.toBitVec - 64 + 24 = rsp.toBitVec - 40 by laddr, show rsp.toBitVec - 64 + 32 = rsp.toBitVec - 32 by laddr,
    show rsp.toBitVec - 64 + 40 = rsp.toBitVec - 24 by laddr, show rsp.toBitVec - 64 + 48 = rsp.toBitVec - 16 by laddr,
    show rsp.toBitVec - 64 - 8 = rsp.toBitVec - 72 by laddr,
    show avail - 24 * 8192 - 32 * 8192 - 24 * 8192 - 32 * 8192 = avail - 917504 by omega,
    show Prysm.SyncCommittee.zz (24 * (8192 - 8192)) = [] from rfl, List.append_nil, List.append_nil,
    List.take_of_length_le (by omega : brs.length ≤ 8192), List.take_of_length_le (by omega : srs.length ≤ 8192)]
    at Hm6
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rax3.toBitVec, rax5.toBitVec, ps1, ps2, m18, m20, m28, m30, mspl, mlo, hps1, hps2,
    q18, q20, q28, q30, qspl, qlo, ?_⟩
  rotate_right
  · ecancel
  all_goals first
    | exact trivial
    | with_reducible rfl
    | (apply UInt64.toBitVec_inj.mp
       simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, Width.bits]
       done)
    | (apply UInt64.toBitVec_inj.mp; laddr)
    | (apply UInt64.toBitVec_inj.mp; simp)

end E2eHb
