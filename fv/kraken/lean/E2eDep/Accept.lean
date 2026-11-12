import E2eSeg.V32Hb
import E2eSeg.RejGInst
import E2eScal.DdAccept
import E2eDep.Stmt

/-!
# Deposit accept path (Go 1.26.10 machine code), proved with the E2eSeg general lemmas

* head 0–30 (hand steps; the text of `E2eHb.hb_e2e_accept_main` 0–29 with this frame);
* Proof loop 40–76, 37–39: `E2eSeg.v32_loop` (n = 33), block and gap facts read from the program;
* 84–105 (hand steps): exit label, `new(Deposit_Data)` (`NewobjectC`), the Data pointer, the arguments
  buf[1056:1240], the call;
* the Deposit_Data decoder: `E2eScal.H4.dd_e2e_accept_main` (machine code in the host, our scratch as its frame);
* 106–107 `test; je` taken (err = nil), epilogue 135–138.
Statement: the frozen `E2eDep.dep_accept_stmt`.
-/

open Fk E2eList E2eHb E2eSeg E2eDep.Code

namespace E2eDep

variable [Host]

theorem split_at (l : List UInt8) (n : Nat) (h : n ≤ l.length) :
    ∃ a b : List UInt8, a.length = n ∧ b.length = l.length - n ∧ l = a ++ b :=
  ⟨l.take n, l.drop n, by simp; omega, by simp, by simp⟩

/-- Our scratch `lo` (Sd + 48 bytes below the return slot y) as the Deposit_Data decoder's frame:
its scratch (Sd), return slot, 24-byte spill area, slice-pointer save and saved rbp. -/
theorem dep_lo (y : BitVec 64) (Sd : Nat) (hSd : Sd < 2 ^ 60) (a b c d e : List UInt8) (ha : a.length = Sd)
    (hb : b.length = 8) (hc : c.length = 24) (hd : d.length = 8) (he : e.length = 8) :
    Eq ((a ++ (b ++ (c ++ (d ++ e)))).At (y - BitVec.ofNat 64 (Sd + 48))) = Eq (a.At (y - 48 - BitVec.ofNat 64 Sd))
      ⋆ Eq (b.At (y - 48)) ⋆ Eq (c.At (y - 40)) ⋆ Eq (d.At (y - 16)) ⋆ Eq (e.At (y - 8)) := by
  rw [show y - BitVec.ofNat 64 (Sd + 48) = y - 48 - BitVec.ofNat 64 Sd by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega,
    at_app _ _ (b := y - 48) (by rw [ha]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub, BitVec.toNat_add]; omega)
      (by simp [ha, hb, hc, hd, he]; omega),
    at_app _ _ (b := y - 40) (by rw [hb]; bv_omega) (by simp [hb, hc, hd, he]),
    at_app _ _ (b := y - 16) (by rw [hc]; bv_omega) (by simp [hc, hd, he]),
    at_app _ _ (b := y - 8) (by rw [hd]; bv_omega) (by simp [hd, he])]
  simp only [Std.ExtHashMap.sep_assoc]

/-- The fresh Deposit_Data object as the receiver chunks of `dd_e2e_accept_main`. -/
theorem dep_obj120 (p : BitVec 64) :
    Eq ((List.replicate 120 (0 : UInt8)).At p) = Eq ((List.replicate 8 0).At p) ⋆ Eq ((List.replicate 8 0).At (p + 8))
      ⋆ Eq ((List.replicate 8 0).At (p + 16)) ⋆ Eq ((List.replicate 8 0).At (p + 24))
      ⋆ Eq ((List.replicate 8 0).At (p + 32)) ⋆ Eq ((List.replicate 8 0).At (p + 40))
      ⋆ Eq ((List.replicate 8 0).At (p + 48)) ⋆ Eq ((List.replicate 8 0).At (p + 56))
      ⋆ Eq ((List.replicate 8 0).At (p + 64)) ⋆ Eq ((List.replicate 8 0).At (p + 72))
      ⋆ Eq ((List.replicate 8 0).At (p + 80)) ⋆ Eq ((List.replicate 32 0).At (p + 88)) := by
  rw [show List.replicate 120 (0 : UInt8) = List.replicate 8 0 ++ (List.replicate 8 0 ++ (List.replicate 8 0
    ++ (List.replicate 8 0 ++ (List.replicate 8 0 ++ (List.replicate 8 0 ++ (List.replicate 8 0
    ++ (List.replicate 8 0 ++ (List.replicate 8 0 ++ (List.replicate 8 0 ++ (List.replicate 8 0
    ++ List.replicate 32 0)))))))))) by rfl]
  rw [at_app _ _ (b := p + 8) (by simp) (by simp), at_app _ _ (b := p + 16) (by simp; bv_omega) (by simp),
    at_app _ _ (b := p + 24) (by simp; bv_omega) (by simp), at_app _ _ (b := p + 32) (by simp; bv_omega) (by simp),
    at_app _ _ (b := p + 40) (by simp; bv_omega) (by simp), at_app _ _ (b := p + 48) (by simp; bv_omega) (by simp),
    at_app _ _ (b := p + 56) (by simp; bv_omega) (by simp), at_app _ _ (b := p + 64) (by simp; bv_omega) (by simp),
    at_app _ _ (b := p + 72) (by simp; bv_omega) (by simp), at_app _ _ (b := p + 80) (by simp; bv_omega) (by simp),
    at_app _ _ (b := p + 88) (by simp; bv_omega) (by simp)]
  simp only [Std.ExtHashMap.sep_assoc]

abbrev depL (s : String) : String := "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_" ++ s

-- Threshold measured on this declaration (logs 95–97, one run each): 200000 (default) fails at `whnf`; 400000 and
-- 800000 pass. Value 800000 = twice the lowest passing value. Cause (profiler, log 98): the length of the one
-- declaration (about 100 directive steps, two runtime calls and the Deposit_Data call): tactic execution 3.37 s,
-- `simp` 1.11 s, no single step above 200 ms except the kernel check (1.58 s).
set_option maxHeartbeats 800000 in
theorem dep_e2e_accept_main : dep_accept_stmt := by
  intro k hk hf kd hkd hfd proofs hps hp pk wc amt sig hpk hwc hamt hsig s ra guard
    fp s1 s2 s4 lI1 lD lI lP spl rslot lo ast aP aL aC aD hfp h1 h2 h4 hlI1 hlD hlI hlP hspl hrs hast haP haL haC haD
    R Sd hSd hlo Heap avail h_mem hguard hlen hav hmsA hms hmm hno hmsD hmmD
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  subst hlen
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; simp only [UInt64.size] at *
  kat hk DepUnmarshal 0
  kat hk DepUnmarshal 1
  kat hk DepUnmarshal 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk DepUnmarshal 3
  split
  · rename_i h; exfalso
    simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk DepUnmarshal 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk DepUnmarshal 5
  kat hk DepUnmarshal 6
  kat hk DepUnmarshal 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by bv_omega) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk DepUnmarshal 8
  kat hk DepUnmarshal 9
  kat hk DepUnmarshal 10
  split
  case isTrue h => exact absurd h (by decide)
  simp only [Effects.All]
  kat hk DepUnmarshal 11
  apply store_step_at _ _ (rsp.toBitVec + 8) _ _ _ s1 _ _ (by bv_omega) (by ecancel) (by exact h1)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk DepUnmarshal 12
  apply store_step_at _ _ (rsp.toBitVec + 32) _ _ _ s4 _ _ (by bv_omega) (by ecancel) (by exact h4)
  intro m3' H3'
  simp only [Width.bytes, Width.bits] at H3'
  kunfold
  kat hk DepUnmarshal 13
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by bv_omega) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  kat hk DepUnmarshal 14
  kat hk DepUnmarshal 15
  kat hk DepUnmarshal 16
  kat hk DepUnmarshal 17
  apply store_step_at _ _ (rsp.toBitVec - 104) _ _ _ rslot _ _ (by laddr) (by ecancel) (by exact hrs)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  rw [show rsp.toBitVec - 8#64 - 88 - 8#64 = rsp.toBitVec - 104 by bv_omega]
  refine eventually_trans _ _ _ _ (hmsA _ (Host.addrOf (k + 17 + 1)) 33 avail lo spl _
    rfl (Nat.le_refl _) (by rfl) (by omega) (by unfold maxAlloc; omega) (by omega) hlo hspl
    (by dsimp only; rw [show rsp.toBitVec - 104 + 8 = rsp.toBitVec - 96 by bv_omega]; ecancel)) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrsp3, hr143, hrbp3, stk3, spm3, hstk3, hspm3, Hm3⟩
  dsimp only at hpc3 hrsp3 hr143 hrbp3 Hm3
  subst hpc3
  obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,
    zmms3, flags3, mem3⟩ := d3
  simp only at hrsp3 hr143 hrbp3 Hm3
  rw [show ({ toBitVec := rsp.toBitVec - 104 } + 8 : UInt64) = { toBitVec := rsp.toBitVec - 96 } by
    apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega] at hrsp3
  subst hrsp3 hr143 hrbp3
  rw [show rsp.toBitVec - 104 + 8 = rsp.toBitVec - 96 by bv_omega] at Hm3
  -- 18 load recv; 19–20 Proof len = cap = 33; 21–22 writeBarrier; 27–28 Proof ptr; 29 rax = 0; 30 jmp L_a2
  kat hk DepUnmarshal 18
  apply load_step_at _ _ (rsp.toBitVec + 8) _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by kaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk DepUnmarshal 19
  apply store_step_at _ _ (rax.toBitVec + 16) _ _ _ aL _ _ (by kaddr) (by ecancel) (by exact haL)
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  kat hk DepUnmarshal 20
  apply store_step_at _ _ (rax.toBitVec + 24) _ _ _ aC _ _ (by kaddr) (by ecancel) (by exact haC)
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  kat hk DepUnmarshal 21
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk DepUnmarshal 22
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf DepUnmarshal 27
  kat hk DepUnmarshal 27
  kat hk DepUnmarshal 28
  apply store_step_at _ _ (rax.toBitVec + 8) _ _ _ aP _ _ (by kaddr) (by ecancel) (by exact haP)
  intro m8 H8
  simp only [Width.bytes, Width.bits] at H8
  kunfold
  kat hk DepUnmarshal 29
  intro _
  kat hk DepUnmarshal 30
  klabel hk hf DepUnmarshal 40
  have e33 : Int.toBytes 8 (BitVec.toInt (33 : BitVec 64)) = Int.toBytes 8 (BitVec.ofNat 64 33).toInt := rfl
  simp only [e33] at H8
  -- the Proof loop: L_a2 (40) → exit label L_166 (84), by the general loop
  have hB1 : (v32Head (OfNat.ofNat 33) (depL "a2") (depL "166")).IsInfixAt Host.prog (k + 40) :=
    E2eScal.infix_sub 40 hk (by simp only [DepUnmarshal, v32Head, depL, List.drop_succ_cons, List.drop_zero,
      List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero] <;> first | rfl | decide)
  have hB2 : (v32Mid (depL "23f") 56 48 40 64 112).IsInfixAt Host.prog (k + 49) :=
    E2eScal.infix_sub 49 hk (by simp only [DepUnmarshal, v32Mid, depL, List.drop_succ_cons, List.drop_zero,
      List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero] <;> first | rfl | decide)
  have hB3 : (v32Mm 104 16 56).IsInfixAt Host.prog (k + 62) :=
    E2eScal.infix_sub 62 hk (by simp only [DepUnmarshal, v32Mm, List.drop_succ_cons, List.drop_zero,
      List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero] <;> first | rfl | decide)
  have hB4 : (v32Hdr (depL "23a") 8).IsInfixAt Host.prog (k + 67) :=
    E2eScal.infix_sub 67 hk (by simp only [DepUnmarshal, v32Hdr, depL, List.drop_succ_cons, List.drop_zero,
      List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero] <;> first | rfl | decide)
  have hB5 : (v32Tail (depL "14c") (depL "99") 64).IsInfixAt Host.prog (k + 74) :=
    E2eScal.infix_sub 74 hk (by simp only [DepUnmarshal, v32Tail, depL, List.drop_succ_cons, List.drop_zero,
      List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero] <;> first | rfl | decide)
  have hB6 : (v32Back (depL "99") 40).IsInfixAt Host.prog (k + 37) :=
    E2eScal.infix_sub 37 hk (by simp only [DepUnmarshal, v32Back, depL, List.drop_succ_cons, List.drop_zero,
      List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero] <;> first | rfl | decide)
  have g1 : Glue (k + 40 + 8) (k + 49) := glue_of hk (a := 48)
    (by simp only [DepUnmarshal, v32Nop, List.getElem?_cons_succ, List.getElem?_cons_zero])
  have hlb := Fk.label_at' hk hf (j := 37)
    (by simp only [DepUnmarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [DepUnmarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  have hle := Fk.label_at' hk hf (j := 84)
    (by simp only [DepUnmarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [DepUnmarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  refine eventually_trans _ _ _ _ (v32_loop 33 (by decide) (depL "a2") (depL "166") (depL "23f") (depL "23a")
    (depL "14c") (depL "99") 56 48 40 64 112 104 16 8 0 (k + 40) (k + 49) (k + 62) (k + 67) (k + 74) (k + 37)
    (k + 84) hB1 hB2 hB3 hB4 hB5 hB6 g1 (Or.inl ⟨rfl, rfl⟩) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) hlb hle
    (rsp.toBitVec - 96) rax.toBitVec rbx.toBitVec rbx.toBitVec rax3.toBitVec
    (rsp.toBitVec - 40) (rsp.toBitVec - 48) (rsp.toBitVec - 56) (rsp.toBitVec - 32) (rsp.toBitVec + 16)
    (rsp.toBitVec + 8) (rax.toBitVec + 16) (rax.toBitVec + 8)
    (by simp only [Int64.toBitVec_ofNat]; laddr) (by simp only [Int64.toBitVec_ofNat]; laddr)
    (by simp only [Int64.toBitVec_ofNat]; laddr) (by simp only [Int64.toBitVec_ofNat]; laddr)
    (by simp only [Int64.toBitVec_ofNat]; laddr) (by simp only [Int64.toBitVec_ofNat]; laddr)
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat]) (by simp)
    proofs hps hp _ _ (Sd + 48) Heap _ hms hmm
    33 0 [] lI lD lI1 lP spm3 (Int.toBytes 8 (Host.addrOf (k + 17 + 1)).toBitVec.toInt) stk3 (avail - 24 * 33)
    _ (by omega) rfl hlI hlD hlI1 hlP hspm3 (Int.toBytes_length 8 _) hstk3 (by omega) (Or.inl (by decide))
    (by simp) rfl rfl rfl
    (by
      dsimp only
      rw [show rsp.toBitVec - 96 - 8 = rsp.toBitVec - 104 by laddr]
      simp only [show lvHdrs 32 [] ++ zz (24 * (33 - 0)) = List.replicate (24 * 33) 0 from rfl, List.take_zero,
        show lvElems [] ([] : List (List UInt8)) = Std.ExtHashMap.emp from rfl, Std.ExtHashMap.sep_emp]
      ecancel)) ?_
  rintro ⟨d4, pc4⟩ ⟨hpc4, hrsp4, hrbp4, hr144, ps', lI', lD', lI1', lP', spl', lo', hps', g5, g6, g7, g8, gspl,
    glo, Hm4⟩
  dsimp only at hpc4 hrsp4 hrbp4 hr144 Hm4
  subst hpc4
  obtain ⟨⟨rax4, rbx4, rcx4, rdx4, rsi4, rdi4, rsp4, rbp4, r84, r94, r104, r114, r124, r134, r144', r154⟩,
    zmms4, flags4, mem4⟩ := d4
  simp only at hrsp4 hrbp4 hr144 Hm4
  subst hrsp4 hrbp4 hr144
  rw [show rsp.toBitVec - 96 - 8 = rsp.toBitVec - 104 by laddr] at Hm4
  obtain ⟨sa, sb, hsa, hsb, rfl⟩ := split_at spl' 8 (by omega)
  obtain ⟨sb1, sb2, hsb1, hsb2, rfl⟩ := split_at sb 8 (by omega)
  have hsb2' : sb2.length = 8 := by simp only [List.length_append] at gspl; omega
  rw [at_app _ _ (b := rsp.toBitVec - 88) (by rw [hsa]; laddr) (by simp [hsa, hsb1, hsb2']),
    at_app _ _ (b := rsp.toBitVec - 80) (by rw [hsb1]; laddr) (by simp [hsb1, hsb2'])] at Hm4
  -- 84–86: exit label, new(Deposit_Data)
  kat hk DepUnmarshal 84
  kat hk DepUnmarshal 85
  kat hk DepUnmarshal 86
  apply store_step_at _ _ (rsp.toBitVec - 104) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 62 + 1 + 1)).toBitVec.toInt) _ _
    (by laddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m9 H9
  simp only [Width.bytes, Width.bits] at H9
  kunfold
  try rw [show rsp.toBitVec - 96 - 8#64 = rsp.toBitVec - 104 by laddr]
  refine eventually_trans _ _ _ _ (hno _ (Host.addrOf (k + 86 + 1)) (avail - 24 * 33 - 32 * 33) lo' sa _
    rfl (by omega) glo hsa
    (by dsimp only; rw [show rsp.toBitVec - 104 + 8 = rsp.toBitVec - 96 by laddr]; ecancel)) ?_
  rintro ⟨d5, pc5⟩ ⟨hpc5, hrsp5, hr145, hrbp5, stk5, spm5, hstk5, hspm5, Hm5⟩
  dsimp only at hpc5 hrsp5 hr145 hrbp5 Hm5
  subst hpc5
  obtain ⟨⟨rax5, rbx5, rcx5, rdx5, rsi5, rdi5, rsp5, rbp5, r85, r95, r105, r115, r125, r135, r145, r155⟩,
    zmms5, flags5, mem5⟩ := d5
  simp only at hrsp5 hr145 hrbp5 Hm5
  rw [show ({ toBitVec := rsp.toBitVec - 104 } + 8 : UInt64) = { toBitVec := rsp.toBitVec - 96 } by
    apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega] at hrsp5
  subst hrsp5 hr145 hrbp5
  rw [show rsp.toBitVec - 104 + 8 = rsp.toBitVec - 96 by laddr] at Hm5
  -- 87–98: writeBarrier, recv, Data pointer
  kat hk DepUnmarshal 87
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk DepUnmarshal 88
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk DepUnmarshal 89
  apply load_step_at _ _ (rsp.toBitVec + 8) _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by laddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk DepUnmarshal 90
  klabel hk hf DepUnmarshal 97
  kat hk DepUnmarshal 97
  kat hk DepUnmarshal 98
  apply store_step_at _ _ (rax.toBitVec + 32) _ _ _ aD _ _ (by kaddr) (by ecancel) (by exact haD)
  intro m10 H10
  simp only [Width.bytes, Width.bits] at H10
  kunfold
  -- 99–105: rbx = buf + 1056, rdi = cap − 1056, rcx = 184, the call
  kat hk DepUnmarshal 99
  apply load_step_at _ _ (rsp.toBitVec + 16) _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by laddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk DepUnmarshal 100
  try intro _
  kat hk DepUnmarshal 101
  apply load_step_at _ _ (rsp.toBitVec + 32) _ _ (Int.toBytes 8 rdi.toBitVec.toInt) _ _ (by laddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  try simp only [ofInt_ofBytes_toBytes64]
  kat hk DepUnmarshal 102
  try intro _
  kat hk DepUnmarshal 103
  kat hk DepUnmarshal 104
  kat hk DepUnmarshal 105
  apply store_step_at _ _ (rsp.toBitVec - 104) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 86 + 1)).toBitVec.toInt) _ _
    (by laddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m11 H11
  simp only [Width.bytes, Width.bits] at H11
  kunfold
  try rw [show rsp.toBitVec - 96 - 8#64 = rsp.toBitVec - 104 by laddr]
  rw [show label "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ"
    = Host.addrOf (kd + 0) from label_at hkd hfd (j := 0) (by rfl) (by intro i hi; omega)]
  -- our scratch as the callee's frame; the fresh object as the callee's receiver
  obtain ⟨fa, r1, hfa, hr1, rfl⟩ := split_at stk5 Sd (by omega)
  have hr1' : r1.length = 48 := by simp only [List.length_append] at hstk5; omega
  obtain ⟨fb, r2, hfb, hr2, rfl⟩ := split_at r1 8 (by omega)
  have hr2' : r2.length = 40 := by simp only [List.length_append] at hr1'; omega
  obtain ⟨fc, r3, hfc, hr3, rfl⟩ := split_at r2 24 (by omega)
  have hr3' : r3.length = 16 := by simp only [List.length_append] at hr2'; omega
  obtain ⟨fd, fe, hfd8, hfe, rfl⟩ := split_at r3 8 (by omega)
  have hfe' : fe.length = 8 := by simp only [List.length_append] at hr3'; omega
  rw [dep_lo (rsp.toBitVec - 104) Sd hSd fa fb fc fd fe hfa hfb hfc hfd8 hfe', dep_obj120 rax5.toBitVec] at H11
  refine eventually_trans _ _ _ _ (E2eScal.H4.dd_e2e_accept_main kd hkd hfd pk wc amt sig hpk hwc hamt hsig _
    (UInt64.ofBitVec (Host.addrOf (k + 105 + 1)).toBitVec) guard
    fe spm5 sb1 fc fd fb fa
    (List.replicate 8 0) (List.replicate 8 0) (List.replicate 8 0) (List.replicate 8 0) (List.replicate 8 0)
    (List.replicate 8 0) (List.replicate 8 0) (List.replicate 8 0) (List.replicate 8 0) (List.replicate 8 0)
    (List.replicate 8 0)
    hfe' hspm5 hsb1 hfc hfd8 hfb (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) _ Sd hfa Heap (avail - 24 * 33 - 32 * 33 - 120)
    (by
      dsimp only
      rw [show rsp.toBitVec - 104 + 8 = rsp.toBitVec - 96 by laddr,
        show rsp.toBitVec - 104 + 16 = rsp.toBitVec - 88 by laddr,
        show 1056 + rbx.toBitVec + 48 = rbx.toBitVec + 1104 by laddr,
        show 1056 + rbx.toBitVec + 80 = rbx.toBitVec + 1136 by laddr,
        show 1056 + rbx.toBitVec + 88 = rbx.toBitVec + 1144 by laddr,
        show 1056 + rbx.toBitVec = rbx.toBitVec + 1056 by laddr]
      ecancel)
    (by
      dsimp only
      show guard.toNat < (rsp.toBitVec - 104).toNat
      have hg := hguard
      rw [← UInt64.toNat_toBitVec rsp] at hg
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, Nat.reducePow]
      omega)
    (by rfl) (by omega) hmsD hmmD) ?_
  rintro ⟨d6, pc6⟩ ⟨hpc6, hrax6, hrbx6, hrsp6, hrbp6, hr146, p1, p2, p3, spl6, lo6, hspl6, hlo6, Hm6⟩
  dsimp only at hpc6 hrax6 hrbx6 hrsp6 hrbp6 hr146 Hm6
  simp only [Int64.ofBitVec_toBitVec] at hpc6 Hm6
  subst hpc6
  obtain ⟨⟨rax6, rbx6, rcx6, rdx6, rsi6, rdi6, rsp6, rbp6, r86, r96, r106, r116, r126, r136, r146, r156⟩,
    zmms6, flags6, mem6⟩ := d6
  simp only at hrax6 hrbx6 hrsp6 hrbp6 hr146 Hm6
  rw [show ({ toBitVec := rsp.toBitVec - 104 } + 8 : UInt64) = { toBitVec := rsp.toBitVec - 96 } by
    apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; laddr] at hrsp6
  subst hrax6 hrbx6 hrsp6 hrbp6 hr146
  rw [show rsp.toBitVec - 104 + 8 = rsp.toBitVec - 96 by laddr,
    show rsp.toBitVec - 104 + 16 = rsp.toBitVec - 88 by laddr,
    show 1056 + rbx.toBitVec + 48 = rbx.toBitVec + 1104 by laddr,
    show 1056 + rbx.toBitVec + 80 = rbx.toBitVec + 1136 by laddr,
    show 1056 + rbx.toBitVec + 88 = rbx.toBitVec + 1144 by laddr] at Hm6
  -- the callee's saved-rbp word and its rbx spill (in our frame): names, so that `ecancel` matches them
  have hvb := Int.toBytes_length 8 (BitVec.toInt (rsp.toBitVec - 8#64))
  generalize Int.toBytes 8 (BitVec.toInt (rsp.toBitVec - 8#64)) = vb at Hm6 hvb
  have hvx := Int.toBytes_length 8 (BitVec.toInt (1056 + rbx.toBitVec))
  generalize Int.toBytes 8 (BitVec.toInt (1056 + rbx.toBitVec)) = vx at Hm6 hvx
  rw [show 1056 + rbx.toBitVec = rbx.toBitVec + 1056 by laddr] at Hm6
  -- 106–107: err = nil, `je L_234` taken; epilogue 135–138
  kat hk DepUnmarshal 106
  try intro _
  kat hk DepUnmarshal 107
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf DepUnmarshal 135
  kat hk DepUnmarshal 135
  kat hk DepUnmarshal 136
  kat hk DepUnmarshal 137
  apply load_step_at _ _ (rsp.toBitVec - 8) _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by laddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk DepUnmarshal 138
  apply load_step_at _ _ rsp.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by laddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  have e33' : Int.toBytes 8 (BitVec.ofNat 64 33).toInt = Int.toBytes 8 33 := by decide
  rw [e33', show zz (24 * (33 - 33)) = [] from rfl, List.append_nil,
    List.take_of_length_le (by omega : proofs.length ≤ 33),
    show avail - 24 * 33 - 32 * 33 - 120 - 176 = avail - 2144 by omega,
    show k + 105 + 1 = k + 106 from rfl] at Hm6
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rax3.toBitVec, rax5.toBitVec, p1, p2, p3, ps', lI1', lD', lI', lP',
    Int.toBytes 8 rax5.toBitVec.toInt ++ (vx ++ sb2),
    lo6 ++ (Int.toBytes 8 (Host.addrOf (kd + 106)).toBitVec.toInt ++ (spl6 ++ (Int.toBytes 8 p3.toInt ++ vb))),
    hps', g7, g6, g5, g8, by simp [hvx, hsb2', Int.toBytes_length], by simp [hlo6, hspl6, hvb, Int.toBytes_length]; try omega, ?_⟩
  rotate_right
  · rw [at_app _ _ (b := rsp.toBitVec - 88) (by simp [Int.toBytes_length]; laddr) (by simp [hvx, hsb2',
        Int.toBytes_length]),
      at_app _ _ (b := rsp.toBitVec - 80) (by rw [hvx]; laddr) (by simp [hvx, hsb2']),
      show rsp.toBitVec - 104 - BitVec.ofNat 64 (Sd + 48) = rsp.toBitVec - 104 - BitVec.ofNat 64 (Sd + 48) from rfl,
      dep_lo (rsp.toBitVec - 104) Sd hSd _ _ _ _ _ hlo6 (Int.toBytes_length 8 _) hspl6 (Int.toBytes_length 8 _) hvb]
    ecancel
  all_goals first
    | exact trivial
    | with_reducible rfl
    | (apply UInt64.toBitVec_inj.mp
       simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, Width.bits]
       done)
    | (apply UInt64.toBitVec_inj.mp; laddr)
    | (apply UInt64.toBitVec_inj.mp; simp)

end E2eDep
