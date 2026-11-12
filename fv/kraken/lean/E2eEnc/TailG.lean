import E2eEnc.LoopG

/-!
# One-growth path: from `L_7c` (directive 29) to the return when site 2 or the loop may grow

`dcg_tail50` starts at `L_cd` (directive 50) with a block `P2 ‖ t` (`P2 = pre ‖ root`) of capacity `cp ≥ len + 36`:
51 writes the offset 36, 52–60 as `dc_tail`, then `dcg_loop` (82 → 100) and the epilogue 100–105.
`dcg_tail` starts at `L_7c` (29) with a block `pre ‖ tail0` of capacity `cp ≥ len + 32`: 30–36 `memmove` of the root,
37–42 site 2: `jb` not taken (43–44 `jmp L_cd`) or taken (45–49: `growslice(bp, len + 36, cp, 4, uint8)` under
`GrowsliceC`; the old block joins the garbage frame `G`), then `dcg_tail50`.
-/

open Machine Runtime TestTarget E2eEnc.Code
variable [Host]

namespace E2eEnc

theorem dcg_tail50 (k : Nat) (hk : DcMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh DcMarshal k)
    (x c pc nb bp lb : BitVec 64) (ra ob : UInt64) (n len cp cap0 : Nat) (hnb : nb.toNat = n) (hn : n ≤ 128)
    (hlb : lb.toNat = len) (cb P2 t : List UInt8) (hcb : cb.length = 8 * n) (hP2 : P2.length = len + 32)
    (htl : P2.length + t.length = cp) (h36 : len + 36 ≤ cp)
    (S : Nat) (Heap : Nat → DataMem → Prop) (R : DataMem → Prop) (hgs : GrowsliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 S)
    (av : Nat) (hC : len + 36 + 8 * n ≤ cp ∨ (cp = cap0 ∧ 4 * (len + 36 + 8 * n) + 8576 ≤ av)) (hmax : av ≤ maxAlloc)
    (hLm : len + 36 + 8 * n < 2 ^ 47)
    (hone : ∀ m, m ≤ len + 36 + 8 * n → cap0 < m → len + 36 + 8 * n ≤ nextSliceCap m cap0) (G : DataMem → Prop)
    (l24 l40 l48 l72 spl rslot scr : List UInt8) (hl24 : l24.length = 8) (hl40 : l40.length = 8)
    (hl48 : l48.length = 8) (hl72 : l72.length = 8) (hspl : spl.length = 40) (hrs : rslot.length = 8)
    (hsc : scr.length = S) (s : MachineData)
    (hrax : s.regs.rax.toBitVec = bp) (hrbx : s.regs.rbx.toBitVec = 4 + (lb + 32)) (hrcx : s.regs.rcx.toNat = cp)
    (hrsp : s.regs.rsp.toBitVec = x - 136)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At x) ⋆ Eq ((Int.toBytes 8 ob.toBitVec.toInt).At (x - 8))
      ⋆ Eq ((Int.toBytes 8 c.toInt).At (x + 8))
      ⋆ Eq (l24.At (x - 24)) ⋆ Eq (l40.At (x - 40)) ⋆ Eq (l48.At (x - 48)) ⋆ Eq (l72.At (x - 72))
      ⋆ Eq (spl.At (x - 136)) ⋆ Eq (rslot.At (x - 144)) ⋆ Eq (scr.At (x - 144 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 pc.toInt).At (c + 32)) ⋆ Eq ((Int.toBytes 8 nb.toInt).At (c + 40))
      ⋆ Eq (cb.At pc) ⋆ Eq ((P2 ++ t).At bp) ⋆ G ⋆ Heap av ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rbx.toNat = len + 36 + 8 * n
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp.toBitVec = x + 8 ∧ st.data.regs.rbp = ob ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (l24' l40' l48' l72' spl' rslot' scr' rest : List UInt8) (av' : Nat) (G' : DataMem → Prop),
          l24'.length = 8 ∧ l40'.length = 8 ∧ l48'.length = 8 ∧ l72'.length = 8 ∧ spl'.length = 40
          ∧ rslot'.length = 8 ∧ scr'.length = S ∧ len + 36 + 8 * n + rest.length = st.data.regs.rcx.toNat ∧ av' ≤ av ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At x) ⋆ Eq ((Int.toBytes 8 ob.toBitVec.toInt).At (x - 8))
          ⋆ Eq ((Int.toBytes 8 c.toInt).At (x + 8))
          ⋆ Eq (l24'.At (x - 24)) ⋆ Eq (l40'.At (x - 40)) ⋆ Eq (l48'.At (x - 48)) ⋆ Eq (l72'.At (x - 72))
          ⋆ Eq (spl'.At (x - 136)) ⋆ Eq (rslot'.At (x - 144)) ⋆ Eq (scr'.At (x - 144 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 pc.toInt).At (c + 32)) ⋆ Eq ((Int.toBytes 8 nb.toInt).At (c + 40))
          ⋆ Eq (cb.At pc) ⋆ Eq ((P2 ++ dcOff ++ cb ++ rest).At st.data.regs.rax.toBitVec) ⋆ G' ⋆ Heap av' ⋆ R)
          st.data.dmem)
      ⟨s, Host.addrOf (k + 50)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, ⟨rspb⟩, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hrax hrbx hrcx hrsp ⊢
  subst hrax hrsp
  have hz3 := rcx.toNat_lt_size
  simp only [UInt64.size] at hz3
  have ht4 : 4 ≤ t.length := by omega
  have esplit : Eq ((P2 ++ t).At rax.toBitVec) = Eq (P2.At rax.toBitVec) ⋆ Eq ((t.take 4).At (rax.toBitVec + lb + 32))
      ⋆ Eq ((t.drop 4).At (rax.toBitVec + lb + 36)) := by
    conv => lhs; rw [← List.take_append_drop 4 t]
    rw [at_app P2 _ (b := rax.toBitVec + lb + 32)
        (by rw [hP2]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega) (by simp; omega),
      at_app (t.take 4) (t.drop 4) (b := rax.toBitVec + lb + 36)
        (by rw [List.length_take, Nat.min_eq_left ht4]; bv_omega) (by simp; omega), ← Std.ExtHashMap.sep_assoc]
  rw [esplit] at h_mem
  kat hk DcMarshal 50
  kat hk DcMarshal 51
  rw [hrbx, dc_off_addr _ _ _ rfl]
  apply store_step _ _ _ _ _ (t.take 4) _ _ (by ecancel) (by simp; omega)
  intro m5 H5
  simp only [Width.bytes, dc_off_bytes] at H5
  kunfold
  kat hk DcMarshal 52
  apply load_step_at _ _ (x + 8) _ _ (Int.toBytes 8 c.toInt) _ _ (by daddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk DcMarshal 53
  apply load_step_at _ _ (c + 40) _ _ (Int.toBytes 8 nb.toInt) _ _ (by daddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk DcMarshal 54
  kat hk DcMarshal 55
  split
  case isTrue h => exfalso; rw [dc_jg128_false _ _ (by omega)] at h; exact Bool.noConfusion h
  simp only [Effects.All]
  kat hk DcMarshal 56
  apply store_step_at _ _ (x - 40) _ _ _ l40 _ _ (by daddr) (by ecancel) (by exact hl40)
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  kat hk DcMarshal 57
  apply load_step_at _ _ (c + 32) _ _ (Int.toBytes 8 pc.toInt) _ _ (by daddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk DcMarshal 58
  apply store_step_at _ _ (x - 24) _ _ _ l24 _ _ (by daddr) (by ecancel) (by exact hl24)
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  kat hk DcMarshal 59
  intro _
  kat hk DcMarshal 60
  klabel hk hf DcMarshal 82
  have hP3 : (P2 ++ dcOff).length = len + 36 := by simp [hP2, dcOff]
  refine eventually_trans _ _ _ _ (dcg_loop k hk hf cb (P2 ++ dcOff) n (len + 36) hcb hP3 hn x pc nb hnb S Heap _ hgs
    cap0 hLm hone _ _ n 0 rax.toBitVec cp (t.drop 4) G av l48 l72 spl rslot scr _ (by omega) (by simp; omega) hC hmax
    hl48 hl72 hspl hrs hsc rfl (by show rbx.toBitVec.toNat = _; rw [hrbx, dc_rbx36 _ _ rfl (by omega), hlb]) (by simpa using hrcx) rfl (by simp)
    (by simpa using hnb) rfl rfl rfl
    (by
      dsimp only
      simp only [Nat.mul_zero, List.take_zero, List.append_nil]
      rw [at_app (P2 ++ dcOff) (t.drop 4) (b := rax.toBitVec + lb + 36)
          (by rw [hP3]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega) (by simp [hP2, dcOff]; omega),
        at_app P2 dcOff (b := rax.toBitVec + lb + 32)
          (by rw [hP2]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega) (by simp [hP2, dcOff]; omega)]
      ecancel)) ?_
  rintro ⟨e2, pc2⟩ ⟨hpc2, bp2, cp2, tail2, G2, av2, a48, a72, aspl, ars, ascr, htl2, hav2, h48, h72, hsp2, hrs2, hsc2,
    hrax2, hrbx2, hrcx2, hrsp2, hrbp2, hr142, Hm2⟩
  dsimp only at hpc2 hrax2 hrbx2 hrcx2 hrsp2 hrbp2 hr142 Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, ⟨rspb2⟩, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := e2
  simp only at hrax2 hrbx2 hrcx2 hrsp2 hrbp2 hr142 Hm2
  subst hrsp2 hrbp2 hr142
  kat hk DcMarshal 100
  kat hk DcMarshal 101
  intro _
  kat hk DcMarshal 102
  intro _
  kat hk DcMarshal 103
  kat hk DcMarshal 104
  apply load_step_at _ _ (x - 8) _ _ (Int.toBytes 8 ob.toBitVec.toInt) _ _ (by daddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk DcMarshal 105
  apply load_step_at _ _ x _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by daddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, Int.toBytes 8 pc.toInt, Int.toBytes 8 nb.toInt, a48, a72, aspl, ars, ascr,
    tail2, av2, G2, Int.toBytes_length 8 _, Int.toBytes_length 8 _, h48, h72, hsp2, hrs2, hsc2, ?len, hav2, ?mem⟩
  case len => rw [hrcx2]; omega
  case mem =>
    rw [hrax2]
    ecancel
  all_goals first
    | trivial
    | rfl
    | (rw [hrbx2]; omega)
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | daddr

theorem dcg_tail (k : Nat) (hk : DcMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh DcMarshal k)
    (x c pr pc nb : BitVec 64) (ra ob : UInt64) (n cp cap0 : Nat) (hnb : nb.toNat = n) (hn : n ≤ 128)
    (root cb pre tail0 : List UInt8) (hroot : root.length = 32) (hcb : cb.length = 8 * n)
    (S : Nat) (Heap : Nat → DataMem → Prop) (R : DataMem → Prop) (hgs : GrowsliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 S)
    (hmm : MemmoveC S) (av : Nat) (G : DataMem → Prop)
    (l24 l32 l40 l48 l56 l64 l72 spl rslot scr : List UInt8) (hl24 : l24.length = 8) (hl32 : l32.length = 8)
    (hl40 : l40.length = 8) (hl48 : l48.length = 8) (hl56 : l56.length = 8) (hl64 : l64.length = 8)
    (hl72 : l72.length = 8) (hspl : spl.length = 40) (hrs : rslot.length = 8) (hsc : scr.length = S)
    (s : MachineData) (bp : BitVec 64)
    (hpre : pre.length = s.regs.rcx.toNat) (htl0 : pre.length + tail0.length = cp) (h32 : s.regs.rcx.toNat + 32 ≤ cp)
    (hC : s.regs.rcx.toNat + 36 + 8 * n ≤ cp ∨ (cp = cap0 ∧ 4 * (s.regs.rcx.toNat + 36 + 8 * n) + 8576 ≤ av))
    (hmax : av ≤ maxAlloc) (hLm : s.regs.rcx.toNat + 36 + 8 * n < 2 ^ 47)
    (hone : ∀ m, m ≤ s.regs.rcx.toNat + 36 + 8 * n → cap0 < m →
      s.regs.rcx.toNat + 36 + 8 * n ≤ nextSliceCap m cap0)
    (hrsp : s.regs.rsp.toBitVec = x - 136) (hrbx : s.regs.rbx.toBitVec = bp) (hrdi : s.regs.rdi.toNat = cp)
    (hr8 : s.regs.r8.toBitVec = s.regs.rcx.toBitVec + 32) (hrdx : s.regs.rdx.toBitVec = pr)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At x) ⋆ Eq ((Int.toBytes 8 ob.toBitVec.toInt).At (x - 8))
      ⋆ Eq ((Int.toBytes 8 c.toInt).At (x + 8))
      ⋆ Eq (l24.At (x - 24)) ⋆ Eq (l32.At (x - 32)) ⋆ Eq (l40.At (x - 40)) ⋆ Eq (l48.At (x - 48))
      ⋆ Eq (l56.At (x - 56)) ⋆ Eq (l64.At (x - 64)) ⋆ Eq (l72.At (x - 72))
      ⋆ Eq (spl.At (x - 136)) ⋆ Eq (rslot.At (x - 144)) ⋆ Eq (scr.At (x - 144 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 pc.toInt).At (c + 32)) ⋆ Eq ((Int.toBytes 8 nb.toInt).At (c + 40))
      ⋆ Eq (root.At pr) ⋆ Eq (cb.At pc) ⋆ Eq ((pre ++ tail0).At bp) ⋆ G ⋆ Heap av ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 36 + 8 * n
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp.toBitVec = x + 8 ∧ st.data.regs.rbp = ob ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (l24' l32' l40' l48' l56' l64' l72' spl' rslot' scr' rest : List UInt8) (av' : Nat) (G' : DataMem → Prop),
          l24'.length = 8 ∧ l32'.length = 8 ∧ l40'.length = 8 ∧ l48'.length = 8 ∧ l56'.length = 8
          ∧ l64'.length = 8 ∧ l72'.length = 8 ∧ spl'.length = 40
          ∧ rslot'.length = 8 ∧ scr'.length = S ∧ s.regs.rcx.toNat + 36 + 8 * n + rest.length = st.data.regs.rcx.toNat
          ∧ av' ≤ av ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At x) ⋆ Eq ((Int.toBytes 8 ob.toBitVec.toInt).At (x - 8))
          ⋆ Eq ((Int.toBytes 8 c.toInt).At (x + 8))
          ⋆ Eq (l24'.At (x - 24)) ⋆ Eq (l32'.At (x - 32)) ⋆ Eq (l40'.At (x - 40)) ⋆ Eq (l48'.At (x - 48))
          ⋆ Eq (l56'.At (x - 56)) ⋆ Eq (l64'.At (x - 64)) ⋆ Eq (l72'.At (x - 72))
          ⋆ Eq (spl'.At (x - 136)) ⋆ Eq (rslot'.At (x - 144)) ⋆ Eq (scr'.At (x - 144 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 pc.toInt).At (c + 32)) ⋆ Eq ((Int.toBytes 8 nb.toInt).At (c + 40))
          ⋆ Eq (root.At pr) ⋆ Eq (cb.At pc) ⋆ Eq ((pre ++ root ++ dcOff ++ cb ++ rest).At st.data.regs.rax.toBitVec)
          ⋆ G' ⋆ Heap av' ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 29)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, ⟨rspb⟩, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hrsp hrbx hrdi hr8 hrdx hpre h32 hC hLm hone ⊢
  subst hrsp hrbx hrdx
  have hz1 := rcx.toNat_lt_size; have hz2 := rdi.toNat_lt_size
  simp only [UInt64.size] at hz1 hz2
  have hpre' : pre.length = rcx.toBitVec.toNat := hpre
  have e3 : Eq ((pre ++ tail0).At rbx.toBitVec) = Eq (pre.At rbx.toBitVec) ⋆ Eq ((tail0.take 32).At (rbx.toBitVec + rcx.toBitVec))
      ⋆ Eq ((tail0.drop 32).At (rbx.toBitVec + rcx.toBitVec + 32)) := by
    conv => lhs; rw [← List.take_append_drop 32 tail0]
    rw [at_app pre _ (b := rbx.toBitVec + rcx.toBitVec) (by rw [hpre']; simp) (by simp; omega),
      at_app (tail0.take 32) (tail0.drop 32) (b := rbx.toBitVec + rcx.toBitVec + 32)
        (by rw [List.length_take, Nat.min_eq_left (by omega)]; rfl) (by simp; omega), ← Std.ExtHashMap.sep_assoc]
  rw [e3] at h_mem
  kat hk DcMarshal 29
  kat hk DcMarshal 30
  apply store_step_at _ _ (x - 64) _ _ _ l64 _ _ (by daddr) (by ecancel) (by exact hl64)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk DcMarshal 31
  apply store_step_at _ _ (x - 32) _ _ _ l32 _ _ (by daddr) (by ecancel) (by exact hl32)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk DcMarshal 32
  apply store_step_at _ _ (x - 56) _ _ _ l56 _ _ (by daddr) (by ecancel) (by exact hl56)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk DcMarshal 33
  kat hk DcMarshal 34
  kat hk DcMarshal 35
  kat hk DcMarshal 36
  apply store_step_at _ _ (x - 144) _ _ _ rslot _ _ (by daddr) (by ecancel) (by exact hrs)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  rw [BitVec.mul_one, show x - 136 - 8#64 = x - 144 by bv_omega]
  refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (k + 36 + 1)) root (tail0.take 32) scr _
    (by rw [hroot]; rfl) (by simp [hroot]; omega) hsc (by dsimp only; ecancel)) ?_
  rintro ⟨e1, pc1⟩ ⟨hpc1, hrsp1, hr141, hrbp1, stk1, hstk1, Hm1⟩
  dsimp only at hpc1 hrsp1 hr141 hrbp1 Hm1
  subst hpc1
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩,
    zmms1, flags1, mem1⟩ := e1
  simp only at hrsp1 hr141 hrbp1 Hm1
  have hrsp1' : rsp1 = { toBitVec := x - 136 } := by
    rw [hrsp1]; apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
  subst hrsp1' hr141 hrbp1
  kat hk DcMarshal 37
  apply load_step_at _ _ (x - 64) _ _ (Int.toBytes 8 r8.toBitVec.toInt) _ _ (by daddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk DcMarshal 38
  kat hk DcMarshal 39
  kat hk DcMarshal 40
  apply load_step_at _ _ (x - 56) _ _ (Int.toBytes 8 rdi.toBitVec.toInt) _ _ (by daddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  have hP2 : (pre ++ root).length = rcx.toNat + 32 := by simp [hroot]; omega
  have e4 : Eq (pre.At rbx.toBitVec) ⋆ Eq (root.At (rbx.toBitVec + rcx.toBitVec)) = Eq ((pre ++ root).At rbx.toBitVec) := by
    rw [at_app pre root (b := rbx.toBitVec + rcx.toBitVec) (by rw [hpre']; simp) (by simp [hroot]; omega)]
  kat hk DcMarshal 41
  kat hk DcMarshal 42
  split
  · -- site 2 grows: 45–49
    rename_i h
    have hg : rdi.toNat < rcx.toNat + 36 := by
      simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
      have e5 : (4 + r8.toBitVec).toNat = rcx.toNat + 36 := by rw [hr8]; simp [BitVec.toNat_add]; omega
      simp [BitVec.toNat_add] at h e5; omega
    have hK : cp = cap0 ∧ 4 * (rcx.toNat + 36 + 8 * n) + 8576 ≤ av := by
      rcases hC with hC | hC
      · omega
      · exact hC
    obtain ⟨hcp0, hK⟩ := hK
    simp only [Effects.All]
    klabel hk hf DcMarshal 45
    kat hk DcMarshal 45
    kat hk DcMarshal 46
    apply load_step_at _ _ (x - 32) _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by daddr) (by ecancel)
      (by exact Int.toBytes_length 8 _)
    kunfold
    kat hk DcMarshal 47
    kat hk DcMarshal 48
    kat hk DcMarshal 49
    apply store_step_at _ _ (x - 144) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 36 + 1)).toBitVec.toInt) _ _ (by daddr)
      (by ecancel) (by exact Int.toBytes_length 8 _)
    intro m5 H5
    simp only [Width.bytes, Width.bits] at H5
    kunfold
    rw [show x - 136 - 8#64 = x - 144 by bv_omega]
    have hnsc := nextSliceCap_le (rcx.toNat + 36) rdi.toNat (by omega)
    have e4' : ({ toBitVec := BitVec.zeroExtend 64 (BitVec.truncate 32 (4 : BitVec 64)) } : UInt64).toNat = 4 := by
      decide
    have enl : ({ toBitVec := 4 + r8.toBitVec } : UInt64).toNat = rcx.toNat + 36 := by
      show (4 + r8.toBitVec).toNat = _; rw [hr8]; simp [BitVec.toNat_add]; omega
    have erd : ({ toBitVec := rdi.toBitVec } : UInt64).toNat = rdi.toNat := rfl
    refine eventually_trans _ _ _ _ (hgs _ (Host.addrOf (k + 49 + 1)) (pre ++ root) stk1 spl av _
      (by decide) rfl ?gnum ?gold ?gcap ?gbud hmax ?glen hstk1 hspl
      (by dsimp only; rw [show x - 144 + 8 = x - 136 by bv_omega, ← e4]; ecancel)) ?_
    case gnum => dsimp only; rw [e4', enl]; omega
    case gold => dsimp only; rw [e4', enl, erd]; omega
    case gcap => dsimp only; rw [enl, erd]; omega
    case gbud => dsimp only; rw [enl, erd]; omega
    case glen => dsimp only; rw [e4', enl, hP2]; omega
    rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, hrbx1, hnc1, hub1, stk2, spl2, tail2, av1, hstk2, hspl2, htail,
      hav1, Hm2⟩
    dsimp only at hpc1 hrsp1 hrbp1 hr141 hrbx1 hnc1 hub1 htail hav1 Hm2
    subst hpc1
    obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩,
      zmms1, flags1, mem1⟩ := d1
    simp only at hrsp1 hrbp1 hr141 hrbx1 hnc1 hub1 htail hav1 Hm2
    simp only [enl, erd, Nat.one_mul, hP2] at hnc1 hub1 htail hav1
    have hrsp1' : rsp1 = { toBitVec := x - 136 } := by
      rw [hrsp1]; apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
    subst hrsp1' hrbp1 hr141 hrbx1
    rw [show x - 144 + 8 = x - 136 by bv_omega] at Hm2
    have hbig := hone (rcx.toNat + 36) (by omega) (by rw [← hcp0, ← hrdi]; omega)
    rw [← hcp0, ← hrdi] at hbig
    refine eventually_mono (dcg_tail50 k hk hf x c pc nb rax1.toBitVec rcx.toBitVec ra ob n rcx.toNat rcx1.toNat cap0
      hnb hn rfl cb (pre ++ root) tail2 hcb hP2 (by rw [hP2]; omega) (by omega) S Heap _ hgs av1
      (Or.inl (by omega)) (by unfold maxAlloc at hmax ⊢; omega) hLm hone
      (G ⋆ Eq ((pre ++ root).At rbx.toBitVec) ⋆ Eq ((tail0.drop 32).At (rbx.toBitVec + rcx.toBitVec + 32)))
      l24 l40 l48 l72 spl2 (Int.toBytes 8 (Host.addrOf (k + 49 + 1)).toBitVec.toInt) stk2 hl24 hl40 hl48 hl72
      hspl2 (Int.toBytes_length 8 _) hstk2 _ rfl (by show 4 + r8.toBitVec = _; rw [hr8]) rfl rfl (by dsimp only; ecancel)) ?_
    rintro st ⟨hpc, hrbx, hrdi', hrsi, hrsp, hrbp, hr14, a24, a40, a48, a72, aspl, ars, ascr, rest, av', G', h24, h40,
      h48, h72, hsp, hrs', hsc', hlen, hav', hm⟩
    exact ⟨hpc, hrbx, hrdi', hrsi, hrsp, hrbp, hr14, a24, Int.toBytes 8 rbx.toBitVec.toInt, a40, a48,
      Int.toBytes 8 rdi.toBitVec.toInt, Int.toBytes 8 r8.toBitVec.toInt, a72, aspl, ars, ascr, rest, av', G', h24,
      Int.toBytes_length 8 _, h40, h48, Int.toBytes_length 8 _, Int.toBytes_length 8 _, h72, hsp, hrs', hsc', hlen,
      by omega, by simp only [List.append_assoc] at hm ⊢; ecancel⟩
  · -- site 2 fits: 43–44 `jmp L_cd`
    rename_i h
    simp only [Effects.All]
    kat hk DcMarshal 43
    apply load_step_at _ _ (x - 32) _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by daddr) (by ecancel)
      (by exact Int.toBytes_length 8 _)
    kunfold
    kat hk DcMarshal 44
    klabel hk hf DcMarshal 50
    have hf36 : rcx.toNat + 36 ≤ rdi.toNat := by
      simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
      have e5 : (4 + r8.toBitVec).toNat = rcx.toNat + 36 := by rw [hr8]; simp [BitVec.toNat_add]; omega
      simp [BitVec.toNat_add] at h e5; omega
    have ej : Eq ((pre ++ root).At rbx.toBitVec) ⋆ Eq ((tail0.drop 32).At (rbx.toBitVec + rcx.toBitVec + 32))
        = Eq ((pre ++ root ++ tail0.drop 32).At rbx.toBitVec) := by
      rw [at_app (pre ++ root) (tail0.drop 32) (b := rbx.toBitVec + rcx.toBitVec + 32)
        (by rw [hP2]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega) (by simp [hroot]; omega)]
    refine eventually_mono (dcg_tail50 k hk hf x c pc nb rbx.toBitVec rcx.toBitVec ra ob n rcx.toNat cp cap0
      hnb hn rfl cb (pre ++ root) (tail0.drop 32) hcb hP2 (by simp [hroot]; omega) (by omega) S Heap _ hgs av
      hC hmax hLm hone G l24 l40 l48 l72 spl (Int.toBytes 8 (Host.addrOf (k + 36 + 1)).toBitVec.toInt) stk1 hl24 hl40
      hl48 hl72 hspl (Int.toBytes_length 8 _) hstk1 _ rfl (by show 4 + r8.toBitVec = _; rw [hr8]) (by simpa using hrdi)
      rfl (by dsimp only; rw [← ej, ← e4]; ecancel)) ?_
    rintro st ⟨hpc, hrbx, hrdi', hrsi, hrsp, hrbp, hr14, a24, a40, a48, a72, aspl, ars, ascr, rest, av', G', h24, h40,
      h48, h72, hsp, hrs', hsc', hlen, hav', hm⟩
    exact ⟨hpc, hrbx, hrdi', hrsi, hrsp, hrbp, hr14, a24, Int.toBytes 8 rbx.toBitVec.toInt, a40, a48,
      Int.toBytes 8 rdi.toBitVec.toInt, Int.toBytes 8 r8.toBitVec.toInt, a72, aspl, ars, ascr, rest, av', G', h24,
      Int.toBytes_length 8 _, h40, h48, Int.toBytes_length 8 _, Int.toBytes_length 8 _, h72, hsp, hrs', hsc', hlen,
      hav', by simp only [List.append_assoc] at hm ⊢; ecancel⟩

end E2eEnc
