import Runtime.Contracts
import Prysm.DataColumnsByRootIdentifier.EncodeLoop
import Prysm.DataColumnsByRootIdentifier.EncodeTail
import Prysm.ElfData.CheckpointAndEpoch

/-!
# Any-site grow path: the Columns loop when any iteration may grow the block

Loop head `L_13a` (directive 82). The invariant: rax = block pointer `bp`, rbx = L + 8i, rcx = the
block capacity `cp`, rdx = pc, rsi = i, r8 = n, rsp = x − 136; the block holds `Pfx ‖ cb.take (8i) ‖ tail` with
`|Pfx| = L` and `|tail| = cp − (L + 8i)`; the slots x − 24 (pc) and x − 40 (n) that the growth branch reloads; the
growth-only slots x − 48, x − 72, the 40-byte spill area x − 136, the return slot x − 144, scratch; the garbage frame
`G`; `Heap av` with `(n − i)·K ≤ av`, K = 4·(L + 8n) + 8576.

One iteration (`Encode.grow_iter`): 82–89 as `Encode.iter`; if `cp ≥ L + 8(i+1)` the `jae` is taken (79–81, as `Encode.iter`);
otherwise 90–94 spill i and the word and call `growslice(bp, L + 8(i+1), cp, 8, uint8)` (`GrowsliceC`), 95–99 reload
and `jmp L_132`, 79–81 store into the new block. The old block (the copied prefix and the old tail) joins `G`.
-/

open Machine Runtime Prysm.DataColumnsByRootIdentifier.Code
variable [Host]

namespace Prysm.DataColumnsByRootIdentifier

omit [Host] in
theorem Encode.grow_loop_split (A tail : List UInt8) (bp : BitVec 64) (L i : Nat) (hA : A.length = L + 8 * i)
    (ht : 8 ≤ tail.length) (hl : A.length + tail.length < 2 ^ 64) :
    Eq ((A ++ tail).At bp) = Eq (A.At bp) ⋆ Eq ((tail.take 8).At (bp + BitVec.ofNat 64 L + BitVec.ofNat 64 (8 * i)))
      ⋆ Eq ((tail.drop 8).At (bp + BitVec.ofNat 64 L + BitVec.ofNat 64 (8 * i) + 8)) := by
  have e1 : tail = tail.take 8 ++ tail.drop 8 := (List.take_append_drop 8 tail).symm
  conv => lhs; rw [e1]
  rw [← List.append_assoc, at_app (A ++ tail.take 8) (tail.drop 8)
      (b := bp + BitVec.ofNat 64 L + BitVec.ofNat 64 (8 * i) + 8)
      (by simp only [List.length_append, List.length_take, hA, Nat.min_eq_left ht]
          apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega)
      (by simp; omega),
    at_app A (tail.take 8) (b := bp + BitVec.ofNat 64 L + BitVec.ofNat 64 (8 * i))
      (by rw [hA]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega) (by simp; omega)]

omit [Host] in
theorem Encode.grow_loop_join (Pfx cb t : List UInt8) (bp : BitVec 64) (n i L : Nat) (hP : Pfx.length = L)
    (hcb : cb.length = 8 * n) (hi : i < n) (hl : L + 8 * (i + 1) + t.length < 2 ^ 64) :
    Eq ((Pfx ++ cb.take (8 * i)).At bp) ⋆ Eq (((cb.drop (8 * i)).take 8).At (bp + BitVec.ofNat 64 L
      + BitVec.ofNat 64 (8 * i))) ⋆ Eq (t.At (bp + BitVec.ofNat 64 L + BitVec.ofNat 64 (8 * i) + 8))
      = Eq ((Pfx ++ cb.take (8 * (i + 1)) ++ t).At bp) := by
  have e1 : cb.take (8 * (i + 1)) = cb.take (8 * i) ++ (cb.drop (8 * i)).take 8 := by
    rw [show 8 * (i + 1) = 8 * i + 8 by omega, List.take_add]
  have l1 : (cb.take (8 * i)).length = 8 * i := by simp; omega
  have l2 : ((cb.drop (8 * i)).take 8).length = 8 := by simp; omega
  rw [e1, ← List.append_assoc, at_app (Pfx ++ cb.take (8 * i) ++ (cb.drop (8 * i)).take 8) t
      (b := bp + BitVec.ofNat 64 L + BitVec.ofNat 64 (8 * i) + 8)
      (by simp only [List.length_append, hP, l1, l2]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega)
      (by simp only [List.length_append, hP, l1, l2]; omega),
    at_app (Pfx ++ cb.take (8 * i)) ((cb.drop (8 * i)).take 8) (b := bp + BitVec.ofNat 64 L + BitVec.ofNat 64 (8 * i))
      (by simp only [List.length_append, hP, l1]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega)
      (by simp only [List.length_append, hP, l1, l2]; omega)]

/-- One iteration of the Columns loop, fitting or growing. -/
theorem Encode.grow_iter (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (cb Pfx : List UInt8) (n i L : Nat) (hcb : cb.length = 8 * n) (hP : Pfx.length = L) (hn : n ≤ 128)
    (hi : i < n) (x pc nb : BitVec 64) (hnb : nb.toNat = n) (S : Nat) (Heap : Nat → DataMem → Prop)
    (R : DataMem → Prop) (hgs : GrowsliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 S)
    (bp : BitVec 64) (cp : Nat) (tail : List UInt8) (htl : tail.length + (L + 8 * i) = cp) (G : DataMem → Prop)
    (cap0 av : Nat) (hC : L + 8 * n ≤ cp ∨ (cp = cap0 ∧ 4 * (L + 8 * n) + 8576 ≤ av)) (hmax : av ≤ maxAlloc)
    (hLm : L + 8 * n < 2 ^ 47) (hone : ∀ m, m ≤ L + 8 * n → cap0 < m → L + 8 * n ≤ nextSliceCap m cap0)
    (l48 l72 spl rslot scr : List UInt8) (hl48 : l48.length = 8) (hl72 : l72.length = 8) (hspl : spl.length = 40)
    (hrs : rslot.length = 8) (hsc : scr.length = S) (s : MachineData)
    (hrax : s.regs.rax.toBitVec = bp) (hrbx : s.regs.rbx.toNat = L + 8 * i) (hrcx : s.regs.rcx.toNat = cp)
    (hrdx : s.regs.rdx.toBitVec = pc) (hrsi : s.regs.rsi.toNat = i) (hr8 : s.regs.r8.toNat = n)
    (hrsp : s.regs.rsp.toBitVec = x - 136) (bpv r14v : UInt64) (hrbp : s.regs.rbp = bpv) (hr14 : s.regs.r14 = r14v)
    (h_mem : s.dmem =⋆ Eq (cb.At pc) ⋆ Eq ((Pfx ++ cb.take (8 * i) ++ tail).At bp)
      ⋆ Eq ((Int.toBytes 8 pc.toInt).At (x - 24)) ⋆ Eq ((Int.toBytes 8 nb.toInt).At (x - 40))
      ⋆ Eq (l48.At (x - 48)) ⋆ Eq (l72.At (x - 72)) ⋆ Eq (spl.At (x - 136)) ⋆ Eq (rslot.At (x - 144))
      ⋆ Eq (scr.At (x - 144 - BitVec.ofNat 64 S)) ⋆ G ⋆ Heap av ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 82) ∧
        ∃ (bp' : BitVec 64) (cp' : Nat) (tail' : List UInt8) (G' : DataMem → Prop) (av' : Nat)
          (l48' l72' spl' rslot' scr' : List UInt8),
          tail'.length + (L + 8 * (i + 1)) = cp' ∧ (L + 8 * n ≤ cp' ∨ (cp' = cap0 ∧ 4 * (L + 8 * n) + 8576 ≤ av'))
          ∧ av' ≤ av
          ∧ l48'.length = 8 ∧ l72'.length = 8 ∧ spl'.length = 40 ∧ rslot'.length = 8 ∧ scr'.length = S
          ∧ st.data.regs.rax.toBitVec = bp' ∧ st.data.regs.rbx.toNat = L + 8 * (i + 1) ∧ st.data.regs.rcx.toNat = cp'
          ∧ st.data.regs.rdx.toBitVec = pc ∧ st.data.regs.rsi.toNat = i + 1 ∧ st.data.regs.r8.toNat = n
          ∧ st.data.regs.rsp.toBitVec = x - 136 ∧ st.data.regs.rbp = bpv ∧ st.data.regs.r14 = r14v
          ∧ (Eq (cb.At pc) ⋆ Eq ((Pfx ++ cb.take (8 * (i + 1)) ++ tail').At bp')
            ⋆ Eq ((Int.toBytes 8 pc.toInt).At (x - 24)) ⋆ Eq ((Int.toBytes 8 nb.toInt).At (x - 40))
            ⋆ Eq (l48'.At (x - 48)) ⋆ Eq (l72'.At (x - 72)) ⋆ Eq (spl'.At (x - 136)) ⋆ Eq (rslot'.At (x - 144))
            ⋆ Eq (scr'.At (x - 144 - BitVec.ofNat 64 S)) ⋆ G' ⋆ Heap av' ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 82)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, ⟨rspb⟩, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hrax hrbx hrcx hrdx hrsi hr8 hrsp hrbp hr14
  subst hrax hrdx hrsp hrbp hr14
  have hz1 := rbx.toNat_lt_size; have hz2 := rsi.toNat_lt_size; have hz3 := rcx.toNat_lt_size
  simp only [UInt64.size] at hz1 hz2 hz3
  have hlen : cb.length < 2 ^ 64 := by omega
  have hA : (Pfx ++ cb.take (8 * i)).length = L + 8 * i := by simp [hP]; omega
  rw [block_split cb rdx.toBitVec (8 * i) (by omega) hlen] at h_mem
  kat hk marshalSSZTo 82
  kat hk marshalSSZTo 83
  kat hk marshalSSZTo 84
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    exact Prysm.SyncCommittee.jge_false512 _ _ (by simp; omega) (by simp; omega) h
  simp only [Effects.All]
  kat hk marshalSSZTo 85
  kat hk marshalSSZTo 86
  rw [Encode.loop_idx _ _ i (by simpa using hrsi) (by omega)]
  apply load_step _ _ _ _ ((cb.drop (8 * i)).take 8) _ _ (by ecancel) (by simp; omega)
  kunfold
  kat hk marshalSSZTo 87
  kat hk marshalSSZTo 88
  kat hk marshalSSZTo 89
  have e1 := Encode.loop_rbx rbx.toBitVec L i (by simpa using hrbx) (by omega)
  split
  · -- the capacity holds the word: `jae L_132` taken (the text of `Encode.iter`)
    rename_i h
    have hfit : L + 8 * (i + 1) ≤ cp := by
      simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
      simp [BitVec.toNat_add] at h e1; omega
    have ht8 : 8 ≤ tail.length := by omega
    rw [Encode.grow_loop_split _ tail rax.toBitVec L i hA ht8 (by omega)] at h_mem
    simp only [Effects.All]
    klabel hk hf marshalSSZTo 79
    kat hk marshalSSZTo 79
    kat hk marshalSSZTo 80
    rw [Encode.loop_addr _ _ L i (by simpa using hrbx) (by omega)]
    apply store_step _ _ _ _ _ (tail.take 8) _ _ (by ecancel) (by simp; omega)
    intro m1 H1
    simp only [Width.bytes, Width.bits,
      toBytes_ofInt_ofBytes 64 8 rfl _ (show ((cb.drop (8 * i)).take 8).length = 8 by simp; omega)] at H1
    kunfold
    kat hk marshalSSZTo 81
    apply Eventually.done
    refine ⟨rfl, rax.toBitVec, cp, tail.drop 8, G, av, l48, l72, spl, rslot, scr, by simp; omega,
      hC, Nat.le_refl _, hl48, hl72, hspl, hrs, hsc, rfl,
      Encode.loop_rbx _ L i (by simpa using hrbx) (by omega), hrcx, rfl, Encode.loop_inc _ i (by simpa using hrsi) (by omega), hr8, rfl,
      rfl, rfl, ?_⟩
    dsimp only
    rw [← Encode.grow_loop_join Pfx cb (tail.drop 8) rax.toBitVec n i L hP hcb hi (by simp; omega),
      block_split cb rdx.toBitVec (8 * i) (by omega) hlen]
    (try simp only [BitVec.ofNat_eq_ofNat] at H1 ⊢)
    ecancel
  · -- growth: 90–99, `growslice(bp, L + 8(i+1), cp, 8, uint8)`, then 79–81 on the new block
    rename_i h
    have hgrow : cp < L + 8 * (i + 1) := by
      simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
      simp [BitVec.toNat_add] at h e1; omega
    have hK : cp = cap0 ∧ 4 * (L + 8 * n) + 8576 ≤ av := by
      rcases hC with hC | hC
      · omega
      · exact hC
    obtain ⟨hcp0, hK⟩ := hK
    rw [at_app (Pfx ++ cb.take (8 * i)) tail (b := rax.toBitVec + BitVec.ofNat 64 (L + 8 * i)) (by rw [hA])
      (by rw [hA]; omega)] at h_mem
    simp only [Effects.All]
    kat hk marshalSSZTo 90
    apply store_step_at _ _ (x - 48) _ _ _ l48 _ _ (by daddr) (by ecancel) (by exact hl48)
    intro m1 H1
    simp only [Width.bytes, Width.bits] at H1
    kunfold
    kat hk marshalSSZTo 91
    apply store_step_at _ _ (x - 72) _ _ _ l72 _ _ (by daddr) (by ecancel) (by exact hl72)
    intro m2 H2
    simp only [Width.bytes, Width.bits,
      toBytes_ofInt_ofBytes 64 8 rfl _ (show ((cb.drop (8 * i)).take 8).length = 8 by simp; omega)] at H2
    kunfold
    kat hk marshalSSZTo 92
    kat hk marshalSSZTo 93
    kat hk marshalSSZTo 94
    apply store_step_at _ _ (x - 144) _ _ _ rslot _ _ (by daddr) (by ecancel) (by exact hrs)
    intro m3 H3
    simp only [Width.bytes, Width.bits] at H3
    kunfold
    rw [show x - 136 - 8#64 = x - 144 by bv_omega]
    have hnsc := nextSliceCap_le (L + 8 * (i + 1)) cp (by omega)
    have e8 : ({ toBitVec := BitVec.zeroExtend 64 (BitVec.truncate 32 (8 : BitVec 64)) } : UInt64).toNat = 8 := by
      decide
    have enl : ({ toBitVec := 8 + rbx.toBitVec } : UInt64).toNat = L + 8 * (i + 1) := e1
    refine eventually_trans _ _ _ _ (hgs _ (Host.addrOf (k + 94 + 1)) (Pfx ++ cb.take (8 * i)) scr spl av _
      (by decide) rfl ?gnum ?gold ?gcap ?gbud hmax ?glen hsc hspl
      (by dsimp only; rw [show x - 144 + 8 = x - 136 by bv_omega]; ecancel)) ?_
    case gnum => dsimp only; rw [e8, enl]; omega
    case gold => dsimp only; rw [e8, enl]; omega
    case gcap => dsimp only; rw [enl]; omega
    case gbud => dsimp only; rw [enl, hrcx]; omega
    case glen => dsimp only; rw [e8, enl, hA]; omega
    rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, hrbx1, hnc1, hub1, stk1, spl1, tail2, av1, hstk1, hspl1, htail,
      hav1, Hm1⟩
    dsimp only at hpc1 hrsp1 hrbp1 hr141 hrbx1 hnc1 hub1 htail hav1 Hm1
    subst hpc1
    obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩,
      zmms1, flags1, mem1⟩ := d1
    simp only at hrsp1 hrbp1 hr141 hrbx1 hnc1 hub1 htail hav1 Hm1
    simp only [enl, hrcx, Nat.one_mul] at hnc1 hub1 htail hav1
    have hrsp1' : rsp1 = { toBitVec := x - 136 } := by
      rw [hrsp1]; apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
    subst hrsp1' hrbp1 hr141 hrbx1
    rw [show x - 144 + 8 = x - 136 by bv_omega] at Hm1
    have hcap1 := hnsc
    have ht2 : 8 ≤ tail2.length := by have := nextSliceCap_ge (L + 8 * (i + 1)) cp; omega
    rw [Encode.grow_loop_split _ tail2 rax1.toBitVec L i hA ht2 (by have := rcx1.toNat_lt_size; simp only [UInt64.size] at this; omega)]
      at Hm1
    kat hk marshalSSZTo 95
    apply load_step_at _ _ (x - 24) _ _ (Int.toBytes 8 rdx.toBitVec.toInt) _ _ (by daddr) (by ecancel)
      (by exact Int.toBytes_length 8 _)
    kunfold
    kat hk marshalSSZTo 96
    apply load_step_at _ _ (x - 48) _ _ (Int.toBytes 8 rsi.toBitVec.toInt) _ _ (by daddr) (by ecancel)
      (by exact Int.toBytes_length 8 _)
    kunfold
    kat hk marshalSSZTo 97
    apply load_step_at _ _ (x - 40) _ _ (Int.toBytes 8 nb.toInt) _ _ (by daddr) (by ecancel)
      (by exact Int.toBytes_length 8 _)
    kunfold
    kat hk marshalSSZTo 98
    apply load_step_at _ _ (x - 72) _ _ ((cb.drop (8 * i)).take 8) _ _ (by daddr) (by ecancel) (by simp; omega)
    kunfold
    kat hk marshalSSZTo 99
    klabel hk hf marshalSSZTo 79
    kat hk marshalSSZTo 79
    kat hk marshalSSZTo 80
    rw [Encode.loop_addr _ _ L i (by simpa using hrbx) (by omega)]
    apply store_step _ _ _ _ _ (tail2.take 8) _ _ (by ecancel) (by simp; omega)
    intro m4 H4
    simp only [Width.bytes, Width.bits,
      toBytes_ofInt_ofBytes 64 8 rfl _ (show ((cb.drop (8 * i)).take 8).length = 8 by simp; omega)] at H4
    kunfold
    kat hk marshalSSZTo 81
    apply Eventually.done
    have hc1 : rcx1.toNat ≤ 4 * (L + 8 * n) + 8576 := by omega
    rw [hA] at htail
    have hb1 : L + 8 * n ≤ rcx1.toNat ∨ (rcx1.toNat = cap0 ∧ 4 * (L + 8 * n) + 8576 ≤ av1) := by
      left; have := hone (L + 8 * (i + 1)) (by omega) (by omega); rw [← hcp0] at this; omega
    have hb2 : av1 ≤ av := by omega
    have hb3 : (tail2.drop 8).length + (L + 8 * (i + 1)) = rcx1.toNat := by simp; omega
    refine ⟨rfl, rax1.toBitVec, rcx1.toNat, tail2.drop 8,
      G ⋆ Eq ((Pfx ++ cb.take (8 * i)).At rax.toBitVec) ⋆ Eq (tail.At (rax.toBitVec + BitVec.ofNat 64 (L + 8 * i))),
      av1, Int.toBytes 8 rsi.toBitVec.toInt, (cb.drop (8 * i)).take 8, spl1,
      Int.toBytes 8 (Host.addrOf (k + 94 + 1)).toBitVec.toInt, stk1, hb3, hb1, hb2,
      Int.toBytes_length 8 _, by simp; omega, hspl1, Int.toBytes_length 8 _, hstk1, rfl, e1, rfl, rfl,
      Encode.loop_inc _ i (by simpa using hrsi) (by omega), by simpa using hnb, rfl, rfl, rfl, ?_⟩
    dsimp only
    rw [← Encode.grow_loop_join Pfx cb (tail2.drop 8) rax1.toBitVec n i L hP hcb hi
        (by have := rcx1.toNat_lt_size; simp only [UInt64.size] at this; simp; omega),
      block_split cb rdx.toBitVec (8 * i) (by omega) hlen]
    (try simp only [BitVec.ofNat_eq_ofNat] at H4 ⊢)
    ecancel

/-- The loop by recursion on the number `j` of iterations left (`i + j = n`). -/
theorem Encode.grow_loop (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (cb Pfx : List UInt8) (n L : Nat) (hcb : cb.length = 8 * n) (hP : Pfx.length = L) (hn : n ≤ 128)
    (x pc nb : BitVec 64) (hnb : nb.toNat = n) (S : Nat) (Heap : Nat → DataMem → Prop)
    (R : DataMem → Prop) (hgs : GrowsliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 S) (cap0 : Nat)
    (hLm : L + 8 * n < 2 ^ 47) (hone : ∀ m, m ≤ L + 8 * n → cap0 < m → L + 8 * n ≤ nextSliceCap m cap0)
    (bpv r14v : UInt64) :
    ∀ j i (bp : BitVec 64) (cp : Nat) (tail : List UInt8) (G : DataMem → Prop) (av : Nat)
      (l48 l72 spl rslot scr : List UInt8) (s : MachineData), i + j = n →
    tail.length + (L + 8 * i) = cp → (L + 8 * n ≤ cp ∨ (cp = cap0 ∧ 4 * (L + 8 * n) + 8576 ≤ av)) →
    av ≤ maxAlloc → l48.length = 8 → l72.length = 8 → spl.length = 40 → rslot.length = 8 → scr.length = S →
    s.regs.rax.toBitVec = bp → s.regs.rbx.toNat = L + 8 * i → s.regs.rcx.toNat = cp →
    s.regs.rdx.toBitVec = pc → s.regs.rsi.toNat = i → s.regs.r8.toNat = n →
    s.regs.rsp.toBitVec = x - 136 → s.regs.rbp = bpv → s.regs.r14 = r14v →
    (s.dmem =⋆ Eq (cb.At pc) ⋆ Eq ((Pfx ++ cb.take (8 * i) ++ tail).At bp)
      ⋆ Eq ((Int.toBytes 8 pc.toInt).At (x - 24)) ⋆ Eq ((Int.toBytes 8 nb.toInt).At (x - 40))
      ⋆ Eq (l48.At (x - 48)) ⋆ Eq (l72.At (x - 72)) ⋆ Eq (spl.At (x - 136)) ⋆ Eq (rslot.At (x - 144))
      ⋆ Eq (scr.At (x - 144 - BitVec.ofNat 64 S)) ⋆ G ⋆ Heap av ⋆ R) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 100) ∧
        ∃ (bp' : BitVec 64) (cp' : Nat) (tail' : List UInt8) (G' : DataMem → Prop) (av' : Nat)
          (l48' l72' spl' rslot' scr' : List UInt8),
          tail'.length + (L + 8 * n) = cp' ∧ av' ≤ av
          ∧ l48'.length = 8 ∧ l72'.length = 8 ∧ spl'.length = 40 ∧ rslot'.length = 8 ∧ scr'.length = S
          ∧ st.data.regs.rax.toBitVec = bp' ∧ st.data.regs.rbx.toNat = L + 8 * n ∧ st.data.regs.rcx.toNat = cp'
          ∧ st.data.regs.rsp.toBitVec = x - 136 ∧ st.data.regs.rbp = bpv ∧ st.data.regs.r14 = r14v
          ∧ (Eq (cb.At pc) ⋆ Eq ((Pfx ++ cb ++ tail').At bp')
            ⋆ Eq ((Int.toBytes 8 pc.toInt).At (x - 24)) ⋆ Eq ((Int.toBytes 8 nb.toInt).At (x - 40))
            ⋆ Eq (l48'.At (x - 48)) ⋆ Eq (l72'.At (x - 72)) ⋆ Eq (spl'.At (x - 136)) ⋆ Eq (rslot'.At (x - 144))
            ⋆ Eq (scr'.At (x - 144 - BitVec.ofNat 64 S)) ⋆ G' ⋆ Heap av' ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 82)⟩
  | 0, i, bp, cp, tail, G, av, l48, l72, spl, rslot, scr, s, hij, htl, _, _, h48, h72, hsp, hrs, hsc,
      hrax, hrbx, hrcx, _, hrsi, hr8, hrsp, hrbp, hr14, h_mem => by
    have hin : i = n := by omega
    subst hin
    refine eventually_mono (Encode.exit k hk hf i hn _ s hrsi hr8 h_mem) ?_
    rintro st ⟨hpc, hregs, hm⟩
    rw [hregs]
    refine ⟨hpc, bp, cp, tail, G, av, l48, l72, spl, rslot, scr, htl, Nat.le_refl _, h48, h72, hsp, hrs, hsc,
      hrax, hrbx, hrcx, hrsp, hrbp, hr14, ?_⟩
    rw [List.take_of_length_le (by omega)] at hm
    exact hm
  | j + 1, i, bp, cp, tail, G, av, l48, l72, spl, rslot, scr, s, hij, htl, hC, hmax, h48, h72, hsp, hrs, hsc,
      hrax, hrbx, hrcx, hrdx, hrsi, hr8, hrsp, hrbp, hr14, h_mem => by
    refine eventually_trans _ _ _ _
      (Encode.grow_iter k hk hf cb Pfx n i L hcb hP hn (by omega) x pc nb hnb S Heap R hgs bp cp tail htl G cap0 av hC hmax
        hLm hone l48 l72 spl rslot scr h48 h72 hsp hrs hsc s hrax hrbx hrcx hrdx hrsi hr8 hrsp bpv r14v hrbp hr14
        h_mem) ?_
    rintro ⟨s', pc'⟩ ⟨hpc, bp', cp', tail', G', av', l48', l72', spl', rslot', scr', h1, h2, h3, h4, h5, h6, h7, h8,
      h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩
    dsimp only at hpc; subst hpc
    refine eventually_mono (Encode.grow_loop k hk hf cb Pfx n L hcb hP hn x pc nb hnb S Heap R hgs cap0 hLm hone bpv r14v
      j (i + 1) bp' cp' tail' G' av' l48' l72' spl' rslot' scr' s' (by omega) h1 h2
      (Nat.le_trans h3 hmax) h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18) ?_
    rintro st ⟨hpc2, bp2, cp2, tail2, G2, av2, a1, a2, a3, a4, a5, e1, e2, e3, e4, e5, e6, e7, r1, r2, r3, r4, r5, r6, m⟩
    exact ⟨hpc2, bp2, cp2, tail2, G2, av2, a1, a2, a3, a4, a5, e1, Nat.le_trans e2 h3, e3, e4, e5, e6, e7, r1, r2, r3,
      r4, r5, r6, m⟩

end Prysm.DataColumnsByRootIdentifier
