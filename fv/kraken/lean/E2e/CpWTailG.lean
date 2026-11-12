import E2e.CpWTail

/-!
# `(*v1alpha1.Checkpoint).MarshalSSZTo` from `L_7b`: the second growslice site

`cpw_tail_grow`: `len(Root) = 32` and `len + 8 ≤ C < len + 40` (the block holds the epoch bytes,
the root does not fit). Directives 33–41 (`jae L_cf` not taken), 42–43 save `len + 8` at rsp0 − 72
and `Root.ptr` at rsp0 − 16, 44–49 `runtime.growslice(old = b, newLen = len + 40, oldCap = C,
num = 32, et = uint8)` with the contract `GrowsliceC Heap e2eU8Type_addr 1 S` (existing form,
instance esz 1; `old` = the first `len + 8` bytes of the block = `pre ++ epoch`), 50–54 restore,
55–62 spills and `memmove(nb + len + 8, Root.ptr, 32)`, 63–70 return `(nb, len + 40, C2, nil)`
with `nextSliceCap (len + 40) C ≤ C2`. The old block is unchanged (it keeps `pre ++ epoch`); the
new block is `pre ++ epoch ++ root ++ rest`.
-/

open Machine Runtime TestTarget E2e.Code
variable [Host]

namespace E2e

theorem cpw_e32 : ({ toBitVec := BitVec.zeroExtend 64 (BitVec.truncate 32 (32 : BitVec 64)) } : UInt64).toNat = 32 := by
  decide

theorem cpw_join (b : BitVec 64) (L : UInt64) (pre e8 : List UInt8) (hpre : pre.length = L.toNat)
    (he8 : e8.length = 8) (hb : L.toNat + 8 < 2 ^ 64) :
    Eq ((pre ++ e8).At b) = Eq (pre.At b) ⋆ Eq (e8.At (b + L.toBitVec)) :=
  at_app pre e8 (by rw [hpre]; apply BitVec.eq_of_toNat_eq; simp) (by omega)

theorem cpw_split2 (np : BitVec 64) (L : UInt64) (pre e8 tail : List UInt8) (hpre : pre.length = L.toNat)
    (he8 : e8.length = 8) (ht : 32 ≤ tail.length) (hb : pre.length + 8 + tail.length < 2 ^ 64) :
    Eq ((pre ++ e8 ++ tail).At np) = Eq (pre.At np) ⋆ Eq (e8.At (np + L.toBitVec))
      ⋆ Eq ((tail.take 32).At (np + L.toBitVec + 8)) ⋆ Eq ((tail.drop 32).At (np + L.toBitVec + 40)) := by
  have e : pre ++ e8 ++ tail = pre ++ (e8 ++ (tail.take 32 ++ tail.drop 32)) := by
    simp only [List.take_append_drop, List.append_assoc]
  rw [e, at_app pre _ (b := np + L.toBitVec) (by rw [hpre]; apply BitVec.eq_of_toNat_eq; simp)
      (by simp only [List.length_append, List.length_take, List.length_drop]; omega),
    at_app e8 _ (b := np + L.toBitVec + 8) (by rw [he8]; rfl)
      (by simp only [List.length_append, List.length_take, List.length_drop]; omega),
    at_app (tail.take 32) _ (b := np + L.toBitVec + 40)
      (by rw [List.length_take, Nat.min_eq_left ht]; bv_omega) (by simp only [List.length_take, List.length_drop]; omega)]
  simp only [Std.ExtHashMap.sep_assoc]

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- Tail from `L_7b`, second capacity test fails (`len + 8 ≤ C < len + 40`): second growslice. -/
theorem cpw_tail_grow (k : Nat) (hk : CpMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh CpMarshal k)
    (rsp0 r140 rbp0 ra L C : UInt64) (rcv b p : BitVec 64)
    (e8 root pre d0 l16 l24 l32 l72 spl rslot scratch : List UInt8) (he8 : e8.length = 8)
    (hroot : root.length = 32) (hpre : pre.length = L.toNat) (hd0 : d0.length = 8) (hl16 : l16.length = 8)
    (hl24 : l24.length = 8) (hl32 : l32.length = 8) (hl72 : l72.length = 8) (hspl : spl.length = 40)
    (hrs : rslot.length = 8)
    (S : Nat) (hsc : scratch.length = S) (R : DataMem → Prop) (Heap : Nat → DataMem → Prop) (avail : Nat)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := rsp0.toBitVec - 112 })
    (hrbp : s.regs.rbp = { toBitVec := rsp0.toBitVec - 8#64 }) (hr14 : s.regs.r14 = r140)
    (hrax : s.regs.rax.toBitVec = rcv) (hrbx : s.regs.rbx.toBitVec = b) (hrcx : s.regs.rcx = L)
    (hrdx : s.regs.rdx = { toBitVec := L.toBitVec + 8 }) (hrdi : s.regs.rdi = C)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At rsp0.toBitVec)
      ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (rsp0.toBitVec - 8))
      ⋆ Eq (l16.At (rsp0.toBitVec - 16)) ⋆ Eq (l24.At (rsp0.toBitVec - 24)) ⋆ Eq (l32.At (rsp0.toBitVec - 32))
      ⋆ Eq (e8.At (rsp0.toBitVec - 64)) ⋆ Eq (l72.At (rsp0.toBitVec - 72)) ⋆ Eq (spl.At (rsp0.toBitVec - 112))
      ⋆ Eq (rslot.At (rsp0.toBitVec - 120)) ⋆ Eq (scratch.At (rsp0.toBitVec - 120 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 p.toInt).At (rcv + 16)) ⋆ Eq ((Int.toBytes 8 32).At (rcv + 24)) ⋆ Eq (root.At p)
      ⋆ Eq (pre.At b) ⋆ Eq (d0.At (b + L.toBitVec)) ⋆ Heap avail ⋆ R)
    (hlo : L.toNat + 8 ≤ C.toNat) (hhi : C.toNat < L.toNat + 40)
    (hbud : 2 * nextSliceCap (L.toNat + 40) C.toNat + 8192 ≤ avail) (hmax : avail ≤ maxAlloc)
    (hgs : GrowsliceC Heap E2e.Data.e2eU8Type_addr 1 S) (hmm : MemmoveC S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec
        ∧ st.data.regs.rbx.toNat = L.toNat + 40 ∧ nextSliceCap (L.toNat + 40) C.toNat ≤ st.data.regs.rcx.toNat
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = rsp0 + 8 ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        ∃ (scr spl' rest : List UInt8) (av' : Nat), scr.length = S ∧ spl'.length = 40
          ∧ L.toNat + 40 + rest.length = st.data.regs.rcx.toNat ∧ av' + st.data.regs.rcx.toNat ≤ avail ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At rsp0.toBitVec)
          ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (rsp0.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 st.data.regs.rax.toBitVec.toInt).At (rsp0.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 st.data.regs.rcx.toBitVec.toInt).At (rsp0.toBitVec - 24))
          ⋆ Eq ((Int.toBytes 8 (L.toBitVec + 40).toInt).At (rsp0.toBitVec - 32))
          ⋆ Eq (e8.At (rsp0.toBitVec - 64))
          ⋆ Eq ((Int.toBytes 8 (L.toBitVec + 8).toInt).At (rsp0.toBitVec - 72))
          ⋆ Eq (spl'.At (rsp0.toBitVec - 112))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 63)).toBitVec.toInt).At (rsp0.toBitVec - 120))
          ⋆ Eq (scr.At (rsp0.toBitVec - 120 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (rcv + 16)) ⋆ Eq ((Int.toBytes 8 32).At (rcv + 24)) ⋆ Eq (root.At p)
          ⋆ Eq (pre.At b) ⋆ Eq (e8.At (b + L.toBitVec))
          ⋆ Eq (pre.At st.data.regs.rax.toBitVec) ⋆ Eq (e8.At (st.data.regs.rax.toBitVec + L.toBitVec))
          ⋆ Eq (root.At (st.data.regs.rax.toBitVec + L.toBitVec + 8))
          ⋆ Eq (rest.At (st.data.regs.rax.toBitVec + L.toBitVec + 40))
          ⋆ Heap av' ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 33)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp hrbp hr14 hrax hrbx hrcx hrdx hrdi h_mem ⊢
  subst rsp rbp r14 rcx rdx rdi hrax hrbx
  have := L.toNat_lt_size; have := C.toNat_lt_size; have := rsp0.toNat_lt_size; simp only [UInt64.size] at *
  have hnsc := nextSliceCap_le (L.toNat + 40) C.toNat (by omega)
  have hnge := nextSliceCap_ge (L.toNat + 40) C.toNat
  have hL48 : L.toNat + 40 ≤ 2 ^ 48 := by unfold maxAlloc at hmax; omega
  have hn40 := cpm_len40 L (by omega)
  kat hk CpMarshal 33
  kat hk CpMarshal 34
  apply load_step_at _ _ (rsp0.toBitVec - 64) _ _ e8 _ _ (by eaddr) (by ecancel) (by exact he8)
  kunfold
  kat hk CpMarshal 35
  rw [cpm_mul]
  apply store_step _ _ _ _ _ d0 _ _ (by ecancel) (by exact hd0)
  intro m6 H6
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl e8 he8] at H6
  kunfold
  kat hk CpMarshal 36
  apply load_step_at _ _ (rax.toBitVec + 16) _ _ (Int.toBytes 8 p.toInt) _ _ (by eaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk CpMarshal 37
  apply load_step_at _ _ (rax.toBitVec + 24) _ _ (Int.toBytes 8 32) _ _ (by eaddr) (by ecancel) (by rfl)
  simp only [show Int.ofBytes (Int.toBytes 8 32) = 32 by decide]
  kunfold
  kat hk CpMarshal 38
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk CpMarshal 39
  kat hk CpMarshal 40
  kat hk CpMarshal 41
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  -- second growslice call (directives 42–49)
  kat hk CpMarshal 42
  apply store_step_at _ _ (rsp0.toBitVec - 72) _ _ _ l72 _ _ (by eaddr) (by ecancel) (by exact hl72)
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  kat hk CpMarshal 43
  apply store_step_at _ _ (rsp0.toBitVec - 16) _ _ _ l16 _ _ (by eaddr) (by ecancel) (by exact hl16)
  intro m8 H8
  simp only [Width.bytes, Width.bits] at H8
  kunfold
  kat hk CpMarshal 44
  kat hk CpMarshal 45
  kat hk CpMarshal 46
  kat hk CpMarshal 47
  kat hk CpMarshal 48
  kat hk CpMarshal 49
  apply store_step_at _ _ (rsp0.toBitVec - 120) _ _ _ rslot _ _ (cpw_call _) (by ecancel) (by exact hrs)
  intro m9 H9
  simp only [Width.bytes, Width.bits] at H9
  kunfold
  rw [cpw_call] at *
  refine eventually_trans _ _ _ _ (hgs _ (Host.addrOf (k + 49 + 1)) (pre ++ e8) scratch spl avail _ (by decide) rfl
    ?gnum ?gold ?gcap ?gbud hmax ?glen hsc hspl
    (by dsimp only; rw [show rsp0.toBitVec - 120 + 8 = rsp0.toBitVec - 112 by bv_omega,
          cpw_join _ L pre e8 hpre he8 (by omega)]; ecancel)) ?_
  case gnum => dsimp only; rw [cpw_e32, hn40]; omega
  case gold => dsimp only; rw [cpw_e32, hn40, cpg_w C]; omega
  case gcap => dsimp only; rw [cpg_w C, hn40]; omega
  case gbud => dsimp only; rw [cpg_w C, hn40]; omega
  case glen => dsimp only; rw [cpw_e32, hn40]; simp only [List.length_append, hpre, he8]; omega
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, hrbx1, hnc1, hub1, stk1, spl1, tail, av1, hstk1, hspl1, htail, hav1,
    Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 hrbx1 hnc1 hub1 htail hav1 Hm1
  subst hpc1
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩,
    zmms1, flags1, mem1⟩ := d1
  simp only at hrsp1 hrbp1 hr141 hrbx1 hnc1 hub1 htail hav1 Hm1
  simp only [cpg_w C, hn40] at hnc1 hub1
  obtain ⟨hc1, hc2⟩ := growslice_cap_bounds (by decide) (Nat.le_trans (by simpa using hbud) hmax) hnc1 hub1
  simp only [List.length_append, hpre, he8, Nat.one_mul] at htail hav1
  have htl : 32 ≤ tail.length := by omega
  have ht32 : (tail.take 32).length = 32 := by simp only [List.length_take]; omega
  rw [cpw_ret] at hrsp1
  subst rsp1 r141 rbp1 rbx1
  rw [cpw_split2 rax1.toBitVec L pre e8 tail hpre he8 htl (by omega),
    cpw_join rbx.toBitVec L pre e8 hpre he8 (by omega),
    show rsp0.toBitVec - 120 + 8 = rsp0.toBitVec - 112 by bv_omega] at Hm1
  kat hk CpMarshal 50
  apply load_step_at _ _ (rsp0.toBitVec - 72) _ _ (Int.toBytes 8 (L.toBitVec + 8).toInt) _ _ (by eaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk CpMarshal 51
  apply load_step_at _ _ (rsp0.toBitVec - 16) _ _ (Int.toBytes 8 p.toInt) _ _ (by eaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk CpMarshal 52
  kat hk CpMarshal 53
  kat hk CpMarshal 54
  kat hk CpMarshal 55
  kat hk CpMarshal 56
  apply store_step_at _ _ (rsp0.toBitVec - 24) _ _ _ l24 _ _ (by eaddr) (by ecancel) (by exact hl24)
  intro m10 H10
  simp only [Width.bytes, Width.bits] at H10
  kunfold
  kat hk CpMarshal 57
  apply store_step_at _ _ (rsp0.toBitVec - 32) _ _ _ l32 _ _ (by eaddr) (by ecancel) (by exact hl32)
  intro m11 H11
  simp only [Width.bytes, Width.bits] at H11
  kunfold
  kat hk CpMarshal 58
  apply store_step_at _ _ (rsp0.toBitVec - 16) _ _ _ (Int.toBytes 8 p.toInt) _ _ (by eaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m12 H12
  simp only [Width.bytes, Width.bits] at H12
  kunfold
  kat hk CpMarshal 59
  kat hk CpMarshal 60
  kat hk CpMarshal 61
  kat hk CpMarshal 62
  apply store_step_at _ _ (rsp0.toBitVec - 120) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 49 + 1)).toBitVec.toInt) _ _
    (by eaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m13 H13
  simp only [Width.bytes, Width.bits] at H13
  kunfold
  try rw [cpw_call] at *
  rw [cpm_dst] at *
  refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (k + 62 + 1)) root (tail.take 32) stk1 _
    (by rw [hroot]; rfl) (by rw [hroot, ht32]) hstk1 (by dsimp only; ecancel)) ?_
  rintro ⟨e1, pc2⟩ ⟨hpc2, hrsp2, hr142, hrbp2, stk2, hstk2, Hm2⟩
  dsimp only at hpc2 hrsp2 hr142 hrbp2 Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := e1
  simp only at hrsp2 hr142 hrbp2 Hm2
  rw [cpw_ret] at hrsp2
  subst rsp2 r142 rbp2
  kat hk CpMarshal 63
  apply load_step_at _ _ (rsp0.toBitVec - 16) _ _ (Int.toBytes 8 rax1.toBitVec.toInt) _ _ (by eaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk CpMarshal 64
  apply load_step_at _ _ (rsp0.toBitVec - 32) _ _ (Int.toBytes 8 (L.toBitVec + 8 + 32).toInt) _ _ (by eaddr)
    (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk CpMarshal 65
  apply load_step_at _ _ (rsp0.toBitVec - 24) _ _ (Int.toBytes 8 rcx1.toBitVec.toInt) _ _ (by eaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk CpMarshal 66
  intro _
  kat hk CpMarshal 67
  intro _
  kat hk CpMarshal 68
  kat hk CpMarshal 69
  apply load_step_at _ _ (rsp0.toBitVec - 8) _ _ (Int.toBytes 8 rbp0.toBitVec.toInt) _ _ (by eaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk CpMarshal 70
  apply load_step_at _ _ rsp0.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by eaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, stk2, spl1, tail.drop 32, av1, hstk2, hspl1, ?hrest, ?hav, ?hmem⟩
  case hmem =>
    rw [show k + 62 + 1 = k + 63 from rfl] at Hm2
    rw [show L.toBitVec + 40 = L.toBitVec + 8 + 32 by bv_omega]
    ecancel
  case hrest => show L.toNat + 40 + (tail.drop 32).length = rcx1.toNat; simp only [List.length_drop]; omega
  case hav => show av1 + rcx1.toNat ≤ avail; omega
  all_goals first
    | exact trivial
    | with_reducible rfl
    | (exact cpm_len40 L (by omega))
    | (exact hnc1)
    | (dsimp only; omega)
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (apply UInt64.toBitVec_inj.mp; eaddr)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- From `L_7b` with `len + 8 ≤ C < len + 40` to the entry of the second `runtime.growslice` call
(directive 49): the exact call state. No runtime contract is used. -/
theorem cpw_tail_grow_call (k : Nat) (hk : CpMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh CpMarshal k)
    (rsp0 r140 rbp0 ra L C : UInt64) (rcv b p : BitVec 64)
    (e8 root pre d0 l16 l24 l32 l72 spl rslot scratch : List UInt8) (he8 : e8.length = 8)
    (hroot : root.length = 32) (hpre : pre.length = L.toNat) (hd0 : d0.length = 8) (hl16 : l16.length = 8)
    (hl24 : l24.length = 8) (hl32 : l32.length = 8) (hl72 : l72.length = 8) (hspl : spl.length = 40)
    (hrs : rslot.length = 8)
    (S : Nat) (hsc : scratch.length = S) (R : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := rsp0.toBitVec - 112 })
    (hrbp : s.regs.rbp = { toBitVec := rsp0.toBitVec - 8#64 }) (hr14 : s.regs.r14 = r140)
    (hrax : s.regs.rax.toBitVec = rcv) (hrbx : s.regs.rbx.toBitVec = b) (hrcx : s.regs.rcx = L)
    (hrdx : s.regs.rdx = { toBitVec := L.toBitVec + 8 }) (hrdi : s.regs.rdi = C)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At rsp0.toBitVec)
      ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (rsp0.toBitVec - 8))
      ⋆ Eq (l16.At (rsp0.toBitVec - 16)) ⋆ Eq (l24.At (rsp0.toBitVec - 24)) ⋆ Eq (l32.At (rsp0.toBitVec - 32))
      ⋆ Eq (e8.At (rsp0.toBitVec - 64)) ⋆ Eq (l72.At (rsp0.toBitVec - 72)) ⋆ Eq (spl.At (rsp0.toBitVec - 112))
      ⋆ Eq (rslot.At (rsp0.toBitVec - 120)) ⋆ Eq (scratch.At (rsp0.toBitVec - 120 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 p.toInt).At (rcv + 16)) ⋆ Eq ((Int.toBytes 8 32).At (rcv + 24)) ⋆ Eq (root.At p)
      ⋆ Eq (pre.At b) ⋆ Eq (d0.At (b + L.toBitVec)) ⋆ R)
    (hlo : L.toNat + 8 ≤ C.toNat) (hhi : C.toNat < L.toNat + 40) (hL : L.toNat + 40 ≤ 2 ^ 48) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = label "runtime.growslice" ∧ st.data.regs.rsp = { toBitVec := rsp0.toBitVec - 120 }
        ∧ st.data.regs.rbp = { toBitVec := rsp0.toBitVec - 8#64 } ∧ st.data.regs.r14 = r140
        ∧ st.data.regs.rax.toBitVec = b ∧ st.data.regs.rbx.toNat = L.toNat + 40 ∧ st.data.regs.rcx = C
        ∧ st.data.regs.rdi.toNat = 32 ∧ st.data.regs.rsi.toBitVec = E2e.Data.e2eU8Type_addr ∧
        (Eq ((Int.toBytes 8 (Host.addrOf (k + 50)).toBitVec.toInt).At (rsp0.toBitVec - 120))
          ⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At rsp0.toBitVec)
          ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (rsp0.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (rsp0.toBitVec - 16)) ⋆ Eq (l24.At (rsp0.toBitVec - 24))
          ⋆ Eq (l32.At (rsp0.toBitVec - 32))
          ⋆ Eq (e8.At (rsp0.toBitVec - 64)) ⋆ Eq ((Int.toBytes 8 (L.toBitVec + 8).toInt).At (rsp0.toBitVec - 72))
          ⋆ Eq (spl.At (rsp0.toBitVec - 112)) ⋆ Eq (scratch.At (rsp0.toBitVec - 120 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (rcv + 16)) ⋆ Eq ((Int.toBytes 8 32).At (rcv + 24)) ⋆ Eq (root.At p)
          ⋆ Eq (pre.At b) ⋆ Eq (e8.At (b + L.toBitVec)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 33)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp hrbp hr14 hrax hrbx hrcx hrdx hrdi h_mem ⊢
  subst rsp rbp r14 rcx rdx rdi hrax hrbx
  have := L.toNat_lt_size; have := C.toNat_lt_size; have := rsp0.toNat_lt_size; simp only [UInt64.size] at *
  have hn40 := cpm_len40 L (by omega)
  kat hk CpMarshal 33
  kat hk CpMarshal 34
  apply load_step_at _ _ (rsp0.toBitVec - 64) _ _ e8 _ _ (by eaddr) (by ecancel) (by exact he8)
  kunfold
  kat hk CpMarshal 35
  rw [cpm_mul]
  apply store_step _ _ _ _ _ d0 _ _ (by ecancel) (by exact hd0)
  intro m6 H6
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl e8 he8] at H6
  kunfold
  kat hk CpMarshal 36
  apply load_step_at _ _ (rax.toBitVec + 16) _ _ (Int.toBytes 8 p.toInt) _ _ (by eaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk CpMarshal 37
  apply load_step_at _ _ (rax.toBitVec + 24) _ _ (Int.toBytes 8 32) _ _ (by eaddr) (by ecancel) (by rfl)
  simp only [show Int.ofBytes (Int.toBytes 8 32) = 32 by decide]
  kunfold
  kat hk CpMarshal 38
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk CpMarshal 39
  kat hk CpMarshal 40
  kat hk CpMarshal 41
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  -- second growslice call (directives 42–49)
  kat hk CpMarshal 42
  apply store_step_at _ _ (rsp0.toBitVec - 72) _ _ _ l72 _ _ (by eaddr) (by ecancel) (by exact hl72)
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  kat hk CpMarshal 43
  apply store_step_at _ _ (rsp0.toBitVec - 16) _ _ _ l16 _ _ (by eaddr) (by ecancel) (by exact hl16)
  intro m8 H8
  simp only [Width.bytes, Width.bits] at H8
  kunfold
  kat hk CpMarshal 44
  kat hk CpMarshal 45
  kat hk CpMarshal 46
  kat hk CpMarshal 47
  kat hk CpMarshal 48
  kat hk CpMarshal 49
  apply store_step_at _ _ (rsp0.toBitVec - 120) _ _ _ rslot _ _ (cpw_call _) (by ecancel) (by exact hrs)
  intro m9 H9
  simp only [Width.bytes, Width.bits] at H9
  kunfold
  rw [cpw_call] at *
  apply Eventually.done
  rw [show k + 49 + 1 = k + 50 from rfl] at H9
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, rfl, ?_, rfl, by ecancel⟩
  · dsimp only; exact hn40
  · dsimp only; exact cpw_e32

end E2e
