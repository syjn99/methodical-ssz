import Fk.LcLoop
import Fk.NeMarshal
import Fk.Bump
import Fk.LcSize
import Fk.LcAcceptSpec

/-!
# ListC.MarshalSSZTo, fast path, on Kraken main

`len(c.Items) = n ≤ 4`, every item non-nil with `len ≤ 16`, `cap(dst)` enough:
the code writes the offset 4, then (loop 2) the n element offsets
`4n + Σ_{j<i} (4 + 8 len_j)`, then (loop 3) for each element the offset 4 and
its words (inner loop). Loop 1 only touches each item (Go nil check).
The items array and the item objects are read-only here; the premise gives
them as one predicate `Objs` with an accessor `hObjs` (per element: the
pointer in the array, the element header, the words).
-/

open Fk Fk.Code Fv1 EthLib.Serialization.Ssz
variable [Host]

theorem sep_mono_right' {P Q Q' : DataMem → Prop} {m : DataMem} (hQ : ∀ m, Q m → Q' m)
    (h : (P ⋆ Q) m) : (P ⋆ Q') m := by
  obtain ⟨a, b, hu, hi, hp, hq⟩ := h
  exact ⟨a, b, hu, hi, hp, hQ b hq⟩

/-- A fact about a separated part holds with `True` around. -/
theorem sep_true_of_part {P C : DataMem → Prop} {m : DataMem} (h : (P ⋆ fun _ => True) m)
    (hP : ∀ m', P m' → (C ⋆ fun _ => True) m') : (C ⋆ fun _ => True) m := by
  have h1 := sep_mono_left hP h
  rw [Std.ExtHashMap.sep_assoc] at h1
  exact sep_mono_right' (fun _ _ => trivial) h1

/-- The registers loop 1 keeps. -/
structure Keep1 (a b : Reg64s) : Prop where
  rax : b.rax = a.rax
  rbx : b.rbx = a.rbx
  rdx : b.rdx = a.rdx
  rdi : b.rdi = a.rdi
  rsp : b.rsp = a.rsp
  rbp : b.rbp = a.rbp
  r8 : b.r8 = a.r8
  r9 : b.r9 = a.r9
  r14 : b.r14 = a.r14

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
theorem lcm1_iter (k : Nat) (hk : ListCMarshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListCMarshalSSZTo k) (A p q : BitVec 64) (n i : Nat) (hn : n ≤ 4) (hi : i < n)
    (s0 : MachineData) (hrcx : s0.regs.rcx.toNat = i) (hr8 : s0.regs.r8.toNat = n) (hr9 : s0.regs.r9.toBitVec = A)
    (hm : (Eq ((Int.toBytes 8 p.toInt).At (A + BitVec.ofNat 64 (8 * i)))
      ⋆ Eq (((Int.toBytes 8 q.toInt).take 1).At p) ⋆ fun _ => True) s0.dmem) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 36) ∧ st.data.regs.rcx.toNat = i + 1 ∧ Keep1 s0.regs st.data.regs
        ∧ st.data.dmem = s0.dmem)
      ⟨s0, Host.addrOf (k + 36)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s0
  simp only at hrcx hr8 hr9 hm ⊢
  subst hr9
  have := rcx.toNat_lt_size; have := r8.toNat_lt_size; simp only [UInt64.size] at *
  kat hk ListCMarshalSSZTo 36
  kat hk ListCMarshalSSZTo 37
  kat hk ListCMarshalSSZTo 38
  rw [jl_val _ _ (by simp; omega) (by simp; omega)]
  simp only [show decide (rcx.toBitVec.toNat < r8.toBitVec.toNat) = true by simp; omega, ↓reduceIte, Effects.All]
  klabel hk hf ListCMarshalSSZTo 30
  kat hk ListCMarshalSSZTo 30
  kat hk ListCMarshalSSZTo 31
  rw [show r9.toBitVec + rcx.toBitVec * 8#64 = r9.toBitVec + BitVec.ofNat 64 (8 * i) by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_mul]; omega]
  apply load_step _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk ListCMarshalSSZTo 32
  apply load_step _ _ _ _ ((Int.toBytes 8 q.toInt).take 1) _ _ (by ecancel) (by simp [Int.toBytes_length])
  kunfold
  intro _
  kat hk ListCMarshalSSZTo 33
  kat hk ListCMarshalSSZTo 34
  kat hk ListCMarshalSSZTo 35
  apply Eventually.done
  refine ⟨rfl, ?_, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  show (rcx.toBitVec + 1).toNat = i + 1; simp [BitVec.toNat_add]; omega

theorem Keep1.trans {a b c : Reg64s} (h1 : Keep1 a b) (h2 : Keep1 b c) : Keep1 a c :=
  ⟨h2.rax.trans h1.rax, h2.rbx.trans h1.rbx, h2.rdx.trans h1.rdx, h2.rdi.trans h1.rdi, h2.rsp.trans h1.rsp,
   h2.rbp.trans h1.rbp, h2.r8.trans h1.r8, h2.r9.trans h1.r9, h2.r14.trans h1.r14⟩

theorem Keep1.refl (a : Reg64s) : Keep1 a a := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
theorem lcm1_loop (k : Nat) (hk : ListCMarshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListCMarshalSSZTo k) (A : BitVec 64) (ps qs : List (BitVec 64)) (n : Nat) (hn : n ≤ 4)
    (hps : ps.length = n) (hqs : qs.length = n) :
    ∀ j i (s0 : MachineData), i + j = n → s0.regs.rcx.toNat = i → s0.regs.r8.toNat = n → s0.regs.r9.toBitVec = A →
    (∀ i' (hi' : i' < n), (Eq ((Int.toBytes 8 (ps[i']'(by omega)).toInt).At (A + BitVec.ofNat 64 (8 * i')))
      ⋆ Eq (((Int.toBytes 8 (qs[i']'(by omega)).toInt).take 1).At (ps[i']'(by omega))) ⋆ fun _ => True) s0.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 39) ∧ Keep1 s0.regs st.data.regs ∧ st.data.dmem = s0.dmem)
      ⟨s0, Host.addrOf (k + 36)⟩ := by
  intro j
  induction j with
  | zero =>
    intro i s0 hij hrcx hr8 _ _
    obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s0
    simp only at hrcx hr8 ⊢
    have hc : rcx = r8 := UInt64.toNat_inj.mp (by omega)
    subst hc
    kat hk ListCMarshalSSZTo 36
    kat hk ListCMarshalSSZTo 37
    kat hk ListCMarshalSSZTo 38
    rw [jl_val _ _ (by simp; omega) (by simp; omega)]
    simp only [show decide (rcx.toBitVec.toNat < rcx.toBitVec.toNat) = false by simp, Bool.false_eq_true,
      ↓reduceIte, Effects.All]
    apply Eventually.done
    exact ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  | succ j ih =>
    intro i s0 hij hrcx hr8 hr9 hacc
    refine eventually_trans _ _ _ _ (lcm1_iter k hk hf A (ps[i]'(by omega)) (qs[i]'(by omega)) n i hn (by omega) s0
      hrcx hr8 hr9 (hacc i (by omega))) ?_
    rintro ⟨d, pc⟩ ⟨hpc, h1, hk1, h2⟩
    dsimp only at hpc h1 hk1 h2
    subst hpc
    have := ih (i + 1) d (by omega) h1 (by rw [hk1.r8]; exact hr8) (by rw [hk1.r9]; exact hr9) (by rw [h2]; exact hacc)
    refine eventually_trans _ _ _ _ this ?_
    rintro st ⟨g1, g2, g3⟩
    exact Eventually.done _ ⟨g1, hk1.trans g2, g3.trans h2⟩

theorem lcm_tb4 (v : Nat) (h : v < 2 ^ 32) :
    Int.toBytes 4 (BitVec.truncate 32 (BitVec.ofNat 64 v)).toInt = (uintBytes 4 v).toList := by
  have := toBytes_ofInt_ofBytes 32 4 rfl (uintBytes 4 v).toList (by simp [Fv.uintBytes_size])
  rw [ofBytes_uintBytes4 v h] at this
  rw [← this]; congr 3
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofInt]
theorem lcm_len (l : Nat) (h : l < 2 ^ 63) : (BitVec.ofNat 64 l).toInt = (l : Int) := by
  rw [BitVec.toInt_eq_toNat_of_lt (by simp; omega)]; simp; omega
theorem mix4_split (ws d : List UInt8) (i : Nat) :
    ws.take (4 * i) ++ d.drop (4 * i) = ws.take (4 * i) ++ ((d.drop (4 * i)).take 4 ++ d.drop (4 * i + 4)) := by
  rw [← List.drop_drop, List.take_append_drop]
theorem mix4_step (ws d : List UInt8) (i : Nat) :
    ws.take (4 * i) ++ ((ws.drop (4 * i)).take 4 ++ d.drop (4 * i + 4)) = ws.take (4 * (i + 1)) ++ d.drop (4 * (i + 1)) := by
  rw [← List.append_assoc, ← List.take_add, show 4 * i + 4 = 4 * (i + 1) by omega]

theorem lcStart_lt (gs : List ListU64) (hn : gs.length ≤ 4) (hgs : ∀ g ∈ gs, g.ok) (i : Nat) :
    lcStart gs i ≤ 16 + 132 * 4 := by
  have := lcStart_le gs i
  have h2 : lcStart gs gs.length ≤ 4 * gs.length + 132 * gs.length := by
    simp only [lcStart, List.take_length]
    have : ∀ l : List ListU64, (∀ g ∈ l, g.ok) → (l.map fun g => 4 + 8 * g.l.length).sum ≤ 132 * l.length := by
      intro l hl; induction l with
      | nil => simp
      | cons g l ih =>
        have hg : g.l.length ≤ 16 := hl g (by simp)
        have := ih (fun x hx => hl x (by simp [hx]))
        simp; omega
    have := this gs hgs; omega
  omega

/-- The registers loops 2 and 3 keep. -/
structure Keep2 (a b : Reg64s) : Prop where
  rax : b.rax = a.rax
  rbx : b.rbx = a.rbx
  rdi : b.rdi = a.rdi
  rsp : b.rsp = a.rsp
  rbp : b.rbp = a.rbp
  r14 : b.r14 = a.r14

theorem Keep2.trans {a b c : Reg64s} (h1 : Keep2 a b) (h2 : Keep2 b c) : Keep2 a c :=
  ⟨h2.rax.trans h1.rax, h2.rbx.trans h1.rbx, h2.rdi.trans h1.rdi, h2.rsp.trans h1.rsp, h2.rbp.trans h1.rbp,
   h2.r14.trans h1.r14⟩

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 200000 in
theorem lcm2_iter (k : Nat) (hk : ListCMarshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListCMarshalSSZTo k) (A b : BitVec 64) (ps : List (BitVec 64)) (gs : List ListU64)
    (hn : gs.length ≤ 4) (hps : ps.length = gs.length) (hgs : ∀ g ∈ gs, g.ok)
    (d : List UInt8) (hd : d.length = 4 * gs.length) (L cap : Nat) (hcap : L + 4 + 4 * gs.length ≤ cap)
    (hcap63 : cap < 2 ^ 63) (i : Nat) (hi : i < gs.length) (Objs R : DataMem → Prop)
    (hObjs : ∀ m, Objs m → ∀ j (hj : j < gs.length),
      (Eq ((Int.toBytes 8 (ps[j]'(by omega)).toInt).At (A + BitVec.ofNat 64 (8 * j)))
        ⋆ Eq ((Int.toBytes 8 (gs[j].l.length : Int)).At ((ps[j]'(by omega)) + 8)) ⋆ fun _ => True) m)
    (s0 : MachineData) (hrcx : s0.regs.rcx.toNat = i) (hr10 : s0.regs.r10.toNat = gs.length)
    (hr9 : s0.regs.r9.toBitVec = A) (hr8 : s0.regs.r8.toBitVec = BitVec.ofNat 64 (lcStart gs i))
    (hrdx : s0.regs.rdx.toNat = L + 4 + 4 * i) (hrbx : s0.regs.rbx.toBitVec = b) (hrdi : s0.regs.rdi.toNat = cap)
    (h_mem : s0.dmem =⋆ Eq (((offTab (4 * gs.length) (gs.map luEncode)).take (4 * i) ++ d.drop (4 * i)).At
      (b + BitVec.ofNat 64 (L + 4))) ⋆ Objs ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 62) ∧ st.data.regs.rcx.toNat = i + 1
        ∧ st.data.regs.r10 = s0.regs.r10 ∧ st.data.regs.r9 = s0.regs.r9
        ∧ st.data.regs.r8.toBitVec = BitVec.ofNat 64 (lcStart gs (i + 1))
        ∧ st.data.regs.rdx.toNat = L + 4 + 4 * (i + 1) ∧ Keep2 s0.regs st.data.regs
        ∧ (Eq (((offTab (4 * gs.length) (gs.map luEncode)).take (4 * (i + 1)) ++ d.drop (4 * (i + 1))).At
          (b + BitVec.ofNat 64 (L + 4))) ⋆ Objs ⋆ R) st.data.dmem)
      ⟨s0, Host.addrOf (k + 62)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s0
  simp only at h_mem hrcx hr10 hr9 hr8 hrdx hrbx hrdi ⊢
  subst hr9 hrbx
  have := rcx.toNat_lt_size; have := r10.toNat_lt_size; have := rdx.toNat_lt_size; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *
  have hst := lcStart_lt gs hn hgs i
  have hacc := sep_true_of_part (sep_true (P := Objs) (by ecancel)) (fun m' h => hObjs m' h i hi)
  generalize hp : ps[i]'(by omega) = p at hacc
  kat hk ListCMarshalSSZTo 62
  kat hk ListCMarshalSSZTo 63
  kat hk ListCMarshalSSZTo 64
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.signed] at h
    exact jge_false rcx.toBitVec r10.toBitVec (by simp; omega) (by simp; omega) (by simpa using h)
  simp only [Effects.All]
  kat hk ListCMarshalSSZTo 65
  kat hk ListCMarshalSSZTo 66
  rw [idx8' _ _ i (by simpa using hrcx) (by omega)]
  apply load_step _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk ListCMarshalSSZTo 67
  kat hk ListCMarshalSSZTo 68
  kat hk ListCMarshalSSZTo 69
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf ListCMarshalSSZTo 56
  kat hk ListCMarshalSSZTo 56
  kat hk ListCMarshalSSZTo 57
  have htl : ((offTab (4 * gs.length) (gs.map luEncode)).drop (4 * i)).take 4 = (uintBytes 4 (lcStart gs i)).toList := by
    rw [offTab_get _ _ i (by simp; omega), lc_sizes]; rfl
  have hot := offTab_length (gs.map luEncode) (4 * gs.length)
  simp only [List.length_map] at hot
  rw [mix4_split, Mem.At_append_sep _ _ _ (by simp; omega), Mem.At_append_sep _ _ _ (by simp; omega)] at h_mem
  simp only [List.length_take, List.length_drop, hot, hd, Nat.min_eq_left (show 4 * i ≤ 4 * gs.length by omega),
    Nat.min_eq_left (show 4 ≤ 4 * gs.length - 4 * i by omega)] at h_mem
  rw [add4_neg4, show rbx.toBitVec + rdx.toBitVec = rbx.toBitVec + BitVec.ofNat 64 (L + 4) + BitVec.ofNat 64 (4 * i) by
    rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega]
  apply store_step _ _ _ _ _ ((d.drop (4 * i)).take 4) _ _ (by ecancel) (by simp; omega)
  intro m1 H1
  have hv : Int.toBytes 4 (BitVec.extractLsb' 0 32 r8.toBitVec).toInt = (uintBytes 4 (lcStart gs i)).toList := by
    rw [hr8, ← lcm_tb4 _ (by omega)]; congr 3
  simp only [Width.bytes, Width.bits, hv, ← htl] at H1
  kunfold
  kat hk ListCMarshalSSZTo 58
  have hacc2 := sep_true_of_part (sep_true (P := Objs) (by ecancel)) (fun m' h => hObjs m' h i hi)
  rw [hp, ← lcm_len _ (by have : gs[i].l.length ≤ 16 := hgs _ (List.getElem_mem hi); omega)] at hacc2
  apply load_step _ _ _ _ (Int.toBytes 8 (BitVec.ofNat 64 gs[i].l.length).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk ListCMarshalSSZTo 59
  kat hk ListCMarshalSSZTo 60
  kat hk ListCMarshalSSZTo 61
  apply Eventually.done
  refine ⟨rfl, ?_, rfl, rfl, ?_, ?_, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · show (rcx.toBitVec + 1).toNat = i + 1; simp [BitVec.toNat_add]; omega
  · show r8.toBitVec + BitVec.ofNat 64 gs[i].l.length * 8#64 + 4 = _
    rw [hr8, lcStart_succ gs i hi]; apply BitVec.eq_of_toNat_eq
    have : gs[i].l.length ≤ 16 := hgs _ (List.getElem_mem hi)
    simp [BitVec.toNat_add, BitVec.toNat_mul]; omega
  · show (4 + rdx.toBitVec).toNat = _; simp [BitVec.toNat_add]; omega
  · dsimp only
    rw [← mix4_step, Mem.At_append_sep _ _ _ (by simp; omega), Mem.At_append_sep _ _ _ (by simp; omega)]
    simp only [List.length_take, List.length_drop, hot, hd, Nat.min_eq_left (show 4 * i ≤ 4 * gs.length by omega),
      Nat.min_eq_left (show 4 ≤ 4 * gs.length - 4 * i by omega)]
    ecancel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 200000 in
theorem lcm2_loop (k : Nat) (hk : ListCMarshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListCMarshalSSZTo k) (A b : BitVec 64) (ps : List (BitVec 64)) (gs : List ListU64)
    (hn : gs.length ≤ 4) (hps : ps.length = gs.length) (hgs : ∀ g ∈ gs, g.ok)
    (d : List UInt8) (hd : d.length = 4 * gs.length) (L cap : Nat) (hcap : L + 4 + 4 * gs.length ≤ cap)
    (hcap63 : cap < 2 ^ 63) (Objs R : DataMem → Prop)
    (hObjs : ∀ m, Objs m → ∀ j (hj : j < gs.length),
      (Eq ((Int.toBytes 8 (ps[j]'(by omega)).toInt).At (A + BitVec.ofNat 64 (8 * j)))
        ⋆ Eq ((Int.toBytes 8 (gs[j].l.length : Int)).At ((ps[j]'(by omega)) + 8)) ⋆ fun _ => True) m) :
    ∀ j i (s0 : MachineData), i + j = gs.length →
    s0.regs.rcx.toNat = i → s0.regs.r10.toNat = gs.length → s0.regs.r9.toBitVec = A →
    s0.regs.r8.toBitVec = BitVec.ofNat 64 (lcStart gs i) → s0.regs.rdx.toNat = L + 4 + 4 * i →
    s0.regs.rbx.toBitVec = b → s0.regs.rdi.toNat = cap →
    (s0.dmem =⋆ Eq (((offTab (4 * gs.length) (gs.map luEncode)).take (4 * i) ++ d.drop (4 * i)).At
      (b + BitVec.ofNat 64 (L + 4))) ⋆ Objs ⋆ R) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 90) ∧ st.data.regs.rdx.toNat = L + 4 + 4 * gs.length
        ∧ Keep2 s0.regs st.data.regs
        ∧ (Eq ((offTab (4 * gs.length) (gs.map luEncode)).At (b + BitVec.ofNat 64 (L + 4))) ⋆ Objs ⋆ R)
          st.data.dmem)
      ⟨s0, Host.addrOf (k + 62)⟩ := by
  intro j
  induction j with
  | zero =>
    intro i s0 hij hrcx hr10 _ _ hrdx _ _ h_mem
    obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s0
    simp only at hrcx hr10 hrdx h_mem ⊢
    have hc : rcx = r10 := UInt64.toNat_inj.mp (by omega)
    subst hc
    have hot := offTab_length (gs.map luEncode) (4 * gs.length)
    simp only [List.length_map] at hot
    kat hk ListCMarshalSSZTo 62
    kat hk ListCMarshalSSZTo 63
    kat hk ListCMarshalSSZTo 64
    split
    case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    simp only [Effects.All]
    klabel hk hf ListCMarshalSSZTo 90
    apply Eventually.done
    refine ⟨rfl, by rw [hrdx]; omega, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    have hi : i = gs.length := by omega
    subst hi
    rw [List.take_of_length_le (by omega), List.drop_of_length_le (by omega), List.append_nil] at h_mem
    exact h_mem
  | succ j ih =>
    intro i s0 hij hrcx hr10 hr9 hr8 hrdx hrbx hrdi h_mem
    refine eventually_trans _ _ _ _ (lcm2_iter k hk hf A b ps gs hn hps hgs d hd L cap hcap hcap63 i (by omega)
      Objs R hObjs s0 hrcx hr10 hr9 hr8 hrdx hrbx hrdi h_mem) ?_
    rintro ⟨s', pc⟩ ⟨hpc, h1, h2, h3, h4, h5, hk2, h6⟩
    dsimp only at hpc h1 h2 h3 h4 h5 hk2 h6
    subst hpc
    have := ih (i + 1) s' (by omega) h1 (by rw [h2]; exact hr10) (by rw [h3]; exact hr9) h4 h5
      (by rw [hk2.rbx]; exact hrbx) (by rw [hk2.rdi]; exact hrdi) h6
    refine eventually_trans _ _ _ _ this ?_
    rintro st ⟨g1, g2, g3, g4⟩
    exact Eventually.done _ ⟨g1, g2, hk2.trans g3, g4⟩

/-! Loop 3, inner: the inlined ListU64 element loop (head `L_213`, directive 149): rcx = index, r11 = len, r10 = element pointer. -/

/-- Registers the inner loop keeps (the outer loop's state). -/
structure Keep3 (a b : Reg64s) : Prop where
  rax : b.rax = a.rax
  r8 : b.r8 = a.r8
  r9 : b.r9 = a.r9
  r14 : b.r14 = a.r14

theorem Keep3.trans {a b c : Reg64s} (h1 : Keep3 a b) (h2 : Keep3 b c) : Keep3 a c :=
  ⟨h2.rax.trans h1.rax, h2.r8.trans h1.r8, h2.r9.trans h1.r9, h2.r14.trans h1.r14⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem lcm3_iter (k : Nat) (hk : ListCMarshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListCMarshalSSZTo k)
    (bs d : List UInt8) (n : Nat) (hn : n ≤ 16) (hbs : bs.length = 8 * n) (hd : d.length = 8 * n) (i : Nat) (hi : i < n)
    (b p : BitVec 64) (L cap : Nat) (hcap : L + 4 + 8 * n ≤ cap) (hcap63 : cap < 2 ^ 63)
    (R : DataMem → Prop) (s : MachineData)
    (hrax : s.regs.rcx.toNat = i) (hrbx : s.regs.rbx.toBitVec = b) (hrdx : s.regs.rdx.toNat = L + 4 + 8 * i)
    (hrdi : s.regs.rdi.toNat = cap) (hr8 : s.regs.r11.toNat = n) (hr9 : s.regs.r10.toBitVec = p)
    (sp bp : UInt64) (hrsp : s.regs.rsp = sp) (hrbp : s.regs.rbp = bp)
    (h_mem : s.dmem =⋆ Eq (bs.At p) ⋆ Eq ((bs.take (8 * i) ++ d.drop (8 * i)).At (b + BitVec.ofNat 64 (L + 4))) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 149) ∧ st.data.regs.rcx.toNat = i + 1 ∧ st.data.regs.rbx.toBitVec = b
        ∧ st.data.regs.rdx.toNat = L + 4 + 8 * (i + 1) ∧ st.data.regs.rdi.toNat = cap ∧ st.data.regs.r11.toNat = n
        ∧ st.data.regs.r10.toBitVec = p ∧ st.data.regs.rsp = sp ∧ st.data.regs.rbp = bp ∧ Keep3 s.regs st.data.regs
        ∧ (Eq (bs.At p) ⋆ Eq ((bs.take (8 * (i + 1)) ++ d.drop (8 * (i + 1))).At (b + BitVec.ofNat 64 (L + 4))) ⋆ R)
          st.data.dmem)
      ⟨s, Host.addrOf (k + 149)⟩ := by
  obtain ⟨⟨xrax, rbx, rax, rdx, rsi, rdi, rsp, rbp, xr8, xr9, r9, r8, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hrax hrbx hrdx hrdi hr8 hr9 hrsp hrbp ⊢
  subst hrbx hr9 hrsp hrbp
  have := rax.toNat_lt_size; have := rdx.toNat_lt_size; have := rdi.toNat_lt_size; have := r8.toNat_lt_size
  simp only [UInt64.size] at *
  have hlen : bs.length < 2 ^ 64 := by omega
  rw [block_split bs r9.toBitVec (8 * i) (by omega) hlen, mix_split bs d i,
    Mem.At_append_sep _ _ _ (by simp; omega), Mem.At_append_sep _ _ _ (by simp; omega)] at h_mem
  simp only [List.length_take, List.length_drop, hbs, hd, Nat.min_eq_left (show 8 * i ≤ 8 * n by omega),
    Nat.min_eq_left (show 8 ≤ 8 * n - 8 * i by omega)] at h_mem
  kat hk ListCMarshalSSZTo 149
  kat hk ListCMarshalSSZTo 150
  kat hk ListCMarshalSSZTo 151
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.signed] at h
    exact jge_false rax.toBitVec r8.toBitVec (by simp; omega) (by simp; omega) (by simpa using h)
  simp only [Effects.All]
  kat hk ListCMarshalSSZTo 152
  kat hk ListCMarshalSSZTo 153
  rw [idx8' _ _ i (by simpa using hrax) (by omega)]
  apply load_step _ _ _ _ ((bs.drop (8 * i)).take 8) _ _ (by ecancel) (by simp; omega)
  kunfold
  kat hk ListCMarshalSSZTo 154
  kat hk ListCMarshalSSZTo 155
  split
  case isFalse h =>
    exfalso; simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    have := lum_room rdx.toBitVec rdi.toBitVec L n i cap (by simpa using hrdx) hi (by simpa using hrdi) hcap hcap63
    simp at h; omega
  simp only [Effects.All]
  klabel hk hf ListCMarshalSSZTo 146
  kat hk ListCMarshalSSZTo 146
  kat hk ListCMarshalSSZTo 147
  rw [lum_addr _ _ L i (by simpa using hrdx) (by omega)]
  apply store_step _ _ _ _ _ ((d.drop (8 * i)).take 8) _ _ (by ecancel) (by simp; omega)
  intro m1 H1
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl _ (show ((bs.drop (8 * i)).take 8).length = 8 by simp; omega)] at H1
  kunfold
  kat hk ListCMarshalSSZTo 148
  apply Eventually.done
  refine ⟨rfl, ?_, rfl, ?_, hrdi, hr8, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  · exact inc_toNat16 _ i (by simpa using hrax) (by omega)
  · exact lum_rdx _ L i (by simpa using hrdx) (by omega)
  · dsimp only
    rw [← mix_step bs d i, Mem.At_append_sep _ _ _ (by simp; omega), Mem.At_append_sep _ _ _ (by simp; omega),
      block_split bs r9.toBitVec (8 * i) (by omega) hlen]
    simp only [List.length_take, List.length_drop, hbs, hd, Nat.min_eq_left (show 8 * i ≤ 8 * n by omega),
      Nat.min_eq_left (show 8 ≤ 8 * n - 8 * i by omega)]
    (try simp only [BitVec.ofNat_eq_ofNat] at H1 ⊢)
    ecancel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem lcm3_exit (k : Nat) (hk : ListCMarshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListCMarshalSSZTo k) (P : MachineState → Prop) (s : MachineData)
    (hrr : s.regs.rcx = s.regs.r11)
    (hP : ∀ f : StatusFlags, P ⟨⟨s.regs, s.zmms, f, s.dmem⟩, Host.addrOf (k + 175)⟩) :
    Eventually (step1 Host.exe) P ⟨s, Host.addrOf (k + 149)⟩ := by
  obtain ⟨⟨xrax, rbx, rax, rdx, rsi, rdi, rsp, rbp, xr8, xr9, r9, r8, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrr hP ⊢
  subst hrr
  kat hk ListCMarshalSSZTo 149
  kat hk ListCMarshalSSZTo 150
  kat hk ListCMarshalSSZTo 151
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
  simp only [Effects.All]
  klabel hk hf ListCMarshalSSZTo 175
  exact Eventually.done _ (hP _)

theorem lcm3_loop (k : Nat) (hk : ListCMarshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListCMarshalSSZTo k)
    (bs d : List UInt8) (n : Nat) (hn : n ≤ 16) (hbs : bs.length = 8 * n) (hd : d.length = 8 * n)
    (b p : BitVec 64) (L cap : Nat) (hcap : L + 4 + 8 * n ≤ cap) (hcap63 : cap < 2 ^ 63)
    (R : DataMem → Prop) (sp bp : UInt64) (r0 : Reg64s) :
    ∀ j i (s : MachineData), i + j = n →
    s.regs.rcx.toNat = i → s.regs.rbx.toBitVec = b → s.regs.rdx.toNat = L + 4 + 8 * i →
    s.regs.rdi.toNat = cap → s.regs.r11.toNat = n → s.regs.r10.toBitVec = p → s.regs.rsp = sp → s.regs.rbp = bp → Keep3 r0 s.regs →
    (s.dmem =⋆ Eq (bs.At p) ⋆ Eq ((bs.take (8 * i) ++ d.drop (8 * i)).At (b + BitVec.ofNat 64 (L + 4))) ⋆ R) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 175) ∧ st.data.regs.rbx.toBitVec = b
        ∧ st.data.regs.rdx.toNat = L + 4 + 8 * n ∧ st.data.regs.rdi.toNat = cap
        ∧ st.data.regs.rsp = sp ∧ st.data.regs.rbp = bp ∧ Keep3 r0 st.data.regs
        ∧ (Eq (bs.At p) ⋆ Eq (bs.At (b + BitVec.ofNat 64 (L + 4))) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 149)⟩
  | 0, i, s, hij, hrax, hrbx, hrdx, hrdi, hr8, _, hrsp, hrbp, hkp, h_mem => by
    have hin : i = n := by omega
    subst hin
    refine lcm3_exit k hk hf _ s (UInt64.toNat_inj.mp (by omega)) fun _ => ⟨rfl, hrbx, hrdx, hrdi, hrsp, hrbp, hkp, ?_⟩
    rw [List.take_of_length_le (by omega), List.drop_of_length_le (by omega), List.append_nil] at h_mem
    exact h_mem
  | j + 1, i, s, hij, hrax, hrbx, hrdx, hrdi, hr8, hr9, hrsp, hrbp, hkp, h_mem => by
    refine eventually_trans _ _ _ _
      (lcm3_iter k hk hf bs d n hn hbs hd i (by omega) b p L cap hcap hcap63 R s hrax hrbx hrdx hrdi hr8 hr9 sp bp hrsp hrbp h_mem) ?_
    rintro ⟨s', pc⟩ ⟨hpc, h1, h2, h3, h4, h5, h6, h7, h8, hk3, h9⟩
    dsimp only at hpc; subst hpc
    exact lcm3_loop k hk hf bs d n hn hbs hd b p L cap hcap hcap63 R sp bp r0 j (i + 1) s' (by omega) h1 h2 h3 h4 h5 h6 h7 h8 (hkp.trans hk3) h9


/-- The element encodings laid end to end (the list body after the offsets). -/
def lcBodyL (gs : List ListU64) : List UInt8 := ((gs.map luEncode).map Array.toList).flatten

/-- Bytes of the encodings before element i. -/
def lcS (gs : List ListU64) (i : Nat) : Nat := ((gs.take i).map fun g => 4 + 8 * g.l.length).sum

theorem lcS_succ (gs : List ListU64) (i : Nat) (hi : i < gs.length) :
    lcS gs (i + 1) = lcS gs i + (4 + 8 * gs[i].l.length) := by
  simp only [lcS, List.take_add_one, List.map_append, List.sum_append, List.getElem?_eq_getElem hi]; simp

theorem lcBodyL_step (gs : List ListU64) (i : Nat) (hi : i < gs.length) :
    (lcBodyL gs).take (lcS gs i) ++ ([4, 0, 0, 0] ++ (u64Bytes gs[i].l).toList) = (lcBodyL gs).take (lcS gs (i + 1)) := by
  have hf := flatten_get ((gs.map luEncode).map Array.toList) i (by simp; omega)
  simp only [List.getElem_map, Array.length_toList, lu_encode_size, lc_take_sizes] at hf
  rw [lcS_succ gs i hi, List.take_add, lcS, lcBodyL, hf, luEncode_toList]

theorem lcBodyL_length (gs : List ListU64) : (lcBodyL gs).length = lcS gs gs.length := by
  simp only [lcBodyL, lcS, List.take_length, List.length_flatten, List.map_map]
  congr 1; apply List.map_congr_left; intro g _; simp [lu_encode_size]

/-- One element's read-only chunks: the pointer in the items array, the
ListU64 header (data pointer, length), the words. -/
def lcElem (A : BitVec 64) (j : Nat) (p q : BitVec 64) (g : ListU64) : DataMem → Prop :=
  Eq ((Int.toBytes 8 p.toInt).At (A + BitVec.ofNat 64 (8 * j))) ⋆ Eq ((Int.toBytes 8 q.toInt).At p)
    ⋆ Eq ((Int.toBytes 8 (g.l.length : Int)).At (p + 8)) ⋆ Eq ((u64Bytes g.l).toList.At q)

theorem jle16_true (a : BitVec 64) (af : Bool) (h : a.toNat ≤ 16) :
    CondCode.le.interp (StatusFlags.from_result (a - 16)
      { cf := BitVec.unsigned (a - 16) != a.unsigned - BitVec.unsigned (16 : BitVec 64), af := af,
        of := BitVec.toInt (a - 16) != a.toInt - BitVec.toInt (16 : BitVec 64) }) = true := by
  have ta : a.toInt = a.toNat := BitVec.toInt_eq_toNat_of_lt (by omega)
  have t2 : BitVec.toInt (16 : BitVec 64) = 16 := by decide
  by_cases h0 : a.toNat = 16
  · have : a = 16 := BitVec.eq_of_toNat_eq h0
    subst this; cases af <;> decide
  · have hs : (a - 16).toInt = (a.toNat : Int) - 16 := by
      rw [BitVec.toInt_sub, ta, t2]; apply Int.bmod_eq_of_le <;> omega
    have hm : (a - 16).msb = true := by rw [BitVec.msb_eq_toInt, hs]; simp; omega
    simp [CondCode.interp, StatusFlags.from_result, ta, hs]
    rw [show (a - 16#64) = a - 16 from rfl, hm, Int.bmod_eq_of_le (by omega) (by omega)]; simp
theorem drop3 (dB : List UInt8) (S w : Nat) :
    dB.drop S = (dB.drop S).take 4 ++ ((dB.drop (S + 4)).take w ++ dB.drop (S + 4 + w)) := by
  rw [show dB.drop (S + 4 + w) = (dB.drop (S + 4)).drop w by simp [List.drop_drop],
    List.take_append_drop, show dB.drop (S + 4) = (dB.drop S).drop 4 by simp [List.drop_drop],
    List.take_append_drop]

/-- Registers that loop 3 keeps. -/
structure Keep4 (a b : Reg64s) : Prop where
  rbx : b.rbx = a.rbx
  rdi : b.rdi = a.rdi
  rsp : b.rsp = a.rsp
  rbp : b.rbp = a.rbp
  r14 : b.r14 = a.r14

theorem Keep4.trans {a b c : Reg64s} (h1 : Keep4 a b) (h2 : Keep4 b c) : Keep4 a c :=
  ⟨h2.rbx.trans h1.rbx, h2.rdi.trans h1.rdi, h2.rsp.trans h1.rsp, h2.rbp.trans h1.rbp, h2.r14.trans h1.r14⟩

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
theorem lcm4_iter (k : Nat) (hk : ListCMarshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListCMarshalSSZTo k) (A b y : BitVec 64) (ps qs : List (BitVec 64)) (gs : List ListU64)
    (hn : gs.length ≤ 4) (hps : ps.length = gs.length) (hqs : qs.length = gs.length) (hgs : ∀ g ∈ gs, g.ok)
    (dB : List UInt8) (hdB : dB.length = lcS gs gs.length) (L0 cap : Nat)
    (hcap : L0 + 4 + 4 * gs.length + lcS gs gs.length ≤ cap) (hcap63 : cap < 2 ^ 63)
    (i : Nat) (hi : i < gs.length) (Objs R : DataMem → Prop)
    (hObjs : ∀ j (hj : j < gs.length), ∃ Rest,
      Objs = lcElem A j (ps[j]'(by omega)) (qs[j]'(by omega)) gs[j] ⋆ Rest)
    (s72 s80 s24 : List UInt8) (h72 : s72.length = 8) (h80 : s80.length = 8) (h24 : s24.length = 8)
    (s0 : MachineData) (hrax : s0.regs.rax.toNat = i) (hr8 : s0.regs.r8.toBitVec = A)
    (hr9 : s0.regs.r9.toNat = gs.length) (hrdx : s0.regs.rdx.toNat = L0 + 4 + 4 * gs.length + lcS gs i)
    (hrbx : s0.regs.rbx.toBitVec = b) (hrdi : s0.regs.rdi.toNat = cap) (hrsp : s0.regs.rsp.toBitVec = y)
    (h_mem : s0.dmem =⋆ Eq (((lcBodyL gs).take (lcS gs i) ++ dB.drop (lcS gs i)).At
      (b + BitVec.ofNat 64 (L0 + 4 + 4 * gs.length))) ⋆ Eq (s72.At (y + 96)) ⋆ Eq (s80.At (y + 88))
      ⋆ Eq (s24.At (y + 144)) ⋆ Objs ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 106) ∧ st.data.regs.rax.toNat = i + 1
        ∧ st.data.regs.r8 = s0.regs.r8 ∧ st.data.regs.r9 = s0.regs.r9
        ∧ st.data.regs.rdx.toNat = L0 + 4 + 4 * gs.length + lcS gs (i + 1) ∧ st.data.regs.rcx = 0
        ∧ st.data.regs.rsi = 0 ∧ Keep4 s0.regs st.data.regs ∧
        ∃ s72' s80' s24' : List UInt8, s72'.length = 8 ∧ s80'.length = 8 ∧ s24'.length = 8 ∧
        (Eq (((lcBodyL gs).take (lcS gs (i + 1)) ++ dB.drop (lcS gs (i + 1))).At
          (b + BitVec.ofNat 64 (L0 + 4 + 4 * gs.length))) ⋆ Eq (s72'.At (y + 96)) ⋆ Eq (s80'.At (y + 88))
          ⋆ Eq (s24'.At (y + 144)) ⋆ Objs ⋆ R) st.data.dmem)
      ⟨s0, Host.addrOf (k + 106)⟩ := by
  obtain ⟨Rest, hRest⟩ := hObjs i hi
  have hg : gs[i].l.length ≤ 16 := hgs _ (List.getElem_mem hi)
  generalize hp : ps[i]'(by omega) = p at hRest
  generalize hq : qs[i]'(by omega) = q at hRest
  rw [hRest] at h_mem ⊢
  simp only [lcElem] at h_mem ⊢
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s0
  simp only at h_mem hrax hr8 hr9 hrdx hrbx hrdi hrsp ⊢
  subst hr8 hrbx hrsp
  have := rax.toNat_lt_size; have := r9.toNat_lt_size; have := rdx.toNat_lt_size; have := rdi.toNat_lt_size
  have hSle : lcS gs (i + 1) ≤ lcS gs gs.length := by
    simp only [lcS]; have := lcStart_le gs (i + 1); simp only [lcStart] at this; omega
  have hSs := lcS_succ gs i hi
  simp only [UInt64.size] at *
  kat hk ListCMarshalSSZTo 106
  kat hk ListCMarshalSSZTo 107
  kat hk ListCMarshalSSZTo 108
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.signed] at h
    exact jge_false rax.toBitVec r9.toBitVec (by simp; omega) (by simp; omega) (by simpa using h)
  simp only [Effects.All]
  kat hk ListCMarshalSSZTo 109
  apply store_step _ _ _ _ _ s72 _ _ (by ecancel) (by exact h72)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk ListCMarshalSSZTo 110
  kat hk ListCMarshalSSZTo 111
  rw [idx8' _ _ i (by simpa using hrax) (by omega)]
  apply load_step _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk ListCMarshalSSZTo 112
  kat hk ListCMarshalSSZTo 113
  kat hk ListCMarshalSSZTo 114
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf ListCMarshalSSZTo 129
  kat hk ListCMarshalSSZTo 129
  kat hk ListCMarshalSSZTo 130
  have hsplit : (lcBodyL gs).take (lcS gs i) ++ dB.drop (lcS gs i) = (lcBodyL gs).take (lcS gs i)
      ++ ((dB.drop (lcS gs i)).take 4 ++ ((dB.drop (lcS gs i + 4)).take (8 * gs[i].l.length)
        ++ dB.drop (lcS gs i + 4 + 8 * gs[i].l.length))) := by
    rw [← drop3]
  have hBL := lcBodyL_length gs
  rw [hsplit, Mem.At_append_sep _ _ _ (by simp; omega), Mem.At_append_sep _ _ _ (by simp; omega),
    Mem.At_append_sep _ _ _ (by simp; omega)] at H1
  simp only [List.length_take, List.length_drop, hBL, hdB, Nat.min_eq_left (show lcS gs i ≤ lcS gs gs.length by omega),
    Nat.min_eq_left (show 4 ≤ lcS gs gs.length - lcS gs i by omega),
    Nat.min_eq_left (show 8 * gs[i].l.length ≤ lcS gs gs.length - (lcS gs i + 4) by omega)] at H1
  rw [add4_neg4, show rbx.toBitVec + rdx.toBitVec = rbx.toBitVec + BitVec.ofNat 64 (L0 + 4 + 4 * gs.length)
      + BitVec.ofNat 64 (lcS gs i) by
    rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega]
  apply store_step _ _ _ _ _ ((dB.drop (lcS gs i)).take 4) _ _ (by ecancel) (by simp; omega)
  intro m2 H2
  simp only [Width.bytes, Width.bits, show Int.toBytes 4 (BitVec.truncate 32 (4 : BitVec 64)).toInt = [4, 0, 0, 0] by decide] at H2
  kunfold
  kat hk ListCMarshalSSZTo 131
  rw [← lcm_len _ (by omega)] at H2
  apply load_step _ _ _ _ (Int.toBytes 8 (BitVec.ofNat 64 gs[i].l.length).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk ListCMarshalSSZTo 132
  kat hk ListCMarshalSSZTo 133
  split
  case isFalse h => exfalso; rw [jle16_true _ _ (by simp; omega)] at h; exact h rfl
  simp only [Effects.All]
  klabel hk hf ListCMarshalSSZTo 140
  kat hk ListCMarshalSSZTo 140
  kat hk ListCMarshalSSZTo 141
  apply store_step _ _ _ _ _ s80 _ _ (by ecancel) (by exact h80)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk ListCMarshalSSZTo 142
  apply load_step _ _ _ _ (Int.toBytes 8 q.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk ListCMarshalSSZTo 143
  apply store_step _ _ _ _ _ s24 _ _ (by ecancel) (by exact h24)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  kat hk ListCMarshalSSZTo 144
  intro _
  kat hk ListCMarshalSSZTo 145
  klabel hk hf ListCMarshalSSZTo 149
  have hL4 : rbx.toBitVec + BitVec.ofNat 64 (L0 + 4 + 4 * gs.length) + BitVec.ofNat 64 (lcS gs i) + 4#64
      = rbx.toBitVec + BitVec.ofNat 64 (L0 + 4 + 4 * gs.length + lcS gs i + 4) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega
  rw [hL4] at H4
  refine eventually_trans _ _ _ _ (lcm3_loop k hk hf (u64Bytes (gs[i]'hi).l).toList
    ((dB.drop (lcS gs i + 4)).take (8 * (gs[i]'hi).l.length)) (gs[i]'hi).l.length hg (by simp [u64Bytes_size])
    (by simp; omega) rbx.toBitVec q (L0 + 4 + 4 * gs.length + lcS gs i) rdi.toNat (by omega) (by omega) _ rsp rbp _
    (gs[i]'hi).l.length 0 _ (by omega) (by simp) rfl
    (by show (4 + rdx.toBitVec).toNat = _; simp [BitVec.toNat_add]; omega)
    rfl (by show (BitVec.ofNat 64 (gs[i]'hi).l.length).toNat = _; simp; omega) rfl rfl rfl ⟨rfl, rfl, rfl, rfl⟩
    (by simp only [Nat.mul_zero, List.take_zero, List.nil_append, List.drop_zero]; ecancel)) ?_
  rintro ⟨e3, pc3⟩ ⟨hpc3, hrbx3, hrdx3, hrdi3, hrsp3, hrbp3, hk3, Hm3⟩
  dsimp only at hpc3 hrbx3 hrdx3 hrdi3 hrsp3 hrbp3 hk3 Hm3
  subst hpc3
  obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,
    zmms3, flags3, mem3⟩ := e3
  obtain ⟨hk3a, hk38, hk39, hk314⟩ := hk3
  simp only at hrbx3 hrdx3 hrdi3 hrsp3 hrbp3 hk3a hk38 hk39 hk314 Hm3
  subst hrsp3 hrbp3 hk3a hk38 hk39 hk314
  kat hk ListCMarshalSSZTo 175
  kat hk ListCMarshalSSZTo 176
  intro _
  kat hk ListCMarshalSSZTo 177
  kat hk ListCMarshalSSZTo 178
  intro _
  kat hk ListCMarshalSSZTo 179
  kat hk ListCMarshalSSZTo 180
  intro _
  kat hk ListCMarshalSSZTo 181
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf ListCMarshalSSZTo 100
  kat hk ListCMarshalSSZTo 100
  kat hk ListCMarshalSSZTo 101
  kat hk ListCMarshalSSZTo 102
  kat hk ListCMarshalSSZTo 103
  kat hk ListCMarshalSSZTo 104
  kat hk ListCMarshalSSZTo 105
  apply Eventually.done
  have hrbx' : rbx3 = rbx := UInt64.toBitVec_inj.mp hrbx3
  have hrdi' : rdi3 = rdi := UInt64.toNat_inj.mp hrdi3
  subst hrbx' hrdi'
  rw [lcm_len _ (by omega), ← hL4] at Hm3
  refine ⟨rfl, ?_, rfl, rfl, ?_, ?_, ?_, ⟨rfl, rfl, rfl, rfl, rfl⟩, Int.toBytes 8 rax3.toBitVec.toInt,
    Int.toBytes 8 ((gs[i]'hi).l.length : Int), Int.toBytes 8 q.toInt, Int.toBytes_length 8 _, Int.toBytes_length 8 _,
    Int.toBytes_length 8 _, ?_⟩
  · show (rax3.toBitVec + 1).toNat = i + 1; simp [BitVec.toNat_add]; omega
  · show rdx3.toNat = _; omega
  · apply UInt64.toBitVec_inj.mp; simp
  · apply UInt64.toBitVec_inj.mp; simp
  have hstep : (lcBodyL gs).take (lcS gs (i + 1)) ++ dB.drop (lcS gs (i + 1)) = (lcBodyL gs).take (lcS gs i)
      ++ ([4, 0, 0, 0] ++ ((u64Bytes (gs[i]'hi).l).toList ++ dB.drop (lcS gs i + 4 + 8 * (gs[i]'hi).l.length))) := by
    rw [← lcBodyL_step gs i hi, hSs, ← Nat.add_assoc]; simp only [List.append_assoc]
  have hu := u64Bytes_size (gs[i]'hi).l
  have hdl : dB.length - (lcS gs i + 4 + 8 * (gs[i]'hi).l.length) ≤ dB.length := Nat.sub_le _ _
  rw [hstep, Mem.At_append_sep _ _ _ (by simp [hu]; omega), Mem.At_append_sep _ _ _ (by simp [hu]; omega),
    Mem.At_append_sep _ _ _ (by simp [hu]; omega)]
  simp only [List.length_take, List.length_drop, hBL, List.length_cons, List.length_nil, Array.length_toList,
    u64Bytes_size, Nat.min_eq_left (show lcS gs i ≤ lcS gs gs.length by omega)]
  simp only [Nat.reduceAdd, Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_emp] at Hm3 ⊢
  generalize (gs[i]'hi) = g at Hm3 ⊢
  generalize rbx3.toBitVec + BitVec.ofNat 64 (L0 + 4 + 4 * gs.length) + BitVec.ofNat 64 (lcS gs i) + 4#64 = A4 at Hm3 ⊢
  generalize (Int.toBytes 8 (g.l.length : Int)) = B8 at Hm3 ⊢
  generalize Rest ⋆ R = RR at Hm3 ⊢
  refine (congrFun ?_ mem3).mp Hm3
  ecancel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
/-- Loop 3 exit: at head 106 with rax = r9 (every element written), `jge` goes
to the epilogue label at 183. -/
theorem lcm4_exit (k : Nat) (hk : ListCMarshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListCMarshalSSZTo k) (P : MachineState → Prop) (s0 : MachineData)
    (hrr : s0.regs.rax = s0.regs.r9)
    (hP : ∀ f : StatusFlags, P ⟨⟨s0.regs, s0.zmms, f, s0.dmem⟩, Host.addrOf (k + 183)⟩) :
    Eventually (step1 Host.exe) P ⟨s0, Host.addrOf (k + 106)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s0
  dsimp only at hrr
  subst hrr
  kat hk ListCMarshalSSZTo 106
  kat hk ListCMarshalSSZTo 107
  kat hk ListCMarshalSSZTo 108
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
  simp only [Effects.All]
  klabel hk hf ListCMarshalSSZTo 183
  exact Eventually.done _ (hP _)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
/-- Loop 3 (element bodies): from head 106 with i elements written, it reaches
the epilogue label 183 with all of `lcBodyL gs` written after the offsets,
rdx = L0 + 4 + 4n + (body length), and a nil error (rcx = rsi = 0). -/
theorem lcm4_loop (k : Nat) (hk : ListCMarshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListCMarshalSSZTo k) (A b y : BitVec 64) (ps qs : List (BitVec 64)) (gs : List ListU64)
    (hn : gs.length ≤ 4) (hps : ps.length = gs.length) (hqs : qs.length = gs.length) (hgs : ∀ g ∈ gs, g.ok)
    (dB : List UInt8) (hdB : dB.length = lcS gs gs.length) (L0 cap : Nat)
    (hcap : L0 + 4 + 4 * gs.length + lcS gs gs.length ≤ cap) (hcap63 : cap < 2 ^ 63)
    (Objs R : DataMem → Prop)
    (hObjs : ∀ j (hj : j < gs.length), ∃ Rest,
      Objs = lcElem A j (ps[j]'(by omega)) (qs[j]'(by omega)) gs[j] ⋆ Rest) :
    ∀ j i (s0 : MachineData) (s72 s80 s24 : List UInt8), i + j = gs.length →
    s72.length = 8 → s80.length = 8 → s24.length = 8 →
    s0.regs.rax.toNat = i → s0.regs.r8.toBitVec = A → s0.regs.r9.toNat = gs.length →
    s0.regs.rdx.toNat = L0 + 4 + 4 * gs.length + lcS gs i → s0.regs.rbx.toBitVec = b →
    s0.regs.rdi.toNat = cap → s0.regs.rsp.toBitVec = y → s0.regs.rcx = 0 → s0.regs.rsi = 0 →
    (s0.dmem =⋆ Eq (((lcBodyL gs).take (lcS gs i) ++ dB.drop (lcS gs i)).At
      (b + BitVec.ofNat 64 (L0 + 4 + 4 * gs.length))) ⋆ Eq (s72.At (y + 96)) ⋆ Eq (s80.At (y + 88))
      ⋆ Eq (s24.At (y + 144)) ⋆ Objs ⋆ R) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 183)
        ∧ st.data.regs.rdx.toNat = L0 + 4 + 4 * gs.length + lcS gs gs.length ∧ st.data.regs.rcx = 0
        ∧ st.data.regs.rsi = 0 ∧ Keep4 s0.regs st.data.regs ∧
        ∃ s72' s80' s24' : List UInt8, s72'.length = 8 ∧ s80'.length = 8 ∧ s24'.length = 8 ∧
        (Eq ((lcBodyL gs).At (b + BitVec.ofNat 64 (L0 + 4 + 4 * gs.length))) ⋆ Eq (s72'.At (y + 96))
          ⋆ Eq (s80'.At (y + 88)) ⋆ Eq (s24'.At (y + 144)) ⋆ Objs ⋆ R) st.data.dmem)
      ⟨s0, Host.addrOf (k + 106)⟩
  | 0, i, s0, s72, s80, s24, hij, h72, h80, h24, hrax, _, hr9, hrdx, _, _, _, hrcx, hrsi, h_mem => by
    have hin : i = gs.length := by omega
    subst hin
    have hBL := lcBodyL_length gs
    refine lcm4_exit k hk hf _ s0 (UInt64.toNat_inj.mp (by omega)) fun _ =>
      ⟨rfl, hrdx, hrcx, hrsi, ⟨rfl, rfl, rfl, rfl, rfl⟩, s72, s80, s24, h72, h80, h24, ?_⟩
    rw [List.take_of_length_le (by omega), List.drop_of_length_le (by omega), List.append_nil] at h_mem
    exact h_mem
  | j + 1, i, s0, s72, s80, s24, hij, h72, h80, h24, hrax, hr8, hr9, hrdx, hrbx, hrdi, hrsp, _, _, h_mem => by
    refine eventually_trans _ _ _ _
      (lcm4_iter k hk hf A b y ps qs gs hn hps hqs hgs dB hdB L0 cap hcap hcap63 i (by omega) Objs R hObjs
        s72 s80 s24 h72 h80 h24 s0 hrax hr8 hr9 hrdx hrbx hrdi hrsp h_mem) ?_
    rintro ⟨s', pc⟩ ⟨hpc, h1, h2, h3, h4, h5, h6, hk4, s72', s80', s24', l1, l2, l3, h9⟩
    dsimp only at hpc; subst hpc
    refine eventually_trans _ _ _ _
      (lcm4_loop k hk hf A b y ps qs gs hn hps hqs hgs dB hdB L0 cap hcap hcap63 Objs R hObjs j (i + 1) s'
        s72' s80' s24' (by omega) l1 l2 l3 h1 (by rw [h2]; exact hr8) (by rw [h3]; exact hr9) h4
        (by rw [hk4.rbx]; exact hrbx) (by rw [hk4.rdi]; exact hrdi) (by rw [hk4.rsp]; exact hrsp) h5 h6 h9) ?_
    rintro st ⟨q1, q2, q3, q4, hk4', q5⟩
    exact Eventually.done _ ⟨q1, q2, q3, q4, hk4.trans hk4', q5⟩

/-- The element pointer and the first byte of the element's slice pointer
(loop 1 reads them) from the equation form of the objects. -/
theorem lc_acc1 (A : BitVec 64) (ps qs : List (BitVec 64)) (gs : List ListU64)
    (hps : ps.length = gs.length) (hqs : qs.length = gs.length) (Objs : DataMem → Prop)
    (hObjs : ∀ j (hj : j < gs.length), ∃ Rest,
      Objs = lcElem A j (ps[j]'(by omega)) (qs[j]'(by omega)) gs[j] ⋆ Rest)
    (m : DataMem) (hm : Objs m) (i : Nat) (hi : i < gs.length) :
    (Eq ((Int.toBytes 8 (ps[i]'(by omega)).toInt).At (A + BitVec.ofNat 64 (8 * i)))
      ⋆ Eq (((Int.toBytes 8 (qs[i]'(by omega)).toInt).take 1).At (ps[i]'(by omega))) ⋆ fun _ => True) m := by
  obtain ⟨Rest, hRest⟩ := hObjs i hi
  rw [hRest] at hm
  simp only [lcElem] at hm
  generalize ps[i]'(by omega) = p at hm ⊢
  have hl : (Int.toBytes 8 (qs[i]'(by omega)).toInt).length = 8 := Int.toBytes_length 8 _
  generalize Int.toBytes 8 (qs[i]'(by omega)).toInt = qb at hm hl ⊢
  rw [← List.take_append_drop 1 qb, Mem.At_append_sep _ _ _ (by simp; omega)] at hm
  exact sep_mono_right' (fun _ _ => trivial) ((congrFun (by ecancel) m).mp hm)

/-- The element pointer and the element's length (loop 2 reads them). -/
theorem lc_acc2 (A : BitVec 64) (ps qs : List (BitVec 64)) (gs : List ListU64)
    (hps : ps.length = gs.length) (hqs : qs.length = gs.length) (Objs : DataMem → Prop)
    (hObjs : ∀ j (hj : j < gs.length), ∃ Rest,
      Objs = lcElem A j (ps[j]'(by omega)) (qs[j]'(by omega)) gs[j] ⋆ Rest)
    (m : DataMem) (hm : Objs m) (i : Nat) (hi : i < gs.length) :
    (Eq ((Int.toBytes 8 (ps[i]'(by omega)).toInt).At (A + BitVec.ofNat 64 (8 * i)))
      ⋆ Eq ((Int.toBytes 8 (gs[i].l.length : Int)).At ((ps[i]'(by omega)) + 8)) ⋆ fun _ => True) m := by
  obtain ⟨Rest, hRest⟩ := hObjs i hi
  rw [hRest] at hm
  simp only [lcElem] at hm
  generalize ps[i]'(by omega) = p at hm ⊢
  exact sep_mono_right' (fun _ _ => trivial) ((congrFun (by ecancel) m).mp hm)

theorem jg4_false (a : BitVec 64) (af : Bool) (h : a.toNat ≤ 4) :
    CondCode.g.interp (StatusFlags.from_result (a - 4)
      { cf := BitVec.unsigned (a - 4) != a.unsigned - BitVec.unsigned (4 : BitVec 64), af := af,
        of := BitVec.toInt (a - 4) != a.toInt - BitVec.toInt (4 : BitVec 64) }) = false := by
  have ta : a.toInt = a.toNat := BitVec.toInt_eq_toNat_of_lt (by omega)
  have t4 : BitVec.toInt (4 : BitVec 64) = 4 := by decide
  have hs : (a - 4).toInt = (a.toNat : Int) - 4 := by
    rw [BitVec.toInt_sub, ta, t4]; apply Int.bmod_eq_of_le <;> omega
  by_cases h4 : a.toNat = 4
  · have : a - 4 = 0#64 := by apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega
    simp [CondCode.interp, StatusFlags.from_result]
    intro h1; exact absurd this h1
  · have hm : (a - 4).msb = true := by
      rw [BitVec.msb_eq_decide]; simp [BitVec.toNat_sub]; omega
    simp [CondCode.interp, StatusFlags.from_result, ta]
    intro _
    rw [show (a - 4#64).msb = true from hm, Int.bmod_eq_of_le (by omega) (by omega)]; simp

theorem lcm_y96 (x : BitVec 64) : x - 72 = x - 8#64 - 160 + 96 := by bv_omega
theorem lcm_y88 (x : BitVec 64) : x - 80 = x - 8#64 - 160 + 88 := by bv_omega
theorem lcm_y144 (x : BitVec 64) : x - 24 = x - 8#64 - 160 + 144 := by bv_omega

theorem lcm_pop (x : BitVec 64) : (160 : BitVec 64) + (x - 8#64 - 160) = x - 8 := by bv_omega
theorem lcm_ret (x : BitVec 64) : x - 8 + 8#64 = x := by bv_omega

theorem toNat_add_neg40 (x : BitVec 64) (h : 40 ≤ x.toNat) : (x + -40).toNat = x.toNat - 40 := by
  rw [← BitVec.sub_eq_add_neg, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simpa using h)]; rfl

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
/-- `ListC.MarshalSSZTo`, fast path (cap ≥ the encoded length, n ≤ 4): it
returns (buf ++ lcEncode, nil). The items array at A holds the element
pointers `ps`; element j is a ListU64 object at `ps[j]` with slice pointer
`qs[j]` (`lcElem`). Premises the Go caller guarantees: receiver ≠ nil and
mapped, non-nil element pointers (the Go code dereferences each one, loop 1),
`len(dst) ≤ cap(dst) < 2^63`. Premises that are fast-path only: the stack
guard (lea -40), cap ≥ len(dst) + 4 + 4n + Σ(4 + 8 len). -/
theorem lc_marshal_main (k : Nat) (hk : ListCMarshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListCMarshalSSZTo k) (A : BitVec 64) (ps qs : List (BitVec 64)) (gs : List ListU64)
    (hn : gs.length ≤ 4) (hps : ps.length = gs.length) (hqs : qs.length = gs.length) (hgs : ∀ g ∈ gs, g.ok)
    (Objs : DataMem → Prop)
    (hObjs : ∀ j (hj : j < gs.length), ∃ Rest,
      Objs = lcElem A j (ps[j]'(by omega)) (qs[j]'(by omega)) gs[j] ⋆ Rest)
    (pre o4 d1 dB : List UInt8) (ho4 : o4.length = 4) (hd1 : d1.length = 4 * gs.length)
    (hdB : dB.length = lcS gs gs.length)
    (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s8 s16 s98 s68 s60 s58 s90 : List UInt8)
    (hfp : fp.length = 8) (hs8 : s8.length = 8) (hs16 : s16.length = 8) (hs98 : s98.length = 8)
    (hs68 : s68.length = 8) (hs60 : s60.length = 8) (hs58 : s58.length = 8) (hs90 : s90.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s8.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s16.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s98.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (s68.At (s.regs.rsp.toBitVec - 64)) ⋆ Eq (s60.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (s58.At (s.regs.rsp.toBitVec - 80)) ⋆ Eq (s90.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 A.toInt).At s.regs.rax.toBitVec)
      ⋆ Eq ((Int.toBytes 8 (gs.length : Int)).At (s.regs.rax.toBitVec + 8)) ⋆ Objs
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (o4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + BitVec.ofNat 64 (s.regs.rcx.toNat + 4)))
      ⋆ Eq (dB.At (s.regs.rbx.toBitVec + BitVec.ofNat 64 (s.regs.rcx.toNat + 4 + 4 * gs.length))) ⋆ R)
    (hguard : guard.toNat + 40 < s.regs.rsp.toNat) (hsp : 208 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 4 + 4 * gs.length + lcS gs gs.length ≤ s.regs.rdi.toNat)
    (hcap63 : s.regs.rdi.toNat < 2 ^ 63) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 4 + 4 * gs.length + lcS gs gs.length
        ∧ st.data.regs.rcx = s.regs.rdi ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq ([4, 0, 0, 0].At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq ((offTab (4 * gs.length) (gs.map luEncode)).At
              (s.regs.rbx.toBitVec + BitVec.ofNat 64 (s.regs.rcx.toNat + 4)))
          ⋆ Eq ((lcBodyL gs).At (s.regs.rbx.toBitVec + BitVec.ofNat 64 (s.regs.rcx.toNat + 4 + 4 * gs.length)))
          ⋆ Objs ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hcap hcap63 hpre ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *
  have hnI : (gs.length : Int) = (BitVec.ofNat 64 gs.length).toInt := (lcm_len _ (by omega)).symm
  rw [hnI] at h_mem
  kat hk ListCMarshalSSZTo 0
  kat hk ListCMarshalSSZTo 1
  kat hk ListCMarshalSSZTo 2
  kat hk ListCMarshalSSZTo 3
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListCMarshalSSZTo 4
  split
  case isTrue h =>
    exfalso
    rw [cmp_be_false _ _ _ _ (by rw [toNat_add_neg40 _ (by simp; omega)]; simp; omega)] at h
    exact absurd h (by simp)
  simp only [Effects.All]
  kat hk ListCMarshalSSZTo 5
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk ListCMarshalSSZTo 6
  kat hk ListCMarshalSSZTo 7
  kat hk ListCMarshalSSZTo 8
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s16 _ _ (by bv_omega) (by ecancel) (by exact hs16)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk ListCMarshalSSZTo 9
  apply store_step_at _ _ (rsp.toBitVec + 8) _ _ _ s8 _ _ (by bv_omega) (by ecancel) (by exact hs8)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk ListCMarshalSSZTo 10
  kat hk ListCMarshalSSZTo 11
  kat hk ListCMarshalSSZTo 12
  kat hk ListCMarshalSSZTo 13
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf ListCMarshalSSZTo 24
  kat hk ListCMarshalSSZTo 24
  kat hk ListCMarshalSSZTo 25
  rw [lum_off]
  apply store_step _ _ _ _ _ o4 _ _ (by ecancel) (by exact ho4)
  intro m4 H4
  simp only [Width.bytes, Width.bits,
    show Int.toBytes 4 (BitVec.truncate 32 (4 : BitVec 64)).toInt = [4, 0, 0, 0] by decide] at H4
  kunfold
  kat hk ListCMarshalSSZTo 26
  apply load_step_at _ _ (rax.toBitVec + 8) _ _ (Int.toBytes 8 (BitVec.ofNat 64 gs.length).toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk ListCMarshalSSZTo 27
  apply load_step _ _ _ _ (Int.toBytes 8 A.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk ListCMarshalSSZTo 28
  intro _
  kat hk ListCMarshalSSZTo 29
  klabel hk hf ListCMarshalSSZTo 36
  have hO4 : (Objs ⋆ fun _ => True) m4 := by
    refine sep_mono_right' (Q := ?Q) (fun _ _ => trivial) ?h
    case h => ecancel
  refine eventually_trans _ _ _ _ (lcm1_loop k hk hf A ps qs gs.length hn hps hqs gs.length 0 _ (by omega)
    (by simp) (by show (BitVec.ofNat 64 gs.length).toNat = _; simp; omega) rfl
    (fun i' hi' => sep_true_of_part hO4 (fun m' hm' => lc_acc1 A ps qs gs hps hqs Objs hObjs m' hm' i' hi'))) ?_
  rintro ⟨e1, pc1⟩ ⟨hpc1, hk1, hm1⟩
  dsimp only at hpc1 hk1 hm1
  subst hpc1
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩,
    zmms1, flags1, mem1⟩ := e1
  obtain ⟨k1a, k1b, k1d, k1di, k1sp, k1bp, k18, k19, k114⟩ := hk1
  simp only at k1a k1b k1d k1di k1sp k1bp k18 k19 k114 hm1
  subst k1a k1b k1d k1di k1sp k1bp k18 k19 k114 hm1
  kat hk ListCMarshalSSZTo 39
  kat hk ListCMarshalSSZTo 40
  split
  case isTrue h =>
    exfalso; rw [jg4_false _ _ (by simp; omega)] at h; simp at h
  simp only [Effects.All]
  kat hk ListCMarshalSSZTo 41
  apply store_step_at _ _ (rsp.toBitVec - 16) _ _ _ s98 _ _ (by bv_omega) (by ecancel) (by exact hs98)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  kat hk ListCMarshalSSZTo 42
  apply store_step_at _ _ (rsp.toBitVec - 64) _ _ _ s68 _ _ (by bv_omega) (by ecancel) (by exact hs68)
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  kat hk ListCMarshalSSZTo 43
  kat hk ListCMarshalSSZTo 44
  kshl64 2
  kat hk ListCMarshalSSZTo 45
  intro _
  kat hk ListCMarshalSSZTo 46
  klabel hk hf ListCMarshalSSZTo 62
  refine eventually_trans _ _ _ _ (lcm2_loop k hk hf A rbx1.toBitVec ps gs hn hps hgs d1 hd1 rcx.toNat rdi1.toNat
    (by omega) hcap63 Objs _ (fun m hm j hj => lc_acc2 A ps qs gs hps hqs Objs hObjs m hm j hj) gs.length 0 _ (by omega)
    (by simp) (by show (BitVec.ofNat 64 gs.length).toNat = _; simp; omega) rfl
    (by apply BitVec.eq_of_toNat_eq; simp [lcStart, BitVec.toNat_shiftLeft]; omega)
    (by show (rcx.toBitVec + 4).toNat = _; simp [BitVec.toNat_add]; omega) rfl rfl
    (by simp only [Nat.mul_zero, List.take_zero, List.nil_append, List.drop_zero]; ecancel)) ?_
  rintro ⟨e2, pc2⟩ ⟨hpc2, hrdx2, hk2, Hm2⟩
  dsimp only at hpc2 hrdx2 hk2 Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := e2
  obtain ⟨k2a, k2b, k2di, k2sp, k2bp, k214⟩ := hk2
  simp only at k2a k2b k2di k2sp k2bp k214 hrdx2 Hm2
  subst k2a k2b k2di k2sp k2bp k214
  kat hk ListCMarshalSSZTo 90
  kat hk ListCMarshalSSZTo 91
  apply load_step _ _ _ _ (Int.toBytes 8 A.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk ListCMarshalSSZTo 92
  apply store_step_at _ _ (rsp.toBitVec - 16) _ _ _ (Int.toBytes 8 A.toInt) _ _ (by bv_omega) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  kat hk ListCMarshalSSZTo 93
  apply load_step_at _ _ (rax2.toBitVec + 8) _ _ (Int.toBytes 8 (BitVec.ofNat 64 gs.length).toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk ListCMarshalSSZTo 94
  apply store_step_at _ _ (rsp.toBitVec - 64) _ _ _ (Int.toBytes 8 (BitVec.ofNat 64 gs.length).toInt) _ _
    (by bv_omega) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m8 H8
  simp only [Width.bytes, Width.bits] at H8
  kunfold
  kat hk ListCMarshalSSZTo 95
  intro _
  kat hk ListCMarshalSSZTo 96
  intro _
  kat hk ListCMarshalSSZTo 97
  intro _
  kat hk ListCMarshalSSZTo 98
  kat hk ListCMarshalSSZTo 99
  klabel hk hf ListCMarshalSSZTo 106
  rw [lcm_y96, lcm_y88, lcm_y144] at H8
  refine eventually_trans _ _ _ _ (lcm4_loop k hk hf A _ (rsp.toBitVec - 8#64 - 160) ps qs gs hn hps hqs hgs dB hdB
    rcx.toNat _ (by omega)
    hcap63 Objs _ hObjs gs.length 0 _ s60 s58 s90 (by omega) hs60 hs58 hs90 (by simp) rfl
    (by show (BitVec.ofNat 64 gs.length).toNat = _; simp; omega) (by simp only [lcS, List.take_zero]; simp; omega)
    rfl rfl (by kaddr) (by apply UInt64.toBitVec_inj.mp; simp) (by apply UInt64.toBitVec_inj.mp; simp)
    (by simp only [lcS, List.take_zero, List.map_nil, List.sum_nil, List.nil_append, List.drop_zero]; ecancel)) ?_
  rintro ⟨e3, pc3⟩ ⟨hpc3, hrdx3, hrcx3, hrsi3, hk4, s60', s58', s90', l60, l58, l90, Hm3⟩
  dsimp only at hpc3 hrdx3 hrcx3 hrsi3 hk4 Hm3
  subst hpc3
  obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,
    zmms3, flags3, mem3⟩ := e3
  obtain ⟨k4b, k4di, k4sp, k4bp, k414⟩ := hk4
  simp only at k4b k4di k4sp k4bp k414 hrdx3 hrcx3 hrsi3 Hm3
  subst k4b k4di k4sp k4bp k414 hrcx3 hrsi3
  kat hk ListCMarshalSSZTo 183
  kat hk ListCMarshalSSZTo 184
  kat hk ListCMarshalSSZTo 185
  kat hk ListCMarshalSSZTo 186
  kat hk ListCMarshalSSZTo 187
  kat hk ListCMarshalSSZTo 188
  kat hk ListCMarshalSSZTo 189
  kat hk ListCMarshalSSZTo 190
  rw [lcm_pop]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListCMarshalSSZTo 191
  rw [lcm_ret]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only
  refine ⟨trivial, trivial, ?_, trivial, UInt64.toBitVec_inj.mp (by simp), trivial,
    UInt64.toBitVec_inj.mp (by simp), trivial, ?_⟩
  · show rdx3.toNat = _; omega
  refine sep_mono_right' (Q := ?Q2) (fun _ _ => trivial) ?h2
  case h2 => ecancel

/-- **Marshal fast path against EthLib**: the bytes `lc_marshal_main` writes at
`dst[len:]` (`[4, 0, 0, 0]`, the offset table, the element encodings) are the
EthLib serialization of `g.toValue`. -/
theorem lc_marshal_spec_k (g : ListCG) (hg : g.ok) :
    serialize lcDesc g.toValue = .ok (lcEncode g) ∧
    (lcEncode g).toList = [4, 0, 0, 0] ++ offTab (4 * g.items.length) (g.items.map luEncode) ++ lcBodyL g.items := by
  refine ⟨lc_serialize g hg, ?_⟩
  simp only [lcEncode, Array.toList_append, lcBody_toList, lcBodyL, List.append_assoc]
  rfl
