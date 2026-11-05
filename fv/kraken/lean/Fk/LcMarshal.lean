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
