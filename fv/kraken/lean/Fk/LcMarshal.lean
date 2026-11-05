import Fk.LcLoop
import Fk.NeMarshal
import Fk.Bump
import Fk.LcSize

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
