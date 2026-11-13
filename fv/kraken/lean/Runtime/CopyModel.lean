import Runtime.BumpAllocator
import Machine.Labels
import Machine.Bytes

/-!
# `runtime.memmove` and `runtime.growslice` models that satisfy their contracts

`RtCopy` (Runtime/RtCopy.S) has three parts:
-/

open Machine Runtime

namespace Runtime
def RtCopy : Program := include_x64_rt "Runtime/RtCopy.S"

variable [Host]

theorem eventually_mono {P Q : MachineState → Prop} {s : MachineState}
    (h : Eventually (step1 Host.exe) P s) (f : ∀ t, P t → Q t) : Eventually (step1 Host.exe) Q s :=
  eventually_trans _ _ _ _ h (fun t ht => Eventually.done _ (f t ht))

theorem rc_split1 (l : List UInt8) (a : BitVec 64) (i : Nat) (h : i < l.length) (hl : l.length < 2 ^ 64) :
    Eq (l.At a) = Eq ((l.take i).At a) ⋆ Eq ([l[i]].At (a + BitVec.ofNat 64 i))
      ⋆ Eq ((l.drop (i + 1)).At (a + BitVec.ofNat 64 i + 1)) := by
  have e1 : l = l.take i ++ ([l[i]] ++ l.drop (i + 1)) := by
    conv => lhs; rw [← List.take_append_drop i l]
    congr 1
    rw [List.drop_eq_getElem_cons h]; rfl
  conv => lhs; rw [e1]
  rw [Mem.At_append_sep _ _ _ (by simp; omega), Mem.At_append_sep _ _ _ (by simp; omega),
    ← Std.ExtHashMap.sep_assoc]
  have l1 : (l.take i).length = i := by simp; omega
  rw [l1]; rfl

theorem rc_toBytes1 (b : UInt8) :
    Int.toBytes 1 (BitVec.extractLsb' 0 8 (BitVec.zeroExtend 64 (BitVec.zeroExtend 32
      (BitVec.ofInt 8 (Int.ofBytes [b]))))).toInt = [b] := by
  rw [zx8]; exact toBytes_ofInt_ofBytes 8 1 rfl [b] rfl

theorem rc_take_succ (src dst : List UInt8) (i : Nat) (hi : i < src.length) (hd : dst.length = src.length) :
    src.take i ++ ([src[i]] ++ dst.drop (i + 1)) = src.take (i + 1) ++ dst.drop (i + 1) := by
  rw [← List.append_assoc, List.take_add_one, List.getElem?_eq_getElem hi]; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- One iteration of the copy loop (directives 17–23, back to 17). -/
theorem rc_iter (j : Nat) (hj : RtCopy.IsInfixAt Host.prog j) (hf : LabelsFresh RtCopy j)
    (src dst : List UInt8) (hd : dst.length = src.length) (hs : src.length < 2 ^ 64) (i : Nat) (hi : i < src.length)
    (a b : BitVec 64) (R : DataMem → Prop) (s : MachineData)
    (hr10 : s.regs.r10.toNat = i) (hrdx : s.regs.rdx.toNat = src.length)
    (hrsi : s.regs.rsi.toBitVec = a) (hrdi : s.regs.rdi.toBitVec = b)
    (h_mem : s.dmem =⋆ Eq (src.At a) ⋆ Eq ((src.take i ++ dst.drop i).At b) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (j + 17) ∧ st.data.regs.r10.toNat = i + 1
        ∧ st.data.regs.rdx = s.regs.rdx ∧ st.data.regs.rsi = s.regs.rsi ∧ st.data.regs.rdi = s.regs.rdi
        ∧ st.data.regs.rax = s.regs.rax ∧ st.data.regs.rbx = s.regs.rbx ∧ st.data.regs.rcx = s.regs.rcx
        ∧ st.data.regs.rsp = s.regs.rsp ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq (src.At a) ⋆ Eq ((src.take (i + 1) ++ dst.drop (i + 1)).At b) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (j + 17)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hr10 hrdx hrsi hrdi ⊢
  subst hrsi hrdi
  have := r10.toNat_lt_size; have := rdx.toNat_lt_size
  simp only [UInt64.size] at *
  have hl : src.length < 2 ^ 64 := by omega
  have hdi : i < dst.length := by omega
  rw [rc_split1 src rsi.toBitVec i hi hl] at h_mem
  rw [show src.take i ++ dst.drop i = src.take i ++ ([dst[i]] ++ dst.drop (i + 1)) by
      rw [List.drop_eq_getElem_cons hdi]; rfl,
    Mem.At_append_sep _ _ _ (by simp; omega), Mem.At_append_sep _ _ _ (by simp; omega)] at h_mem
  simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi), List.length_cons, List.length_nil] at h_mem
  kat hj RtCopy 17
  kat hj RtCopy 18
  kat hj RtCopy 19
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hj RtCopy 20
  rw [show rsi.toBitVec + r10.toBitVec * 1#64 = rsi.toBitVec + BitVec.ofNat 64 i by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, hr10]]
  apply load_step _ _ _ _ [src[i]] _ _ (by ecancel) (by rfl)
  kunfold
  kat hj RtCopy 21
  rw [show rdi.toBitVec + r10.toBitVec * 1#64 = rdi.toBitVec + BitVec.ofNat 64 i by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, hr10]]
  apply store_step _ _ _ _ _ [dst[i]] _ _ (by ecancel) (by rfl)
  intro m1 H1
  simp only [Width.bytes, Width.bits, rc_toBytes1] at H1
  kunfold
  kat hj RtCopy 22
  kat hj RtCopy 23
  klabel hj hf RtCopy 17
  apply Eventually.done
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · show (1 + r10.toBitVec).toNat = i + 1
    simp [BitVec.toNat_add, hr10]; omega
  · dsimp only
    rw [rc_split1 src rsi.toBitVec i hi hl, ← rc_take_succ src dst i hi hd,
      Mem.At_append_sep _ _ _ (by simp; omega), Mem.At_append_sep _ _ _ (by simp; omega)]
    simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi), List.length_cons, List.length_nil]
    ecancel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- The loop exit (r10 = n): `je` to `L_fvcopy_done`, `retq`. -/
theorem rc_exit (j : Nat) (hj : RtCopy.IsInfixAt Host.prog j) (hf : LabelsFresh RtCopy j)
    (ret : Int64) (M : DataMem → Prop) (s : MachineData) (hrdx : s.regs.rdx = s.regs.r10)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ret.toBitVec.toInt).At s.regs.rsp.toBitVec) ⋆ M) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ret ∧ st.data.regs.rsp = s.regs.rsp + 8
        ∧ st.data.regs.rax = s.regs.rax ∧ st.data.regs.rbx = s.regs.rbx ∧ st.data.regs.rcx = s.regs.rcx
        ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At s.regs.rsp.toBitVec) ⋆ M) st.data.dmem)
      ⟨s, Host.addrOf (j + 17)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hrdx ⊢
  subst hrdx
  kat hj RtCopy 17
  kat hj RtCopy 18
  kat hj RtCopy 19
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hj hf RtCopy 24
  kat hj RtCopy 24
  kat hj RtCopy 25
  apply load_step _ _ _ _ (Int.toBytes 8 ret.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  refine ⟨by simp, ?_, rfl, rfl, rfl, rfl, rfl, h_mem⟩
  apply UInt64.toBitVec_inj.mp; simp

/-- The copy loop from iteration `i` to the return. -/
theorem rc_loop (j : Nat) (hj : RtCopy.IsInfixAt Host.prog j) (hf : LabelsFresh RtCopy j)
    (src dst : List UInt8) (hd : dst.length = src.length) (hs : src.length < 2 ^ 64)
    (a b : BitVec 64) (ret : Int64) (R : DataMem → Prop) :
    ∀ (d i : Nat) (s : MachineData), d = src.length - i → i ≤ src.length →
      s.regs.r10.toNat = i → s.regs.rdx.toNat = src.length →
      s.regs.rsi.toBitVec = a → s.regs.rdi.toBitVec = b →
      (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At s.regs.rsp.toBitVec) ⋆ Eq (src.At a)
        ⋆ Eq ((src.take i ++ dst.drop i).At b) ⋆ R) s.dmem →
      Eventually (step1 Host.exe)
        (fun st => st.pc = ret ∧ st.data.regs.rsp = s.regs.rsp + 8
          ∧ st.data.regs.rax = s.regs.rax ∧ st.data.regs.rbx = s.regs.rbx ∧ st.data.regs.rcx = s.regs.rcx
          ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
          ∧ (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At s.regs.rsp.toBitVec) ⋆ Eq (src.At a)
            ⋆ Eq (src.At b) ⋆ R) st.data.dmem)
        ⟨s, Host.addrOf (j + 17)⟩ := by
  intro d
  induction d with
  | zero =>
    intro i s hd0 hi hr10 hrdx _ _ hm
    have hin : i = src.length := by omega
    subst hin
    have hrr : s.regs.rdx = s.regs.r10 := by
      apply UInt64.toNat_inj.mp; omega
    have e : src.take src.length ++ dst.drop src.length = src := by
      rw [List.take_length, List.drop_eq_nil_of_le (by omega), List.append_nil]
    rw [e] at hm
    refine eventually_mono (rc_exit j hj hf ret (Eq (src.At a) ⋆ Eq (src.At b) ⋆ R) s hrr (by ecancel)) ?_
    rintro st ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, by ecancel⟩
  | succ d ih =>
    intro i s hd0 hi hr10 hrdx hrsi hrdi hm
    have hil : i < src.length := by omega
    refine eventually_trans _ _ _ _ (rc_iter j hj hf src dst hd hs i hil a b
      (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At s.regs.rsp.toBitVec) ⋆ R) s hr10 hrdx hrsi hrdi (by ecancel)) ?_
    rintro ⟨s', pc'⟩ ⟨hpc, h10, hdx, hsi, hdi, hax, hbx, hcx, hsp, hbp, h14, hm'⟩
    dsimp only at hpc h10 hdx hsi hdi hax hbx hcx hsp hbp h14 hm'
    subst hpc
    have := ih (i + 1) s' (by omega) (by omega) h10 (by rw [hdx]; exact hrdx) (by rw [hsi]; exact hrsi)
      (by rw [hdi]; exact hrdi) (by rw [hsp]; ecancel)
    refine eventually_mono this ?_
    rintro st ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact ⟨h1, by rw [h2, hsp], by rw [h3, hax], by rw [h4, hbx], by rw [h5, hcx], by rw [h6, hbp], by rw [h7, h14],
      by rw [hsp] at h8; exact h8⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **`runtime.memmove` model.** The code at `runtime.memmove` satisfies `MemmoveC S` for every `S`. -/
theorem rt_memmove (j : Nat) (hj : RtCopy.IsInfixAt Host.prog j) (hf : LabelsFresh RtCopy j) (S : Nat) :
    MemmoveC S := by
  intro st ret src dst stk F hrcx hd hstk hm
  rw [label_at' hj hf (j := 0) (by rfl) (by rfl)]
  have hs : src.length < 2 ^ 64 := by rw [← hrcx]; exact st.regs.rcx.toNat_lt_size
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := st
  simp only at hrcx hm ⊢
  kat hj RtCopy 0
  kat hj RtCopy 1
  kat hj RtCopy 2
  kat hj RtCopy 3
  kat hj RtCopy 4
  klabel hj hf RtCopy 15
  kat hj RtCopy 15
  kat hj RtCopy 16
  refine eventually_mono (rc_loop j hj hf src dst hd hs rbx.toBitVec rax.toBitVec ret
    (Eq (stk.At (rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ F) _ 0 _ rfl (Nat.zero_le _) (by simp) (by simpa using hrcx)
    rfl rfl (by simp only [List.take_zero, List.drop_zero, List.nil_append]; ecancel)) ?_
  rintro st ⟨h1, h2, -, -, -, h6, h7, h8⟩
  exact ⟨h1, h2, h7, h6, stk, hstk, by ecancel⟩

theorem rg_zero3 (a b c : Nat) (hab : a ≤ b) (hbc : b ≤ c) :
    List.replicate c (0 : UInt8) = List.replicate a 0 ++ (List.replicate (b - a) 0 ++ List.replicate (c - b) 0) := by
  rw [List.replicate_append_replicate, List.replicate_append_replicate]; congr 1; omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **`runtime.growslice` model (1-byte elements).** The code at
`runtime.growslice` satisfies `GrowsliceC bumpHeap ty 1 S` for every `ty`, `S`:
new capacity `2·newLen + 192`, taken from the bump heap. -/
theorem rt_growslice (j : Nat) (hj : RtCopy.IsInfixAt Host.prog j) (hf : LabelsFresh RtCopy j)
    (ty : BitVec 64) (S : Nat) : GrowsliceC bumpHeap ty 1 S := by
  intro st ret old stk spill avail F _hesz _hty hnum holdcap hcap hbud hmax hold hstk hsp hm
  klabel hj hf RtCopy 5
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := st
  simp only at hnum holdcap hcap hbud hold hm ⊢
  have hnc := nextSliceCap_ge rbx.toNat rcx.toNat
  unfold maxAlloc at hmax
  simp only [Nat.one_mul] at hbud hold ⊢
  generalize hn : rbx.toNat = n at *
  generalize hol : n - rdi.toNat = ol at *
  have hm' : (bumpHeap avail ⋆ (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At rsp.toBitVec)
      ⋆ Eq (stk.At (rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (spill.At (rsp.toBitVec + 8))
      ⋆ Eq (old.At rax.toBitVec) ⋆ F)) mem := by ecancel
  obtain ⟨p, hp⟩ := sep_exists_left (Q := fun (p : BitVec 64) (m : DataMem) => p.toNat + avail < 2 ^ 64 ∧
    (Eq ((Int.toBytes 8 p.toInt).At (label "runtime.fvBump").toBitVec) ⋆ Eq ((List.replicate avail 0).At p)) m) hm'
  obtain ⟨hpa, hp⟩ := sep_pure_left hp
  have hnc' : 2 * n + 192 ≤ avail := by omega
  rw [rg_zero3 ol (2 * n + 192) avail (by omega) hnc', Mem.At_append_sep _ _ _ (by simp; omega),
    Mem.At_append_sep _ _ _ (by simp; omega)] at hp
  simp only [List.length_replicate] at hp
  kat hj RtCopy 5
  kat hj RtCopy 6
  kat hj RtCopy 7
  kat hj RtCopy 8
  kat hj RtCopy 9
  apply load_step _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hj RtCopy 10
  kat hj RtCopy 11
  kat hj RtCopy 12
  apply store_step _ _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hj RtCopy 13
  kat hj RtCopy 14
  klabel hj hf RtCopy 15
  kat hj RtCopy 15
  kat hj RtCopy 16
  have hc : (rbx.toBitVec + rbx.toBitVec * 1#64 + (192 : BitVec 64)).toNat = 2 * n + 192 := by
    have h192 : (192 : BitVec 64).toNat = 192 := rfl
    simp only [BitVec.mul_one, BitVec.toNat_add, UInt64.toNat_toBitVec, hn, h192]; omega
  have hq : (p + (rbx.toBitVec + rbx.toBitVec * 1#64 + (192 : BitVec 64)) * 1#64) = p + BitVec.ofNat 64 (2 * n + 192) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.mul_one, BitVec.toNat_add, hc]; simp
  have hq2 : p + BitVec.ofNat 64 ol + BitVec.ofNat 64 (2 * n + 192 - ol) = p + BitVec.ofNat 64 (2 * n + 192) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega
  rw [hq] at H1
  rw [hq2] at H1
  refine eventually_mono (rc_loop j hj hf old (List.replicate ol 0) (by simp; omega) (by omega) rax.toBitVec p ret
    (Eq ((List.replicate (2 * n + 192 - ol) 0).At (p + BitVec.ofNat 64 ol))
      ⋆ Eq ((Int.toBytes 8 (p + BitVec.ofNat 64 (2 * n + 192)).toInt).At (label "runtime.fvBump").toBitVec)
      ⋆ Eq ((List.replicate (avail - (2 * n + 192)) 0).At (p + BitVec.ofNat 64 (2 * n + 192)))
      ⋆ Eq (stk.At (rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (spill.At (rsp.toBitVec + 8)) ⋆ F)
    _ 0 _ rfl (Nat.zero_le _) (by simp)
    (by show (rbx.toBitVec - rdi.toBitVec).toNat = old.length
        rw [BitVec.toNat_sub, UInt64.toNat_toBitVec, UInt64.toNat_toBitVec, hn]; omega) rfl rfl
    (by simp only [List.take_zero, List.drop_zero, List.nil_append]; ecancel)) ?_
  rintro st ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  dsimp only at h2 h3 h4 h5 h6 h7 h8
  have hrc : st.data.regs.rcx.toNat = 2 * n + 192 := by rw [h5]; exact hc
  refine ⟨h1, h2, h6, h7, h4, by rw [hrc]; exact nextSliceCap_le n rcx.toNat hcap,
    by rw [hrc]; omega, stk, spill, List.replicate (2 * n + 192 - ol) 0, avail - (2 * n + 192), hstk, hsp,
    by simp; omega, by omega, ?_⟩
  have H : (bumpHeap (avail - (2 * n + 192)) ⋆ (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At rsp.toBitVec) ⋆ Eq (old.At rax.toBitVec) ⋆ Eq (old.At p)
      ⋆ Eq ((List.replicate (2 * n + 192 - ol) 0).At (p + BitVec.ofNat 64 ol))
      ⋆ Eq (stk.At (rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (spill.At (rsp.toBitVec + 8)) ⋆ F)) st.data.dmem := sep_mono_left (P' := bumpHeap (avail - (2 * n + 192)))
    (R := Eq ((Int.toBytes 8 ret.toBitVec.toInt).At rsp.toBitVec) ⋆ Eq (old.At rax.toBitVec) ⋆ Eq (old.At p)
      ⋆ Eq ((List.replicate (2 * n + 192 - ol) 0).At (p + BitVec.ofNat 64 ol))
      ⋆ Eq (stk.At (rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (spill.At (rsp.toBitVec + 8)) ⋆ F)
    (fun m hm => ⟨p + BitVec.ofNat 64 (2 * n + 192), by simp [BitVec.toNat_add]; omega, hm⟩) (by ecancel)
  rw [h3, Mem.At_append_sep _ _ _ (by simp; omega), hold]
  dsimp only
  have e : ∀ (A B C D E G I J : DataMem → Prop), (I ⋆ (A ⋆ D ⋆ E ⋆ G ⋆ B ⋆ C ⋆ J)) = (A ⋆ B ⋆ C ⋆ D ⋆ (E ⋆ G) ⋆ I ⋆ J) := by
    intro A B C D E G I J; ac_rfl
  rw [e] at H
  exact H

end Runtime
