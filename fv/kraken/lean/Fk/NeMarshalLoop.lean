import Fk.LuMarshal

/-!
# Nested.MarshalSSZTo: the inlined ListU64 element loop

Head `L_478` (directive 285): rax = i, rbx = dst ptr, rdx = base + 8i,
rdi = cap, r9 = n, r8 = element pointer p.
-/

open Fk Fk.Code
variable [Host]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem nem_iter (k : Nat) (hk : NestedMarshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh NestedMarshalSSZTo k)
    (bs d : List UInt8) (n : Nat) (hn : n ≤ 16) (hbs : bs.length = 8 * n) (hd : d.length = 8 * n) (i : Nat) (hi : i < n)
    (b p : BitVec 64) (L cap : Nat) (hcap : L + 4 + 8 * n ≤ cap) (hcap63 : cap < 2 ^ 63)
    (R : DataMem → Prop) (s : MachineData)
    (hrax : s.regs.rax.toNat = i) (hrbx : s.regs.rbx.toBitVec = b) (hrdx : s.regs.rdx.toNat = L + 4 + 8 * i)
    (hrdi : s.regs.rdi.toNat = cap) (hr8 : s.regs.r9.toNat = n) (hr9 : s.regs.r8.toBitVec = p)
    (sp bp : UInt64) (hrsp : s.regs.rsp = sp) (hrbp : s.regs.rbp = bp)
    (h_mem : s.dmem =⋆ Eq (bs.At p) ⋆ Eq ((bs.take (8 * i) ++ d.drop (8 * i)).At (b + BitVec.ofNat 64 (L + 4))) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 285) ∧ st.data.regs.rax.toNat = i + 1 ∧ st.data.regs.rbx.toBitVec = b
        ∧ st.data.regs.rdx.toNat = L + 4 + 8 * (i + 1) ∧ st.data.regs.rdi.toNat = cap ∧ st.data.regs.r9.toNat = n
        ∧ st.data.regs.r8.toBitVec = p ∧ st.data.regs.rsp = sp ∧ st.data.regs.rbp = bp
        ∧ (Eq (bs.At p) ⋆ Eq ((bs.take (8 * (i + 1)) ++ d.drop (8 * (i + 1))).At (b + BitVec.ofNat 64 (L + 4))) ⋆ R)
          st.data.dmem)
      ⟨s, Host.addrOf (k + 285)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hrax hrbx hrdx hrdi hr8 hr9 hrsp hrbp ⊢
  subst hrbx hr9 hrsp hrbp
  have := rax.toNat_lt_size; have := rdx.toNat_lt_size; have := rdi.toNat_lt_size; have := r9.toNat_lt_size
  simp only [UInt64.size] at *
  have hlen : bs.length < 2 ^ 64 := by omega
  rw [block_split bs r8.toBitVec (8 * i) (by omega) hlen, mix_split bs d i,
    Mem.At_append_sep _ _ _ (by simp; omega), Mem.At_append_sep _ _ _ (by simp; omega)] at h_mem
  simp only [List.length_take, List.length_drop, hbs, hd, Nat.min_eq_left (show 8 * i ≤ 8 * n by omega),
    Nat.min_eq_left (show 8 ≤ 8 * n - 8 * i by omega)] at h_mem
  kat hk NestedMarshalSSZTo 285
  kat hk NestedMarshalSSZTo 286
  kat hk NestedMarshalSSZTo 287
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.signed] at h
    exact jge_false rax.toBitVec r9.toBitVec (by simp; omega) (by simp; omega) (by simpa using h)
  simp only [Effects.All]
  kat hk NestedMarshalSSZTo 288
  kat hk NestedMarshalSSZTo 289
  rw [idx8' _ _ i (by simpa using hrax) (by omega)]
  apply load_step _ _ _ _ ((bs.drop (8 * i)).take 8) _ _ (by ecancel) (by simp; omega)
  kunfold
  kat hk NestedMarshalSSZTo 290
  kat hk NestedMarshalSSZTo 291
  split
  case isFalse h =>
    exfalso; simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    have := lum_room rdx.toBitVec rdi.toBitVec L n i cap (by simpa using hrdx) hi (by simpa using hrdi) hcap hcap63
    simp at h; omega
  simp only [Effects.All]
  klabel hk hf NestedMarshalSSZTo 282
  kat hk NestedMarshalSSZTo 282
  kat hk NestedMarshalSSZTo 283
  rw [lum_addr _ _ L i (by simpa using hrdx) (by omega)]
  apply store_step _ _ _ _ _ ((d.drop (8 * i)).take 8) _ _ (by ecancel) (by simp; omega)
  intro m1 H1
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl _ (show ((bs.drop (8 * i)).take 8).length = 8 by simp; omega)] at H1
  kunfold
  kat hk NestedMarshalSSZTo 284
  apply Eventually.done
  refine ⟨rfl, ?_, rfl, ?_, hrdi, hr8, rfl, rfl, rfl, ?_⟩
  · exact inc_toNat16 _ i (by simpa using hrax) (by omega)
  · exact lum_rdx _ L i (by simpa using hrdx) (by omega)
  · dsimp only
    rw [← mix_step bs d i, Mem.At_append_sep _ _ _ (by simp; omega), Mem.At_append_sep _ _ _ (by simp; omega),
      block_split bs r8.toBitVec (8 * i) (by omega) hlen]
    simp only [List.length_take, List.length_drop, hbs, hd, Nat.min_eq_left (show 8 * i ≤ 8 * n by omega),
      Nat.min_eq_left (show 8 ≤ 8 * n - 8 * i by omega)]
    (try simp only [BitVec.ofNat_eq_ofNat] at H1 ⊢)
    ecancel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem nem_exit (k : Nat) (hk : NestedMarshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh NestedMarshalSSZTo k) (P : MachineState → Prop) (s : MachineData)
    (hrr : s.regs.rax = s.regs.r9)
    (hP : ∀ f : StatusFlags, P ⟨⟨s.regs, s.zmms, f, s.dmem⟩, Host.addrOf (k + 308)⟩) :
    Eventually (step1 Host.exe) P ⟨s, Host.addrOf (k + 285)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrr hP ⊢
  subst hrr
  kat hk NestedMarshalSSZTo 285
  kat hk NestedMarshalSSZTo 286
  kat hk NestedMarshalSSZTo 287
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
  simp only [Effects.All]
  klabel hk hf NestedMarshalSSZTo 308
  exact Eventually.done _ (hP _)

theorem nem_loop (k : Nat) (hk : NestedMarshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh NestedMarshalSSZTo k)
    (bs d : List UInt8) (n : Nat) (hn : n ≤ 16) (hbs : bs.length = 8 * n) (hd : d.length = 8 * n)
    (b p : BitVec 64) (L cap : Nat) (hcap : L + 4 + 8 * n ≤ cap) (hcap63 : cap < 2 ^ 63)
    (R : DataMem → Prop) (sp bp : UInt64) :
    ∀ j i (s : MachineData), i + j = n →
    s.regs.rax.toNat = i → s.regs.rbx.toBitVec = b → s.regs.rdx.toNat = L + 4 + 8 * i →
    s.regs.rdi.toNat = cap → s.regs.r9.toNat = n → s.regs.r8.toBitVec = p → s.regs.rsp = sp → s.regs.rbp = bp →
    (s.dmem =⋆ Eq (bs.At p) ⋆ Eq ((bs.take (8 * i) ++ d.drop (8 * i)).At (b + BitVec.ofNat 64 (L + 4))) ⋆ R) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 308) ∧ st.data.regs.rbx.toBitVec = b
        ∧ st.data.regs.rdx.toNat = L + 4 + 8 * n ∧ st.data.regs.rdi.toNat = cap
        ∧ st.data.regs.rsp = sp ∧ st.data.regs.rbp = bp
        ∧ (Eq (bs.At p) ⋆ Eq (bs.At (b + BitVec.ofNat 64 (L + 4))) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 285)⟩
  | 0, i, s, hij, hrax, hrbx, hrdx, hrdi, hr8, _, hrsp, hrbp, h_mem => by
    have hin : i = n := by omega
    subst hin
    refine nem_exit k hk hf _ s (UInt64.toNat_inj.mp (by omega)) fun _ => ⟨rfl, hrbx, hrdx, hrdi, hrsp, hrbp, ?_⟩
    rw [List.take_of_length_le (by omega), List.drop_of_length_le (by omega), List.append_nil] at h_mem
    exact h_mem
  | j + 1, i, s, hij, hrax, hrbx, hrdx, hrdi, hr8, hr9, hrsp, hrbp, h_mem => by
    refine eventually_trans _ _ _ _
      (nem_iter k hk hf bs d n hn hbs hd i (by omega) b p L cap hcap hcap63 R s hrax hrbx hrdx hrdi hr8 hr9 sp bp hrsp hrbp h_mem) ?_
    rintro ⟨s', pc⟩ ⟨hpc, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    dsimp only at hpc; subst hpc
    exact nem_loop k hk hf bs d n hn hbs hd b p L cap hcap hcap63 R sp bp j (i + 1) s' (by omega) h1 h2 h3 h4 h5 h6 h7 h8 h9

