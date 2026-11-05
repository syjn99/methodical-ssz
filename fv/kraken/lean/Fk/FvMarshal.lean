import Fk.FvAccept

/-!
# FixedVec.MarshalSSZTo, fast path, on Kraken main

When `dst` has room (`len + 64 ≤ cap`) and `len(c.W) = 4`, the function appends
R (32 bytes, by `runtime.memmove`) and the four W elements (8 bytes each, LE) to
`dst` and returns `(ptr, len + 64, cap, nil)`. `dst[:len]` (`pre`) is unchanged.
No `growslice` call is taken.

Loop (`fvm_iter`, head `L_d0` = directive 56): rax = i, rbx = dst ptr,
rdx = len + 32 + 8i, rdi = cap, r8 = W ptr. Output at dst + len + 32:
`ws.take (8i) ++ d.drop (8i)` (old bytes `d` past the written part).
-/

open Fk Fk.Code
variable [Host]

theorem mix_split (ws d : List UInt8) (i : Nat) :
    ws.take (8 * i) ++ d.drop (8 * i) = ws.take (8 * i) ++ ((d.drop (8 * i)).take 8 ++ d.drop (8 * i + 8)) := by
  rw [← List.drop_drop, List.take_append_drop]

theorem mix_step (ws d : List UInt8) (i : Nat) :
    ws.take (8 * i) ++ ((ws.drop (8 * i)).take 8 ++ d.drop (8 * i + 8)) = ws.take (8 * (i + 1)) ++ d.drop (8 * (i + 1)) := by
  rw [← List.append_assoc, ← List.take_add, show 8 * i + 8 = 8 * (i + 1) by omega]

theorem idx8 (x y : BitVec 64) (i : Nat) (h : y.toNat = i) (hi : i < 4) :
    x + y * 8#64 = x + BitVec.ofNat 64 (8 * i) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_mul]; omega

theorem add8_neg8 (x y : BitVec 64) : 8 + y + x * 1#64 + -8 = x + y := by
  rw [BitVec.mul_one, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm 8, BitVec.add_assoc, BitVec.add_assoc]
  rw [show (-8 : BitVec 64) + 8 = 0 by decide, Fk.add_lit_zero, BitVec.add_comm]

theorem fvm_addr (x y : BitVec 64) (L i : Nat) (h : y.toNat = L + 32 + 8 * i) (hL : L + 64 < 2 ^ 63) :
    8 + y + x * 1#64 + -8 = x + BitVec.ofNat 64 (L + 32) + BitVec.ofNat 64 (8 * i) := by
  rw [add8_neg8, BitVec.add_assoc]; congr 1
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega

theorem fvm_room (y z : BitVec 64) (L i cap : Nat) (h : y.toNat = L + 32 + 8 * i) (hi : i < 4)
    (hz : z.toNat = cap) (hc : L + 64 ≤ cap) (hc63 : cap < 2 ^ 63) : (8 + y).toNat ≤ z.toNat := by
  simp [BitVec.toNat_add]; omega

theorem fvm_rdx (y : BitVec 64) (L i : Nat) (h : y.toNat = L + 32 + 8 * i) (hi : i < 4) (hL : L + 64 < 2 ^ 63) :
    (8 + y).toNat = L + 32 + 8 * (i + 1) := by
  simp [BitVec.toNat_add]; omega

theorem inc_toNat (x : BitVec 64) (i : Nat) (h : x.toNat = i) (hi : i < 4) : (x + 1).toNat = i + 1 := by
  simp [BitVec.toNat_add]; omega

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem fvm_iter (k : Nat) (hk : FixedVecMarshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh FixedVecMarshalSSZTo k)
    (ws d : List UInt8) (hws : ws.length = 32) (hd : d.length = 32) (i : Nat) (hi : i < 4)
    (b w : BitVec 64) (L cap : Nat) (hcap : L + 64 ≤ cap) (hcap63 : cap < 2 ^ 63)
    (R : DataMem → Prop) (s : MachineData)
    (hrax : s.regs.rax.toNat = i) (hrbx : s.regs.rbx.toBitVec = b) (hrdx : s.regs.rdx.toNat = L + 32 + 8 * i)
    (hrdi : s.regs.rdi.toNat = cap) (hr8 : s.regs.r8.toBitVec = w)
    (sp bp : UInt64) (hrsp : s.regs.rsp = sp) (hrbp : s.regs.rbp = bp)
    (h_mem : s.dmem =⋆ Eq (ws.At w) ⋆ Eq ((ws.take (8 * i) ++ d.drop (8 * i)).At (b + BitVec.ofNat 64 (L + 32))) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 56) ∧ st.data.regs.rax.toNat = i + 1 ∧ st.data.regs.rbx.toBitVec = b
        ∧ st.data.regs.rdx.toNat = L + 32 + 8 * (i + 1) ∧ st.data.regs.rdi.toNat = cap ∧ st.data.regs.r8.toBitVec = w
        ∧ st.data.regs.rsp = sp ∧ st.data.regs.rbp = bp
        ∧ (Eq (ws.At w) ⋆ Eq ((ws.take (8 * (i + 1)) ++ d.drop (8 * (i + 1))).At (b + BitVec.ofNat 64 (L + 32))) ⋆ R)
          st.data.dmem)
      ⟨s, Host.addrOf (k + 56)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hrax hrbx hrdx hrdi hr8 hrsp hrbp ⊢
  subst hrbx hr8 hrsp hrbp
  have := rax.toNat_lt_size; have := rdx.toNat_lt_size; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *
  have hlen : ws.length < 2 ^ 64 := by omega
  rw [block_split ws r8.toBitVec (8 * i) (by omega) hlen, mix_split ws d i,
    Mem.At_append_sep _ _ _ (by simp; omega), Mem.At_append_sep _ _ _ (by simp; omega)] at h_mem
  simp only [List.length_take, List.length_drop, hws, hd, Nat.min_eq_left (show 8 * i ≤ 32 by omega),
    Nat.min_eq_left (show 8 ≤ 32 - 8 * i by omega)] at h_mem
  kat hk FixedVecMarshalSSZTo 56
  kat hk FixedVecMarshalSSZTo 57
  kat hk FixedVecMarshalSSZTo 58
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.signed] at h
    exact jge_false rax.toBitVec 4 (by simp) (by simp; omega) (by simpa using h)
  simp only [Effects.All]
  kat hk FixedVecMarshalSSZTo 59
  kat hk FixedVecMarshalSSZTo 60
  rw [idx8 _ _ i (by simpa using hrax) hi]
  apply load_step _ _ _ _ ((ws.drop (8 * i)).take 8) _ _ (by ecancel) (by simp; omega)
  kunfold
  kat hk FixedVecMarshalSSZTo 61
  kat hk FixedVecMarshalSSZTo 62
  kat hk FixedVecMarshalSSZTo 63
  split
  case isFalse h =>
    exfalso; simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    have := fvm_room rdx.toBitVec rdi.toBitVec L i cap (by simpa using hrdx) hi (by simpa using hrdi) hcap hcap63
    simp at h; omega
  simp only [Effects.All]
  klabel hk hf FixedVecMarshalSSZTo 53
  kat hk FixedVecMarshalSSZTo 53
  kat hk FixedVecMarshalSSZTo 54
  rw [fvm_addr _ _ L i (by simpa using hrdx) (by omega)]
  apply store_step _ _ _ _ _ ((d.drop (8 * i)).take 8) _ _ (by ecancel) (by simp; omega)
  intro m1 H1
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl _ (show ((ws.drop (8 * i)).take 8).length = 8 by simp; omega)] at H1
  kunfold
  kat hk FixedVecMarshalSSZTo 55
  apply Eventually.done
  refine ⟨rfl, ?_, rfl, ?_, hrdi, rfl, rfl, rfl, ?_⟩
  · exact inc_toNat _ i (by simpa using hrax) hi
  · exact fvm_rdx _ L i (by simpa using hrdx) hi (by omega)
  · dsimp only
    rw [← mix_step ws d i, Mem.At_append_sep _ _ _ (by simp; omega), Mem.At_append_sep _ _ _ (by simp; omega),
      block_split ws r8.toBitVec (8 * i) (by omega) hlen]
    simp only [List.length_take, List.length_drop, hws, hd, Nat.min_eq_left (show 8 * i ≤ 32 by omega),
      Nat.min_eq_left (show 8 ≤ 32 - 8 * i by omega)]
    (try simp only [BitVec.ofNat_eq_ofNat] at H1 ⊢)
    ecancel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem fvm_exit (k : Nat) (hk : FixedVecMarshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh FixedVecMarshalSSZTo k) (P : MachineState → Prop) (s : MachineData)
    (hrax : s.regs.rax.toNat = 4) (hP : ∀ f : StatusFlags, P ⟨⟨s.regs, s.zmms, f, s.dmem⟩, Host.addrOf (k + 79)⟩) :
    Eventually (step1 Host.exe) P ⟨s, Host.addrOf (k + 56)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrax hP ⊢
  have hr : rax = 4 := UInt64.toNat_inj.mp (by simpa using hrax)
  subst hr
  kat hk FixedVecMarshalSSZTo 56
  kat hk FixedVecMarshalSSZTo 57
  kat hk FixedVecMarshalSSZTo 58
  split
  case isFalse h => exfalso; exact h (by decide)
  simp only [Effects.All]
  klabel hk hf FixedVecMarshalSSZTo 79
  exact Eventually.done _ (hP _)

theorem fvm_loop (k : Nat) (hk : FixedVecMarshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh FixedVecMarshalSSZTo k)
    (ws d : List UInt8) (hws : ws.length = 32) (hd : d.length = 32)
    (b w : BitVec 64) (L cap : Nat) (hcap : L + 64 ≤ cap) (hcap63 : cap < 2 ^ 63)
    (R : DataMem → Prop) (sp bp : UInt64) :
    ∀ j i (s : MachineData), i + j = 4 →
    s.regs.rax.toNat = i → s.regs.rbx.toBitVec = b → s.regs.rdx.toNat = L + 32 + 8 * i →
    s.regs.rdi.toNat = cap → s.regs.r8.toBitVec = w → s.regs.rsp = sp → s.regs.rbp = bp →
    (s.dmem =⋆ Eq (ws.At w) ⋆ Eq ((ws.take (8 * i) ++ d.drop (8 * i)).At (b + BitVec.ofNat 64 (L + 32))) ⋆ R) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 79) ∧ st.data.regs.rbx.toBitVec = b
        ∧ st.data.regs.rdx.toNat = L + 64 ∧ st.data.regs.rdi.toNat = cap
        ∧ st.data.regs.rsp = sp ∧ st.data.regs.rbp = bp
        ∧ (Eq (ws.At w) ⋆ Eq (ws.At (b + BitVec.ofNat 64 (L + 32))) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 56)⟩
  | 0, i, s, hij, hrax, hrbx, hrdx, hrdi, _, hrsp, hrbp, h_mem => by
    have hin : i = 4 := by omega
    subst hin
    refine fvm_exit k hk hf _ s hrax fun _ => ⟨rfl, hrbx, by rw [hrdx], hrdi, hrsp, hrbp, ?_⟩
    rw [List.take_of_length_le (by omega), List.drop_of_length_le (by omega), List.append_nil] at h_mem
    exact h_mem
  | j + 1, i, s, hij, hrax, hrbx, hrdx, hrdi, hr8, hrsp, hrbp, h_mem => by
    refine eventually_trans _ _ _ _
      (fvm_iter k hk hf ws d hws hd i (by omega) b w L cap hcap hcap63 R s hrax hrbx hrdx hrdi hr8 sp bp hrsp hrbp h_mem) ?_
    rintro ⟨s', pc⟩ ⟨hpc, h1, h2, h3, h4, h5, h6, h7, h8⟩
    dsimp only at hpc; subst hpc
    exact fvm_loop k hk hf ws d hws hd b w L cap hcap hcap63 R sp bp j (i + 1) s' (by omega) h1 h2 h3 h4 h5 h6 h7 h8

theorem slot120 (x : BitVec 64) : x - 8#64 - 104 - 8#64 = x - 120 := by bv_omega
theorem f96 (x : BitVec 64) : x - 8#64 - 104 + 96 = x - 16 := by bv_omega
theorem f88 (x : BitVec 64) : x - 8#64 - 104 + 88 = x - 24 := by bv_omega
theorem f80 (x : BitVec 64) : x - 8#64 - 104 + 80 = x - 32 := by bv_omega
theorem f72 (x : BitVec 64) : x - 8#64 - 104 + 72 = x - 40 := by bv_omega
theorem f120 (x : BitVec 64) : x - 8#64 - 104 + 120 = x + 8 := by bv_omega
theorem g120 (x : BitVec 64) (o : BitVec 64) :
    ({ toBitVec := x - 120 } + 8 : UInt64).toBitVec + o = x - 112 + o := by
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
theorem h120 (x : BitVec 64) : x - 112 + 120 = x + 8 := by bv_omega
theorem k104 (x : BitVec 64) : 104 + ({ toBitVec := x - 120 } + 8 : UInt64).toBitVec = x - 8 := by
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
theorem h72 (x : BitVec 64) : x - 112 + 72 = x - 40 := by bv_omega
theorem h96 (x : BitVec 64) : x - 112 + 96 = x - 16 := by bv_omega
theorem h80 (x : BitVec 64) : x - 112 + 80 = x - 32 := by bv_omega
theorem h88 (x : BitVec 64) : x - 112 + 88 = x - 24 := by bv_omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem fv_marshal_main (k : Nat) (hk : FixedVecMarshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh FixedVecMarshalSSZTo k)
    (rb ws pre d0 d1 : List UInt8) (hrb : rb.length = 32) (hws : ws.length = 32)
    (hd0 : d0.length = 32) (hd1 : d1.length = 32) (w : BitVec 64)
    (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l1 l2 l3 l4 rslot r0 r1 : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (hl1 : l1.length = 8) (hl2 : l2.length = 8)
    (hl3 : l3.length = 8) (hl4 : l4.length = 8) (hrs : rslot.length = 8)
    (hr0 : r0 ++ r1 = rb) (hr0l : r0.length = 1)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (l1.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (l2.At (s.regs.rsp.toBitVec - 24)) ⋆ Eq (l3.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (l4.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 120)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (r0.At s.regs.rax.toBitVec) ⋆ Eq (r1.At (s.regs.rax.toBitVec + 1))
      ⋆ Eq ((Int.toBytes 8 w.toInt).At (s.regs.rax.toBitVec + 32)) ⋆ Eq ((Int.toBytes 8 4).At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (ws.At w)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + BitVec.ofNat 64 (s.regs.rcx.toNat + 32))) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 120 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 64 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hmm : MemmoveC S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 64 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (rb.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (ws.At (s.regs.rbx.toBitVec + BitVec.ofNat 64 (s.regs.rcx.toNat + 32)))
          ⋆ Eq (rb.At s.regs.rax.toBitVec) ⋆ Eq (ws.At w) ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hcap hcap63 hpre ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *
  kat hk FixedVecMarshalSSZTo 0
  kat hk FixedVecMarshalSSZTo 1
  kat hk FixedVecMarshalSSZTo 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk FixedVecMarshalSSZTo 3
  split
  · rename_i h; exfalso
    simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk FixedVecMarshalSSZTo 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk FixedVecMarshalSSZTo 5
  kat hk FixedVecMarshalSSZTo 6
  kat hk FixedVecMarshalSSZTo 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by bv_omega) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk FixedVecMarshalSSZTo 8
  apply store_step_at _ _ (rsp.toBitVec + 8) _ _ _ s1 _ _ (by bv_omega) (by ecancel) (by exact h1)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk FixedVecMarshalSSZTo 9
  apply load_step _ _ _ _ r0 _ _ (by ecancel) (by exact hr0l)
  kunfold
  intro _
  kat hk FixedVecMarshalSSZTo 10
  kat hk FixedVecMarshalSSZTo 11
  kat hk FixedVecMarshalSSZTo 12
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf FixedVecMarshalSSZTo 25
  kat hk FixedVecMarshalSSZTo 25
  kat hk FixedVecMarshalSSZTo 26
  apply store_step_at _ _ (rsp.toBitVec - 16) _ _ _ l1 _ _ (f96 _) (by ecancel) (by exact hl1)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  kat hk FixedVecMarshalSSZTo 27
  apply store_step_at _ _ (rsp.toBitVec - 32) _ _ _ l3 _ _ (f80 _) (by ecancel) (by exact hl3)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  kat hk FixedVecMarshalSSZTo 28
  apply store_step_at _ _ (rsp.toBitVec - 40) _ _ _ l4 _ _ (f72 _) (by ecancel) (by exact hl4)
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  kat hk FixedVecMarshalSSZTo 29
  kat hk FixedVecMarshalSSZTo 30
  kat hk FixedVecMarshalSSZTo 31
  kat hk FixedVecMarshalSSZTo 32
  kat hk FixedVecMarshalSSZTo 33
  apply store_step_at _ _ (rsp.toBitVec - 120) _ _ _ rslot _ _ (slot120 _) (by ecancel) (by exact hrs)
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  have hmerge : Eq (rb.At rax.toBitVec) = Eq (r0.At rax.toBitVec) ⋆ Eq (r1.At (rax.toBitVec + 1)) := by
    rw [← hr0, Mem.At_append_sep _ _ _ (by rw [← List.length_append, hr0, hrb]; decide), hr0l]; rfl
  rw [slot120] at *
  rw [show rbx.toBitVec + rcx.toBitVec * 1#64 = rbx.toBitVec + rcx.toBitVec by rw [BitVec.mul_one]] at *
  refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (k + 33 + 1)) rb d0 scratch _
    (by rw [hrb]; rfl) (by rw [hrb, hd0]) hsc (by dsimp only; rw [hmerge]; ecancel)) ?_
  rintro ⟨e1, pc1⟩ ⟨hpc1, hrsp1, stk1, hstk1, Hm1⟩
  dsimp only at hpc1 hrsp1 Hm1
  subst hpc1
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩,
    zmms1, flags1, mem1⟩ := e1
  simp only at hrsp1 Hm1
  subst hrsp1
  kat hk FixedVecMarshalSSZTo 34
  rw [g120, h120]
  apply load_step _ _ _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk FixedVecMarshalSSZTo 35
  apply load_step_at _ _ (rax.toBitVec + 40) _ _ (Int.toBytes 8 4) _ _ (by kaddr) (by ecancel) (by rfl)
  simp only [show Int.ofBytes (Int.toBytes 8 4) = 4 by decide]
  kunfold
  kat hk FixedVecMarshalSSZTo 36
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk FixedVecMarshalSSZTo 37
  apply load_step_at _ _ (rax.toBitVec + 32) _ _ (Int.toBytes 8 w.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk FixedVecMarshalSSZTo 38
  rw [g120, h88]
  apply store_step _ _ _ _ _ l2 _ _ (by ecancel) (by exact hl2)
  intro m8 H8
  simp only [Width.bytes, Width.bits] at H8
  kunfold
  kat hk FixedVecMarshalSSZTo 39
  rw [g120, h72]
  apply load_step _ _ _ _ (Int.toBytes 8 rdi.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk FixedVecMarshalSSZTo 40
  rw [g120, h96]
  apply load_step _ _ _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk FixedVecMarshalSSZTo 41
  rw [g120, h80]
  apply load_step _ _ _ _ (Int.toBytes 8 (rcx.toBitVec + 32).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk FixedVecMarshalSSZTo 42
  intro _
  kat hk FixedVecMarshalSSZTo 43
  klabel hk hf FixedVecMarshalSSZTo 56
  refine eventually_trans _ _ _ _ (fvm_loop k hk hf ws d1 hws hd1 rbx.toBitVec w rcx.toNat rdi.toNat hcap hcap63 _ _ _ 4 0 _
    (by omega) (by simp) (by simp [Fk.ofInt_ofBytes_toBytes64]) (by simp [BitVec.toNat_add, show UInt64.toNat 32 = 32 from rfl]; omega) (by simp) (by simp) rfl rfl
    (by simp only [Nat.mul_zero, List.take_zero, List.nil_append, List.drop_zero]; ecancel)) ?_
  rintro ⟨e3, pc3⟩ ⟨hpc3, hrbx3, hrdx3, hrdi3, hrsp3, hrbp3, Hm3⟩
  dsimp only at hpc3 hrbx3 hrdx3 hrdi3 hrsp3 hrbp3 Hm3
  subst hpc3
  obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,
    zmms3, flags3, mem3⟩ := e3
  simp only at hrbx3 hrdx3 hrdi3 hrsp3 hrbp3 Hm3
  subst hrsp3 hrbp3
  kat hk FixedVecMarshalSSZTo 79
  kat hk FixedVecMarshalSSZTo 80
  kat hk FixedVecMarshalSSZTo 81
  kat hk FixedVecMarshalSSZTo 82
  kat hk FixedVecMarshalSSZTo 83
  intro _
  kat hk FixedVecMarshalSSZTo 84
  intro _
  kat hk FixedVecMarshalSSZTo 85
  kat hk FixedVecMarshalSSZTo 86
  rw [k104]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk FixedVecMarshalSSZTo 87
  rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, ?_, trivial, ?_⟩
  · exact UInt64.toBitVec_inj.mp hrbx3
  · simpa using hrdx3
  · exact UInt64.toNat_inj.mp (by simpa using hrdi3)
  · apply UInt64.toBitVec_inj.mp; simp
  · apply UInt64.toBitVec_inj.mp; simp
  · apply UInt64.toBitVec_inj.mp; simp
  · exact sep_true (by ecancel)
