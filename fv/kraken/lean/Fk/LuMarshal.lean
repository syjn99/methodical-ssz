import Fk.FvMarshal
import Fk.LuRejectCall

/-!
# ListU64.MarshalSSZTo, fast path, on Kraken main

When `dst` has room (`len + 4 + 8n ≤ cap`, n = len(c.L) ≤ 16), the function
appends the offset 4 (`ssz.WriteOffset`, 4 bytes) and the n elements (8 bytes
each, LE), and returns `(ptr, len + 4 + 8n, cap, nil)`.
-/

open Fk Fk.Code
variable [Host]

theorem lum_addr (x y : BitVec 64) (L i : Nat) (h : y.toNat = L + 4 + 8 * i) (hL : L + 4 + 8 * i < 2 ^ 63) :
    8 + y + x * 1#64 + -8 = x + BitVec.ofNat 64 (L + 4) + BitVec.ofNat 64 (8 * i) := by
  rw [add8_neg8, BitVec.add_assoc]; congr 1
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega

theorem lum_room (y z : BitVec 64) (L n i cap : Nat) (h : y.toNat = L + 4 + 8 * i) (hi : i < n)
    (hz : z.toNat = cap) (hc : L + 4 + 8 * n ≤ cap) (hc63 : cap < 2 ^ 63) : (8 + y).toNat ≤ z.toNat := by
  simp [BitVec.toNat_add]; omega

theorem lum_rdx (y : BitVec 64) (L i : Nat) (h : y.toNat = L + 4 + 8 * i) (hL : L + 4 + 8 * (i + 1) < 2 ^ 63) :
    (8 + y).toNat = L + 4 + 8 * (i + 1) := by
  simp [BitVec.toNat_add]; omega

theorem inc_toNat16 (x : BitVec 64) (i : Nat) (h : x.toNat = i) (hi : i < 16) : (x + 1).toNat = i + 1 := by
  simp [BitVec.toNat_add]; omega

theorem idx8' (x y : BitVec 64) (i : Nat) (h : y.toNat = i) (hi : i < 16) :
    x + y * 8#64 = x + BitVec.ofNat 64 (8 * i) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_mul]; omega

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem lum_iter (k : Nat) (hk : ListU64MarshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListU64MarshalSSZTo k)
    (bs d : List UInt8) (n : Nat) (hn : n ≤ 16) (hbs : bs.length = 8 * n) (hd : d.length = 8 * n) (i : Nat) (hi : i < n)
    (b p : BitVec 64) (L cap : Nat) (hcap : L + 4 + 8 * n ≤ cap) (hcap63 : cap < 2 ^ 63)
    (R : DataMem → Prop) (s : MachineData)
    (hrax : s.regs.rax.toNat = i) (hrbx : s.regs.rbx.toBitVec = b) (hrdx : s.regs.rdx.toNat = L + 4 + 8 * i)
    (hrdi : s.regs.rdi.toNat = cap) (hr8 : s.regs.r8.toNat = n) (hr9 : s.regs.r9.toBitVec = p)
    (sp bp : UInt64) (hrsp : s.regs.rsp = sp) (hrbp : s.regs.rbp = bp)
    (h_mem : s.dmem =⋆ Eq (bs.At p) ⋆ Eq ((bs.take (8 * i) ++ d.drop (8 * i)).At (b + BitVec.ofNat 64 (L + 4))) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 48) ∧ st.data.regs.rax.toNat = i + 1 ∧ st.data.regs.rbx.toBitVec = b
        ∧ st.data.regs.rdx.toNat = L + 4 + 8 * (i + 1) ∧ st.data.regs.rdi.toNat = cap ∧ st.data.regs.r8.toNat = n
        ∧ st.data.regs.r9.toBitVec = p ∧ st.data.regs.rsp = sp ∧ st.data.regs.rbp = bp
        ∧ (Eq (bs.At p) ⋆ Eq ((bs.take (8 * (i + 1)) ++ d.drop (8 * (i + 1))).At (b + BitVec.ofNat 64 (L + 4))) ⋆ R)
          st.data.dmem)
      ⟨s, Host.addrOf (k + 48)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hrax hrbx hrdx hrdi hr8 hr9 hrsp hrbp ⊢
  subst hrbx hr9 hrsp hrbp
  have := rax.toNat_lt_size; have := rdx.toNat_lt_size; have := rdi.toNat_lt_size; have := r8.toNat_lt_size
  simp only [UInt64.size] at *
  have hlen : bs.length < 2 ^ 64 := by omega
  rw [block_split bs r9.toBitVec (8 * i) (by omega) hlen, mix_split bs d i,
    Mem.At_append_sep _ _ _ (by simp; omega), Mem.At_append_sep _ _ _ (by simp; omega)] at h_mem
  simp only [List.length_take, List.length_drop, hbs, hd, Nat.min_eq_left (show 8 * i ≤ 8 * n by omega),
    Nat.min_eq_left (show 8 ≤ 8 * n - 8 * i by omega)] at h_mem
  kat hk ListU64MarshalSSZTo 48
  kat hk ListU64MarshalSSZTo 49
  kat hk ListU64MarshalSSZTo 50
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.signed] at h
    exact jge_false rax.toBitVec r8.toBitVec (by simp; omega) (by simp; omega) (by simpa using h)
  simp only [Effects.All]
  kat hk ListU64MarshalSSZTo 51
  kat hk ListU64MarshalSSZTo 52
  rw [idx8' _ _ i (by simpa using hrax) (by omega)]
  apply load_step _ _ _ _ ((bs.drop (8 * i)).take 8) _ _ (by ecancel) (by simp; omega)
  kunfold
  kat hk ListU64MarshalSSZTo 53
  kat hk ListU64MarshalSSZTo 54
  split
  case isFalse h =>
    exfalso; simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    have := lum_room rdx.toBitVec rdi.toBitVec L n i cap (by simpa using hrdx) hi (by simpa using hrdi) hcap hcap63
    simp at h; omega
  simp only [Effects.All]
  klabel hk hf ListU64MarshalSSZTo 45
  kat hk ListU64MarshalSSZTo 45
  kat hk ListU64MarshalSSZTo 46
  rw [lum_addr _ _ L i (by simpa using hrdx) (by omega)]
  apply store_step _ _ _ _ _ ((d.drop (8 * i)).take 8) _ _ (by ecancel) (by simp; omega)
  intro m1 H1
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl _ (show ((bs.drop (8 * i)).take 8).length = 8 by simp; omega)] at H1
  kunfold
  kat hk ListU64MarshalSSZTo 47
  apply Eventually.done
  refine ⟨rfl, ?_, rfl, ?_, hrdi, hr8, rfl, rfl, rfl, ?_⟩
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
theorem lum_exit (k : Nat) (hk : ListU64MarshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListU64MarshalSSZTo k) (P : MachineState → Prop) (s : MachineData)
    (hrr : s.regs.rax = s.regs.r8)
    (hP : ∀ f : StatusFlags, P ⟨⟨s.regs, s.zmms, f, s.dmem⟩, Host.addrOf (k + 71)⟩) :
    Eventually (step1 Host.exe) P ⟨s, Host.addrOf (k + 48)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrr hP ⊢
  subst hrr
  kat hk ListU64MarshalSSZTo 48
  kat hk ListU64MarshalSSZTo 49
  kat hk ListU64MarshalSSZTo 50
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
  simp only [Effects.All]
  klabel hk hf ListU64MarshalSSZTo 71
  exact Eventually.done _ (hP _)

theorem lum_loop (k : Nat) (hk : ListU64MarshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListU64MarshalSSZTo k)
    (bs d : List UInt8) (n : Nat) (hn : n ≤ 16) (hbs : bs.length = 8 * n) (hd : d.length = 8 * n)
    (b p : BitVec 64) (L cap : Nat) (hcap : L + 4 + 8 * n ≤ cap) (hcap63 : cap < 2 ^ 63)
    (R : DataMem → Prop) (sp bp : UInt64) :
    ∀ j i (s : MachineData), i + j = n →
    s.regs.rax.toNat = i → s.regs.rbx.toBitVec = b → s.regs.rdx.toNat = L + 4 + 8 * i →
    s.regs.rdi.toNat = cap → s.regs.r8.toNat = n → s.regs.r9.toBitVec = p → s.regs.rsp = sp → s.regs.rbp = bp →
    (s.dmem =⋆ Eq (bs.At p) ⋆ Eq ((bs.take (8 * i) ++ d.drop (8 * i)).At (b + BitVec.ofNat 64 (L + 4))) ⋆ R) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 71) ∧ st.data.regs.rbx.toBitVec = b
        ∧ st.data.regs.rdx.toNat = L + 4 + 8 * n ∧ st.data.regs.rdi.toNat = cap
        ∧ st.data.regs.rsp = sp ∧ st.data.regs.rbp = bp
        ∧ (Eq (bs.At p) ⋆ Eq (bs.At (b + BitVec.ofNat 64 (L + 4))) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 48)⟩
  | 0, i, s, hij, hrax, hrbx, hrdx, hrdi, hr8, _, hrsp, hrbp, h_mem => by
    have hin : i = n := by omega
    subst hin
    refine lum_exit k hk hf _ s (UInt64.toNat_inj.mp (by omega)) fun _ => ⟨rfl, hrbx, hrdx, hrdi, hrsp, hrbp, ?_⟩
    rw [List.take_of_length_le (by omega), List.drop_of_length_le (by omega), List.append_nil] at h_mem
    exact h_mem
  | j + 1, i, s, hij, hrax, hrbx, hrdx, hrdi, hr8, hr9, hrsp, hrbp, h_mem => by
    refine eventually_trans _ _ _ _
      (lum_iter k hk hf bs d n hn hbs hd i (by omega) b p L cap hcap hcap63 R s hrax hrbx hrdx hrdi hr8 hr9 sp bp hrsp hrbp h_mem) ?_
    rintro ⟨s', pc⟩ ⟨hpc, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    dsimp only at hpc; subst hpc
    exact lum_loop k hk hf bs d n hn hbs hd b p L cap hcap hcap63 R sp bp j (i + 1) s' (by omega) h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem lum_s120 (x : BitVec 64) : x - 8#64 - 96 + 120 = x + 16 := by bv_omega
theorem lum_s80 (x : BitVec 64) : x - 8#64 - 96 + 80 = x - 24 := by bv_omega
theorem lum_s88 (x : BitVec 64) : x - 8#64 - 96 + 88 = x - 16 := by bv_omega
theorem lum_s96 (x : BitVec 64) : 96 + (x - 8#64 - 96) = x - 8 := by bv_omega
theorem lum_off (x y : BitVec 64) : y + 4 + x * 1#64 + -4 = x + y := by
  rw [BitVec.mul_one, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm 4, BitVec.add_assoc,
    show (-4 : BitVec 64) + 4 = 0 by decide, Fk.add_lit_zero, BitVec.add_comm]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem lu_marshal_main (k : Nat) (hk : ListU64MarshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListU64MarshalSSZTo k)
    (bs pre o4 d : List UInt8) (n : Nat) (hn : n ≤ 16) (hbs : bs.length = 8 * n) (hd : d.length = 8 * n)
    (ho4 : o4.length = 4) (p : BitVec 64)
    (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp slot l1 l2 : List UInt8)
    (hfp : fp.length = 8) (hsl : slot.length = 8) (hl1 : l1.length = 8) (hl2 : l2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l1.At (s.regs.rsp.toBitVec - 24)) ⋆ Eq (l2.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 p.toInt).At s.regs.rax.toBitVec) ⋆ Eq ((Int.toBytes 8 (n : Int)).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (bs.At p)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (o4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d.At (s.regs.rbx.toBitVec + BitVec.ofNat 64 (s.regs.rcx.toNat + 4))) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 8 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 4 + 8 * n ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 4 + 8 * n ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq ([4, 0, 0, 0].At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (bs.At (s.regs.rbx.toBitVec + BitVec.ofNat 64 (s.regs.rcx.toNat + 4)))
          ⋆ Eq (bs.At p) ⋆ R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hcap hcap63 hpre ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *
  have hnI : (n : Int) = (BitVec.ofNat 64 n).toInt := by
    rw [BitVec.toInt_eq_toNat_of_lt (by simp; omega)]; simp; omega
  rw [hnI] at h_mem
  kat hk ListU64MarshalSSZTo 0
  kat hk ListU64MarshalSSZTo 1
  kat hk ListU64MarshalSSZTo 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListU64MarshalSSZTo 3
  split
  · rename_i h; exfalso
    simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk ListU64MarshalSSZTo 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk ListU64MarshalSSZTo 5
  kat hk ListU64MarshalSSZTo 6
  kat hk ListU64MarshalSSZTo 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ slot _ _ (lum_s120 _) (by ecancel) (by exact hsl)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk ListU64MarshalSSZTo 8
  kat hk ListU64MarshalSSZTo 9
  kat hk ListU64MarshalSSZTo 10
  kat hk ListU64MarshalSSZTo 11
  kat hk ListU64MarshalSSZTo 12
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf ListU64MarshalSSZTo 25
  kat hk ListU64MarshalSSZTo 25
  kat hk ListU64MarshalSSZTo 26
  rw [lum_off]
  apply store_step _ _ _ _ _ o4 _ _ (by ecancel) (by exact ho4)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  rw [show Int.toBytes 4 (BitVec.truncate 32 (4 : BitVec 64)).toInt = [4, 0, 0, 0] by decide] at H3
  kunfold
  kat hk ListU64MarshalSSZTo 27
  apply load_step_at _ _ (rax.toBitVec + 8) _ _ (Int.toBytes 8 (BitVec.ofNat 64 n).toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListU64MarshalSSZTo 28
  kat hk ListU64MarshalSSZTo 29
  kat hk ListU64MarshalSSZTo 30
  split
  case isTrue h =>
    exfalso; rw [jg16_false _ _ (by simp; omega)] at h; simp at h
  simp only [Effects.All]
  kat hk ListU64MarshalSSZTo 31
  apply store_step_at _ _ (rsp.toBitVec - 24) _ _ _ l1 _ _ (lum_s80 _) (by ecancel) (by exact hl1)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  kat hk ListU64MarshalSSZTo 32
  apply load_step _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListU64MarshalSSZTo 33
  apply store_step_at _ _ (rsp.toBitVec - 16) _ _ _ l2 _ _ (lum_s88 _) (by ecancel) (by exact hl2)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  kat hk ListU64MarshalSSZTo 34
  intro _
  kat hk ListU64MarshalSSZTo 35
  klabel hk hf ListU64MarshalSSZTo 48
  refine eventually_trans _ _ _ _ (lum_loop k hk hf bs d n hn hbs hd rbx.toBitVec p rcx.toNat rdi.toNat hcap hcap63 _ _ _ n 0 _
    (by omega) (by simp) rfl (by show (rcx.toBitVec + 4).toNat = rcx.toNat + 4; simp [BitVec.toNat_add]; omega)
    (by simp) (by show (BitVec.ofNat 64 n).toNat = n; simp; omega) rfl rfl rfl
    (by simp only [Nat.mul_zero, List.take_zero, List.nil_append, List.drop_zero]; ecancel)) ?_
  rintro ⟨e3, pc3⟩ ⟨hpc3, hrbx3, hrdx3, hrdi3, hrsp3, hrbp3, Hm3⟩
  dsimp only at hpc3 hrbx3 hrdx3 hrdi3 hrsp3 hrbp3 Hm3
  subst hpc3
  obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,
    zmms3, flags3, mem3⟩ := e3
  simp only at hrbx3 hrdx3 hrdi3 hrsp3 hrbp3 Hm3
  subst hrsp3 hrbp3
  kat hk ListU64MarshalSSZTo 71
  kat hk ListU64MarshalSSZTo 72
  kat hk ListU64MarshalSSZTo 73
  kat hk ListU64MarshalSSZTo 74
  kat hk ListU64MarshalSSZTo 75
  intro _
  kat hk ListU64MarshalSSZTo 76
  intro _
  kat hk ListU64MarshalSSZTo 77
  kat hk ListU64MarshalSSZTo 78
  rw [lum_s96]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListU64MarshalSSZTo 79
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

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem lu_marshal_reject_main (k : Nat) (hk : ListU64MarshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListU64MarshalSSZTo k)
    (pre o4 : List UInt8) (n : Nat) (hn : 16 < n) (hn63 : n < 2 ^ 59)
    (ho4 : o4.length = 4) (p e0 e1 : BitVec 64)
    (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp slot l1 l2 : List UInt8)
    (hfp : fp.length = 8) (hsl : slot.length = 8) (hl1 : l1.length = 8) (hl2 : l2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l1.At (s.regs.rsp.toBitVec - 24)) ⋆ Eq (l2.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 p.toInt).At s.regs.rax.toBitVec) ⋆ Eq ((Int.toBytes 8 (n : Int)).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (o4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq ((Int.toBytes 8 e0.toInt).At (label "ssz.ErrListTooBig").toBitVec)
      ⋆ Eq ((Int.toBytes 8 e1.toInt).At (label "ssz.ErrListTooBig" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 8 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 4 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rcx = 0 ∧ st.data.regs.rdi.toBitVec = e0 ∧ st.data.regs.rsi.toBitVec = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (Eq (pre.At s.regs.rbx.toBitVec) ⋆ R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hcap hcap63 hpre ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *
  have hnI : (n : Int) = (BitVec.ofNat 64 n).toInt := by
    rw [BitVec.toInt_eq_toNat_of_lt (by simp; omega)]; simp; omega
  rw [hnI] at h_mem
  kat hk ListU64MarshalSSZTo 0
  kat hk ListU64MarshalSSZTo 1
  kat hk ListU64MarshalSSZTo 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListU64MarshalSSZTo 3
  split
  · rename_i h; exfalso
    simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk ListU64MarshalSSZTo 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk ListU64MarshalSSZTo 5
  kat hk ListU64MarshalSSZTo 6
  kat hk ListU64MarshalSSZTo 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ slot _ _ (lum_s120 _) (by ecancel) (by exact hsl)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk ListU64MarshalSSZTo 8
  kat hk ListU64MarshalSSZTo 9
  kat hk ListU64MarshalSSZTo 10
  kat hk ListU64MarshalSSZTo 11
  kat hk ListU64MarshalSSZTo 12
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf ListU64MarshalSSZTo 25
  kat hk ListU64MarshalSSZTo 25
  kat hk ListU64MarshalSSZTo 26
  rw [lum_off]
  apply store_step _ _ _ _ _ o4 _ _ (by ecancel) (by exact ho4)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  rw [show Int.toBytes 4 (BitVec.truncate 32 (4 : BitVec 64)).toInt = [4, 0, 0, 0] by decide] at H3
  kunfold
  kat hk ListU64MarshalSSZTo 27
  apply load_step_at _ _ (rax.toBitVec + 8) _ _ (Int.toBytes 8 (BitVec.ofNat 64 n).toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListU64MarshalSSZTo 28
  kat hk ListU64MarshalSSZTo 29
  kat hk ListU64MarshalSSZTo 30
  split
  case isFalse h =>
    exfalso; rw [jg16_true _ _ (by simp; omega) (by simp; omega)] at h; simp at h
  simp only [Effects.All]
  klabel hk hf ListU64MarshalSSZTo 36
  kat hk ListU64MarshalSSZTo 36
  kat hk ListU64MarshalSSZTo 37
  apply load_step _ _ _ _ (Int.toBytes 8 e0.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListU64MarshalSSZTo 38
  apply load_step _ _ _ _ (Int.toBytes 8 e1.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListU64MarshalSSZTo 39
  intro _
  kat hk ListU64MarshalSSZTo 40
  intro _
  kat hk ListU64MarshalSSZTo 41
  kat hk ListU64MarshalSSZTo 42
  kat hk ListU64MarshalSSZTo 43
  rw [lum_s96]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListU64MarshalSSZTo 44
  rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, ?_, trivial, ?_⟩
  all_goals first
    | rfl
    | (simp [Fk.ofInt_ofBytes_toBytes64]; done)
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | exact sep_true (P := Eq (pre.At rbx.toBitVec) ⋆ R) (by ecancel)

/-- ListU64.SizeSSZ: returns 4 + 8 len(c.L) (`n < 2^60`, a Go slice length bound). -/
theorem lu_size_main (k : Nat) (hk : ListU64SizeSSZ.IsInfixAt Host.prog k) (s : MachineData) (ra : UInt64)
    (n : Nat) (hn : n < 2 ^ 60) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 n).toInt).At (s.regs.rax.toBitVec + 8)) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax.toNat = 4 + 8 * n
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem ⊢
  kat hk ListU64SizeSSZ 0
  kat hk ListU64SizeSSZ 1
  apply load_step _ _ _ _ (Int.toBytes 8 (BitVec.ofNat 64 n).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListU64SizeSSZ 2
  kshl64 3
  kat hk ListU64SizeSSZ 3
  kat hk ListU64SizeSSZ 4
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨trivial, ?_, ?_, trivial⟩
  · show (4 + BitVec.ofNat 64 n <<< 3).toNat = _
    simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  · apply UInt64.toBitVec_inj.mp; simp
