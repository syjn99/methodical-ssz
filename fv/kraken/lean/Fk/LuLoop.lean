import Fk.Block
import Fk.Labels

/-!
# ListU64.UnmarshalSSZ element loop, on Kraken main (6064eec)

Loop head `L_240` (directive 148). Invariant at element `i`: rax = i, rdx = n,
rcx ≥ 8n (capacity of the slice after the offset), rdi = d (elements), rsi = c (receiver), the
receiver header holds (p, nb) with nb = n, and the output block at p is
`bs.take (8i) ++ 0^(8(n-i))`. `lu_iter`: one iteration (19 directives, two
bounds checks shown not to branch to `panicBounds`). `lu_exit`: at i = n the loop
leaves to `L_275` (directive 167). `lu_loop`: induction on n - i; the output
block ends equal to the input block `bs`.

Method: block split around element i (`block_split`, Kraken's `At_append_sep`),
`load_step`/`store_step`, rejoin (`out_step`).
-/

open Fk Fk.Code
variable [Host]

set_option maxHeartbeats 4000000 in
theorem lu_iter (k : Nat) (hk : ListU64UnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListU64UnmarshalSSZ k)
    (bs : List UInt8) (n i : Nat) (hbs : bs.length = 8 * n) (hn : n ≤ 16) (hi : i < n)
    (d c p nb : BitVec 64) (hnb : nb.toNat = n) (R : DataMem → Prop) (s : MachineData)
    (hrax : s.regs.rax.toNat = i) (hrdx : s.regs.rdx.toNat = n) (hrcx : 8 * n ≤ s.regs.rcx.toNat)
    (hrdi : s.regs.rdi.toBitVec = d) (hrsi : s.regs.rsi.toBitVec = c)
    (sp bp : UInt64) (hrsp : s.regs.rsp = sp) (hrbp : s.regs.rbp = bp)
    (h_mem : s.dmem =⋆ Eq (bs.At d) ⋆ Eq ((Int.toBytes 8 p.toInt).At c) ⋆ Eq ((Int.toBytes 8 nb.toInt).At (c + 8))
      ⋆ Eq ((bs.take (8 * i) ++ List.replicate (8 * (n - i)) 0).At p) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 148) ∧ st.data.regs.rax.toNat = i + 1 ∧ st.data.regs.rdx.toNat = n
        ∧ 8 * n ≤ st.data.regs.rcx.toNat ∧ st.data.regs.rdi.toBitVec = d ∧ st.data.regs.rsi.toBitVec = c
        ∧ st.data.regs.rsp = sp ∧ st.data.regs.rbp = bp
        ∧ (Eq (bs.At d) ⋆ Eq ((Int.toBytes 8 p.toInt).At c) ⋆ Eq ((Int.toBytes 8 nb.toInt).At (c + 8))
          ⋆ Eq ((bs.take (8 * (i + 1)) ++ List.replicate (8 * (n - (i + 1))) 0).At p) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 148)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hrax hrdx hrcx hrdi hrsi hrsp hrbp ⊢
  subst hrdi hrsi hrsp hrbp
  have := rax.toNat_lt_size; have := rdx.toNat_lt_size; have := rcx.toNat_lt_size
  simp only [UInt64.size] at *
  have hlen : bs.length < 2 ^ 64 := by omega
  rw [block_split bs rdi.toBitVec (8 * i) (by omega) hlen, out_next bs n i hbs hi,
    Mem.At_append_sep _ _ _ (by simp; omega), Mem.At_append_sep _ _ _ (by simp; omega)] at h_mem
  simp only [List.length_take, List.length_replicate, hbs, Nat.min_eq_left (show 8 * i ≤ 8 * n by omega)] at h_mem
  kat hk ListU64UnmarshalSSZ 148
  kat hk ListU64UnmarshalSSZ 149
  kat hk ListU64UnmarshalSSZ 150
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.signed] at h
    exact jge_false _ _ (by simp; omega) (by simp; omega) h
  simp only [Effects.All]
  -- 151 lea 1(%rax),%r8 ; 152 mov ; 153 shl $3,%r8 ; 154 cmp %rcx,%r8 ; 155 ja (not taken)
  kat hk ListU64UnmarshalSSZ 151
  kat hk ListU64UnmarshalSSZ 152
  kat hk ListU64UnmarshalSSZ 153
  kshl64 3
  kat hk ListU64UnmarshalSSZ 154
  kat hk ListU64UnmarshalSSZ 155
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    (try simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Int.shiftLeft_eq] at h)
    obtain ⟨h1, h2⟩ := h; apply h2; apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_sub, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_add]; omega
  simp only [Effects.All]
  kat hk ListU64UnmarshalSSZ 156
  kat hk ListU64UnmarshalSSZ 157
  kshl64 3
  kat hk ListU64UnmarshalSSZ 158
  kat hk ListU64UnmarshalSSZ 159
  kat hk ListU64UnmarshalSSZ 160
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    (try simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Int.shiftLeft_eq] at h); omega
  simp only [Effects.All]
  kat hk ListU64UnmarshalSSZ 161
  apply load_step_at _ _ (rsi.toBitVec + 8) _ _ (Int.toBytes 8 nb.toInt) _ _ (by bv_omega) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListU64UnmarshalSSZ 162
  kat hk ListU64UnmarshalSSZ 163
  rw [show rdi.toBitVec + rax.toBitVec * 8#64 = rdi.toBitVec + BitVec.ofNat 64 (8 * i) by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_mul]; omega]
  apply load_step _ _ _ _ ((bs.drop (8 * i)).take 8) _ _ (by ecancel) (by simp; omega)
  kunfold
  kat hk ListU64UnmarshalSSZ 164
  kat hk ListU64UnmarshalSSZ 165
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
  simp only [Effects.All]
  klabel hk hf ListU64UnmarshalSSZ 143
  kat hk ListU64UnmarshalSSZ 143
  kat hk ListU64UnmarshalSSZ 144
  apply load_step_at _ _ rsi.toBitVec _ _ (Int.toBytes 8 p.toInt) _ _ (by bv_omega) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListU64UnmarshalSSZ 145
  rw [show p + rax.toBitVec * 8#64 = p + BitVec.ofNat 64 (8 * i) by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_mul]; omega]
  apply store_step _ _ _ _ _ (List.replicate 8 0) _ _ (by ecancel) (by simp)
  intro m1 H1
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl _ (show ((bs.drop (8 * i)).take 8).length = 8 by simp; omega)] at H1
  kunfold
  kat hk ListU64UnmarshalSSZ 146
  kat hk ListU64UnmarshalSSZ 147
  apply Eventually.done
  refine ⟨rfl, ?_, hrdx, hrcx, rfl, rfl, rfl, rfl, ?_⟩
  · show (rax.toBitVec + 1).toNat = i + 1; simp [BitVec.toNat_add]; omega
  · dsimp only
    rw [← out_step bs n i hbs hi, Mem.At_append_sep _ _ _ (by simp; omega), Mem.At_append_sep _ _ _ (by simp; omega),
      block_split bs rdi.toBitVec (8 * i) (by omega) hlen]
    simp only [List.length_take, List.length_replicate, List.length_drop, hbs,
      Nat.min_eq_left (show 8 * i ≤ 8 * n by omega), Nat.min_eq_left (show 8 ≤ 8 * n - 8 * i by omega)]
    (try simp only [BitVec.ofNat_eq_ofNat] at H1 ⊢)
    ecancel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem lu_exit (k : Nat) (hk : ListU64UnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListU64UnmarshalSSZ k)
    (bs : List UInt8) (n : Nat) (hbs : bs.length = 8 * n) (hn : n ≤ 16)
    (d c p nb : BitVec 64) (R : DataMem → Prop) (s : MachineData)
    (hrax : s.regs.rax.toNat = n) (hrdx : s.regs.rdx.toNat = n)
    (sp bp : UInt64) (hrsp : s.regs.rsp = sp) (hrbp : s.regs.rbp = bp)
    (h_mem : s.dmem =⋆ Eq (bs.At d) ⋆ Eq ((Int.toBytes 8 p.toInt).At c) ⋆ Eq ((Int.toBytes 8 nb.toInt).At (c + 8))
      ⋆ Eq ((bs.take (8 * n) ++ List.replicate (8 * (n - n)) 0).At p) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 167) ∧ st.data.regs.rsp = sp ∧ st.data.regs.rbp = bp
        ∧ (Eq (bs.At d) ⋆ Eq ((Int.toBytes 8 p.toInt).At c) ⋆ Eq ((Int.toBytes 8 nb.toInt).At (c + 8))
          ⋆ Eq (bs.At p) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 148)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hrax hrdx hrsp hrbp ⊢
  subst hrsp hrbp
  have hrr : rax = rdx := UInt64.toNat_inj.mp (by omega)
  subst hrr
  kat hk ListU64UnmarshalSSZ 148
  kat hk ListU64UnmarshalSSZ 149
  kat hk ListU64UnmarshalSSZ 150
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
  simp only [Effects.All]
  klabel hk hf ListU64UnmarshalSSZ 167
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, ?_⟩
  rw [Nat.sub_self, Nat.mul_zero, List.replicate_zero, List.append_nil, List.take_of_length_le (by omega)] at h_mem
  exact h_mem

theorem lu_loop (k : Nat) (hk : ListU64UnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListU64UnmarshalSSZ k)
    (bs : List UInt8) (n : Nat) (hbs : bs.length = 8 * n) (hn : n ≤ 16)
    (d c p nb : BitVec 64) (hnb : nb.toNat = n) (R : DataMem → Prop) (sp bp : UInt64) :
    ∀ j i (s : MachineData), i + j = n →
    s.regs.rax.toNat = i → s.regs.rdx.toNat = n → 8 * n ≤ s.regs.rcx.toNat →
    s.regs.rdi.toBitVec = d → s.regs.rsi.toBitVec = c → s.regs.rsp = sp → s.regs.rbp = bp →
    (s.dmem =⋆ Eq (bs.At d) ⋆ Eq ((Int.toBytes 8 p.toInt).At c) ⋆ Eq ((Int.toBytes 8 nb.toInt).At (c + 8))
      ⋆ Eq ((bs.take (8 * i) ++ List.replicate (8 * (n - i)) 0).At p) ⋆ R) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 167) ∧ st.data.regs.rsp = sp ∧ st.data.regs.rbp = bp
        ∧ (Eq (bs.At d) ⋆ Eq ((Int.toBytes 8 p.toInt).At c) ⋆ Eq ((Int.toBytes 8 nb.toInt).At (c + 8))
          ⋆ Eq (bs.At p) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 148)⟩
  | 0, i, s, hij, hrax, hrdx, _, _, _, hrsp, hrbp, h_mem => by
    have hin : i = n := by omega
    rw [hin] at hrax h_mem
    exact lu_exit k hk hf bs n hbs hn d c p nb R s hrax hrdx sp bp hrsp hrbp h_mem
  | j + 1, i, s, hij, hrax, hrdx, hrcx, hrdi, hrsi, hrsp, hrbp, h_mem => by
    refine eventually_trans _ _ _ _
      (lu_iter k hk hf bs n i hbs hn (by omega) d c p nb hnb R s hrax hrdx hrcx hrdi hrsi sp bp hrsp hrbp h_mem) ?_
    rintro ⟨s', pc⟩ ⟨hpc, h1, h2, h3, h4, h5, h6, h7, h8⟩
    dsimp only at hpc; subst hpc
    exact lu_loop k hk hf bs n hbs hn d c p nb hnb R sp bp j (i + 1) s' (by omega) h1 h2 h3 h4 h5 h6 h7 h8
