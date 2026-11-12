import Fk.Block
import Fk.Labels
import Fk.Frame
import E2eEnc.Code
import E2eList.ScLemmas
import Fk.RtCopy
import Fk.FvMarshal

/-!
# `(*v1alpha1.DataColumnsByRootIdentifier).MarshalSSZTo`: the Columns loop (capacity sufficient)

Loop head `L_13a` (directive 82). One iteration: 83–84 `cmp %r8,%rsi; jge` not taken (i < n), 85 rbx += 8,
86 `mov (%rdx,%rsi,8),%r9` (8 bytes of the column backing array), 88–89 `cmp %rbx,%rcx; jae L_132` taken (capacity
sufficient, so growslice 94 is not reached), 79 `L_132`, 80 `mov %r9,-0x8(%rbx,%rax,1)` (8 bytes to the block),
81 `inc %rsi`. Exit: i = n, the `jge` goes to `L_17e` (directive 100).

Registers: rax = block pointer `bp`, rbx = L + 8i (bytes written so far, L = len + 36), rcx = capacity `cp`,
rdx = column pointer `pc`, rsi = i, r8 = n. The block from `bp + L` holds `cb.take (8i) ++ w.drop (8i)`: the first
8i column bytes, then the 8(n − i) bytes not written yet. The shape of `E2eList.ia_iter` / `ia_exit` / `ia_loop`.
-/

open Fk E2eEnc.Code
variable [Host]

namespace E2eEnc

/-- Address equation by `toNat` and `omega`. -/
macro "daddr" : tactic => `(tactic| (
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_neg, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat,
    BitVec.toNat_mul, UInt64.toNat_toBitVec, UInt64.toBitVec_add, UInt64.toBitVec_ofNat, Width.bits, Nat.reducePow]
  all_goals omega))

theorem enc_split (cb w : List UInt8) (n i : Nat) (hcb : cb.length = 8 * n) (hw : w.length = 8 * n) (hi : i < n)
    (a : BitVec 64) (hl : 8 * n < 2 ^ 64) :
    Eq ((cb.take (8 * i) ++ w.drop (8 * i)).At a) = Eq ((cb.take (8 * i)).At a)
      ⋆ Eq (((w.drop (8 * i)).take 8).At (a + BitVec.ofNat 64 (8 * i)))
      ⋆ Eq ((w.drop (8 * i + 8)).At (a + BitVec.ofNat 64 (8 * i) + 8)) := by
  have e1 : w.drop (8 * i) = (w.drop (8 * i)).take 8 ++ w.drop (8 * i + 8) := by
    rw [← List.drop_drop, List.take_append_drop]
  conv => lhs; rw [e1]
  rw [Mem.At_append_sep _ _ _ (by simp; omega), Mem.At_append_sep _ _ _ (by simp; omega),
    ← Std.ExtHashMap.sep_assoc]
  have l1 : (cb.take (8 * i)).length = 8 * i := by simp; omega
  have l2 : ((w.drop (8 * i)).take 8).length = 8 := by simp; omega
  rw [l1, l2]; rfl

theorem enc_join (cb w : List UInt8) (n i : Nat) (hcb : cb.length = 8 * n) (hw : w.length = 8 * n) (hi : i < n)
    (a : BitVec 64) (hl : 8 * n < 2 ^ 64) :
    Eq ((cb.take (8 * i)).At a) ⋆ Eq (((cb.drop (8 * i)).take 8).At (a + BitVec.ofNat 64 (8 * i)))
      ⋆ Eq ((w.drop (8 * i + 8)).At (a + BitVec.ofNat 64 (8 * i) + 8))
      = Eq ((cb.take (8 * (i + 1)) ++ w.drop (8 * (i + 1))).At a) := by
  have e1 : cb.take (8 * (i + 1)) = cb.take (8 * i) ++ (cb.drop (8 * i)).take 8 := by
    rw [show 8 * (i + 1) = 8 * i + 8 by omega, List.take_add]
  rw [e1, show 8 * (i + 1) = 8 * i + 8 by omega, List.append_assoc, Mem.At_append_sep _ _ _ (by simp; omega),
    Mem.At_append_sep _ _ _ (by simp; omega), ← Std.ExtHashMap.sep_assoc]
  have l1 : (cb.take (8 * i)).length = 8 * i := by simp; omega
  have l2 : ((cb.drop (8 * i)).take 8).length = 8 := by simp; omega
  rw [l1, l2]; rfl

theorem dc_addr (x y : BitVec 64) (L i : Nat) (h : y.toNat = L + 8 * i) (hL : L + 8 * i < 2 ^ 64) :
    8 + y + x * 1#64 + -8 = x + BitVec.ofNat 64 L + BitVec.ofNat 64 (8 * i) := by
  rw [add8_neg8, BitVec.add_assoc]; congr 1
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega

omit [Host] in
theorem dc_room (y z : BitVec 64) (L n i cp : Nat) (h : y.toNat = L + 8 * i) (hi : i < n)
    (hz : z.toNat = cp) (hc : L + 8 * n ≤ cp) (hc64 : cp < 2 ^ 64) : (8 + y).toNat ≤ z.toNat := by
  simp [BitVec.toNat_add]; omega

omit [Host] in
theorem dc_rbx (y : BitVec 64) (L i : Nat) (h : y.toNat = L + 8 * i) (hL : L + 8 * (i + 1) < 2 ^ 64) :
    (8 + y).toNat = L + 8 * (i + 1) := by
  simp [BitVec.toNat_add]; omega

omit [Host] in
theorem dc_inc (x : BitVec 64) (i : Nat) (h : x.toNat = i) (hi : i < 128) : (x + 1).toNat = i + 1 := by
  simp [BitVec.toNat_add]; omega

omit [Host] in
theorem dc_idx (x y : BitVec 64) (i : Nat) (h : y.toNat = i) (hi : i < 128) :
    x + y * 8#64 = x + BitVec.ofNat 64 (8 * i) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_mul]; omega

theorem dc_iter (k : Nat) (hk : DcMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh DcMarshal k)
    (cb w : List UInt8) (n i L cp : Nat) (hcb : cb.length = 8 * n) (hw : w.length = 8 * n) (hn : n ≤ 128)
    (hi : i < n) (hcp : L + 8 * n ≤ cp) (hcp64 : cp < 2 ^ 64)
    (bp pc : BitVec 64) (R : DataMem → Prop) (s : MachineData)
    (hrax : s.regs.rax.toBitVec = bp) (hrbx : s.regs.rbx.toNat = L + 8 * i) (hrcx : s.regs.rcx.toNat = cp)
    (hrdx : s.regs.rdx.toBitVec = pc) (hrsi : s.regs.rsi.toNat = i) (hr8 : s.regs.r8.toNat = n)
    (sp bpv r14v : UInt64) (hrsp : s.regs.rsp = sp) (hrbp : s.regs.rbp = bpv) (hr14 : s.regs.r14 = r14v)
    (h_mem : s.dmem =⋆ Eq (cb.At pc) ⋆ Eq ((cb.take (8 * i) ++ w.drop (8 * i)).At (bp + BitVec.ofNat 64 L)) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 82) ∧ st.data.regs.rax.toBitVec = bp
        ∧ st.data.regs.rbx.toNat = L + 8 * (i + 1) ∧ st.data.regs.rcx.toNat = cp
        ∧ st.data.regs.rdx.toBitVec = pc ∧ st.data.regs.rsi.toNat = i + 1 ∧ st.data.regs.r8.toNat = n
        ∧ st.data.regs.rsp = sp ∧ st.data.regs.rbp = bpv ∧ st.data.regs.r14 = r14v
        ∧ (Eq (cb.At pc) ⋆ Eq ((cb.take (8 * (i + 1)) ++ w.drop (8 * (i + 1))).At (bp + BitVec.ofNat 64 L)) ⋆ R)
          st.data.dmem)
      ⟨s, Host.addrOf (k + 82)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hrax hrbx hrcx hrdx hrsi hr8 hrsp hrbp hr14
  subst hrax hrdx hrsp hrbp hr14
  have hz1 := rbx.toNat_lt_size; have hz2 := rsi.toNat_lt_size; have hz3 := r8.toNat_lt_size
  simp only [UInt64.size] at hz1 hz2 hz3
  have hlen : cb.length < 2 ^ 64 := by omega
  rw [enc_split cb w n i hcb hw hi _ (by omega),
    block_split cb rdx.toBitVec (8 * i) (by omega) hlen] at h_mem
  kat hk DcMarshal 82
  kat hk DcMarshal 83
  kat hk DcMarshal 84
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    exact E2eList.jge_false512 _ _ (by simp; omega) (by simp; omega) h
  simp only [Effects.All]
  kat hk DcMarshal 85
  kat hk DcMarshal 86
  rw [dc_idx _ _ i (by simpa using hrsi) (by omega)]
  apply load_step _ _ _ _ ((cb.drop (8 * i)).take 8) _ _ (by ecancel) (by simp; omega)
  kunfold
  kat hk DcMarshal 87
  kat hk DcMarshal 88
  kat hk DcMarshal 89
  split
  case isFalse h =>
    exfalso; simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    have := dc_room rbx.toBitVec rcx.toBitVec L n i cp (by simpa using hrbx) hi (by simpa using hrcx) hcp hcp64
    simp at h; omega
  simp only [Effects.All]
  klabel hk hf DcMarshal 79
  kat hk DcMarshal 79
  kat hk DcMarshal 80
  rw [dc_addr _ _ L i (by simpa using hrbx) (by omega)]
  apply store_step _ _ _ _ _ ((w.drop (8 * i)).take 8) _ _ (by ecancel) (by simp; omega)
  intro m1 H1
  simp only [Width.bytes, Width.bits,
    toBytes_ofInt_ofBytes 64 8 rfl _ (show ((cb.drop (8 * i)).take 8).length = 8 by simp; omega)] at H1
  kunfold
  kat hk DcMarshal 81
  apply Eventually.done
  refine ⟨rfl, rfl, ?_, hrcx, rfl, ?_, hr8, rfl, rfl, rfl, ?_⟩
  · exact dc_rbx _ L i (by simpa using hrbx) (by omega)
  · exact dc_inc _ i (by simpa using hrsi) (by omega)
  · dsimp only
    rw [← enc_join cb w n i hcb hw hi _ (by omega), block_split cb rdx.toBitVec (8 * i) (by omega) hlen]
    (try simp only [BitVec.ofNat_eq_ofNat] at H1 ⊢)
    ecancel

theorem dc_exit (k : Nat) (hk : DcMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh DcMarshal k)
    (n : Nat) (hn : n ≤ 128) (R : DataMem → Prop) (s : MachineData)
    (hrsi : s.regs.rsi.toNat = n) (hr8 : s.regs.r8.toNat = n) (h_mem : R s.dmem) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 100) ∧ st.data.regs = s.regs ∧ R st.data.dmem)
      ⟨s, Host.addrOf (k + 82)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hrsi hr8
  have hrr : rsi = r8 := UInt64.toNat_inj.mp (by omega)
  subst hrr
  kat hk DcMarshal 82
  kat hk DcMarshal 83
  kat hk DcMarshal 84
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
  simp only [Effects.All]
  klabel hk hf DcMarshal 100
  apply Eventually.done
  exact ⟨rfl, rfl, h_mem⟩

/-- The loop by recursion on the number `j` of iterations left (`i + j = n`); `n = 0` is `j = 0, i = 0`. -/
theorem dc_loop (k : Nat) (hk : DcMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh DcMarshal k)
    (cb w : List UInt8) (n L cp : Nat) (hcb : cb.length = 8 * n) (hw : w.length = 8 * n) (hn : n ≤ 128)
    (hcp : L + 8 * n ≤ cp) (hcp64 : cp < 2 ^ 64) (bp pc : BitVec 64) (R : DataMem → Prop) (sp bpv r14v : UInt64) :
    ∀ j i (s : MachineData), i + j = n →
    s.regs.rax.toBitVec = bp → s.regs.rbx.toNat = L + 8 * i → s.regs.rcx.toNat = cp →
    s.regs.rdx.toBitVec = pc → s.regs.rsi.toNat = i → s.regs.r8.toNat = n →
    s.regs.rsp = sp → s.regs.rbp = bpv → s.regs.r14 = r14v →
    (s.dmem =⋆ Eq (cb.At pc) ⋆ Eq ((cb.take (8 * i) ++ w.drop (8 * i)).At (bp + BitVec.ofNat 64 L)) ⋆ R) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 100) ∧ st.data.regs.rax.toBitVec = bp
        ∧ st.data.regs.rbx.toNat = L + 8 * n ∧ st.data.regs.rcx.toNat = cp
        ∧ st.data.regs.rsp = sp ∧ st.data.regs.rbp = bpv ∧ st.data.regs.r14 = r14v
        ∧ (Eq (cb.At pc) ⋆ Eq (cb.At (bp + BitVec.ofNat 64 L)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 82)⟩
  | 0, i, s, hij, hrax, hrbx, hrcx, _, hrsi, hr8, hrsp, hrbp, hr14, h_mem => by
    have hin : i = n := by omega
    subst hin
    refine eventually_mono (dc_exit k hk hf i hn _ s hrsi hr8 h_mem) ?_
    rintro st ⟨hpc, hregs, hm⟩
    rw [hregs]
    refine ⟨hpc, hrax, hrbx, hrcx, hrsp, hrbp, hr14, ?_⟩
    rw [List.take_of_length_le (by omega), List.drop_of_length_le (by omega), List.append_nil] at hm
    exact hm
  | j + 1, i, s, hij, hrax, hrbx, hrcx, hrdx, hrsi, hr8, hrsp, hrbp, hr14, h_mem => by
    refine eventually_trans _ _ _ _
      (dc_iter k hk hf cb w n i L cp hcb hw hn (by omega) hcp hcp64 bp pc R s hrax hrbx hrcx hrdx hrsi hr8
        sp bpv r14v hrsp hrbp hr14 h_mem) ?_
    rintro ⟨s', pc'⟩ ⟨hpc, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    dsimp only at hpc; subst hpc
    exact dc_loop k hk hf cb w n L cp hcb hw hn hcp hcp64 bp pc R sp bpv r14v j (i + 1) s' (by omega)
      h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

end E2eEnc
