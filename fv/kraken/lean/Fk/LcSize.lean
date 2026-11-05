import Fk.Block
import Fk.Labels
import Fk.Bytes
import Fv1.SpecListC

/-!
# ListC.SizeSSZ on Kraken main

    size := 4; for _, o := range c.Items { size += 4; size += o.SizeSSZ() }

`ListU64.SizeSSZ` (4 + 8·len) is inlined. The loop reads `c.Items[i]` (a
pointer `p_i` in the array at q) and `len(p_i.L)` at `p_i + 8`. It writes no
memory, so the loop invariant keeps `dmem` equal to the start.

`lc_size_main`: returns `4 + Σ (8 + 8·len_i)` = `4 + Σ (4 + (4 + 8·len_i))`,
the EthLib size of the encoding (`lcEncode`: one offset per element, then
`luEncode` of each).
Premises the Go caller provides: the receiver's slice header (q, n) at rax,
for each i < n the pointer bytes at q + 8i and the length at p_i + 8
(non-nil elements: a nil element makes Go panic at `mov 0x8(%rsi)`), and the
sum below 2^63 (Go `int`).
-/

open Fk Fk.Code
variable [Host]

theorem jl_val (a b : BitVec 64) (ha : a.toNat < 2 ^ 62) (hb : b.toNat < 2 ^ 62) (af : Bool) :
    CondCode.l.interp (StatusFlags.from_result (a - b)
      { cf := BitVec.unsigned (a - b) != a.unsigned - b.unsigned, af := af,
        of := BitVec.toInt (a - b) != a.toInt - b.toInt }) = decide (a.toNat < b.toNat) := by
  have ta : a.toInt = a.toNat := BitVec.toInt_eq_toNat_of_lt (by omega)
  have tb : b.toInt = b.toNat := BitVec.toInt_eq_toNat_of_lt (by omega)
  have hs : (a - b).toInt = (a.toNat : Int) - b.toNat := by
    rw [BitVec.toInt_sub, ta, tb]; apply Int.bmod_eq_of_le <;> omega
  have hm : (a - b).msb = decide (a.toNat < b.toNat) := by
    rw [BitVec.msb_eq_toInt, hs]; simp; omega
  simp only [CondCode.interp, StatusFlags.from_result, hm, hs, ta, tb]
  simp
theorem sum_take_le (f : Nat → Nat) (ls : List Nat) (i : Nat) :
    ((ls.take i).map f).sum ≤ (ls.map f).sum := by
  conv => rhs; rw [← List.take_append_drop i ls]
  rw [List.map_append, List.sum_append]; omega

/-- The sum the loop computes after the first `i` elements. -/
def lcAcc (ls : List Nat) (i : Nat) : Nat := 4 + ((ls.take i).map fun l => 8 + 8 * l).sum

theorem lcAcc_succ (ls : List Nat) (i : Nat) (hi : i < ls.length) :
    lcAcc ls (i + 1) = lcAcc ls i + 8 + 8 * ls[i] := by
  simp only [lcAcc, List.take_add_one, List.map_append, List.sum_append, List.getElem?_eq_getElem hi]
  simp; omega

theorem lcAcc_le (ls : List Nat) (i : Nat) : lcAcc ls i ≤ lcAcc ls ls.length := by
  simp only [lcAcc, List.take_length]
  have := sum_take_le (fun l => 8 + 8 * l) ls i
  omega

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem lcs_iter (k : Nat) (hk : ListCSizeSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListCSizeSSZ k)
    (q p : BitVec 64) (n i acc l : Nat) (hi : i < n) (hn : n < 2 ^ 62) (hl : 8 + 8 * l + acc < 2 ^ 63)
    (s : MachineData) (R : DataMem → Prop)
    (hrax : s.regs.rax.toNat = i) (hrbx : s.regs.rbx.toNat = acc) (hrcx : s.regs.rcx.toBitVec = q)
    (hrdx : s.regs.rdx.toNat = n)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 p.toInt).At (q + BitVec.ofNat 64 (8 * i)))
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 l).toInt).At (p + 8)) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 12) ∧ st.data.regs.rax.toNat = i + 1
        ∧ st.data.regs.rbx.toNat = acc + 8 + 8 * l ∧ st.data.regs.rcx.toBitVec = q
        ∧ st.data.regs.rdx.toNat = n ∧ st.data.regs.rsp = s.regs.rsp ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf (k + 12)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hrax hrbx hrcx hrdx ⊢
  subst hrcx
  have := rax.toNat_lt_size; have := rbx.toNat_lt_size; have := rdx.toNat_lt_size
  simp only [UInt64.size] at *
  kat hk ListCSizeSSZ 12
  kat hk ListCSizeSSZ 13
  kat hk ListCSizeSSZ 14
  rw [jl_val _ _ (by simp; omega) (by simp; omega)]
  simp only [show decide (rax.toBitVec.toNat < rdx.toBitVec.toNat) = true by simp; omega, ↓reduceIte, Effects.All]
  klabel hk hf ListCSizeSSZ 6
  kat hk ListCSizeSSZ 6
  kat hk ListCSizeSSZ 7
  rw [show rcx.toBitVec + rax.toBitVec * 8#64 = rcx.toBitVec + BitVec.ofNat 64 (8 * i) by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_mul]; omega]
  apply load_step _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk ListCSizeSSZ 8
  apply load_step _ _ _ _ (Int.toBytes 8 (BitVec.ofNat 64 l).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk ListCSizeSSZ 9
  kat hk ListCSizeSSZ 10
  kat hk ListCSizeSSZ 11
  apply Eventually.done
  refine ⟨rfl, ?_, ?_, rfl, hrdx, rfl, rfl⟩
  · show (rax.toBitVec + 1).toNat = i + 1; simp [BitVec.toNat_add]; omega
  · show (rbx.toBitVec + BitVec.ofNat 64 l * 8#64 + 8).toNat = _
    simp [BitVec.toNat_add, BitVec.toNat_mul]; omega

/-- Loop head at directive 12: after the remaining `n - i` iterations, the
function returns `lcAcc ls n`. -/
theorem lcs_loop (k : Nat) (hk : ListCSizeSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListCSizeSSZ k) (q : BitVec 64) (ps : List (BitVec 64)) (ls : List Nat)
    (hlen : ps.length = ls.length) (hn : ls.length < 2 ^ 62) (hsum : lcAcc ls ls.length < 2 ^ 63)
    (ra : UInt64) (R : DataMem → Prop) :
    ∀ (j : Nat) (s : MachineData), j ≤ ls.length → s.regs.rax.toNat = ls.length - j →
      s.regs.rbx.toNat = lcAcc ls (ls.length - j) → s.regs.rcx.toBitVec = q → s.regs.rdx.toNat = ls.length →
      (∀ i (hi : i < ls.length), (Eq ((Int.toBytes 8 (ps[i]'(by omega)).toInt).At (q + BitVec.ofNat 64 (8 * i)))
        ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 ls[i]).toInt).At (ps[i]'(by omega) + 8)) ⋆ fun _ => True) s.dmem) →
      (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec) ⋆ R) s.dmem →
      Eventually (step1 Host.exe)
        (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax.toNat = lcAcc ls ls.length
          ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.dmem = s.dmem)
        ⟨s, Host.addrOf (k + 12)⟩ := by
  intro j
  induction j with
  | zero =>
    intro s _ hrax hrbx hrcx hrdx _ hret
    obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
    simp only at hrax hrbx hrcx hrdx hret ⊢
    have := rax.toNat_lt_size; have := rdx.toNat_lt_size; simp only [UInt64.size] at *
    kat hk ListCSizeSSZ 12
    kat hk ListCSizeSSZ 13
    kat hk ListCSizeSSZ 14
    rw [jl_val _ _ (by simp; omega) (by simp; omega)]
    simp only [show decide (rax.toBitVec.toNat < rdx.toBitVec.toNat) = false by simp; omega, Bool.false_eq_true,
      ↓reduceIte, Effects.All]
    kat hk ListCSizeSSZ 15
    kat hk ListCSizeSSZ 16
    apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    kunfold
    apply Eventually.done
    simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
    refine ⟨trivial, ?_, ?_, ?_⟩
    · simpa using hrbx
    · apply UInt64.toBitVec_inj.mp; simp
    · first | trivial | rfl
  | succ j ih =>
    intro s hj hrax hrbx hrcx hrdx hall hret
    have hi : ls.length - (j + 1) < ls.length := by omega
    have hacc := lcAcc_succ ls (ls.length - (j + 1)) hi
    have hle := lcAcc_le ls (ls.length - (j + 1) + 1)
    refine eventually_trans _ _ _ _ (lcs_iter k hk hf q (ps[ls.length - (j + 1)]'(by omega)) ls.length
      (ls.length - (j + 1)) (lcAcc ls (ls.length - (j + 1))) ls[ls.length - (j + 1)] hi hn (by omega) s
      (fun _ => True) hrax hrbx hrcx hrdx (hall _ hi)) ?_
    rintro ⟨d, pc⟩ ⟨hpc, hrax', hrbx', hrcx', hrdx', hrsp', hmem'⟩
    dsimp only at hpc hrax' hrbx' hrcx' hrdx' hrsp' hmem'
    subst hpc
    have := ih d (by omega) (by rw [hrax']; omega) (by rw [hrbx', ← hacc]; congr 1; omega) hrcx' hrdx'
      (by rw [hmem']; exact hall) (by rw [hmem', hrsp']; exact hret)
    simpa [hrsp', hmem'] using this

theorem lc_size_main (k : Nat) (hk : ListCSizeSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListCSizeSSZ k) (q : BitVec 64) (ps : List (BitVec 64)) (ls : List Nat)
    (hlen : ps.length = ls.length) (hn : ls.length < 2 ^ 62) (hsum : lcAcc ls ls.length < 2 ^ 63)
    (s : MachineData) (ra : UInt64) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq ((Int.toBytes 8 q.toInt).At s.regs.rax.toBitVec)
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 ls.length).toInt).At (s.regs.rax.toBitVec + 8)) ⋆ R)
    (hall : ∀ i (hi : i < ls.length), (Eq ((Int.toBytes 8 (ps[i]'(by omega)).toInt).At (q + BitVec.ofNat 64 (8 * i)))
        ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 ls[i]).toInt).At (ps[i]'(by omega) + 8)) ⋆ fun _ => True) s.dmem) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax.toNat = lcAcc ls ls.length
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hall ⊢
  kat hk ListCSizeSSZ 0
  kat hk ListCSizeSSZ 1
  apply load_step _ _ _ _ (Int.toBytes 8 q.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk ListCSizeSSZ 2
  apply load_step _ _ _ _ (Int.toBytes 8 (BitVec.ofNat 64 ls.length).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk ListCSizeSSZ 3
  intro _
  kat hk ListCSizeSSZ 4
  kat hk ListCSizeSSZ 5
  klabel hk hf ListCSizeSSZ 12
  refine eventually_trans _ _ _ _ (lcs_loop k hk hf q ps ls hlen hn hsum ra (fun _ => True) ls.length _
    (Nat.le_refl _) (by simp) (by simp [lcAcc]; rfl)
    rfl (by show (BitVec.ofNat 64 ls.length).toNat = _; simp; omega) hall (sep_true (by ecancel))) ?_
  rintro st ⟨h1, h2, h3, h4⟩
  apply Eventually.done
  exact ⟨h1, h2, h3, h4⟩

open Fv1 EthLib.Serialization.Ssz in
theorem lc_bodies_size : ∀ (items : List ListU64),
    (bodiesOf (offsetSlots (items.map luEncode))).size = ((items.map fun x => x.l.length).map fun l => 4 + 8 * l).sum
  | [] => by simp [bodiesOf]
  | x :: rest => by
    simp only [List.map_cons, offsetSlots_cons, bodiesOf, Array.size_append, List.sum_cons, lu_encode_size,
      lc_bodies_size rest]

open Fv1 EthLib.Serialization.Ssz in
/-- The value SizeSSZ returns is the length of the EthLib encoding. -/
theorem lc_size_eq (g : ListCG) :
    (lcEncode g).size = lcAcc (g.items.map fun x => x.l.length) g.items.length := by
  simp only [lcEncode, lcBody, lcParts, Array.size_append, headOf_offsetSlots_size, List.length_map,
    lc_bodies_size, lcAcc, List.take_length, Fv.uintBytes_size]
  induction g.items with
  | nil => simp
  | cons x rest ih => simp [List.sum_cons] at ih ⊢; omega
