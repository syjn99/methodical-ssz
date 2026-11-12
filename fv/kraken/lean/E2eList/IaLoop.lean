import Fk.Block
import Fk.Labels
import E2eList.CodeIa
import E2eList.ScLemmas

/-!
# T3 `(*v1alpha1.IndexedAttestation).UnmarshalSSZ`: the element loop (LV)

Loop head `L_28a` (directive 147). The text of the Go 1.26.3 `lu_iter` / `lu_exit` / `lu_loop` (`Fk/LuLoop.lean`) with
this function's registers: rax = i, rdx = n, rcx = cap − 228 (bytes), rbx = the input pointer `p0` (buf + 228),
rsi = the receiver `c`; the receiver's AttestingIndices words at `c + 8` (pointer A) and `c + 16` (len).
One iteration (147–165, 143–146): `jge` not taken (i < n); `(i+1)·8 ≤ cap − 228`: the `ja L_475` (panicBounds 266) is
not taken; `i·8 ≤ (i+1)·8`: the `jb L_470` (panicBounds 264) is not taken; the 8-byte load from `p0 + 8i`;
`i < len` read from the receiver: the `jb L_27f` is taken, so `jmpq L_46b` (panicBounds 262) is not reached; the
8-byte store to `A + 8i`; rax = i + 1.
-/

open Fk E2eList.Code
variable [Host]

namespace E2eList

-- Measured cause (logs 135, 136): as in `IaReject.lean`, `kat` unfolds the 279-directive program literal
-- `IaUnmarshal`; without this option the first `kat` (directive 147) fails with "maximum recursion depth"; 1024 passes.
set_option maxRecDepth 1024 in
theorem ia_iter (k : Nat) (hk : IaUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh IaUnmarshal k)
    (ib : List UInt8) (n i : Nat) (hib : ib.length = 8 * n) (hn : n ≤ 2048) (hi : i < n)
    (p0 c A nb : BitVec 64) (hnb : nb.toNat = n) (R : DataMem → Prop) (s : MachineData)
    (hrax : s.regs.rax.toNat = i) (hrdx : s.regs.rdx.toNat = n) (hrcx : 8 * n ≤ s.regs.rcx.toNat)
    (hrbx : s.regs.rbx.toBitVec = p0) (hrsi : s.regs.rsi.toBitVec = c)
    (sp bp r14v : UInt64) (hrsp : s.regs.rsp = sp) (hrbp : s.regs.rbp = bp) (hr14 : s.regs.r14 = r14v)
    (h_mem : s.dmem =⋆ Eq (ib.At p0) ⋆ Eq ((Int.toBytes 8 A.toInt).At (c + 8)) ⋆ Eq ((Int.toBytes 8 nb.toInt).At (c + 16))
      ⋆ Eq ((ib.take (8 * i) ++ List.replicate (8 * (n - i)) 0).At A) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 147) ∧ st.data.regs.rax.toNat = i + 1 ∧ st.data.regs.rdx.toNat = n
        ∧ 8 * n ≤ st.data.regs.rcx.toNat ∧ st.data.regs.rbx.toBitVec = p0 ∧ st.data.regs.rsi.toBitVec = c
        ∧ st.data.regs.rsp = sp ∧ st.data.regs.rbp = bp ∧ st.data.regs.r14 = r14v
        ∧ (Eq (ib.At p0) ⋆ Eq ((Int.toBytes 8 A.toInt).At (c + 8)) ⋆ Eq ((Int.toBytes 8 nb.toInt).At (c + 16))
          ⋆ Eq ((ib.take (8 * (i + 1)) ++ List.replicate (8 * (n - (i + 1))) 0).At A) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 147)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hrax hrdx hrcx hrbx hrsi hrsp hrbp hr14
  subst hrbx hrsi hrsp hrbp hr14
  have hz1 := rax.toNat_lt_size; have hz2 := rdx.toNat_lt_size; have hz3 := rcx.toNat_lt_size
  simp only [UInt64.size] at hz1 hz2 hz3
  have hlen : ib.length < 2 ^ 64 := by omega
  rw [block_split ib rbx.toBitVec (8 * i) (by omega) hlen, out_next ib n i hib hi,
    Mem.At_append_sep _ _ _ (by simp; omega), Mem.At_append_sep _ _ _ (by simp; omega)] at h_mem
  simp only [List.length_take, List.length_replicate, hib, Nat.min_eq_left (show 8 * i ≤ 8 * n by omega)] at h_mem
  kat hk IaUnmarshal 147
  kat hk IaUnmarshal 148
  kat hk IaUnmarshal 149
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    exact jge_false512 _ _ (by simp; omega) (by simp; omega) h
  simp only [Effects.All]
  kat hk IaUnmarshal 150
  kat hk IaUnmarshal 151
  kat hk IaUnmarshal 152
  kshl64 3
  kat hk IaUnmarshal 153
  kat hk IaUnmarshal 154
  kat hk IaUnmarshal 155
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    (try simp only [Int.shiftLeft_eq] at h)
    obtain ⟨h1, h2⟩ := h; apply h2; apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_sub, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_add]; omega
  simp only [Effects.All]
  kat hk IaUnmarshal 156
  kat hk IaUnmarshal 157
  kshl64 3
  kat hk IaUnmarshal 158
  kat hk IaUnmarshal 159
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    (try simp only [Nat.shiftLeft_eq, Int.shiftLeft_eq] at h); omega
  simp only [Effects.All]
  kat hk IaUnmarshal 160
  apply load_step_at _ _ (rsi.toBitVec + 16) _ _ (Int.toBytes 8 nb.toInt) _ _ (by bv_omega) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk IaUnmarshal 161
  kat hk IaUnmarshal 162
  rw [show rbx.toBitVec + rax.toBitVec * 8#64 = rbx.toBitVec + BitVec.ofNat 64 (8 * i) by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_mul]; omega]
  apply load_step _ _ _ _ ((ib.drop (8 * i)).take 8) _ _ (by ecancel) (by simp; omega)
  kunfold
  kat hk IaUnmarshal 163
  kat hk IaUnmarshal 164
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
  simp only [Effects.All]
  klabel hk hf IaUnmarshal 143
  kat hk IaUnmarshal 143
  kat hk IaUnmarshal 144
  apply load_step_at _ _ (rsi.toBitVec + 8) _ _ (Int.toBytes 8 A.toInt) _ _ (by bv_omega) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk IaUnmarshal 145
  rw [show A + rax.toBitVec * 8#64 = A + BitVec.ofNat 64 (8 * i) by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_mul]; omega]
  apply store_step _ _ _ _ _ (List.replicate 8 0) _ _ (by ecancel) (by simp)
  intro m1 H1
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl _ (show ((ib.drop (8 * i)).take 8).length = 8 by simp; omega)] at H1
  kunfold
  kat hk IaUnmarshal 146
  apply Eventually.done
  refine ⟨rfl, ?_, hrdx, hrcx, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · show (rax.toBitVec + 1).toNat = i + 1; simp [BitVec.toNat_add]; omega
  · dsimp only
    rw [← out_step ib n i hib hi, Mem.At_append_sep _ _ _ (by simp; omega), Mem.At_append_sep _ _ _ (by simp; omega),
      block_split ib rbx.toBitVec (8 * i) (by omega) hlen]
    simp only [List.length_take, List.length_drop, hib,
      Nat.min_eq_left (show 8 * i ≤ 8 * n by omega), Nat.min_eq_left (show 8 ≤ 8 * n - 8 * i by omega)]
    (try simp only [BitVec.ofNat_eq_ofNat] at H1 ⊢)
    ecancel

-- Measured cause (log 139): as for `ia_iter`; without this option the first `kat` fails with "maximum recursion depth".
set_option maxRecDepth 1024 in
theorem ia_exit (k : Nat) (hk : IaUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh IaUnmarshal k)
    (ib : List UInt8) (n : Nat) (hib : ib.length = 8 * n) (_hn : n ≤ 2048)
    (p0 c A nb : BitVec 64) (R : DataMem → Prop) (s : MachineData)
    (hrax : s.regs.rax.toNat = n) (hrdx : s.regs.rdx.toNat = n)
    (sp bp r14v : UInt64) (hrsp : s.regs.rsp = sp) (hrbp : s.regs.rbp = bp) (hr14 : s.regs.r14 = r14v)
    (h_mem : s.dmem =⋆ Eq (ib.At p0) ⋆ Eq ((Int.toBytes 8 A.toInt).At (c + 8)) ⋆ Eq ((Int.toBytes 8 nb.toInt).At (c + 16))
      ⋆ Eq ((ib.take (8 * n) ++ List.replicate (8 * (n - n)) 0).At A) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 166) ∧ st.data.regs.rsp = sp ∧ st.data.regs.rbp = bp ∧ st.data.regs.r14 = r14v
        ∧ (Eq (ib.At p0) ⋆ Eq ((Int.toBytes 8 A.toInt).At (c + 8)) ⋆ Eq ((Int.toBytes 8 nb.toInt).At (c + 16))
          ⋆ Eq (ib.At A) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 147)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hrax hrdx hrsp hrbp hr14
  subst hrsp hrbp hr14
  have hrr : rax = rdx := UInt64.toNat_inj.mp (by omega)
  subst hrr
  kat hk IaUnmarshal 147
  kat hk IaUnmarshal 148
  kat hk IaUnmarshal 149
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
  simp only [Effects.All]
  klabel hk hf IaUnmarshal 166
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  rw [Nat.sub_self, Nat.mul_zero, List.replicate_zero, List.append_nil, List.take_of_length_le (by omega)] at h_mem
  exact h_mem

/-- The loop by recursion on the number `j` of iterations left (`i + j = n`); `n = 0` is the case `j = 0, i = 0`. -/
theorem ia_loop (k : Nat) (hk : IaUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh IaUnmarshal k)
    (ib : List UInt8) (n : Nat) (hib : ib.length = 8 * n) (hn : n ≤ 2048)
    (p0 c A nb : BitVec 64) (hnb : nb.toNat = n) (R : DataMem → Prop) (sp bp r14v : UInt64) :
    ∀ j i (s : MachineData), i + j = n →
    s.regs.rax.toNat = i → s.regs.rdx.toNat = n → 8 * n ≤ s.regs.rcx.toNat →
    s.regs.rbx.toBitVec = p0 → s.regs.rsi.toBitVec = c → s.regs.rsp = sp → s.regs.rbp = bp → s.regs.r14 = r14v →
    (s.dmem =⋆ Eq (ib.At p0) ⋆ Eq ((Int.toBytes 8 A.toInt).At (c + 8)) ⋆ Eq ((Int.toBytes 8 nb.toInt).At (c + 16))
      ⋆ Eq ((ib.take (8 * i) ++ List.replicate (8 * (n - i)) 0).At A) ⋆ R) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 166) ∧ st.data.regs.rsp = sp ∧ st.data.regs.rbp = bp ∧ st.data.regs.r14 = r14v
        ∧ (Eq (ib.At p0) ⋆ Eq ((Int.toBytes 8 A.toInt).At (c + 8)) ⋆ Eq ((Int.toBytes 8 nb.toInt).At (c + 16))
          ⋆ Eq (ib.At A) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 147)⟩
  | 0, i, s, hij, hrax, hrdx, _, _, _, hrsp, hrbp, hr14, h_mem => by
    have hin : i = n := by omega
    rw [hin] at hrax h_mem
    exact ia_exit k hk hf ib n hib hn p0 c A nb R s hrax hrdx sp bp r14v hrsp hrbp hr14 h_mem
  | j + 1, i, s, hij, hrax, hrdx, hrcx, hrbx, hrsi, hrsp, hrbp, hr14, h_mem => by
    refine eventually_trans _ _ _ _
      (ia_iter k hk hf ib n i hib hn (by omega) p0 c A nb hnb R s hrax hrdx hrcx hrbx hrsi sp bp r14v hrsp hrbp hr14 h_mem) ?_
    rintro ⟨s', pc⟩ ⟨hpc, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    dsimp only at hpc; subst hpc
    exact ia_loop k hk hf ib n hib hn p0 c A nb hnb R sp bp r14v j (i + 1) s' (by omega) h1 h2 h3 h4 h5 h6 h7 h8 h9

end E2eList
