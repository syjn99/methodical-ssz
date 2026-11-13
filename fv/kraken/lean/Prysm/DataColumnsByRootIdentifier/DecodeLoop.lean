import Machine.Block
import Machine.Labels
import Prysm.DataColumnsByRootIdentifier.CodeUnmarshalSSZ
import Prysm.SyncCommittee.DecodeLoopLemmas

/-!
# Decoder: the element loop (the text of `Prysm/IndexedAttestation/DecodeLoop.lean`)

Loop head `L_320` (directive 185). The same instruction order as `Prysm.IndexedAttestation.Decode.iter` (147–165, 143–146) with this
function's registers and slots: rax = i, rdx = n, rcx = cap − 36, rdi = the input pointer `p0` (buf + 36), rsi = the
receiver `c`; the receiver's Columns words at `c + 32` (pointer A) and `c + 40` (len). Index map `Prysm/IndexedAttestation/DecodeLoop.lean` → here:
147–152 → 185–190, 154–157 → 191–194 (195 nop), 158–164 → 196–202, 143–146 → 180–183 (184 nop), exit 166 → 204.
-/

open Machine Runtime TestTarget Prysm.DataColumnsByRootIdentifier.Code
variable [Host]

namespace Prysm.DataColumnsByRootIdentifier

-- Measured: without this option `klabel` (directive 180) stops with "maximum recursion depth" (the
-- `simp` that unfolds the program literal, as in `Prysm/IndexedAttestation/DecodeLoop.lean`); 1024 passes.
set_option maxRecDepth 1024 in
theorem Decode.iter (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (ib : List UInt8) (n i : Nat) (hib : ib.length = 8 * n) (hn : n ≤ 128) (hi : i < n)
    (p0 c A nb : BitVec 64) (hnb : nb.toNat = n) (R : DataMem → Prop) (s : MachineData)
    (hrax : s.regs.rax.toNat = i) (hrdx : s.regs.rdx.toNat = n) (hrcx : 8 * n ≤ s.regs.rcx.toNat)
    (hrdi : s.regs.rdi.toBitVec = p0) (hrsi : s.regs.rsi.toBitVec = c)
    (sp bp r14v : UInt64) (hrsp : s.regs.rsp = sp) (hrbp : s.regs.rbp = bp) (hr14 : s.regs.r14 = r14v)
    (h_mem : s.dmem =⋆ Eq (ib.At p0) ⋆ Eq ((Int.toBytes 8 A.toInt).At (c + 32)) ⋆ Eq ((Int.toBytes 8 nb.toInt).At (c + 40))
      ⋆ Eq ((ib.take (8 * i) ++ List.replicate (8 * (n - i)) 0).At A) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 185) ∧ st.data.regs.rax.toNat = i + 1 ∧ st.data.regs.rdx.toNat = n
        ∧ 8 * n ≤ st.data.regs.rcx.toNat ∧ st.data.regs.rdi.toBitVec = p0 ∧ st.data.regs.rsi.toBitVec = c
        ∧ st.data.regs.rsp = sp ∧ st.data.regs.rbp = bp ∧ st.data.regs.r14 = r14v
        ∧ (Eq (ib.At p0) ⋆ Eq ((Int.toBytes 8 A.toInt).At (c + 32)) ⋆ Eq ((Int.toBytes 8 nb.toInt).At (c + 40))
          ⋆ Eq ((ib.take (8 * (i + 1)) ++ List.replicate (8 * (n - (i + 1))) 0).At A) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 185)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hrax hrdx hrcx hrdi hrsi hrsp hrbp hr14
  subst hrdi hrsi hrsp hrbp hr14
  have hz1 := rax.toNat_lt_size; have hz2 := rdx.toNat_lt_size; have hz3 := rcx.toNat_lt_size
  simp only [UInt64.size] at hz1 hz2 hz3
  have hlen : ib.length < 2 ^ 64 := by omega
  rw [block_split ib rdi.toBitVec (8 * i) (by omega) hlen, out_next ib n i hib hi,
    Mem.At_append_sep _ _ _ (by simp; omega), Mem.At_append_sep _ _ _ (by simp; omega)] at h_mem
  simp only [List.length_take, List.length_replicate, hib, Nat.min_eq_left (show 8 * i ≤ 8 * n by omega)] at h_mem
  kat hk unmarshalSSZ 185
  kat hk unmarshalSSZ 186
  kat hk unmarshalSSZ 187
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    exact Prysm.SyncCommittee.jge_false512 _ _ (by simp; omega) (by simp; omega) h
  simp only [Effects.All]
  kat hk unmarshalSSZ 188
  kat hk unmarshalSSZ 189
  kat hk unmarshalSSZ 190
  kshl64 3
  kat hk unmarshalSSZ 191
  kat hk unmarshalSSZ 192
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    (try simp only [Int.shiftLeft_eq] at h)
    obtain ⟨h1, h2⟩ := h; apply h2; apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_sub, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_add]; omega
  simp only [Effects.All]
  kat hk unmarshalSSZ 193
  kat hk unmarshalSSZ 194
  kshl64 3
  kat hk unmarshalSSZ 195
  kat hk unmarshalSSZ 196
  kat hk unmarshalSSZ 197
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    (try simp only [Nat.shiftLeft_eq, Int.shiftLeft_eq] at h); omega
  simp only [Effects.All]
  kat hk unmarshalSSZ 198
  apply load_step_at _ _ (rsi.toBitVec + 40) _ _ (Int.toBytes 8 nb.toInt) _ _ (by bv_omega) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk unmarshalSSZ 199
  kat hk unmarshalSSZ 200
  rw [show rdi.toBitVec + rax.toBitVec * 8#64 = rdi.toBitVec + BitVec.ofNat 64 (8 * i) by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_mul]; omega]
  apply load_step _ _ _ _ ((ib.drop (8 * i)).take 8) _ _ (by ecancel) (by simp; omega)
  kunfold
  kat hk unmarshalSSZ 201
  kat hk unmarshalSSZ 202
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
  simp only [Effects.All]
  klabel hk hf unmarshalSSZ 180
  kat hk unmarshalSSZ 180
  kat hk unmarshalSSZ 181
  apply load_step_at _ _ (rsi.toBitVec + 32) _ _ (Int.toBytes 8 A.toInt) _ _ (by bv_omega) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk unmarshalSSZ 182
  rw [show A + rax.toBitVec * 8#64 = A + BitVec.ofNat 64 (8 * i) by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_mul]; omega]
  apply store_step _ _ _ _ _ (List.replicate 8 0) _ _ (by ecancel) (by simp)
  intro m1 H1
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl _ (show ((ib.drop (8 * i)).take 8).length = 8 by simp; omega)] at H1
  kunfold
  kat hk unmarshalSSZ 183
  kat hk unmarshalSSZ 184
  apply Eventually.done
  refine ⟨rfl, ?_, hrdx, hrcx, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · show (rax.toBitVec + 1).toNat = i + 1; simp [BitVec.toNat_add]; omega
  · dsimp only
    rw [← out_step ib n i hib hi, Mem.At_append_sep _ _ _ (by simp; omega), Mem.At_append_sep _ _ _ (by simp; omega),
      block_split ib rdi.toBitVec (8 * i) (by omega) hlen]
    simp only [List.length_take, List.length_drop, hib,
      Nat.min_eq_left (show 8 * i ≤ 8 * n by omega), Nat.min_eq_left (show 8 ≤ 8 * n - 8 * i by omega)]
    (try simp only [BitVec.ofNat_eq_ofNat] at H1 ⊢)
    ecancel

-- Measured: without this option `klabel` (directive 204) stops with "maximum recursion depth"; 1024 passes.
set_option maxRecDepth 1024 in
theorem Decode.exit (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (ib : List UInt8) (n : Nat) (hib : ib.length = 8 * n) (_hn : n ≤ 128)
    (p0 c A nb : BitVec 64) (R : DataMem → Prop) (s : MachineData)
    (hrax : s.regs.rax.toNat = n) (hrdx : s.regs.rdx.toNat = n)
    (sp bp r14v : UInt64) (hrsp : s.regs.rsp = sp) (hrbp : s.regs.rbp = bp) (hr14 : s.regs.r14 = r14v)
    (h_mem : s.dmem =⋆ Eq (ib.At p0) ⋆ Eq ((Int.toBytes 8 A.toInt).At (c + 32)) ⋆ Eq ((Int.toBytes 8 nb.toInt).At (c + 40))
      ⋆ Eq ((ib.take (8 * n) ++ List.replicate (8 * (n - n)) 0).At A) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 204) ∧ st.data.regs.rsp = sp ∧ st.data.regs.rbp = bp ∧ st.data.regs.r14 = r14v
        ∧ (Eq (ib.At p0) ⋆ Eq ((Int.toBytes 8 A.toInt).At (c + 32)) ⋆ Eq ((Int.toBytes 8 nb.toInt).At (c + 40))
          ⋆ Eq (ib.At A) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 185)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hrax hrdx hrsp hrbp hr14
  subst hrsp hrbp hr14
  have hrr : rax = rdx := UInt64.toNat_inj.mp (by omega)
  subst hrr
  kat hk unmarshalSSZ 185
  kat hk unmarshalSSZ 186
  kat hk unmarshalSSZ 187
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
  simp only [Effects.All]
  klabel hk hf unmarshalSSZ 204
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  rw [Nat.sub_self, Nat.mul_zero, List.replicate_zero, List.append_nil, List.take_of_length_le (by omega)] at h_mem
  exact h_mem

/-- The loop by recursion on the number `j` of iterations left (`i + j = n`); `n = 0` is the case `j = 0, i = 0`. -/
theorem Decode.loop (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (ib : List UInt8) (n : Nat) (hib : ib.length = 8 * n) (hn : n ≤ 128)
    (p0 c A nb : BitVec 64) (hnb : nb.toNat = n) (R : DataMem → Prop) (sp bp r14v : UInt64) :
    ∀ j i (s : MachineData), i + j = n →
    s.regs.rax.toNat = i → s.regs.rdx.toNat = n → 8 * n ≤ s.regs.rcx.toNat →
    s.regs.rdi.toBitVec = p0 → s.regs.rsi.toBitVec = c → s.regs.rsp = sp → s.regs.rbp = bp → s.regs.r14 = r14v →
    (s.dmem =⋆ Eq (ib.At p0) ⋆ Eq ((Int.toBytes 8 A.toInt).At (c + 32)) ⋆ Eq ((Int.toBytes 8 nb.toInt).At (c + 40))
      ⋆ Eq ((ib.take (8 * i) ++ List.replicate (8 * (n - i)) 0).At A) ⋆ R) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 204) ∧ st.data.regs.rsp = sp ∧ st.data.regs.rbp = bp ∧ st.data.regs.r14 = r14v
        ∧ (Eq (ib.At p0) ⋆ Eq ((Int.toBytes 8 A.toInt).At (c + 32)) ⋆ Eq ((Int.toBytes 8 nb.toInt).At (c + 40))
          ⋆ Eq (ib.At A) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 185)⟩
  | 0, i, s, hij, hrax, hrdx, _, _, _, hrsp, hrbp, hr14, h_mem => by
    have hin : i = n := by omega
    rw [hin] at hrax h_mem
    exact Decode.exit k hk hf ib n hib hn p0 c A nb R s hrax hrdx sp bp r14v hrsp hrbp hr14 h_mem
  | j + 1, i, s, hij, hrax, hrdx, hrcx, hrdi, hrsi, hrsp, hrbp, hr14, h_mem => by
    refine eventually_trans _ _ _ _
      (Decode.iter k hk hf ib n i hib hn (by omega) p0 c A nb hnb R s hrax hrdx hrcx hrdi hrsi sp bp r14v hrsp hrbp hr14 h_mem) ?_
    rintro ⟨s', pc⟩ ⟨hpc, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    dsimp only at hpc; subst hpc
    exact Decode.loop k hk hf ib n hib hn p0 c A nb hnb R sp bp r14v j (i + 1) s' (by omega) h1 h2 h3 h4 h5 h6 h7 h8 h9

end Prysm.DataColumnsByRootIdentifier
