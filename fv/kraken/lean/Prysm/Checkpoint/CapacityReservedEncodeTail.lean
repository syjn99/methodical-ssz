import Prysm.Checkpoint.CapacityReservedCode
import Prysm.Checkpoint.EncodeTail

/-!
# OPT-R1 reserve encoder from `L_e5` (directive 48): the two tails

At `L_e5` both prefixes meet: `rax` = receiver `rcv`, `rbx` = block `b`, `rcx` = `len` `L`,
`rdx` = block capacity `C`; rsp = rsp0 − 152 (frame `sub $0x90`), rbp = rsp0 − 8. The block is
the caller's `dst` on the fast path (`cap − len ≥ 40`) and the `growslice` block after the reserve.
From here the code is the baseline's inlined Epoch append and root append; both tails need only
`L + 8 ≤ C` (resp. `L + 40 ≤ C`), so the two `growslice` calls of this part are never reached.

- `tail_fit` (`len(Root) = 32`, `L + 40 ≤ C`): directives 48–59 (`jae L_13e` taken), 72–80
  (`jae L_19c` taken), 94–110: epoch bytes at `b[L..L+8]`, `memmove(b + L + 8, Root.ptr, 32)`,
  return `(b, L + 40, C, nil)`.
- `tail_rej` (`len(Root) ≠ 32`, `L + 8 ≤ C`): directives 48–59, 72–77 (`jne L_1e7` taken), 111–119:
  the two words of `ssz.ErrBytesLength`, `rax = rbx = rcx = 0`. The epoch bytes are in `b[L..L+8]`.

The stack temp of the inlined `AppendUint64` is rsp0 − 64 … rsp0 − 33 (as in the baseline);
X15 is not assumed zero (bytes 8–31 of the temp are existential). Directive indices are those of
`Prysm.Checkpoint.CapacityReserved.Code.marshalSSZTo`.
-/

open Machine Runtime Prysm.Checkpoint.CapacityReserved.Code
variable [Host]

namespace Prysm.Checkpoint.CapacityReserved

theorem Encode.reserve_call (x : BitVec 64) : x - 152 - 8#64 = x - 160 := by bv_omega

theorem Encode.reserve_ret (x : BitVec 64) : ({ toBitVec := x - 160 } + 8 : UInt64) = { toBitVec := x - 152 } := by
  apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- Tail from `L_e5`, `len(Root) = 32`, `L + 40 ≤ C`. -/
theorem Encode.tail_fit (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (rsp0 r140 rbp0 ra L C : UInt64) (rcv b p : BitVec 64)
    (e8 root pre d0 d1 l16 l24 l32 t40 t30 rslot scratch : List UInt8) (he8 : e8.length = 8)
    (hroot : root.length = 32) (hpre : pre.length = L.toNat) (hd0 : d0.length = 8) (hd1 : d1.length = 32)
    (hl16 : l16.length = 8) (hl24 : l24.length = 8) (hl32 : l32.length = 8) (ht40 : t40.length = 16)
    (ht30 : t30.length = 16) (hrs : rslot.length = 8)
    (S : Nat) (hsc : scratch.length = S) (R : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := rsp0.toBitVec - 152 })
    (hrbp : s.regs.rbp = { toBitVec := rsp0.toBitVec - 8#64 }) (hr14 : s.regs.r14 = r140)
    (hrax : s.regs.rax.toBitVec = rcv) (hrbx : s.regs.rbx.toBitVec = b) (hrcx : s.regs.rcx = L)
    (hrdx : s.regs.rdx = C)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At rsp0.toBitVec)
      ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (rsp0.toBitVec - 8))
      ⋆ Eq (l16.At (rsp0.toBitVec - 16)) ⋆ Eq (l24.At (rsp0.toBitVec - 24)) ⋆ Eq (l32.At (rsp0.toBitVec - 32))
      ⋆ Eq (t30.At (rsp0.toBitVec - 48)) ⋆ Eq (t40.At (rsp0.toBitVec - 64))
      ⋆ Eq (rslot.At (rsp0.toBitVec - 160)) ⋆ Eq (scratch.At (rsp0.toBitVec - 160 - BitVec.ofNat 64 S))
      ⋆ Eq (e8.At (rcv + 8))
      ⋆ Eq ((Int.toBytes 8 p.toInt).At (rcv + 16)) ⋆ Eq ((Int.toBytes 8 32).At (rcv + 24)) ⋆ Eq (root.At p)
      ⋆ Eq (pre.At b) ⋆ Eq (d0.At (b + L.toBitVec)) ⋆ Eq (d1.At (b + L.toBitVec + 8)) ⋆ R)
    (hcap : L.toNat + 40 ≤ C.toNat) (hmm : MemmoveC S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax.toBitVec = b
        ∧ st.data.regs.rbx.toNat = L.toNat + 40 ∧ st.data.regs.rcx = C
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = rsp0 + 8 ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        ∃ (t u scr : List UInt8), t.length = 8 ∧ u.length = 16 ∧ scr.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At rsp0.toBitVec)
          ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (rsp0.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 b.toInt).At (rsp0.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 C.toBitVec.toInt).At (rsp0.toBitVec - 24))
          ⋆ Eq ((Int.toBytes 8 (L.toBitVec + 40).toInt).At (rsp0.toBitVec - 32))
          ⋆ Eq (u.At (rsp0.toBitVec - 48)) ⋆ Eq (e8.At (rsp0.toBitVec - 64)) ⋆ Eq (t.At (rsp0.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 103)).toBitVec.toInt).At (rsp0.toBitVec - 160))
          ⋆ Eq (scr.At (rsp0.toBitVec - 160 - BitVec.ofNat 64 S))
          ⋆ Eq (e8.At (rcv + 8))
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (rcv + 16)) ⋆ Eq ((Int.toBytes 8 32).At (rcv + 24)) ⋆ Eq (root.At p)
          ⋆ Eq (pre.At b) ⋆ Eq (e8.At (b + L.toBitVec)) ⋆ Eq (root.At (b + L.toBitVec + 8)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 48)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp hrbp hr14 hrax hrbx hrcx hrdx h_mem ⊢
  subst rsp rbp r14 rcx rdx hrax hrbx
  have := L.toNat_lt_size; have := C.toNat_lt_size; have := rsp0.toNat_lt_size; simp only [UInt64.size] at *
  kat hk marshalSSZTo 48
  kat hk marshalSSZTo 49
  kat hk marshalSSZTo 50
  apply load_step _ _ _ _ e8 _ _ (by ecancel) (by exact he8)
  kunfold
  kat hk marshalSSZTo 51
  kat hk marshalSSZTo 52
  kat hk marshalSSZTo 53
  kat hk marshalSSZTo 54
  kat hk marshalSSZTo 55
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  kunfold
  rw [show rsp0.toBitVec - 152 + 88 = rsp0.toBitVec - 64 by bv_omega]
  apply Machine.store_avx_step _ _ _ _ t40 _ _ (by ecancel) (by exact ht40) (by decide)
  intro m3 H3
  kunfold
  kat hk marshalSSZTo 56
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  kunfold
  rw [show rsp0.toBitVec - 64 + 16 = rsp0.toBitVec - 48 by bv_omega]
  apply Machine.store_avx_step _ _ _ _ t30 _ _ (by ecancel) (by exact ht30) (by decide)
  intro m4 H4
  kunfold
  rw [Machine.at_split16 _ (Int.toBytes_length 16 _) (rsp0.toBitVec - 64),
    show rsp0.toBitVec - 64 + 8 = rsp0.toBitVec - 56 by bv_omega] at H4
  kat hk marshalSSZTo 57
  apply store_step_at _ _ (rsp0.toBitVec - 64) _ _ _ ((Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).take 8)
    _ _ (by eaddr) (by ecancel) (by rw [List.length_take, Int.toBytes_length]; rfl)
  intro m5 H5
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl e8 he8] at H5
  kunfold
  kat hk marshalSSZTo 58
  kat hk marshalSSZTo 59
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf marshalSSZTo 72
  kat hk marshalSSZTo 72
  kat hk marshalSSZTo 73
  apply load_step_at _ _ (rsp0.toBitVec - 64) _ _ e8 _ _ (by eaddr) (by ecancel) (by exact he8)
  kunfold
  kat hk marshalSSZTo 74
  rw [Codec.add_mul_one]
  apply store_step _ _ _ _ _ d0 _ _ (by ecancel) (by exact hd0)
  intro m6 H6
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl e8 he8] at H6
  kunfold
  kat hk marshalSSZTo 75
  apply load_step_at _ _ (rax.toBitVec + 16) _ _ (Int.toBytes 8 p.toInt) _ _ (by eaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 76
  apply load_step_at _ _ (rax.toBitVec + 24) _ _ (Int.toBytes 8 32) _ _ (by eaddr) (by ecancel) (by rfl)
  simp only [show Int.ofBytes (Int.toBytes 8 32) = 32 by decide]
  kunfold
  kat hk marshalSSZTo 77
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk marshalSSZTo 78
  kat hk marshalSSZTo 79
  kat hk marshalSSZTo 80
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf marshalSSZTo 94
  kat hk marshalSSZTo 94
  kat hk marshalSSZTo 95
  apply store_step_at _ _ (rsp0.toBitVec - 24) _ _ _ l24 _ _ (by eaddr) (by ecancel) (by exact hl24)
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  kat hk marshalSSZTo 96
  apply store_step_at _ _ (rsp0.toBitVec - 32) _ _ _ l32 _ _ (by eaddr) (by ecancel) (by exact hl32)
  intro m8 H8
  simp only [Width.bytes, Width.bits] at H8
  kunfold
  kat hk marshalSSZTo 97
  apply store_step_at _ _ (rsp0.toBitVec - 16) _ _ _ l16 _ _ (by eaddr) (by ecancel) (by exact hl16)
  intro m9 H9
  simp only [Width.bytes, Width.bits] at H9
  kunfold
  kat hk marshalSSZTo 98
  kat hk marshalSSZTo 99
  kat hk marshalSSZTo 100
  kat hk marshalSSZTo 101
  kat hk marshalSSZTo 102
  apply store_step_at _ _ (rsp0.toBitVec - 160) _ _ _ rslot _ _ (Encode.reserve_call _) (by ecancel) (by exact hrs)
  intro m10 H10
  simp only [Width.bytes, Width.bits] at H10
  kunfold
  rw [Encode.reserve_call] at *
  rw [Codec.add_add_8_mul_one] at *
  refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (k + 102 + 1)) root d1 scratch _
    (by rw [hroot]; rfl) (by rw [hroot, hd1]) hsc (by dsimp only; ecancel)) ?_
  rintro ⟨e1, pc1⟩ ⟨hpc1, hrsp1, hr141, hrbp1, stk1, hstk1, Hm1⟩
  dsimp only at hpc1 hrsp1 hr141 hrbp1 Hm1
  subst hpc1
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩,
    zmms1, flags1, mem1⟩ := e1
  simp only at hrsp1 hr141 hrbp1 Hm1
  rw [Encode.reserve_ret] at hrsp1
  subst rsp1 r141 rbp1
  kat hk marshalSSZTo 103
  apply load_step_at _ _ (rsp0.toBitVec - 16) _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by eaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 104
  apply load_step_at _ _ (rsp0.toBitVec - 32) _ _ (Int.toBytes 8 (L.toBitVec + 8 + 32).toInt) _ _ (by eaddr)
    (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 105
  apply load_step_at _ _ (rsp0.toBitVec - 24) _ _ (Int.toBytes 8 C.toBitVec.toInt) _ _ (by eaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 106
  intro _
  kat hk marshalSSZTo 107
  intro _
  kat hk marshalSSZTo 108
  kat hk marshalSSZTo 109
  apply load_step_at _ _ (rsp0.toBitVec - 8) _ _ (Int.toBytes 8 rbp0.toBitVec.toInt) _ _ (by eaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 110
  apply load_step_at _ _ rsp0.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by eaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?tt, ?uu, stk1, ?htt, ?huu, hstk1, ?hmem⟩
  case hmem =>
    rw [show k + 102 + 1 = k + 103 from rfl] at Hm1
    rw [show L.toBitVec + 40 = L.toBitVec + 8 + 32 by bv_omega]
    ecancel
  case htt => simp [Int.toBytes_length]
  case huu => simp [Int.toBytes_length]
  all_goals first
    | exact trivial
    | with_reducible rfl
    | (exact Encode.fast_path_len40 L (by omega))
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (apply UInt64.toBitVec_inj.mp; eaddr)

end Prysm.Checkpoint.CapacityReserved
