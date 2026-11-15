import Machine.Frame
import Machine.StoreLemmas
import Prysm.Epoch.EncodeCode
import Codec.EncodeBitVecLemmas

/-!
# Real Prysm `(*primitives.Epoch).MarshalSSZTo`, fast path, Go 1.26.10 machine code

The hand-written method appends the 8 little-endian bytes of the value to `dst` and returns `(dst, nil)`.
The compiler zeroes a 32-byte stack temp (`movups %xmm15` twice), stores the value word in it
and copies 8 bytes from it to `dst[len:]`.
X15 is not assumed to be zero: the temp's bytes 8–31 are existential in the conclusion.

Directive indices of `Prysm.Epoch.Code.marshalSSZTo`: 2–3 guard, 4–7 prologue (`sub $0x48`, rbx spill),
8 `lea 0x8(%rcx),%rdx`, 9 load of the value, 12–15 temp, 16–17 `cmp %rdx,%rdi; jae L_61` (capacity),
29 `L_61`, 30–31 store the value bytes at `dst[len:]`, 32–36 return `(dst, len+8, cap, nil)`, 37–39 epilogue.

**Fast path only**: `len(dst) + 8 ≤ cap(dst)` (no `runtime.growslice` call) and the stack check passes
(no `runtime.morestack_noctxt` call).
-/

open Machine Runtime Prysm.Epoch.Code

namespace Prysm.Epoch

theorem Encode.fast_path_len8 (x : UInt64) (h : x.toNat + 8 < 2 ^ 64) :
    ({ toBitVec := x.toBitVec + 8 } : UInt64).toNat = x.toNat + 8 := by
  have h' : x.toBitVec.toNat + 8 < 2 ^ 64 := h
  show (x.toBitVec + 8).toNat = x.toBitVec.toNat + 8
  bv_omega

variable [Host]

theorem Encode.fast_path (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (e8 pre d0 : List UInt8) (he8 : e8.length = 8) (hd0 : d0.length = 8)
    (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s2 t28 t18 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)
    (ht28 : t28.length = 16) (ht18 : t18.length = 16)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (t28.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (t18.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (e8.At s.regs.rax.toBitVec)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec)) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 8 ≤ s.regs.rdi.toNat) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 8 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (t u : List UInt8), t.length = 8 ∧ u.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (e8.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (t.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (u.At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (e8.At s.regs.rax.toBitVec)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (e8.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hcap hpre ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *
  step_directive hk marshalSSZTo 0
  step_directive hk marshalSSZTo 1
  step_directive hk marshalSSZTo 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk marshalSSZTo 3
  split
  · rename_i h; exfalso
    simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  step_directive hk marshalSSZTo 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  unfold_step
  step_directive hk marshalSSZTo 5
  step_directive hk marshalSSZTo 6
  step_directive hk marshalSSZTo 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by bv_omega) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  unfold_step
  step_directive hk marshalSSZTo 8
  step_directive hk marshalSSZTo 9
  apply load_step _ _ _ _ e8 _ _ (by ecancel) (by exact he8)
  unfold_step
  step_directive hk marshalSSZTo 10
  step_directive hk marshalSSZTo 11
  step_directive hk marshalSSZTo 12
  step_directive hk marshalSSZTo 13
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  unfold_step
  rw [show rsp.toBitVec - 8#64 - 72 + 40 = rsp.toBitVec - 40 by bv_omega]
  apply Machine.store_avx_step _ _ _ _ t28 _ _ (by ecancel) (by exact ht28) (by decide)
  intro m3 H3
  unfold_step
  step_directive hk marshalSSZTo 14
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  unfold_step
  rw [show rsp.toBitVec - 40 + 16 = rsp.toBitVec - 24 by bv_omega]
  apply Machine.store_avx_step _ _ _ _ t18 _ _ (by ecancel) (by exact ht18) (by decide)
  intro m4 H4
  unfold_step
  rw [Machine.at_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 40),
    show rsp.toBitVec - 40 + 8 = rsp.toBitVec - 32 by bv_omega] at H4
  step_directive hk marshalSSZTo 15
  apply store_step_at _ _ (rsp.toBitVec - 40) _ _ _ ((Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).take 8)
    _ _ (by checkpoint_addr) (by ecancel) (by rw [List.length_take, Int.toBytes_length]; rfl)
  intro m5 H5
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl e8 he8] at H5
  unfold_step
  step_directive hk marshalSSZTo 16
  step_directive hk marshalSSZTo 17
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  label_address hk hf marshalSSZTo 29
  step_directive hk marshalSSZTo 29
  step_directive hk marshalSSZTo 30
  apply load_step_at _ _ (rsp.toBitVec - 40) _ _ e8 _ _ (by checkpoint_addr) (by ecancel) (by exact he8)
  unfold_step
  step_directive hk marshalSSZTo 31
  rw [Codec.add_mul_one]
  apply store_step _ _ _ _ _ d0 _ _ (by ecancel) (by exact hd0)
  intro m6 H6
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl e8 he8] at H6
  unfold_step
  step_directive hk marshalSSZTo 32
  step_directive hk marshalSSZTo 33
  step_directive hk marshalSSZTo 34
  step_directive hk marshalSSZTo 35
  intro _
  step_directive hk marshalSSZTo 36
  intro _
  step_directive hk marshalSSZTo 37
  step_directive hk marshalSSZTo 38
  apply load_step_at _ _ (rsp.toBitVec - 8) _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by checkpoint_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk marshalSSZTo 39
  apply load_step_at _ _ rsp.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by checkpoint_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  apply Eventually.done
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, (Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8,
    Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt, ?htt, ?huu, ?hmem⟩
  case hmem =>
    simp only [show AvxWidth.W128.bytes = 16 from rfl, Std.ExtHashMap.sep_emp] at H6
    refine cast (congrFun (?_ : _ = _) m6) H6
    ac_rfl
  case htt => simp [Int.toBytes_length]
  case huu => simp [Int.toBytes_length]
  all_goals first
    | exact trivial
    | with_reducible rfl
    | (exact Encode.fast_path_len8 rcx (by omega))
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (apply UInt64.toBitVec_inj.mp; checkpoint_addr)

end Prysm.Epoch
