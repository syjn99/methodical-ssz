import Prysm.Checkpoint.FunctionSpecsAsNestedField
import Codec.StackGuard

/-!
# `(*v1alpha1.AttestationData).MarshalSSZTo`, fast path, segment 1: entry to `L_88`

    dst = ssz.MarshalUint64(dst, a.Slot)   // inlined; this segment ends before the 8-byte store

Directive indices of `Prysm.AttestationData.Code.marshalSSZTo` follow.
2–4: the stack check `lea -0x38(%rsp),%r12; cmp; jbe`.
5–7: the prologue (`sub $0xb0`).
8: spill rbx at rsp + 16.
9: spill rax at rsp + 8.
10: `lea 0x8(%rcx),%rdx`.
11: load `Slot` (offset 8).
15–18: the 32-byte temp at rsp − 80.
19–20: `cmp %rdx,%rdi; jae L_88` (capacity test, taken).
33: `L_88`.
X15 is not assumed to be zero.
So bytes 8–31 of the temp are existential in the conclusion.
-/

open Machine Runtime Prysm.AttestationData.Code
variable [Host]

namespace Prysm.AttestationData

/-- The label `L_88` (directive 33) of the encoder.
The lemma is at the top level, because the tactic `label_address` exceeds the default recursion depth in the segment. -/
theorem Encode.label_88 (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k) :
    label "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_88" = Host.addrOf (k + 33) :=
  Machine.label_at' hk hf (j := 33)
    (by simp only [marshalSSZTo, List.getElem?_cons_succ, List.getElem?_cons_zero])
    (by simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)

/-- Segment 1 of the encoder fast path: from the entry to `L_88` (directive 33). -/
theorem Encode.head_slot (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (s : MachineData) (ra guard : UInt64) (sl fp a8 b16 ta tb : List UInt8) (hsl : sl.length = 8)
    (hfp : fp.length = 8) (ha8 : a8.length = 8) (hb16 : b16.length = 8) (hta : ta.length = 16) (htb : tb.length = 16)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (a8.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (b16.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (ta.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (tb.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (sl.At (s.regs.rax.toBitVec + 8)) ⋆ R)
    (hguard : guard.toNat + 56 < s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 8 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 33) ∧ st.data.regs.rax = s.regs.rax ∧ st.data.regs.rbx = s.regs.rbx
        ∧ st.data.regs.rcx = s.regs.rcx ∧ st.data.regs.rdx.toBitVec = s.regs.rcx.toBitVec + 8
        ∧ st.data.regs.rdi = s.regs.rdi
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 184 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 } ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (t u : List UInt8), t.length = 8 ∧ u.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (sl.At (s.regs.rsp.toBitVec - 80)) ⋆ Eq (t.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (u.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (sl.At (s.regs.rax.toBitVec + 8)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hcap hcap63 ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *
  step_directive hk marshalSSZTo 0
  step_directive hk marshalSSZTo 1
  step_directive hk marshalSSZTo 2
  step_directive hk marshalSSZTo 3
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk marshalSSZTo 4
  split
  · rename_i h
    rw [Codec.lea_cmp_be_false rsp.toBitVec _ guard.toBitVec _ _ 56 (by rfl) hguard] at h
    exact Bool.noConfusion h
  simp only [Effects.All]
  step_directive hk marshalSSZTo 5
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by checkpoint_addr) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  unfold_step
  step_directive hk marshalSSZTo 6
  step_directive hk marshalSSZTo 7
  step_directive hk marshalSSZTo 8
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ b16 _ _ (by checkpoint_addr) (by ecancel) (by exact hb16)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  unfold_step
  step_directive hk marshalSSZTo 9
  apply store_step_at _ _ (rsp.toBitVec + 8) _ _ _ a8 _ _ (by checkpoint_addr) (by ecancel) (by exact ha8)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  unfold_step
  step_directive hk marshalSSZTo 10
  step_directive hk marshalSSZTo 11
  apply load_step _ _ _ _ sl _ _ (by ecancel) (by exact hsl)
  unfold_step
  step_directive hk marshalSSZTo 12
  step_directive hk marshalSSZTo 13
  step_directive hk marshalSSZTo 14
  step_directive hk marshalSSZTo 15
  step_directive hk marshalSSZTo 16
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  unfold_step
  rw [show rsp.toBitVec - 8#64 - 176 + 104 = rsp.toBitVec - 80 by checkpoint_addr]
  apply Machine.store_avx_step _ _ _ _ ta _ _ (by ecancel) (by exact hta) (by decide)
  intro m4 H4
  unfold_step
  step_directive hk marshalSSZTo 17
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  unfold_step
  rw [show rsp.toBitVec - 80 + 16 = rsp.toBitVec - 64 by checkpoint_addr]
  apply Machine.store_avx_step _ _ _ _ tb _ _ (by ecancel) (by exact htb) (by decide)
  intro m5 H5
  unfold_step
  rw [Machine.at_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 80),
    show rsp.toBitVec - 80 + 8 = rsp.toBitVec - 72 by checkpoint_addr] at H5
  step_directive hk marshalSSZTo 18
  apply store_step_at _ _ (rsp.toBitVec - 80) _ _ _ ((Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).take 8)
    _ _ (by checkpoint_addr) (by ecancel) (by rw [List.length_take, Int.toBytes_length]; rfl)
  intro m6 H6
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl sl hsl] at H6
  unfold_step
  step_directive hk marshalSSZTo 19
  step_directive hk marshalSSZTo 20
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  rw [Encode.label_88 k hk hf]
  apply Eventually.done
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    List.drop 8 (Int.toBytes 16 (BitVec.toInt (zmms.get (AvxReg.xmm RegMm.mm15)))),
    Int.toBytes AvxWidth.W128.bytes (BitVec.toInt (zmms.get (AvxReg.xmm RegMm.mm15))), ?htt, ?huu, ?hmem⟩
  case hmem =>
    dsimp only
    simp only [Std.ExtHashMap.sep_emp] at H6
    exact cast (congrFun (by ac_rfl) _) H6
  case htt => simp [Int.toBytes_length]
  case huu => rw [Int.toBytes_length]
  all_goals first
    | exact trivial
    | with_reducible rfl
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (apply UInt64.toBitVec_inj.mp; checkpoint_addr)
    | (simp; done)

end Prysm.AttestationData
