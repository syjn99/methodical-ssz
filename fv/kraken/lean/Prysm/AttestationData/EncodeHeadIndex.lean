import Prysm.AttestationData.EncodeHeadSlot

/-!
# `(*v1alpha1.AttestationData).MarshalSSZTo`, fast path, segment 2: `L_88` to `L_e9`

    dst = ssz.MarshalUint64(dst, a.Slot)             // the 8-byte store
    dst = ssz.MarshalUint64(dst, a.CommitteeIndex)   // inlined; ends before its 8-byte store

Directive indices of `Prysm.AttestationData.Code.marshalSSZTo` follow.
33: `L_88`.
34–35: copy the Slot word of the temp at rsp − 80 to `dst[len:]`.
36: `lea 0x8(%rdx),%r8`.
37: load `CommitteeIndex` (offset 16).
41–44: the 32-byte temp at rsp − 112.
45–46: `cmp %r8,%rdi; jae L_e9` (capacity test, taken).
59: `L_e9`.
Here `x` is the entry rsp, and the frame base is x − 184.
-/

open Machine Runtime Prysm.AttestationData.Code
variable [Host]

namespace Prysm.AttestationData

/-- The label `L_e9` (directive 59) of the encoder. -/
theorem Encode.label_e9 (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k) :
    label "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_e9" = Host.addrOf (k + 59) :=
  Machine.label_at' hk hf (j := 59)
    (by simp only [marshalSSZTo, List.getElem?_cons_succ, List.getElem?_cons_zero])
    (by simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)

/-- Segment 2 of the encoder fast path: from `L_88` (directive 33) to `L_e9` (directive 59). -/
theorem Encode.head_index (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (x : BitVec 64) (s : MachineData) (sl ix d0 ta tb : List UInt8) (hsl : sl.length = 8) (hix : ix.length = 8)
    (hd0 : d0.length = 8) (hta : ta.length = 16) (htb : tb.length = 16)
    (hrsp : s.regs.rsp = { toBitVec := x - 184 }) (hrdx : s.regs.rdx = { toBitVec := s.regs.rcx.toBitVec + 8 })
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq (sl.At (x - 80)) ⋆ Eq (ta.At (x - 112)) ⋆ Eq (tb.At (x - 96))
      ⋆ Eq (ix.At (s.regs.rax.toBitVec + 16)) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec)) ⋆ R)
    (hcap : s.regs.rcx.toNat + 16 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 59) ∧ st.data.regs.rax = s.regs.rax ∧ st.data.regs.rbx = s.regs.rbx
        ∧ st.data.regs.rdx = s.regs.rdx ∧ st.data.regs.r8.toBitVec = s.regs.rcx.toBitVec + 8 + 8
        ∧ st.data.regs.rdi = s.regs.rdi
        ∧ st.data.regs.rsp = s.regs.rsp ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (t u : List UInt8), t.length = 8 ∧ u.length = 16 ∧
        (Eq (sl.At (x - 80)) ⋆ Eq (ix.At (x - 112)) ⋆ Eq (t.At (x - 104)) ⋆ Eq (u.At (x - 96))
          ⋆ Eq (ix.At (s.regs.rax.toBitVec + 16)) ⋆ Eq (sl.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec)) ⋆ R)
          st.data.dmem)
      ⟨s, Host.addrOf (k + 33)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hcap hcap63 hrsp hrdx ⊢
  subst rsp rdx
  have := rcx.toNat_lt_size; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *
  step_directive hk marshalSSZTo 33
  step_directive hk marshalSSZTo 34
  apply load_step_at _ _ (x - 80) _ _ sl _ _ (by checkpoint_addr) (by ecancel) (by exact hsl)
  unfold_step
  step_directive hk marshalSSZTo 35
  rw [Codec.add_mul_one]
  apply store_step _ _ _ _ _ d0 _ _ (by ecancel) (by exact hd0)
  intro m1 H1
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl sl hsl] at H1
  unfold_step
  step_directive hk marshalSSZTo 36
  step_directive hk marshalSSZTo 37
  apply load_step _ _ _ _ ix _ _ (by ecancel) (by exact hix)
  unfold_step
  step_directive hk marshalSSZTo 38
  step_directive hk marshalSSZTo 39
  step_directive hk marshalSSZTo 40
  step_directive hk marshalSSZTo 41
  step_directive hk marshalSSZTo 42
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  unfold_step
  rw [show x - 184 + 72 = x - 112 by checkpoint_addr]
  apply Machine.store_avx_step _ _ _ _ ta _ _ (by ecancel) (by exact hta) (by decide)
  intro m2 H2
  unfold_step
  step_directive hk marshalSSZTo 43
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  unfold_step
  rw [show x - 112 + 16 = x - 96 by checkpoint_addr]
  apply Machine.store_avx_step _ _ _ _ tb _ _ (by ecancel) (by exact htb) (by decide)
  intro m3 H3
  unfold_step
  rw [Machine.at_split16 _ (Int.toBytes_length 16 _) (x - 112),
    show x - 112 + 8 = x - 104 by checkpoint_addr] at H3
  step_directive hk marshalSSZTo 44
  apply store_step_at _ _ (x - 112) _ _ _ ((Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).take 8)
    _ _ (by checkpoint_addr) (by ecancel) (by rw [List.length_take, Int.toBytes_length]; rfl)
  intro m4 H4
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl ix hix] at H4
  unfold_step
  step_directive hk marshalSSZTo 45
  step_directive hk marshalSSZTo 46
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  rw [Encode.label_e9 k hk hf]
  apply Eventually.done
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    List.drop 8 (Int.toBytes 16 (BitVec.toInt (zmms.get (AvxReg.xmm RegMm.mm15)))),
    Int.toBytes AvxWidth.W128.bytes (BitVec.toInt (zmms.get (AvxReg.xmm RegMm.mm15))), ?htt, ?huu, ?hmem⟩
  case hmem =>
    dsimp only
    simp only [Std.ExtHashMap.sep_emp] at H4
    exact cast (congrFun (by ac_rfl) _) H4
  case htt => simp [Int.toBytes_length]
  case huu => rw [Int.toBytes_length]
  all_goals first
    | exact trivial
    | with_reducible rfl
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (apply UInt64.toBitVec_inj.mp; checkpoint_addr)
    | (simp; done)

end Prysm.AttestationData
