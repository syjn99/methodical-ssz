import Fk.LcMarshal
import Fk.LcReject

/-!
# ListC.UnmarshalSSZ: the empty list (`len(buf) = 4`)

`lc_accept_empty_main`: with `buf = [4, 0, 0, 0]` the decoder sets `c.Items`
to the empty slice (pointer `runtime.noptrbss`, len 0, cap 0) and returns nil.
`lc_unmarshal_accept_empty_spec_k`: EthLib accepts a 4-byte input only as the
empty list, and the machine result holds that value.

Premises the Go caller guarantees: receiver ≠ nil (24 mapped bytes), X15 = 0
(Go ABIInternal on amd64 keeps X15 zero; the `movups %xmm15` store writes
len = cap = 0). Fast-path premises: the stack guard, the write barrier flag 0.
-/

namespace Fk
open Fk.Code Fv1 EthLib.Serialization.Ssz
variable [Host]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem lc_accept_empty_main (k : Nat) (hk : ListCUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListCUnmarshalSSZ k)
    (s : MachineData) (ra guard : UInt64) (fp slot cP cLC : List UInt8) (hfp : fp.length = 8)
    (hsl : slot.length = 8) (hcP : cP.length = 8) (hcLC : cLC.length = 16)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ([4, 0, 0, 0].At s.regs.rbx.toBitVec)
      ⋆ Eq (cP.At s.regs.rax.toBitVec) ⋆ Eq (cLC.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat + 96 < s.regs.rsp.toNat) (hsp : 232 ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rcx.toNat = 4) (hcap : s.regs.rcx.toNat ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hx15 : s.zmms.get (AvxReg.xmm RegMm.mm15) = 0) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (Eq ((Int.toBytes 8 (label "runtime.noptrbss").toBitVec.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((List.replicate 16 0).At (s.regs.rax.toBitVec + 8))
          ⋆ R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hlen hcap hcap63 hx15 ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *
  kat hk ListCUnmarshalSSZ 0
  kat hk ListCUnmarshalSSZ 1
  kat hk ListCUnmarshalSSZ 2
  kat hk ListCUnmarshalSSZ 3
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListCUnmarshalSSZ 4
  split
  case isTrue h =>
    exfalso
    rw [cmp_be_false _ _ _ _ (by rw [toNat_add_neg96 _ (by simp; omega)]; simp; omega)] at h
    exact absurd h (by simp)
  simp only [Effects.All]
  kat hk ListCUnmarshalSSZ 5
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk ListCUnmarshalSSZ 6
  kat hk ListCUnmarshalSSZ 7
  kat hk ListCUnmarshalSSZ 8
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ slot _ _ (lc_s16 _) (by ecancel) (by exact hsl)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk ListCUnmarshalSSZ 9
  kat hk ListCUnmarshalSSZ 10
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
  simp only [Effects.All]
  kat hk ListCUnmarshalSSZ 11
  apply load_step_at _ _ rbx.toBitVec _ _ [4, 0, 0, 0] _ _ (by bv_omega) (by ecancel) (by simp)
  simp only [show Int.ofBytes [4, 0, 0, 0] = 4 by simp [Int.ofBytes]]
  kunfold
  kat hk ListCUnmarshalSSZ 12
  kat hk ListCUnmarshalSSZ 13
  kat hk ListCUnmarshalSSZ 14
  kat hk ListCUnmarshalSSZ 15
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk ListCUnmarshalSSZ 16
  kat hk ListCUnmarshalSSZ 17
  kat hk ListCUnmarshalSSZ 18
  kat hk ListCUnmarshalSSZ 19
  kshl64 63
  kat hk ListCUnmarshalSSZ 20
  intro _
  kat hk ListCUnmarshalSSZ 21
  kat hk ListCUnmarshalSSZ 22
  kat hk ListCUnmarshalSSZ 23
  kat hk ListCUnmarshalSSZ 24
  kat hk ListCUnmarshalSSZ 25
  kat hk ListCUnmarshalSSZ 26
  kat hk ListCUnmarshalSSZ 27
  rw [jle3_true _ (by rw [BitVec.add_comm, ← BitVec.sub_eq_add_neg, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp; omega)]
  simp only [↓reduceIte, Effects.All]
  klabel hk hf ListCUnmarshalSSZ 178
  kat hk ListCUnmarshalSSZ 178
  kat hk ListCUnmarshalSSZ 179
  kat hk ListCUnmarshalSSZ 180
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    apply h; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega
  simp only [Effects.All]
  kat hk ListCUnmarshalSSZ 181
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  kunfold
  apply store_avx_step _ _ _ _ cLC _ _ (by ecancel) (by exact hcLC) (by decide)
  intro m3 H3
  kunfold
  rw [hx15, show Int.toBytes AvxWidth.W128.bytes (0 : BitVec 128).toInt = List.replicate 16 0 by decide] at H3
  kat hk ListCUnmarshalSSZ 182
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk ListCUnmarshalSSZ 183
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf ListCUnmarshalSSZ 187
  kat hk ListCUnmarshalSSZ 187
  kat hk ListCUnmarshalSSZ 188
  kat hk ListCUnmarshalSSZ 189
  apply store_step_at _ _ rax.toBitVec _ _ _ cP _ _ (by kaddr) (by ecancel) (by exact hcP)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  kat hk ListCUnmarshalSSZ 190
  intro _
  kat hk ListCUnmarshalSSZ 191
  intro _
  kat hk ListCUnmarshalSSZ 192
  klabel hk hf ListCUnmarshalSSZ 226
  kat hk ListCUnmarshalSSZ 226
  kat hk ListCUnmarshalSSZ 227
  kat hk ListCUnmarshalSSZ 228
  kat hk ListCUnmarshalSSZ 229
  rw [lc_pop]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListCUnmarshalSSZ 230
  rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only
  refine ⟨trivial, UInt64.toBitVec_inj.mp (by simp), UInt64.toBitVec_inj.mp (by simp),
    UInt64.toBitVec_inj.mp (by simp), trivial, ?_⟩
  refine sep_mono_right' (Q := ?Q) (fun _ _ => trivial) ?h
  case h => ecancel

set_option maxHeartbeats 4000000 in
/-- **ListC empty list against EthLib.** If EthLib accepts a 4-byte input
`bsA` as `v`, then `v` is the empty list (`g.items = []`), `bsA = lcEncode g`,
and the machine sets `c.Items` to (`runtime.noptrbss`, 0, 0) and returns nil. -/
theorem lc_unmarshal_accept_empty_spec_k (k : Nat) (hk : ListCUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListCUnmarshalSSZ k)
    (bsA : Array UInt8) (v : Value) (hd : deserialize lcDesc bsA = .ok v) (h4 : bsA.size = 4)
    (s : MachineData) (ra guard : UInt64) (fp slot cP cLC : List UInt8) (hfp : fp.length = 8)
    (hsl : slot.length = 8) (hcP : cP.length = 8) (hcLC : cLC.length = 16)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (bsA.toList.At s.regs.rbx.toBitVec)
      ⋆ Eq (cP.At s.regs.rax.toBitVec) ⋆ Eq (cLC.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat + 96 < s.regs.rsp.toNat) (hsp : 232 ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rcx.toNat = bsA.size) (hcap : s.regs.rcx.toNat ≤ s.regs.rdi.toNat)
    (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hx15 : s.zmms.get (AvxReg.xmm RegMm.mm15) = 0) :
    ∃ g : ListCG, g.items = [] ∧ g.toValue = v ∧ bsA = lcEncode g ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (Eq ((Int.toBytes 8 (label "runtime.noptrbss").toBitVec.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((List.replicate 16 0).At (s.regs.rax.toBitVec + 8))
          ⋆ R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨g, hg, rfl, rfl⟩ := lc_accepted bsA v hd
  obtain ⟨hsz, -, -, hne⟩ := lc_shape g hg
  have he : g.items = [] := by
    cases h : g.items with
    | nil => rfl
    | cons x xs => exfalso; have := (hne (by simp [h])).1; omega
  refine ⟨g, he, rfl, rfl, ?_⟩
  have hb : (lcEncode g).toList = [4, 0, 0, 0] := by
    rw [(lc_marshal_spec_k g hg).2, he]; rfl
  rw [hb] at h_mem
  exact lc_accept_empty_main k hk hf s ra guard fp slot cP cLC hfp hsl hcP hcLC R h_mem hguard hsp
    (by rw [hlen, h4]) hcap hcap63 hx15

end Fk
