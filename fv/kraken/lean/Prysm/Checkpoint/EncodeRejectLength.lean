import Prysm.Checkpoint.EncodeFastPath
import Prysm.ElfData.PrysmTarget
import Codec.EncodeBitVecLemmas

/-!
# Real Prysm `(*v1alpha1.Checkpoint).MarshalSSZTo`, reject `len(c.Root) != 32` (Go 1.26.10)

Go source `phase0.ssz.go:1967`: `return nil, ssz.ErrBytesLength`. The inlined
Epoch encoder runs first: with `cap ≥ len + 8` the code (directives 0–35, the
same prefix as `Encode.fast_path`) has already written the 8 epoch bytes at
`dst[len:len+8]` when directives 37–38 (`cmpq $0x20,0x18(%rax); jne L_108`)
find `len(Root) ≠ 32`. Directives 71–79: `rdi, rsi` = the two words of
`ssz.ErrBytesLength` (address = data item `sszErrBytesLength_addr`),
`rax = rbx = rcx = 0` (nil slice), epilogue.

The conclusion states the side effect exactly (the epoch bytes are written before the root length test): `dst[len:len+8]`
holds the epoch bytes, everything else of `dst` is unchanged, the returned
slice is nil. The 32-byte stack temp is named as in the fast path.
After the split of this module, the BitVec lemma that other types use is in `Codec/EncodeBitVecLemmas.lean`.
-/

open Machine Runtime Prysm.Checkpoint.Code
variable [Host]

namespace Prysm.Checkpoint

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem Encode.reject_length (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (cst e8 cC ctl pre d0 : List UInt8) (hcst : cst.length = 8) (he8 : e8.length = 8) (hcC : cC.length = 8)
    (hctl : ctl.length = 32) (hd0 : d0.length = 8)
    (p : BitVec 64) (rl : UInt64) (hrl : rl ≠ 32)
    (s : MachineData) (ra guard e0 e1 : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s2 t40 t30 : List UInt8)
    (hfp : fp.length = 8) (h2 : s2.length = 8) (ht40 : t40.length = 16) (ht30 : t30.length = 16)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (t30.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq (e8.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 rl.toBitVec.toInt).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (ctl.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrBytesLength_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrBytesLength" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 120 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 8 ≤ s.regs.rdi.toNat) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rcx = 0 ∧ st.data.regs.rdi = e0 ∧ st.data.regs.rsi = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (t u : List UInt8), t.length = 8 ∧ u.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (u.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (e8.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (t.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq (e8.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 rl.toBitVec.toInt).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (ctl.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (e8.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrBytesLength_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrBytesLength" + 8).toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hcap hpre hrl ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *
  kat hk marshalSSZTo 0
  kat hk marshalSSZTo 1
  kat hk marshalSSZTo 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 3
  split
  · rename_i h; exfalso
    simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk marshalSSZTo 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk marshalSSZTo 5
  kat hk marshalSSZTo 6
  kat hk marshalSSZTo 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by bv_omega) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk marshalSSZTo 8
  kat hk marshalSSZTo 9
  apply load_step _ _ _ _ e8 _ _ (by ecancel) (by exact he8)
  kunfold
  kat hk marshalSSZTo 10
  kat hk marshalSSZTo 11
  kat hk marshalSSZTo 12
  kat hk marshalSSZTo 13
  kat hk marshalSSZTo 14
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  kunfold
  rw [show rsp.toBitVec - 8#64 - 104 + 48 = rsp.toBitVec - 64 by bv_omega]
  apply Machine.store_avx_step _ _ _ _ t40 _ _ (by ecancel) (by exact ht40) (by decide)
  intro m3 H3
  kunfold
  kat hk marshalSSZTo 15
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  kunfold
  rw [show rsp.toBitVec - 64 + 16 = rsp.toBitVec - 48 by bv_omega]
  apply Machine.store_avx_step _ _ _ _ t30 _ _ (by ecancel) (by exact ht30) (by decide)
  intro m4 H4
  kunfold
  rw [Machine.at_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 64),
    show rsp.toBitVec - 64 + 8 = rsp.toBitVec - 56 by bv_omega] at H4
  kat hk marshalSSZTo 16
  apply store_step_at _ _ (rsp.toBitVec - 64) _ _ _ ((Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).take 8)
    _ _ (by checkpoint_addr) (by ecancel) (by rw [List.length_take, Int.toBytes_length]; rfl)
  intro m5 H5
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl e8 he8] at H5
  kunfold
  kat hk marshalSSZTo 17
  kat hk marshalSSZTo 18
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf marshalSSZTo 33
  kat hk marshalSSZTo 33
  kat hk marshalSSZTo 34
  apply load_step_at _ _ (rsp.toBitVec - 64) _ _ e8 _ _ (by checkpoint_addr) (by ecancel) (by exact he8)
  kunfold
  kat hk marshalSSZTo 35
  rw [Codec.add_mul_one]
  apply store_step _ _ _ _ _ d0 _ _ (by ecancel) (by exact hd0)
  intro m6 H6
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl e8 he8] at H6
  kunfold
  kat hk marshalSSZTo 36
  apply load_step_at _ _ (rax.toBitVec + 16) _ _ (Int.toBytes 8 p.toInt) _ _ (by checkpoint_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 37
  apply load_step_at _ _ (rax.toBitVec + 24) _ _ (Int.toBytes 8 rl.toBitVec.toInt) _ _ (by checkpoint_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk marshalSSZTo 38
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, Width.bits] at h
    exact hrl (UInt64.toBitVec_inj.mp (Codec.eq_32_of_sub_eq_zero _ h))
  simp only [Effects.All]
  klabel hk hf marshalSSZTo 71
  kat hk marshalSSZTo 71
  kat hk marshalSSZTo 72
  rw [← ElfData.PrysmTarget.sszErrBytesLength_addr_eq]
  apply load_step _ _ _ _ (Int.toBytes 8 e0.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 73
  apply load_step _ _ _ _ (Int.toBytes 8 e1.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 74
  intro _
  kat hk marshalSSZTo 75
  intro _
  kat hk marshalSSZTo 76
  kat hk marshalSSZTo 77
  kat hk marshalSSZTo 78
  apply load_step_at _ _ (rsp.toBitVec - 8) _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by checkpoint_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 79
  apply load_step_at _ _ rsp.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by checkpoint_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?tt, ?uu, ?htt, ?huu, ?hmem⟩
  case hmem => ecancel
  case htt => simp [Int.toBytes_length]
  case huu => simp [Int.toBytes_length]
  all_goals first
    | exact trivial
    | with_reducible rfl
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (apply UInt64.toBitVec_inj.mp; checkpoint_addr)

end Prysm.Checkpoint
