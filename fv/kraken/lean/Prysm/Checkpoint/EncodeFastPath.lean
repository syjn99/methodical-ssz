import Runtime.Contracts
import Machine.Frame
import Prysm.Checkpoint.Code
import Prysm.Checkpoint.DecodeAccept
import Machine.StoreLemmas
import Runtime.StaticBoxLemmas
import Codec.EncodeBitVecLemmas

/-!
# Real Prysm `(*v1alpha1.Checkpoint).MarshalSSZTo`, fast path, Go 1.26.10 machine code

    func (c *Checkpoint) MarshalSSZTo(dst []byte) ([]byte, error) {
        if dst, err = c.Epoch.MarshalSSZTo(dst); err != nil { ... }   // inlined, cannot fail
        if len(c.Root) != 32 { return nil, ssz.ErrBytesLength }
        dst = append(dst, c.Root...); return dst, err }

`(*Epoch).MarshalSSZTo` → `MarshalSSZ` → `MarshalUint64([]byte{}, e)` →
`binary.LittleEndian.AppendUint64` are inlined (compiler `-m=2` report, `prysm/go1.26.10/evidence/gcflags-m2.txt`): the
compiler zeroes a 32-byte stack temp (`movups %xmm15` twice, directives 13–15),
stores the epoch word in it (16) and copies 8 bytes from it to `dst[len:]`
(34–35). X15 is not assumed to be zero: the temp's bytes 8–31 are existential
in the conclusion.

Directive indices of `Prysm.Checkpoint.Code.marshalSSZTo`: 2–3 guard, 4–7 prologue (`sub $0x68`,
rbx spill), 8 `lea 0x8(%rcx),%rdx`, 9 load Epoch (offset 8), 13–16 temp,
17–18 `cmp %rdx,%rdi; jae L_7b` (capacity), 33 `L_7b`, 34–35 store the epoch
bytes, 36 load `Root.ptr`, 37–38 `cmpq $0x20,0x18(%rax); jne` (`len(Root)`),
39–41 capacity for the root, 55 `L_cf`, 56–58 spills, 59–62 `memmove(dst+len+8,
Root.ptr, 32)`, 63–70 return `(dst, len+40, cap, nil)`.
After the split of this module, the BitVec lemma that other types use is in `Codec/EncodeBitVecLemmas.lean`.
-/

open Machine Runtime Prysm.Checkpoint.Code
variable [Host]

namespace Prysm.Checkpoint

theorem Encode.fast_path_slot (x : BitVec 64) : x - 8#64 - 104 - 8#64 = x - 120 := by bv_omega

theorem Encode.fast_path_ret (x : BitVec 64) : ({ toBitVec := x - 120 } + 8 : UInt64) = { toBitVec := x - 112 } := by
  apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega

theorem Encode.fast_path_split16 (L : List UInt8) (a : BitVec 64) (h : L.length = 16) :
    Eq (L.At a) = Eq ((L.take 8).At a) ⋆ Eq ((L.drop 8).At (a + 8)) := by
  conv => lhs; rw [← List.take_append_drop 8 L]
  exact at_app _ _ (by rw [List.length_take, h]; rfl) (by simp [h])

theorem Encode.fast_path_len40 (x : UInt64) (h : x.toNat + 40 < 2 ^ 64) :
    ({ toBitVec := x.toBitVec + 8 + 32 } : UInt64).toNat = x.toNat + 40 := by
  have h' : x.toBitVec.toNat + 40 < 2 ^ 64 := h
  show (x.toBitVec + 8 + 32).toNat = x.toBitVec.toNat + 40
  bv_omega

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem Encode.fast_path (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (cst e8 cC ctl root pre d0 d1 : List UInt8) (hcst : cst.length = 8) (he8 : e8.length = 8) (hcC : cC.length = 8)
    (hctl : ctl.length = 32) (hroot : root.length = 32) (hd0 : d0.length = 8) (hd1 : d1.length = 32)
    (p : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s2 l16 l24 l32 t40 t30 rslot : List UInt8)
    (hfp : fp.length = 8) (h2 : s2.length = 8) (hl16 : l16.length = 8) (hl24 : l24.length = 8)
    (hl32 : l32.length = 8) (ht40 : t40.length = 16) (ht30 : t30.length = 16) (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16)) ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32)) ⋆ Eq (t30.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 120)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq (e8.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (ctl.At (s.regs.rax.toBitVec + 40)) ⋆ Eq (root.At p)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8)) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 120 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 40 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hmm : MemmoveContract S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 40 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (t u scr : List UInt8), t.length = 8 ∧ u.length = 16 ∧ scr.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 40).toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (u.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (e8.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (t.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 63)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq (e8.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (ctl.At (s.regs.rax.toBitVec + 40)) ⋆ Eq (root.At p)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (e8.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (root.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hcap hcap63 hpre ⊢
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
  step_directive hk marshalSSZTo 14
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  unfold_step
  rw [show rsp.toBitVec - 8#64 - 104 + 48 = rsp.toBitVec - 64 by bv_omega]
  apply Machine.store_avx_step _ _ _ _ t40 _ _ (by ecancel) (by exact ht40) (by decide)
  intro m3 H3
  unfold_step
  step_directive hk marshalSSZTo 15
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  unfold_step
  rw [show rsp.toBitVec - 64 + 16 = rsp.toBitVec - 48 by bv_omega]
  apply Machine.store_avx_step _ _ _ _ t30 _ _ (by ecancel) (by exact ht30) (by decide)
  intro m4 H4
  unfold_step
  rw [Machine.at_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 64),
    show rsp.toBitVec - 64 + 8 = rsp.toBitVec - 56 by bv_omega] at H4
  step_directive hk marshalSSZTo 16
  apply store_step_at _ _ (rsp.toBitVec - 64) _ _ _ ((Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).take 8)
    _ _ (by checkpoint_addr) (by ecancel) (by rw [List.length_take, Int.toBytes_length]; rfl)
  intro m5 H5
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl e8 he8] at H5
  unfold_step
  step_directive hk marshalSSZTo 17
  step_directive hk marshalSSZTo 18
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  label_address hk hf marshalSSZTo 33
  step_directive hk marshalSSZTo 33
  step_directive hk marshalSSZTo 34
  apply load_step_at _ _ (rsp.toBitVec - 64) _ _ e8 _ _ (by checkpoint_addr) (by ecancel) (by exact he8)
  unfold_step
  step_directive hk marshalSSZTo 35
  rw [Codec.add_mul_one]
  apply store_step _ _ _ _ _ d0 _ _ (by ecancel) (by exact hd0)
  intro m6 H6
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl e8 he8] at H6
  unfold_step
  step_directive hk marshalSSZTo 36
  apply load_step_at _ _ (rax.toBitVec + 16) _ _ (Int.toBytes 8 p.toInt) _ _ (by checkpoint_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk marshalSSZTo 37
  apply load_step_at _ _ (rax.toBitVec + 24) _ _ (Int.toBytes 8 32) _ _ (by checkpoint_addr) (by ecancel) (by rfl)
  simp only [show Int.ofBytes (Int.toBytes 8 32) = 32 by decide]
  unfold_step
  step_directive hk marshalSSZTo 38
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  step_directive hk marshalSSZTo 39
  step_directive hk marshalSSZTo 40
  step_directive hk marshalSSZTo 41
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  label_address hk hf marshalSSZTo 55
  step_directive hk marshalSSZTo 55
  step_directive hk marshalSSZTo 56
  apply store_step_at _ _ (rsp.toBitVec - 24) _ _ _ l24 _ _ (by checkpoint_addr) (by ecancel) (by exact hl24)
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  unfold_step
  step_directive hk marshalSSZTo 57
  apply store_step_at _ _ (rsp.toBitVec - 32) _ _ _ l32 _ _ (by checkpoint_addr) (by ecancel) (by exact hl32)
  intro m8 H8
  simp only [Width.bytes, Width.bits] at H8
  unfold_step
  step_directive hk marshalSSZTo 58
  apply store_step_at _ _ (rsp.toBitVec - 16) _ _ _ l16 _ _ (by checkpoint_addr) (by ecancel) (by exact hl16)
  intro m9 H9
  simp only [Width.bytes, Width.bits] at H9
  unfold_step
  step_directive hk marshalSSZTo 59
  step_directive hk marshalSSZTo 60
  step_directive hk marshalSSZTo 61
  step_directive hk marshalSSZTo 62
  apply store_step_at _ _ (rsp.toBitVec - 120) _ _ _ rslot _ _ (Encode.fast_path_slot _) (by ecancel) (by exact hrs)
  intro m10 H10
  simp only [Width.bytes, Width.bits] at H10
  unfold_step
  rw [Encode.fast_path_slot] at *
  rw [Codec.add_add_8_mul_one] at *
  refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (k + 62 + 1)) root d1 scratch _
    (by rw [hroot]; rfl) (by rw [hroot, hd1]) hsc (by dsimp only; ecancel)) ?_
  rintro ⟨e1, pc1⟩ ⟨hpc1, hrsp1, hr141, hrbp1, stk1, hstk1, Hm1⟩
  dsimp only at hpc1 hrsp1 hr141 hrbp1 Hm1
  subst hpc1
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩,
    zmms1, flags1, mem1⟩ := e1
  simp only at hrsp1 hr141 hrbp1 Hm1
  rw [Encode.fast_path_ret] at hrsp1
  subst rsp1 r141 rbp1
  step_directive hk marshalSSZTo 63
  apply load_step_at _ _ (rsp.toBitVec - 16) _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by checkpoint_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk marshalSSZTo 64
  apply load_step_at _ _ (rsp.toBitVec - 32) _ _ (Int.toBytes 8 (rcx.toBitVec + 8 + 32).toInt) _ _ (by checkpoint_addr)
    (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk marshalSSZTo 65
  apply load_step_at _ _ (rsp.toBitVec - 24) _ _ (Int.toBytes 8 rdi.toBitVec.toInt) _ _ (by checkpoint_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk marshalSSZTo 66
  intro _
  step_directive hk marshalSSZTo 67
  intro _
  step_directive hk marshalSSZTo 68
  step_directive hk marshalSSZTo 69
  apply load_step_at _ _ (rsp.toBitVec - 8) _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by checkpoint_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk marshalSSZTo 70
  apply load_step_at _ _ rsp.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by checkpoint_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?tt, ?uu, stk1, ?htt, ?huu, hstk1, ?hmem⟩
  case hmem =>
    rw [show k + 62 + 1 = k + 63 from rfl] at Hm1
    rw [show rcx.toBitVec + 40 = rcx.toBitVec + 8 + 32 by bv_omega]
    ecancel
  case htt => simp [Int.toBytes_length]
  case huu => simp [Int.toBytes_length]
  all_goals first
    | exact trivial
    | with_reducible rfl
    | (exact Encode.fast_path_len40 rcx (by omega))
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (apply UInt64.toBitVec_inj.mp; checkpoint_addr)

end Prysm.Checkpoint
