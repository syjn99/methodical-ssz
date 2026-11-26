module

public import Codec.SegmentAddress
public import Prysm.AttestationData.EncodeHeadIndex

@[expose] public section

/-!
# `(*v1alpha1.AttestationData).MarshalSSZTo`, fast path, segment 3: `L_e9` to the return of `runtime.memmove`

    dst = ssz.MarshalUint64(dst, a.CommitteeIndex)   // the 8-byte store
    if len(a.BeaconBlockRoot) != 32 { return nil, ssz.ErrBytesLength }
    dst = append(dst, a.BeaconBlockRoot...)

Directive indices of `Prysm.AttestationData.Code.marshalSSZTo` follow.
59: `L_e9`.
60–61: copy the index word of the temp at rsp − 112 to `dst[len+8:]`.
62: load `BeaconBlockRoot.ptr` (offset 24).
63–65: `cmpq $0x20,0x20(%rax); jne` (length test, not taken).
66–68: `lea 0x20(%r8),%r9; cmp %r9,%rdi; jae L_14c` (capacity test, taken).
82: `L_14c`.
83–85: spill `dst.ptr` (rsp − 48), `len + 48` (rsp − 120) and `cap` (rsp − 128).
86–89: `memmove(dst + len + 16, root, 32)` through `MemmoveContract S`.
The call returns to directive 90.
Here `x` is the entry rsp, and the frame base is x − 184.
The return slot of the call is x − 192.
The contract keeps only rsp, rbp and r14.
Directives 90–111 load every other value from memory again.
-/

open Machine Runtime Prysm.AttestationData.Code
variable [Host]

namespace Prysm.AttestationData

/-- The label `L_14c` (directive 82) of the encoder. -/
theorem Encode.label_14c (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k) :
    label "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_14c" = Host.addrOf (k + 82) :=
  Machine.label_at' hk hf (j := 82)
    (by simp only [marshalSSZTo, List.getElem?_cons_succ, List.getElem?_cons_zero])
    (by simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)

/-- The rsp after the return from a call with its return slot at x − 192. -/
theorem Encode.root_ret (x : BitVec 64) : ({ toBitVec := x - 192 } + 8 : UInt64) = { toBitVec := x - 184 } := by
  apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega

/-- Segment 3 of the encoder fast path: from `L_e9` (directive 59) to the return of `runtime.memmove` (directive 90). -/
theorem Encode.head_root (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (x n : BitVec 64) (s : MachineData) (rp : BitVec 64) (ix root d1 d2 q48 q120 q128 rslot : List UInt8)
    (hix : ix.length = 8) (hroot : root.length = 32) (hd1 : d1.length = 8) (hd2 : d2.length = 32)
    (h48 : q48.length = 8) (h120 : q120.length = 8) (h128 : q128.length = 8) (hrs : rslot.length = 8)
    (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hrsp : s.regs.rsp = { toBitVec := x - 184 }) (hrdx : s.regs.rdx = { toBitVec := n + 8 })
    (hr8 : s.regs.r8 = { toBitVec := n + 8 + 8 })
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq (ix.At (x - 112)) ⋆ Eq (q48.At (x - 48)) ⋆ Eq (q120.At (x - 120))
      ⋆ Eq (q128.At (x - 128)) ⋆ Eq (rslot.At (x - 192)) ⋆ Eq (scratch.At (x - 192 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 rp.toInt).At (s.regs.rax.toBitVec + 24)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (root.At rp)
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + n + 8)) ⋆ Eq (d2.At (s.regs.rbx.toBitVec + n + 16)) ⋆ R)
    (hcap : n.toNat + 48 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hmm : MemmoveContract S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 90)
        ∧ st.data.regs.rsp = s.regs.rsp ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ scr : List UInt8, scr.length = S ∧
        (Eq (ix.At (x - 112)) ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (x - 48))
          ⋆ Eq ((Int.toBytes 8 (n + 48).toInt).At (x - 120))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (x - 128))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 90)).toBitVec.toInt).At (x - 192))
          ⋆ Eq (scr.At (x - 192 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 rp.toInt).At (s.regs.rax.toBitVec + 24)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (root.At rp)
          ⋆ Eq (ix.At (s.regs.rbx.toBitVec + n + 8)) ⋆ Eq (root.At (s.regs.rbx.toBitVec + n + 16)) ⋆ R)
          st.data.dmem)
      ⟨s, Host.addrOf (k + 59)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hcap hcap63 hrsp hrdx hr8 ⊢
  subst rsp rdx r8
  have := n.isLt; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *
  step_directive hk marshalSSZTo 59
  step_directive hk marshalSSZTo 60
  apply load_step_at _ _ (x - 112) _ _ ix _ _ (by segment_addr) (by ecancel) (by exact hix)
  unfold_step
  step_directive hk marshalSSZTo 61
  rw [Codec.add_mul_one]
  apply store_step_at _ _ (rbx.toBitVec + n + 8) _ _ _ d1 _ _ (by segment_addr) (by ecancel) (by exact hd1)
  intro m1 H1
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl ix hix] at H1
  unfold_step
  step_directive hk marshalSSZTo 62
  apply load_step_at _ _ (rax.toBitVec + 24) _ _ (Int.toBytes 8 rp.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk marshalSSZTo 63
  apply load_step_at _ _ (rax.toBitVec + 32) _ _ (Int.toBytes 8 32) _ _ (by segment_addr) (by ecancel) (by rfl)
  simp only [show Int.ofBytes (Int.toBytes 8 32) = 32 by decide]
  unfold_step
  step_directive hk marshalSSZTo 64
  step_directive hk marshalSSZTo 65
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  step_directive hk marshalSSZTo 66
  step_directive hk marshalSSZTo 67
  step_directive hk marshalSSZTo 68
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  rw [Encode.label_14c k hk hf]
  step_directive hk marshalSSZTo 82
  step_directive hk marshalSSZTo 83
  apply store_step_at _ _ (x - 48) _ _ _ q48 _ _ (by segment_addr) (by ecancel) (by exact h48)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  unfold_step
  step_directive hk marshalSSZTo 84
  apply store_step_at _ _ (x - 120) _ _ _ q120 _ _ (by segment_addr) (by ecancel) (by exact h120)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  unfold_step
  step_directive hk marshalSSZTo 85
  apply store_step_at _ _ (x - 128) _ _ _ q128 _ _ (by segment_addr) (by ecancel) (by exact h128)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  unfold_step
  step_directive hk marshalSSZTo 86
  step_directive hk marshalSSZTo 87
  step_directive hk marshalSSZTo 88
  step_directive hk marshalSSZTo 89
  apply store_step_at _ _ (x - 192) _ _ _ rslot _ _ (by segment_addr) (by ecancel) (by exact hrs)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  unfold_step
  rw [Codec.add_mul_one, show rbx.toBitVec + (n + 8 + 8) = rbx.toBitVec + n + 16 by segment_addr,
    show x - 184 - 8#64 = x - 192 by segment_addr]
  refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (k + 89 + 1)) root d2 scratch _
    (by rw [hroot]; rfl) (by rw [hroot, hd2]) hsc (by dsimp only; ecancel)) ?_
  rintro ⟨e1, pc1⟩ ⟨hpc1, hrsp1, hr141, hrbp1, stk1, hstk1, Hm1⟩
  dsimp only at hpc1 hrsp1 hr141 hrbp1 Hm1
  subst hpc1
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩,
    zmms1, flags1, mem1⟩ := e1
  simp only at hrsp1 hr141 hrbp1 Hm1
  rw [Encode.root_ret] at hrsp1
  subst rsp1 r141 rbp1
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, stk1, hstk1, ?_⟩
  rw [show k + 89 + 1 = k + 90 from rfl, show n + 8 + 8 + 32 = n + 48 by segment_addr] at Hm1
  simp only [Std.ExtHashMap.sep_emp, Std.ExtHashMap.emp_sep] at Hm1
  dsimp only
  exact cast (congrFun (by ac_rfl) _) Hm1

end Prysm.AttestationData
