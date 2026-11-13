import Prysm.Checkpoint.EncodeGrowFirstSite
import Prysm.Checkpoint.EncodeRejectLength

/-!
# `(*v1alpha1.Checkpoint).MarshalSSZTo` from `L_7b` (directive 33): the three tails

At `L_7b` the inlined Epoch append has its block: `rbx` = block pointer `b`, `rcx` = `len`,
`rdx` = `len + 8`, `rdi` = block capacity `C` (the caller's `dst` when the first capacity test
passed, the `growslice` result otherwise), and the epoch word in the stack temp at rsp0 − 64.
From here the code is the same for both prefixes. Three tails, by the code's branches:

- `Encode.tail_fit` (`len(Root) = 32`, `len + 40 ≤ C`): directives 33–41 (`jae L_cf` taken), 55–70:
  epoch bytes at `b[len..len+8]`, memmove of the root to `b[len+8..len+40]`, return
  `(b, len + 40, C, nil)`.
- `Encode.tail_grow` (`len(Root) = 32`, `len + 8 ≤ C < len + 40`): directives 33–41 (`jae` not
  taken), 42–49 the second `runtime.growslice(old = b, newLen = len + 40, oldCap = C, num = 32,
  et = uint8)` (contract `GrowsliceC Heap typeUint8_addr 1 S`, the existing form, instance esz 1),
  50–54 restore, 55–70 memmove into the new block and return `(nb, len + 40, C2, nil)`. The old
  block keeps `pre ++ epoch` (it is the growslice source).
- `Encode.tail_rej` (`len(Root) ≠ 32`): directives 33–38 (`jne L_108` taken), 71–79: the two words of
  `ssz.ErrBytesLength`, `rax = rbx = rcx = 0`. The epoch bytes are in `b[len..len+8]` (written before the root length test).

`rsp0`, `rbp0`, `r140` are rsp, rbp, r14 at the entry of `MarshalSSZTo`; the frame is rsp0 − 112 …
rsp0 − 8. Every directive index is the Go 1.26.10 `.S`'s (`Prysm.Checkpoint.Code.marshalSSZTo`).
-/

open Machine Runtime Prysm.Checkpoint.Code
variable [Host]

namespace Prysm.Checkpoint

theorem Encode.tail_rsp8 (x : UInt64) : ({ toBitVec := x.toBitVec - 8 + 8#64 + 8#64 } : UInt64) = x + 8 := by
  apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- Tail from `L_7b`, second capacity test passes (`len + 40 ≤ C`). -/
theorem Encode.tail_fit (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (rsp0 r140 rbp0 ra L C : UInt64) (rcv b p : BitVec 64)
    (e8 root pre d0 d1 l16 l24 l32 rslot scratch : List UInt8) (he8 : e8.length = 8) (hroot : root.length = 32)
    (hpre : pre.length = L.toNat) (hd0 : d0.length = 8) (hd1 : d1.length = 32) (hl16 : l16.length = 8)
    (hl24 : l24.length = 8) (hl32 : l32.length = 8) (hrs : rslot.length = 8)
    (S : Nat) (hsc : scratch.length = S) (R : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := rsp0.toBitVec - 112 })
    (hrbp : s.regs.rbp = { toBitVec := rsp0.toBitVec - 8#64 }) (hr14 : s.regs.r14 = r140)
    (hrax : s.regs.rax.toBitVec = rcv) (hrbx : s.regs.rbx.toBitVec = b) (hrcx : s.regs.rcx = L)
    (hrdx : s.regs.rdx = { toBitVec := L.toBitVec + 8 }) (hrdi : s.regs.rdi = C)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At rsp0.toBitVec)
      ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (rsp0.toBitVec - 8))
      ⋆ Eq (l16.At (rsp0.toBitVec - 16)) ⋆ Eq (l24.At (rsp0.toBitVec - 24)) ⋆ Eq (l32.At (rsp0.toBitVec - 32))
      ⋆ Eq (e8.At (rsp0.toBitVec - 64))
      ⋆ Eq (rslot.At (rsp0.toBitVec - 120)) ⋆ Eq (scratch.At (rsp0.toBitVec - 120 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 p.toInt).At (rcv + 16)) ⋆ Eq ((Int.toBytes 8 32).At (rcv + 24)) ⋆ Eq (root.At p)
      ⋆ Eq (pre.At b) ⋆ Eq (d0.At (b + L.toBitVec)) ⋆ Eq (d1.At (b + L.toBitVec + 8)) ⋆ R)
    (hcap : L.toNat + 40 ≤ C.toNat) (hmm : MemmoveC S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax.toBitVec = b
        ∧ st.data.regs.rbx.toNat = L.toNat + 40 ∧ st.data.regs.rcx = C
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = rsp0 + 8 ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        ∃ scr : List UInt8, scr.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At rsp0.toBitVec)
          ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (rsp0.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 b.toInt).At (rsp0.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 C.toBitVec.toInt).At (rsp0.toBitVec - 24))
          ⋆ Eq ((Int.toBytes 8 (L.toBitVec + 40).toInt).At (rsp0.toBitVec - 32))
          ⋆ Eq (e8.At (rsp0.toBitVec - 64))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 63)).toBitVec.toInt).At (rsp0.toBitVec - 120))
          ⋆ Eq (scr.At (rsp0.toBitVec - 120 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (rcv + 16)) ⋆ Eq ((Int.toBytes 8 32).At (rcv + 24)) ⋆ Eq (root.At p)
          ⋆ Eq (pre.At b) ⋆ Eq (e8.At (b + L.toBitVec)) ⋆ Eq (root.At (b + L.toBitVec + 8)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 33)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp hrbp hr14 hrax hrbx hrcx hrdx hrdi h_mem ⊢
  subst rsp rbp r14 rcx rdx rdi hrax hrbx
  have := L.toNat_lt_size; have := C.toNat_lt_size; have := rsp0.toNat_lt_size; simp only [UInt64.size] at *
  kat hk marshalSSZTo 33
  kat hk marshalSSZTo 34
  apply load_step_at _ _ (rsp0.toBitVec - 64) _ _ e8 _ _ (by checkpoint_addr) (by ecancel) (by exact he8)
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
  apply load_step_at _ _ (rax.toBitVec + 24) _ _ (Int.toBytes 8 32) _ _ (by checkpoint_addr) (by ecancel) (by rfl)
  simp only [show Int.ofBytes (Int.toBytes 8 32) = 32 by decide]
  kunfold
  kat hk marshalSSZTo 38
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk marshalSSZTo 39
  kat hk marshalSSZTo 40
  kat hk marshalSSZTo 41
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf marshalSSZTo 55
  kat hk marshalSSZTo 55
  kat hk marshalSSZTo 56
  apply store_step_at _ _ (rsp0.toBitVec - 24) _ _ _ l24 _ _ (by checkpoint_addr) (by ecancel) (by exact hl24)
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  kat hk marshalSSZTo 57
  apply store_step_at _ _ (rsp0.toBitVec - 32) _ _ _ l32 _ _ (by checkpoint_addr) (by ecancel) (by exact hl32)
  intro m8 H8
  simp only [Width.bytes, Width.bits] at H8
  kunfold
  kat hk marshalSSZTo 58
  apply store_step_at _ _ (rsp0.toBitVec - 16) _ _ _ l16 _ _ (by checkpoint_addr) (by ecancel) (by exact hl16)
  intro m9 H9
  simp only [Width.bytes, Width.bits] at H9
  kunfold
  kat hk marshalSSZTo 59
  kat hk marshalSSZTo 60
  kat hk marshalSSZTo 61
  kat hk marshalSSZTo 62
  apply store_step_at _ _ (rsp0.toBitVec - 120) _ _ _ rslot _ _ (Encode.grow_first_site_slot2 _) (by ecancel) (by exact hrs)
  intro m10 H10
  simp only [Width.bytes, Width.bits] at H10
  kunfold
  rw [Encode.grow_first_site_slot2] at *
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
  kat hk marshalSSZTo 63
  apply load_step_at _ _ (rsp0.toBitVec - 16) _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by checkpoint_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 64
  apply load_step_at _ _ (rsp0.toBitVec - 32) _ _ (Int.toBytes 8 (L.toBitVec + 8 + 32).toInt) _ _ (by checkpoint_addr)
    (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 65
  apply load_step_at _ _ (rsp0.toBitVec - 24) _ _ (Int.toBytes 8 C.toBitVec.toInt) _ _ (by checkpoint_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 66
  intro _
  kat hk marshalSSZTo 67
  intro _
  kat hk marshalSSZTo 68
  kat hk marshalSSZTo 69
  apply load_step_at _ _ (rsp0.toBitVec - 8) _ _ (Int.toBytes 8 rbp0.toBitVec.toInt) _ _ (by checkpoint_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 70
  apply load_step_at _ _ rsp0.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by checkpoint_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, stk1, hstk1, ?hmem⟩
  case hmem =>
    rw [show k + 62 + 1 = k + 63 from rfl] at Hm1
    rw [show L.toBitVec + 40 = L.toBitVec + 8 + 32 by bv_omega]
    ecancel
  all_goals first
    | exact trivial
    | with_reducible rfl
    | (exact Encode.fast_path_len40 L (by omega))
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (apply UInt64.toBitVec_inj.mp; checkpoint_addr)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- Tail from `L_7b`, `len(Root) ≠ 32`: `(nil, ssz.ErrBytesLength)`; the epoch bytes are already in
`b[len..len+8]` (written before the root length test, in the current block). -/
theorem Encode.tail_rej (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (rsp0 r140 rbp0 ra L C e0 e1 rl : UInt64) (hrl : rl ≠ 32) (rcv b p : BitVec 64)
    (e8 pre d0 : List UInt8) (he8 : e8.length = 8) (hd0 : d0.length = 8) (R : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := rsp0.toBitVec - 112 })
    (hrbp : s.regs.rbp = { toBitVec := rsp0.toBitVec - 8#64 }) (hr14 : s.regs.r14 = r140)
    (hrax : s.regs.rax.toBitVec = rcv) (hrbx : s.regs.rbx.toBitVec = b) (hrcx : s.regs.rcx = L)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At rsp0.toBitVec)
      ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (rsp0.toBitVec - 8))
      ⋆ Eq (e8.At (rsp0.toBitVec - 64))
      ⋆ Eq ((Int.toBytes 8 p.toInt).At (rcv + 16)) ⋆ Eq ((Int.toBytes 8 rl.toBitVec.toInt).At (rcv + 24))
      ⋆ Eq (pre.At b) ⋆ Eq (d0.At (b + L.toBitVec))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrBytesLength_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrBytesLength" + 8).toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rcx = 0 ∧ st.data.regs.rdi = e0 ∧ st.data.regs.rsi = e1
        ∧ st.data.regs.rsp = rsp0 + 8 ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At rsp0.toBitVec)
          ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (rsp0.toBitVec - 8))
          ⋆ Eq (e8.At (rsp0.toBitVec - 64))
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (rcv + 16)) ⋆ Eq ((Int.toBytes 8 rl.toBitVec.toInt).At (rcv + 24))
          ⋆ Eq (pre.At b) ⋆ Eq (e8.At (b + L.toBitVec))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrBytesLength_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrBytesLength" + 8).toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 33)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp hrbp hr14 hrax hrbx hrcx h_mem hrl ⊢
  subst rsp rbp r14 rcx hrax hrbx
  have := rsp0.toNat_lt_size; simp only [UInt64.size] at *
  kat hk marshalSSZTo 33
  kat hk marshalSSZTo 34
  apply load_step_at _ _ (rsp0.toBitVec - 64) _ _ e8 _ _ (by checkpoint_addr) (by ecancel) (by exact he8)
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
  apply load_step_at _ _ (rsp0.toBitVec - 8) _ _ (Int.toBytes 8 rbp0.toBitVec.toInt) _ _ (by checkpoint_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 79
  apply load_step_at _ _ rsp0.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by checkpoint_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?hmem⟩
  case hmem => ecancel
  all_goals first
    | exact trivial
    | with_reducible rfl
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (apply UInt64.toBitVec_inj.mp; checkpoint_addr)

end Prysm.Checkpoint
