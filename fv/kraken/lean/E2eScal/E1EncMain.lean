import TestTarget.ListU64DecodeRejectCall
import Prysm.Checkpoint.EncodeFastPath
import E2eScal.E1Code
import Codec.StackGuard
import Codec.EncodeMemmove

/-!
# Real Prysm `(*v1alpha1.Eth1Data).MarshalSSZTo`, fast path, Go 1.26.10 machine code

    func (e *Eth1Data) MarshalSSZTo(buf []byte) (dst []byte, err error) {
        dst = buf
        if size := len(e.DepositRoot); size != 32 { return nil, ssz.ErrBytesLength }
        dst = append(dst, e.DepositRoot...)
        dst = ssz.MarshalUint64(dst, e.DepositCount)            // inlined
        if size := len(e.BlockHash); size != 32 { return nil, ssz.ErrBytesLength }
        dst = append(dst, e.BlockHash...)
        return }

**Fast path only**: `len(dst) + 72 ≤ cap(dst)` and both roots of length 32. The three `runtime.growslice`
branches (directives 16–28, 46–53, 63–72), the two length rejects (89–107) and the morestack path
(108–118) are not covered. Directive indices of `E2eScal.E1Code.E1Marshal`:

* `e1_enc_a` 0–36 + `runtime.memmove`: 2–4 stack guard (`lea -0x8(%rsp),%r12; cmp 0x10(%r14),%r12; jbe`,
  closed with `Codec.lea_cmp_be_false`, N = 8), 5–8 prologue (`add $-0x80,%rsp`, rbx spill to rsp + 16),
  9–11 `len(DepositRoot)`, 12 receiver spill to rsp + 8, 13–15 capacity (`jae` taken), 29–35 spills of the
  slice pointer (rsp − 24), the new length (rsp − 56) and the capacity (rsp − 48), 36 the call.
* `e1_enc_m` 37–80 + `runtime.memmove`: 37–45 reload, DepositCount load (receiver + 32), capacity (`jb` not
  taken), 54–55 the 8 bytes stored at `dst + len`, 56–58 `len(BlockHash)`, 59–62 capacity (`jae` taken),
  73–79 spills (pointer rsp − 16, new length `v + 40` rsp − 32, capacity rsp − 40), 80 the call.
* `e1_enc_e` 81–88: reload of the result slice, `xor`, `sub $-0x80,%rsp`, `pop %rbp`, `retq`.

Both calls (36, 80) are one application of the block `Codec.enc32_call` each; the straight-line steps
before them are stepped here (they differ per site). Receiver (gc amd64 layout, `prysm/ir/ir-mainnet.json`):
`state` 0, `DepositRoot` 8 (ptr, len, cap), `DepositCount` 32, `BlockHash` 40 (ptr, len, cap). `rsp` is the
entry rsp; the frame base is rsp − 136; the `memmove` return slot is rsp − 144.
-/

open Machine Runtime TestTarget E2eScal.E1Code
variable [Host]

open Codec
namespace E2eScal.E1

set_option maxRecDepth 100000 in
/-- Code fact of the block for the two call sites (directives 36, 80). -/
theorem e1_call_at (k : Nat) (hk : E1Marshal.IsInfixAt Host.prog k) :
    callMemmove.IsInfixAt Host.prog (k + 36) ∧ callMemmove.IsInfixAt Host.prog (k + 80) := by
  refine ⟨infix_sub 36 hk ?_, infix_sub 80 hk ?_⟩ <;>
    simp only [E1Marshal, callMemmove, List.drop_succ_cons, List.drop_zero, List.length_cons,
      List.length_nil, List.take_succ_cons, List.take_zero]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- DepositRoot segment: entry to the return of the first `memmove` (directive 37): stack guard passed, frame set
up, DepositRoot appended. -/
theorem e1_enc_a (k : Nat) (hk : E1Marshal.IsInfixAt Host.prog k) (hf : LabelsFresh E1Marshal k)
    (r1 d0 : List UInt8) (hr1 : r1.length = 32) (hd0 : d0.length = 32) (p1 : BitVec 64)
    (s : MachineData) (guard : UInt64)
    (fp s1 s2 l24 l48 l56 rslot scratch : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (hl24 : l24.length = 8)
    (hl48 : l48.length = 8) (hl56 : l56.length = 8) (hrs : rslot.length = 8)
    (S : Nat) (hsc : scratch.length = S) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24)) ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (l56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 144))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (r1.At p1) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec)) ⋆ R)
    (hguard : guard.toNat + 8 < s.regs.rsp.toNat) (hsp : 144 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 32 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hmm : MemmoveC S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 37)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 136 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8#64 } ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ scr : List UInt8, scr.length = S ∧
        (Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 32).toInt).At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 37)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (r1.At p1) ⋆ Eq (r1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hcap hcap63 ⊢
  have := rsp.toNat_lt_size; have := rcx.toNat_lt_size; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *
  kat hk E1Marshal 0
  kat hk E1Marshal 1
  kat hk E1Marshal 2
  kat hk E1Marshal 3
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk E1Marshal 4
  split
  case isTrue h =>
    exfalso
    rw [lea_cmp_be_false rsp.toBitVec _ guard.toBitVec _ _ 8 (by rfl) hguard] at h
    exact Bool.noConfusion h
  simp only [Effects.All]
  kat hk E1Marshal 5
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk E1Marshal 6
  kat hk E1Marshal 7
  kat hk E1Marshal 8
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by eaddr) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk E1Marshal 9
  apply load_step _ _ _ _ (Int.toBytes 8 p1.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk E1Marshal 10
  apply load_step _ _ _ _ (Int.toBytes 8 32) _ _ (by ecancel) (by rfl)
  simp only [show Int.ofBytes (Int.toBytes 8 32) = 32 by decide]
  kunfold
  kat hk E1Marshal 11
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk E1Marshal 12
  apply store_step_at _ _ (rsp.toBitVec + 8) _ _ _ s1 _ _ (by eaddr) (by ecancel) (by exact h1)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk E1Marshal 13
  kat hk E1Marshal 14
  kat hk E1Marshal 15
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf E1Marshal 29
  kat hk E1Marshal 29
  kat hk E1Marshal 30
  apply store_step_at _ _ (rsp.toBitVec - 24) _ _ _ l24 _ _ (by eaddr) (by ecancel) (by exact hl24)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  kat hk E1Marshal 31
  apply store_step_at _ _ (rsp.toBitVec - 56) _ _ _ l56 _ _ (by eaddr) (by ecancel) (by exact hl56)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  kat hk E1Marshal 32
  apply store_step_at _ _ (rsp.toBitVec - 48) _ _ _ l48 _ _ (by eaddr) (by ecancel) (by exact hl48)
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  kat hk E1Marshal 33
  kat hk E1Marshal 34
  kat hk E1Marshal 35
  rw [Prysm.Checkpoint.Encode.fast_path_mul]
  refine eventually_trans _ _ _ _ (enc32_call (k + 36) (e1_call_at k hk).1 (-128 + (rsp.toBitVec - 8#64))
    (rbx.toBitVec + rcx.toBitVec) p1 (rsp.toBitVec - 144) (rsp.toBitVec - 144 - BitVec.ofNat 64 S) S
    (by eaddr) (by first | (exact congrArg (· - BitVec.ofNat 64 S) (by eaddr)) | eaddr)
    r1 d0 rslot scratch hr1 hd0 hrs hsc _ _ (by rfl) (by first | rfl | exact BitVec.add_comm _ _ | eaddr)
    (by rfl) (by rfl) (by dsimp only; ecancel) hmm) ?_
  rintro ⟨e1', pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, stk1, hstk1, Hm1⟩
  dsimp only at hpc1 hrsp1 hr141 hrbp1 Hm1
  apply Eventually.done
  refine ⟨hpc1, ?grsp, hrbp1, hr141, stk1, hstk1, ?hmem⟩
  case grsp => exact hrsp1.trans (congrArg UInt64.ofBitVec (by eaddr))
  case hmem =>
    rw [show k + 36 + 1 = k + 37 from rfl] at Hm1
    first | ecancel | (simp only [Std.ExtHashMap.sep_emp] at Hm1; ecancel)

/-- Address of `mov %rsi,-0x8(%rbx,%rax,1)` with rbx = 8 + v, rax = dst. -/
theorem e1m_dc (x y : BitVec 64) : 8 + x + y + -8 = y + x := by bv_omega
theorem e1m_d2 (x y : BitVec 64) : 8 + x + y = y + x + 8 := by bv_omega
theorem e1m_n40 (x : BitVec 64) : 8 + x + 32 = x + 40 := by bv_omega

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- DepositCount and BlockHash segment: directive 37 to the return of the second `memmove` (directive 81): DepositCount stored at
`dst + v`, BlockHash appended at `dst + v + 8`. `v` is the length after DepositRoot. -/
theorem e1_enc_m (k : Nat) (hk : E1Marshal.IsInfixAt Host.prog k) (hf : LabelsFresh E1Marshal k)
    (dc r2 d1 d2 : List UInt8) (hdc : dc.length = 8) (hr2 : r2.length = 32) (hd1 : d1.length = 8)
    (hd2 : d2.length = 32)
    (s : MachineData) (rsp : UInt64) (recv dst v cap p2 : BitVec 64)
    (l16 l32 l40 rslot scratch : List UInt8) (hl16 : l16.length = 8) (hl32 : l32.length = 8)
    (hl40 : l40.length = 8) (hrs : rslot.length = 8)
    (S : Nat) (hsc : scratch.length = S) (R : DataMem → Prop)
    (hrsp : s.regs.rsp = { toBitVec := rsp.toBitVec - 136 })
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 recv.toInt).At (rsp.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 dst.toInt).At (rsp.toBitVec - 24))
      ⋆ Eq ((Int.toBytes 8 cap.toInt).At (rsp.toBitVec - 48))
      ⋆ Eq ((Int.toBytes 8 v.toInt).At (rsp.toBitVec - 56))
      ⋆ Eq (l16.At (rsp.toBitVec - 16)) ⋆ Eq (l32.At (rsp.toBitVec - 32)) ⋆ Eq (l40.At (rsp.toBitVec - 40))
      ⋆ Eq (rslot.At (rsp.toBitVec - 144)) ⋆ Eq (scratch.At (rsp.toBitVec - 144 - BitVec.ofNat 64 S))
      ⋆ Eq (dc.At (recv + 32)) ⋆ Eq ((Int.toBytes 8 p2.toInt).At (recv + 40))
      ⋆ Eq ((Int.toBytes 8 32).At (recv + 48))
      ⋆ Eq (r2.At p2) ⋆ Eq (d1.At (dst + v)) ⋆ Eq (d2.At (dst + v + 8)) ⋆ R)
    (hcap : v.toNat + 40 ≤ cap.toNat) (hcap63 : cap.toNat < 2 ^ 63) (hmm : MemmoveC S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 81) ∧ st.data.regs.rsp = s.regs.rsp ∧ st.data.regs.rbp = s.regs.rbp
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ scr : List UInt8, scr.length = S ∧
        (Eq ((Int.toBytes 8 recv.toInt).At (rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 dst.toInt).At (rsp.toBitVec - 24))
          ⋆ Eq ((Int.toBytes 8 cap.toInt).At (rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 v.toInt).At (rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 dst.toInt).At (rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (v + 40).toInt).At (rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 cap.toInt).At (rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 81)).toBitVec.toInt).At (rsp.toBitVec - 144))
          ⋆ Eq (scr.At (rsp.toBitVec - 144 - BitVec.ofNat 64 S))
          ⋆ Eq (dc.At (recv + 32)) ⋆ Eq ((Int.toBytes 8 p2.toInt).At (recv + 40))
          ⋆ Eq ((Int.toBytes 8 32).At (recv + 48))
          ⋆ Eq (r2.At p2) ⋆ Eq (dc.At (dst + v)) ⋆ Eq (r2.At (dst + v + 8)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 37)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rspc, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp h_mem ⊢
  subst hrsp
  have := v.isLt; have := cap.isLt
  kat hk E1Marshal 37
  apply load_step_at _ _ (rsp.toBitVec - 56) _ _ (Int.toBytes 8 v.toInt) _ _ (by eaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk E1Marshal 38
  kat hk E1Marshal 39
  apply load_step_at _ _ (rsp.toBitVec + 8) _ _ (Int.toBytes 8 recv.toInt) _ _ (by eaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk E1Marshal 40
  apply load_step_at _ _ (recv + 32) _ _ dc _ _ (by eaddr) (by ecancel) (by exact hdc)
  kunfold
  kat hk E1Marshal 41
  apply load_step_at _ _ (rsp.toBitVec - 48) _ _ (Int.toBytes 8 cap.toInt) _ _ (by eaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk E1Marshal 42
  kat hk E1Marshal 43
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  kat hk E1Marshal 44
  apply load_step_at _ _ (rsp.toBitVec - 24) _ _ (Int.toBytes 8 dst.toInt) _ _ (by eaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk E1Marshal 45
  klabel hk hf E1Marshal 54
  kat hk E1Marshal 54
  kat hk E1Marshal 55
  rw [Prysm.Checkpoint.Encode.fast_path_mul, e1m_dc]
  apply store_step _ _ _ _ _ d1 _ _ (by ecancel) (by exact hd1)
  intro m1 H1
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl dc hdc] at H1
  kunfold
  kat hk E1Marshal 56
  apply load_step_at _ _ (recv + 40) _ _ (Int.toBytes 8 p2.toInt) _ _ (by eaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk E1Marshal 57
  apply load_step_at _ _ (recv + 48) _ _ (Int.toBytes 8 32) _ _ (by eaddr) (by ecancel) (by rfl)
  simp only [show Int.ofBytes (Int.toBytes 8 32) = 32 by decide]
  kunfold
  kat hk E1Marshal 58
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk E1Marshal 59
  kat hk E1Marshal 60
  kat hk E1Marshal 61
  kat hk E1Marshal 62
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf E1Marshal 73
  kat hk E1Marshal 73
  kat hk E1Marshal 74
  apply store_step_at _ _ (rsp.toBitVec - 16) _ _ _ l16 _ _ (by eaddr) (by ecancel) (by exact hl16)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk E1Marshal 75
  apply store_step_at _ _ (rsp.toBitVec - 32) _ _ _ l32 _ _ (by eaddr) (by ecancel) (by exact hl32)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk E1Marshal 76
  apply store_step_at _ _ (rsp.toBitVec - 40) _ _ _ l40 _ _ (by eaddr) (by ecancel) (by exact hl40)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  kat hk E1Marshal 77
  kat hk E1Marshal 78
  kat hk E1Marshal 79
  refine eventually_trans _ _ _ _ (enc32_call (k + 80) (e1_call_at k hk).2 (rsp.toBitVec - 136)
    (dst + v + 8) p2 (rsp.toBitVec - 144) (rsp.toBitVec - 144 - BitVec.ofNat 64 S) S
    (by eaddr) (by first | (exact congrArg (· - BitVec.ofNat 64 S) (by eaddr)) | eaddr)
    r2 d2 rslot scratch hr2 hd2 hrs hsc _ _ (by rfl)
    (by first | rfl | exact BitVec.add_comm _ _ | exact e1m_d2 _ _ | eaddr)
    (by rfl) (by rfl) (by dsimp only; ecancel) hmm) ?_
  rintro ⟨e1', pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, stk1, hstk1, Hm1⟩
  dsimp only at hpc1 hrsp1 hr141 hrbp1 Hm1
  apply Eventually.done
  refine ⟨hpc1, hrsp1, hrbp1, hr141, stk1, hstk1, ?hmem⟩
  case hmem =>
    rw [show k + 80 + 1 = k + 81 from rfl, e1m_n40 v] at Hm1
    first | ecancel | (simp only [Std.ExtHashMap.sep_emp] at Hm1; ecancel)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Return segment: directive 81 to the return (`retq`, directive 88). Memory unchanged. -/
theorem e1_enc_e (k : Nat) (hk : E1Marshal.IsInfixAt Host.prog k)
    (s : MachineData) (rsp ra rbp0 : UInt64) (dst v cap : BitVec 64) (R : DataMem → Prop)
    (hrsp : s.regs.rsp = { toBitVec := rsp.toBitVec - 136 })
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At rsp.toBitVec)
      ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (rsp.toBitVec - 8))
      ⋆ Eq ((Int.toBytes 8 dst.toInt).At (rsp.toBitVec - 16))
      ⋆ Eq ((Int.toBytes 8 v.toInt).At (rsp.toBitVec - 32))
      ⋆ Eq ((Int.toBytes 8 cap.toInt).At (rsp.toBitVec - 40)) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = { toBitVec := dst }
        ∧ st.data.regs.rbx = { toBitVec := v } ∧ st.data.regs.rcx = { toBitVec := cap }
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = rsp + 8 ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = s.regs.r14 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 dst.toInt).At (rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 v.toInt).At (rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 cap.toInt).At (rsp.toBitVec - 40)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 81)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rspc, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp h_mem ⊢
  subst hrsp
  have hrl := rsp.toNat_lt_size
  simp only [UInt64.size] at hrl
  kat hk E1Marshal 81
  apply load_step_at _ _ (rsp.toBitVec - 16) _ _ (Int.toBytes 8 dst.toInt) _ _ (by eaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk E1Marshal 82
  apply load_step_at _ _ (rsp.toBitVec - 32) _ _ (Int.toBytes 8 v.toInt) _ _ (by eaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk E1Marshal 83
  apply load_step_at _ _ (rsp.toBitVec - 40) _ _ (Int.toBytes 8 cap.toInt) _ _ (by eaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk E1Marshal 84
  intro _
  kat hk E1Marshal 85
  intro _
  kat hk E1Marshal 86
  kat hk E1Marshal 87
  apply load_step_at _ _ (rsp.toBitVec - 8) _ _ (Int.toBytes 8 rbp0.toBitVec.toInt) _ _ (by eaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk E1Marshal 88
  apply load_step_at _ _ rsp.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by eaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h_mem⟩
  all_goals first
    | exact trivial
    | with_reducible rfl
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (apply UInt64.toBitVec_inj.mp; eaddr)

theorem e1m_o32 (x y : BitVec 64) : x + y + 32 = x + (y + 32) := by bv_omega
theorem e1m_o40 (x y : BitVec 64) : x + y + 40 = x + (y + 32) + 8 := by bv_omega
theorem e1m_v72 (y : BitVec 64) : y + 72 = y + 32 + 40 := by bv_omega

theorem e1m_cap (a b : BitVec 64) (h : a.toNat + 72 ≤ b.toNat) : (a + 32).toNat + 40 ≤ b.toNat := by
  bv_omega

theorem e1m_len72 (x : UInt64) (h : x.toNat + 72 < 2 ^ 64) :
    ({ toBitVec := x.toBitVec + 32 + 40 } : UInt64).toNat = x.toNat + 72 := by
  have h' : x.toBitVec.toNat + 72 < 2 ^ 64 := h
  show (x.toBitVec + 32 + 40).toNat = x.toBitVec.toNat + 72
  bv_omega

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Fast path of the real `(*v1alpha1.Eth1Data).MarshalSSZTo` (Go 1.26.10)**: with
`len(dst) + 72 ≤ cap(dst)` and both roots of length 32 it returns `(dst, len + 72, cap, nil)` and the 72
bytes after the prefix are DepositRoot ‖ DepositCount ‖ BlockHash; the receiver, the roots, the prefix,
the caller's frame `R` and the stack guard are unchanged. Fast path only. -/
theorem e1_e2e_marshal_main (k : Nat) (hk : E1Marshal.IsInfixAt Host.prog k) (hf : LabelsFresh E1Marshal k)
    (ast dc c1 c2 r1 r2 pre d0 d1 d2 : List UInt8)
    (hast : ast.length = 8) (hdc : dc.length = 8) (hc1 : c1.length = 8) (hc2 : c2.length = 8)
    (hr1 : r1.length = 32) (hr2 : r2.length = 32)
    (hd0 : d0.length = 32) (hd1 : d1.length = 8) (hd2 : d2.length = 32)
    (p1 p2 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l24 l32 l40 l48 l56 rslot : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (hl16 : l16.length = 8)
    (hl24 : l24.length = 8) (hl32 : l32.length = 8) (hl40 : l40.length = 8) (hl48 : l48.length = 8)
    (hl56 : l56.length = 8) (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16)) ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32)) ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (l56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 144)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16)) ⋆ Eq (c1.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (dc.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 40))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 48)) ⋆ Eq (c2.At (s.regs.rax.toBitVec + 56))
      ⋆ Eq (r1.At p1) ⋆ Eq (r2.At p2)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 32))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 40)) ⋆ R)
    (hguard : guard.toNat + 8 < s.regs.rsp.toNat) (hsp : 144 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 72 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hmm : MemmoveC S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 72 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ scr : List UInt8, scr.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 72).toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 32).toInt).At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 81)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16)) ⋆ Eq (c1.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (dc.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 48)) ⋆ Eq (c2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (r1.At p1) ⋆ Eq (r2.At p2)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (r1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (dc.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 32))
          ⋆ Eq (r2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 40)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  have hC := s.regs.rdi.toNat_lt_size
  simp only [UInt64.size] at hC
  have hcM := e1m_cap s.regs.rcx.toBitVec s.regs.rdi.toBitVec hcap
  have hc63 : s.regs.rdi.toBitVec.toNat < 2 ^ 63 := hcap63
  rw [e1m_o32 s.regs.rbx.toBitVec s.regs.rcx.toBitVec, e1m_o40 s.regs.rbx.toBitVec s.regs.rcx.toBitVec] at h_mem
  -- DepositRoot segment, directives 0–36, memmove
  refine eventually_trans _ _ _ _ (e1_enc_a k hk hf r1 d0 hr1 hd0 p1 s guard fp s1 s2 l24 l48 l56 rslot scratch
    hfp h1 h2 hl24 hl48 hl56 hrs S hsc _ (by ecancel) hguard hsp (by omega) hcap63 hmm) ?_
  rintro ⟨e1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, scr1, hscr1, Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 Hm1
  subst hpc1
  -- DepositCount and BlockHash segment, directives 37–80, memmove
  refine eventually_trans _ _ _ _ (e1_enc_m k hk hf dc r2 d1 d2 hdc hr2 hd1 hd2 e1 s.regs.rsp
    s.regs.rax.toBitVec s.regs.rbx.toBitVec (s.regs.rcx.toBitVec + 32) s.regs.rdi.toBitVec p2
    l16 l32 l40 (Int.toBytes 8 (Host.addrOf (k + 37)).toBitVec.toInt) scr1 hl16 hl32 hl40
    (Int.toBytes_length 8 _) S hscr1 _ hrsp1 (by ecancel) hcM hc63 hmm) ?_
  rintro ⟨e2, pc2⟩ ⟨hpc2, hrsp2, hrbp2, hr142, scr2, hscr2, Hm2⟩
  dsimp only at hpc2 hrsp2 hrbp2 hr142 Hm2
  subst hpc2
  -- Return segment, directives 81–88
  refine eventually_trans _ _ _ _ (e1_enc_e k hk e2 s.regs.rsp ra s.regs.rbp s.regs.rbx.toBitVec
    (s.regs.rcx.toBitVec + 32 + 40) s.regs.rdi.toBitVec _ (hrsp2.trans hrsp1) (by ecancel)) ?_
  rintro ⟨e3, pc3⟩ ⟨hpc3, hrax3, hrbx3, hrcx3, hrdi3, hrsi3, hrsp3, hrbp3, hr143, Hm3⟩
  dsimp only at hpc3 hrax3 hrbx3 hrcx3 hrdi3 hrsi3 hrsp3 hrbp3 hr143 Hm3
  apply Eventually.done
  refine ⟨hpc3, hrax3, ?grbx, hrcx3, hrdi3, hrsi3, hrsp3, hrbp3, ?gr14, scr2, hscr2, ?hmem⟩
  case grbx => exact (congrArg UInt64.toNat hrbx3).trans (e1m_len72 s.regs.rcx (by omega))
  case gr14 => exact hr143.trans (hr142.trans hr141)
  case hmem =>
    rw [e1m_o32 s.regs.rbx.toBitVec s.regs.rcx.toBitVec, e1m_o40 s.regs.rbx.toBitVec s.regs.rcx.toBitVec,
      e1m_v72 s.regs.rcx.toBitVec]
    first | ecancel | (simp only [Std.ExtHashMap.sep_emp] at Hm3; ecancel)

end E2eScal.E1
