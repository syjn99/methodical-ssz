import Prysm.BeaconBlockHeader.EncodeRootFields
import Codec.EncodeMemmove

/-!
# The three root blocks of `BeaconBlockHeader.MarshalSSZTo` through `Codec.encode32_memmove_call`

`Encode.encode_parent_root_via_block`, `Encode.encode_state_root_via_block`, `Encode.encode_body_root_via_block` have the statements of `Encode.encode_parent_root`,
`Encode.encode_state_root`, `Encode.encode_body_root` (`Prysm/BeaconBlockHeader/EncodeRootFields.lean`, unchanged); the `example`s after each theorem check
that the two types are the same term (`rfl`). In each proof the straight-line steps before the call are
the text of the hand proof (they differ per site); the call, the return and the frame are one
application of the block `encode32_memmove_call`. Fast path only.
-/

open Machine Runtime Prysm.BeaconBlockHeader.Code
variable [Host]

open Codec
namespace Prysm.BeaconBlockHeader

set_option maxRecDepth 100000 in
/-- Code fact of the block for the three call sites (directives 89, 117, 147). -/
theorem Encode.call_at (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) :
    callMemmove.IsInfixAt Host.prog (k + 89) ∧ callMemmove.IsInfixAt Host.prog (k + 117)
      ∧ callMemmove.IsInfixAt Host.prog (k + 147) := by
  refine ⟨infix_sub 89 hk ?_, infix_sub 117 hk ?_, infix_sub 147 hk ?_⟩ <;>
    simp only [marshalSSZTo, callMemmove, List.drop_succ_cons, List.drop_zero, List.length_cons,
      List.length_nil, List.take_succ_cons, List.take_zero]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- (through `encode32_memmove_call`) ParentRoot segment: directive 62 to the return of the first `memmove` (directive 90): ParentRoot appended. -/
theorem Encode.encode_parent_root_via_block (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (r1 e1 : List UInt8) (hr1 : r1.length = 32) (he1 : e1.length = 32)
    (s : MachineData) (rsp : UInt64) (recv dst v cap p1 : BitVec 64)
    (l16 l96 l104 rslot scratch : List UInt8)
    (hl16 : l16.length = 8) (hl96 : l96.length = 8) (hl104 : l104.length = 8) (hrs : rslot.length = 8)
    (S : Nat) (hsc : scratch.length = S) (R : DataMem → Prop)
    (hrsp : s.regs.rsp = { toBitVec := rsp.toBitVec - 8#64 - 152 })
    (hrax : s.regs.rax = { toBitVec := recv }) (hrbx : s.regs.rbx = { toBitVec := dst })
    (hr8 : s.regs.r8 = { toBitVec := v }) (hrdi : s.regs.rdi = { toBitVec := cap })
    (h_mem : s.dmem =⋆ Eq (l16.At (rsp.toBitVec - 16)) ⋆ Eq (l96.At (rsp.toBitVec - 96))
      ⋆ Eq (l104.At (rsp.toBitVec - 104))
      ⋆ Eq (rslot.At (rsp.toBitVec - 168)) ⋆ Eq (scratch.At (rsp.toBitVec - 168 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 p1.toInt).At (recv + 24)) ⋆ Eq ((Int.toBytes 8 32).At (recv + 32))
      ⋆ Eq (r1.At p1) ⋆ Eq (e1.At (dst + v)) ⋆ R)
    (hcap : v.toNat + 32 ≤ cap.toNat) (hcap63 : cap.toNat < 2 ^ 63) (hmm : MemmoveContract S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 90) ∧ st.data.regs.rsp = s.regs.rsp ∧ st.data.regs.rbp = s.regs.rbp
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ scr : List UInt8, scr.length = S ∧
        (Eq ((Int.toBytes 8 dst.toInt).At (rsp.toBitVec - 16)) ⋆ Eq ((Int.toBytes 8 (v + 32).toInt).At (rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 cap.toInt).At (rsp.toBitVec - 104))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 90)).toBitVec.toInt).At (rsp.toBitVec - 168))
          ⋆ Eq (scr.At (rsp.toBitVec - 168 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (recv + 24)) ⋆ Eq ((Int.toBytes 8 32).At (recv + 32))
          ⋆ Eq (r1.At p1) ⋆ Eq (r1.At (dst + v)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 62)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rspc, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp hrax hrbx hr8 hrdi h_mem ⊢
  subst hrsp hrax hrbx hr8 hrdi
  have := v.isLt; have := cap.isLt
  step_directive hk marshalSSZTo 62
  apply load_step_at _ _ (recv + 24) _ _ (Int.toBytes 8 p1.toInt) _ _ (by checkpoint_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk marshalSSZTo 63
  apply load_step_at _ _ (recv + 32) _ _ (Int.toBytes 8 32) _ _ (by checkpoint_addr) (by ecancel) (by rfl)
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
  label_address hk hf marshalSSZTo 82
  step_directive hk marshalSSZTo 82
  step_directive hk marshalSSZTo 83
  apply store_step_at _ _ (rsp.toBitVec - 16) _ _ _ l16 _ _ (by checkpoint_addr) (by ecancel) (by exact hl16)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  unfold_step
  step_directive hk marshalSSZTo 84
  apply store_step_at _ _ (rsp.toBitVec - 96) _ _ _ l96 _ _ (by checkpoint_addr) (by ecancel) (by exact hl96)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  unfold_step
  step_directive hk marshalSSZTo 85
  apply store_step_at _ _ (rsp.toBitVec - 104) _ _ _ l104 _ _ (by checkpoint_addr) (by ecancel) (by exact hl104)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  unfold_step
  step_directive hk marshalSSZTo 86
  step_directive hk marshalSSZTo 87
  step_directive hk marshalSSZTo 88
  rw [Codec.add_mul_one]
  refine eventually_trans _ _ _ _ (encode32_memmove_call (k + 89) (Encode.call_at k hk).1 (rsp.toBitVec - 8#64 - 152) (dst + v) p1
    (rsp.toBitVec - 168) (rsp.toBitVec - 168 - BitVec.ofNat 64 S) S (Encode.slot _)
    (congrArg (· - BitVec.ofNat 64 S) (Encode.slot _)) r1 e1 rslot scratch hr1 he1 hrs hsc _ _
    (by rfl) (by first | rfl | exact BitVec.add_comm _ _) (by rfl) (by rfl) (by dsimp only; ecancel) hmm) ?_
  rintro ⟨e1', pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, stk1, hstk1, Hm1⟩
  dsimp only at hpc1 hrsp1 hr141 hrbp1 Hm1
  apply Eventually.done
  refine ⟨hpc1, hrsp1, hrbp1, hr141, stk1, hstk1, ?hmem⟩
  case hmem =>
    rw [show k + 89 + 1 = k + 90 from rfl] at Hm1
    first | ecancel | (simp only [Std.ExtHashMap.sep_emp] at Hm1; ecancel)

example : type_of% @Encode.encode_parent_root_via_block = type_of% @Encode.encode_parent_root := rfl


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- (through `encode32_memmove_call`) StateRoot segment: directive 90 to the return of the second `memmove` (directive 118): StateRoot appended. On entry the length is at rsp − 96 and the capacity at rsp − 104; on exit they are swapped. -/
theorem Encode.encode_state_root_via_block (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (rr ee : List UInt8) (hrr : rr.length = 32) (hee : ee.length = 32)
    (s : MachineData) (rsp : UInt64) (recv dst v cap p2 : BitVec 64)
    (rslot scratch : List UInt8) (hrs : rslot.length = 8)
    (S : Nat) (hsc : scratch.length = S) (R : DataMem → Prop)
    (hrsp : s.regs.rsp = { toBitVec := rsp.toBitVec - 8#64 - 152 })
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 recv.toInt).At (rsp.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 dst.toInt).At (rsp.toBitVec - 16))
      ⋆ Eq ((Int.toBytes 8 v.toInt).At (rsp.toBitVec - 96))
      ⋆ Eq ((Int.toBytes 8 cap.toInt).At (rsp.toBitVec - 104))
      ⋆ Eq (rslot.At (rsp.toBitVec - 168)) ⋆ Eq (scratch.At (rsp.toBitVec - 168 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 p2.toInt).At (recv + 48)) ⋆ Eq ((Int.toBytes 8 32).At (recv + 56))
      ⋆ Eq (rr.At p2) ⋆ Eq (ee.At (dst + v)) ⋆ R)
    (hcap : v.toNat + 32 ≤ cap.toNat) (hcap63 : cap.toNat < 2 ^ 63) (hmm : MemmoveContract S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 118) ∧ st.data.regs.rsp = s.regs.rsp ∧ st.data.regs.rbp = s.regs.rbp
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ scr : List UInt8, scr.length = S ∧
        (Eq ((Int.toBytes 8 recv.toInt).At (rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 dst.toInt).At (rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 cap.toInt).At (rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 (v + 32).toInt).At (rsp.toBitVec - 104))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 118)).toBitVec.toInt).At (rsp.toBitVec - 168))
          ⋆ Eq (scr.At (rsp.toBitVec - 168 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (recv + 48)) ⋆ Eq ((Int.toBytes 8 32).At (recv + 56))
          ⋆ Eq (rr.At p2) ⋆ Eq (rr.At (dst + v)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 90)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rspc, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp h_mem ⊢
  subst hrsp
  have := v.isLt; have := cap.isLt
  step_directive hk marshalSSZTo 90
  apply load_step_at _ _ (rsp.toBitVec + 8) _ _ (Int.toBytes 8 recv.toInt) _ _ (by checkpoint_addr) (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk marshalSSZTo 91
  apply load_step_at _ _ (recv + 48) _ _ (Int.toBytes 8 p2.toInt) _ _ (by checkpoint_addr) (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk marshalSSZTo 92
  apply load_step_at _ _ (recv + 56) _ _ (Int.toBytes 8 32) _ _ (by checkpoint_addr) (by ecancel) (by rfl)
  simp only [show Int.ofBytes (Int.toBytes 8 32) = 32 by decide]
  unfold_step
  step_directive hk marshalSSZTo 93
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  step_directive hk marshalSSZTo 94
  apply load_step_at _ _ (rsp.toBitVec - 96) _ _ (Int.toBytes 8 v.toInt) _ _ (by checkpoint_addr) (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk marshalSSZTo 95
  step_directive hk marshalSSZTo 96
  apply load_step_at _ _ (rsp.toBitVec - 104) _ _ (Int.toBytes 8 cap.toInt) _ _ (by checkpoint_addr) (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk marshalSSZTo 97
  step_directive hk marshalSSZTo 98
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  step_directive hk marshalSSZTo 99
  apply load_step_at _ _ (rsp.toBitVec - 16) _ _ (Int.toBytes 8 dst.toInt) _ _ (by checkpoint_addr) (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk marshalSSZTo 100
  label_address hk hf marshalSSZTo 111
  step_directive hk marshalSSZTo 111
  step_directive hk marshalSSZTo 112
  apply store_step_at _ _ (rsp.toBitVec - 96) _ _ _ (Int.toBytes 8 v.toInt) _ _ (by checkpoint_addr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro h1 H1
  simp only [Width.bytes, Width.bits] at H1
  unfold_step
  step_directive hk marshalSSZTo 113
  apply store_step_at _ _ (rsp.toBitVec - 104) _ _ _ (Int.toBytes 8 cap.toInt) _ _ (by checkpoint_addr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro h2 H2
  simp only [Width.bytes, Width.bits] at H2
  unfold_step
  step_directive hk marshalSSZTo 114
  apply store_step_at _ _ (rsp.toBitVec - 16) _ _ _ (Int.toBytes 8 dst.toInt) _ _ (by checkpoint_addr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro h3 H3
  simp only [Width.bytes, Width.bits] at H3
  unfold_step
  step_directive hk marshalSSZTo 115
  step_directive hk marshalSSZTo 116
  try rw [BitVec.add_comm v dst]
  refine eventually_trans _ _ _ _ (encode32_memmove_call (k + 117) (Encode.call_at k hk).2.1 (rsp.toBitVec - 8#64 - 152) (dst + v) p2
    (rsp.toBitVec - 168) (rsp.toBitVec - 168 - BitVec.ofNat 64 S) S (Encode.slot _)
    (congrArg (· - BitVec.ofNat 64 S) (Encode.slot _)) rr ee rslot scratch hrr hee hrs hsc _ _
    (by rfl) (by first | rfl | exact BitVec.add_comm _ _) (by rfl) (by rfl) (by dsimp only; ecancel) hmm) ?_
  rintro ⟨e1', pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, stk1, hstk1, Hm1⟩
  dsimp only at hpc1 hrsp1 hr141 hrbp1 Hm1
  apply Eventually.done
  refine ⟨hpc1, hrsp1, hrbp1, hr141, stk1, hstk1, ?hmem⟩
  case hmem =>
    rw [show k + 117 + 1 = k + 118 from rfl] at Hm1
    first | ecancel | (simp only [Std.ExtHashMap.sep_emp] at Hm1; ecancel)

example : type_of% @Encode.encode_state_root_via_block = type_of% @Encode.encode_state_root := rfl


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- (through `encode32_memmove_call`) BodyRoot segment: directive 118 to the return of the third `memmove` (directive 148): BodyRoot appended. On entry the length is at rsp − 104 and the capacity at rsp − 96; they stay there. -/
theorem Encode.encode_body_root_via_block (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (rr ee : List UInt8) (hrr : rr.length = 32) (hee : ee.length = 32)
    (s : MachineData) (rsp : UInt64) (recv dst v cap p3 : BitVec 64)
    (rslot scratch : List UInt8) (hrs : rslot.length = 8)
    (S : Nat) (hsc : scratch.length = S) (R : DataMem → Prop)
    (hrsp : s.regs.rsp = { toBitVec := rsp.toBitVec - 8#64 - 152 })
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 recv.toInt).At (rsp.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 dst.toInt).At (rsp.toBitVec - 16))
      ⋆ Eq ((Int.toBytes 8 cap.toInt).At (rsp.toBitVec - 96))
      ⋆ Eq ((Int.toBytes 8 v.toInt).At (rsp.toBitVec - 104))
      ⋆ Eq (rslot.At (rsp.toBitVec - 168)) ⋆ Eq (scratch.At (rsp.toBitVec - 168 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 p3.toInt).At (recv + 72)) ⋆ Eq ((Int.toBytes 8 32).At (recv + 80))
      ⋆ Eq (rr.At p3) ⋆ Eq (ee.At (dst + v)) ⋆ R)
    (hcap : v.toNat + 32 ≤ cap.toNat) (hcap63 : cap.toNat < 2 ^ 63) (hmm : MemmoveContract S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 148) ∧ st.data.regs.rsp = s.regs.rsp ∧ st.data.regs.rbp = s.regs.rbp
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ scr : List UInt8, scr.length = S ∧
        (Eq ((Int.toBytes 8 recv.toInt).At (rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 dst.toInt).At (rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 cap.toInt).At (rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 (v + 32).toInt).At (rsp.toBitVec - 104))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 148)).toBitVec.toInt).At (rsp.toBitVec - 168))
          ⋆ Eq (scr.At (rsp.toBitVec - 168 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (recv + 72)) ⋆ Eq ((Int.toBytes 8 32).At (recv + 80))
          ⋆ Eq (rr.At p3) ⋆ Eq (rr.At (dst + v)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 118)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rspc, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp h_mem ⊢
  subst hrsp
  have := v.isLt; have := cap.isLt
  step_directive hk marshalSSZTo 118
  apply load_step_at _ _ (rsp.toBitVec + 8) _ _ (Int.toBytes 8 recv.toInt) _ _ (by checkpoint_addr) (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk marshalSSZTo 119
  apply load_step_at _ _ (recv + 72) _ _ (Int.toBytes 8 p3.toInt) _ _ (by checkpoint_addr) (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk marshalSSZTo 120
  apply load_step_at _ _ (recv + 80) _ _ (Int.toBytes 8 32) _ _ (by checkpoint_addr) (by ecancel) (by rfl)
  simp only [show Int.ofBytes (Int.toBytes 8 32) = 32 by decide]
  unfold_step
  step_directive hk marshalSSZTo 121
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  step_directive hk marshalSSZTo 122
  apply load_step_at _ _ (rsp.toBitVec - 104) _ _ (Int.toBytes 8 v.toInt) _ _ (by checkpoint_addr) (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk marshalSSZTo 123
  step_directive hk marshalSSZTo 124
  apply load_step_at _ _ (rsp.toBitVec - 96) _ _ (Int.toBytes 8 cap.toInt) _ _ (by checkpoint_addr) (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk marshalSSZTo 125
  step_directive hk marshalSSZTo 126
  step_directive hk marshalSSZTo 127
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  step_directive hk marshalSSZTo 128
  apply load_step_at _ _ (rsp.toBitVec - 16) _ _ (Int.toBytes 8 dst.toInt) _ _ (by checkpoint_addr) (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk marshalSSZTo 129
  label_address hk hf marshalSSZTo 140
  step_directive hk marshalSSZTo 140
  step_directive hk marshalSSZTo 141
  apply store_step_at _ _ (rsp.toBitVec - 96) _ _ _ (Int.toBytes 8 cap.toInt) _ _ (by checkpoint_addr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro h1 H1
  simp only [Width.bytes, Width.bits] at H1
  unfold_step
  step_directive hk marshalSSZTo 142
  apply store_step_at _ _ (rsp.toBitVec - 104) _ _ _ (Int.toBytes 8 v.toInt) _ _ (by checkpoint_addr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro h2 H2
  simp only [Width.bytes, Width.bits] at H2
  unfold_step
  step_directive hk marshalSSZTo 143
  apply store_step_at _ _ (rsp.toBitVec - 16) _ _ _ (Int.toBytes 8 dst.toInt) _ _ (by checkpoint_addr) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro h3 H3
  simp only [Width.bytes, Width.bits] at H3
  unfold_step
  step_directive hk marshalSSZTo 144
  step_directive hk marshalSSZTo 145
  step_directive hk marshalSSZTo 146
  try rw [BitVec.add_comm v dst]
  refine eventually_trans _ _ _ _ (encode32_memmove_call (k + 147) (Encode.call_at k hk).2.2 (rsp.toBitVec - 8#64 - 152) (dst + v) p3
    (rsp.toBitVec - 168) (rsp.toBitVec - 168 - BitVec.ofNat 64 S) S (Encode.slot _)
    (congrArg (· - BitVec.ofNat 64 S) (Encode.slot _)) rr ee rslot scratch hrr hee hrs hsc _ _
    (by rfl) (by first | rfl | exact BitVec.add_comm _ _) (by rfl) (by rfl) (by dsimp only; ecancel) hmm) ?_
  rintro ⟨e1', pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, stk1, hstk1, Hm1⟩
  dsimp only at hpc1 hrsp1 hr141 hrbp1 Hm1
  apply Eventually.done
  refine ⟨hpc1, hrsp1, hrbp1, hr141, stk1, hstk1, ?hmem⟩
  case hmem =>
    rw [show k + 147 + 1 = k + 148 from rfl] at Hm1
    first | ecancel | (simp only [Std.ExtHashMap.sep_emp] at Hm1; ecancel)

example : type_of% @Encode.encode_body_root_via_block = type_of% @Encode.encode_body_root := rfl


end Prysm.BeaconBlockHeader
