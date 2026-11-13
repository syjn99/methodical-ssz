import Runtime.Contracts
import Machine.Step
import Machine.Labels
import Codec.StackGuard
import Prysm.DataColumnsByRootIdentifier.StatementsEncode
import Prysm.DataColumnsByRootIdentifier.EncodeTail

/-!
# `(*v1alpha1.DataColumnsByRootIdentifier).MarshalSSZTo`: fast path (capacity sufficient)

`Encode.fast_path : Encode.fast_path_statement`. Directives 2–4 large-frame guard `lea -0x8(%rsp),%r12` (closed with
`Codec.lea_cmp_be_false`, N = 8), 5–7 prologue (`push %rbp`, `add $-0x80`), 8 rbx spill to x + 16, 9 BlockRoot
pointer, 10–11 `cmpq $0x20,0x10(%rax); jne` not taken, 12 rax spill to x + 8, 13–15 `len + 32 ≤ cap`: `jae L_7c`
taken, then `Encode.tail_fit` (directive 29 to the return).
-/

open Machine Runtime Prysm.DataColumnsByRootIdentifier.Code
variable [Host]

namespace Prysm.DataColumnsByRootIdentifier

theorem Encode.fast_path : Encode.fast_path_statement := by
  intro k hk hf s ra guard pr pc nb n hnb hn root cb pre d hroot hcb hpre hd fp s1 s2 l24 l32 l40 l56 l64 rslot
    hfp h1 h2 hl24 hl32 hl40 hl56 hl64 hrs S scratch hsc R h_mem hguard hcap hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hcap hpre ⊢
  have hz1 := rsp.toNat_lt_size; have hz2 := guard.toNat_lt_size; have hz3 := rcx.toNat_lt_size
  have hz4 := rdi.toNat_lt_size
  simp only [UInt64.size] at hz1 hz2 hz3 hz4
  step_directive hk marshalSSZTo 0
  step_directive hk marshalSSZTo 1
  step_directive hk marshalSSZTo 2
  step_directive hk marshalSSZTo 3
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk marshalSSZTo 4
  split
  case isTrue h =>
    exfalso
    rw [Codec.lea_cmp_be_false rsp.toBitVec _ guard.toBitVec _ _ 8 (by rfl) hguard] at h
    exact Bool.noConfusion h
  simp only [Effects.All]
  step_directive hk marshalSSZTo 5
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by data_columns_by_root_identifier_encode_addr) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  unfold_step
  step_directive hk marshalSSZTo 6
  step_directive hk marshalSSZTo 7
  step_directive hk marshalSSZTo 8
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by data_columns_by_root_identifier_encode_addr) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  unfold_step
  step_directive hk marshalSSZTo 9
  apply load_step_at _ _ (rax.toBitVec + 8) _ _ (Int.toBytes 8 pr.toInt) _ _ (by data_columns_by_root_identifier_encode_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk marshalSSZTo 10
  apply load_step_at _ _ (rax.toBitVec + 16) _ _ (Int.toBytes 8 32) _ _ (by data_columns_by_root_identifier_encode_addr) (by ecancel) (by rfl)
  simp only [show Int.ofBytes (Int.toBytes 8 32) = 32 by decide]
  unfold_step
  step_directive hk marshalSSZTo 11
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  step_directive hk marshalSSZTo 12
  apply store_step_at _ _ (rsp.toBitVec + 8) _ _ _ s1 _ _ (by data_columns_by_root_identifier_encode_addr) (by ecancel) (by exact h1)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  unfold_step
  step_directive hk marshalSSZTo 13
  step_directive hk marshalSSZTo 14
  step_directive hk marshalSSZTo 15
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  label_address hk hf marshalSSZTo 29
  refine eventually_mono (Encode.tail_fit k hk hf rsp.toBitVec rax.toBitVec pr pc nb rbx.toBitVec ra rbp n rdi.toNat hnb hn
    root cb d hroot hcb hd l24 l32 l40 l56 l64 rslot hl24 hl32 hl40 hl56 hl64 hrs S scratch hsc _ _
    (by show -128 + (rsp.toBitVec - 8#64) = rsp.toBitVec - 136; bv_omega) rfl rfl rfl rfl hcap (by ecancel) hmm) ?_
  rintro st ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, hrsp, hrbp, hr14, l24', l32', l40', l56', l64', rslot', scr,
    h24, h32, h40, h56, h64, hrs', hscr, hm⟩
  refine ⟨hpc, UInt64.toBitVec_inj.mp hrax, hrbx, UInt64.toNat_inj.mp hrcx, hrdi, hrsi,
    UInt64.toBitVec_inj.mp (by rw [hrsp]; simp), hrbp, hr14, l24', l32', l40', l56', l64', rslot', scr,
    h24, h32, h40, h56, h64, hrs', hscr, ?_⟩
  rw [List.append_assoc pre root offsetBytes, List.append_assoc pre (root ++ offsetBytes) cb,
    at_app pre _ (b := rbx.toBitVec + rcx.toBitVec) (by rw [hpre]; simp) (by simp [hpre, hroot, hcb, offsetBytes]; omega)]
  ecancel

end Prysm.DataColumnsByRootIdentifier
