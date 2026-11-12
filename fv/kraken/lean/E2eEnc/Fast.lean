import Fk.Contracts
import Fk.Step
import Fk.Labels
import E2eScal.StackGuard
import E2eEnc.StmtEnc
import E2eEnc.Tail

/-!
# ENC `(*v1alpha1.DataColumnsByRootIdentifier).MarshalSSZTo`: capacity-sufficient path F

`dc_marshal_fast_main : dc_marshal_fast_stmt`. Directives 2–4 large-frame guard `lea -0x8(%rsp),%r12` (closed with
`E2eScal.lea_cmp_be_false`, N = 8), 5–7 prologue (`push %rbp`, `add $-0x80`), 8 rbx spill to x + 16, 9 BlockRoot
pointer, 10–11 `cmpq $0x20,0x10(%rax); jne` not taken, 12 rax spill to x + 8, 13–15 `len + 32 ≤ cap`: `jae L_7c`
taken, then `dc_tail` (directive 29 to the return).
-/

open Fk E2eEnc.Code
variable [Host]

namespace E2eEnc

theorem dc_e2e_marshal_fast_main : dc_marshal_fast_stmt := by
  intro k hk hf s ra guard pr pc nb n hnb hn root cb pre d hroot hcb hpre hd fp s1 s2 l24 l32 l40 l56 l64 rslot
    hfp h1 h2 hl24 hl32 hl40 hl56 hl64 hrs S scratch hsc R h_mem hguard hcap hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hcap hpre ⊢
  have hz1 := rsp.toNat_lt_size; have hz2 := guard.toNat_lt_size; have hz3 := rcx.toNat_lt_size
  have hz4 := rdi.toNat_lt_size
  simp only [UInt64.size] at hz1 hz2 hz3 hz4
  kat hk DcMarshal 0
  kat hk DcMarshal 1
  kat hk DcMarshal 2
  kat hk DcMarshal 3
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk DcMarshal 4
  split
  case isTrue h =>
    exfalso
    rw [E2eScal.lea_cmp_be_false rsp.toBitVec _ guard.toBitVec _ _ 8 (by rfl) hguard] at h
    exact Bool.noConfusion h
  simp only [Effects.All]
  kat hk DcMarshal 5
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by daddr) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk DcMarshal 6
  kat hk DcMarshal 7
  kat hk DcMarshal 8
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by daddr) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk DcMarshal 9
  apply load_step_at _ _ (rax.toBitVec + 8) _ _ (Int.toBytes 8 pr.toInt) _ _ (by daddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk DcMarshal 10
  apply load_step_at _ _ (rax.toBitVec + 16) _ _ (Int.toBytes 8 32) _ _ (by daddr) (by ecancel) (by rfl)
  simp only [show Int.ofBytes (Int.toBytes 8 32) = 32 by decide]
  kunfold
  kat hk DcMarshal 11
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk DcMarshal 12
  apply store_step_at _ _ (rsp.toBitVec + 8) _ _ _ s1 _ _ (by daddr) (by ecancel) (by exact h1)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk DcMarshal 13
  kat hk DcMarshal 14
  kat hk DcMarshal 15
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf DcMarshal 29
  refine eventually_mono (dc_tail k hk hf rsp.toBitVec rax.toBitVec pr pc nb rbx.toBitVec ra rbp n rdi.toNat hnb hn
    root cb d hroot hcb hd l24 l32 l40 l56 l64 rslot hl24 hl32 hl40 hl56 hl64 hrs S scratch hsc _ _
    (by show -128 + (rsp.toBitVec - 8#64) = rsp.toBitVec - 136; bv_omega) rfl rfl rfl rfl hcap (by ecancel) hmm) ?_
  rintro st ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, hrsp, hrbp, hr14, l24', l32', l40', l56', l64', rslot', scr,
    h24, h32, h40, h56, h64, hrs', hscr, hm⟩
  refine ⟨hpc, UInt64.toBitVec_inj.mp hrax, hrbx, UInt64.toNat_inj.mp hrcx, hrdi, hrsi,
    UInt64.toBitVec_inj.mp (by rw [hrsp]; simp), hrbp, hr14, l24', l32', l40', l56', l64', rslot', scr,
    h24, h32, h40, h56, h64, hrs', hscr, ?_⟩
  rw [List.append_assoc pre root dcOff, List.append_assoc pre (root ++ dcOff) cb,
    at_app pre _ (b := rbx.toBitVec + rcx.toBitVec) (by rw [hpre]; simp) (by simp [hpre, hroot, hcb, dcOff]; omega)]
  ecancel

end E2eEnc
