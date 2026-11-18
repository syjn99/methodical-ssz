import Codec.Kind.EncodeFastPathAnyFrame
import Codec.EncodeFrameTest
import Prysm.BuilderPendingWithdrawal.Code

/-!
# Fast path (`encoder --fast-path`): encoder fast path of `(*v1alpha1.BuilderPendingWithdrawal).MarshalSSZTo`

Generated from the `.S` file and the IR: a symbolic dataflow walk of the fast path, one application of a
step lemma per directive (windows with the nops erased), boundary states between the fields. Every theorem
has a `_kind` line (`encodeHeadKindAnyFrame`, `encodeFieldKindAnyFrame`, `encodeEpilogueKindAnyFrame`, `encodeFastPathKindAnyFrame`).
**Fast path only**: `len(dst) + 36 ≤ cap(dst)` and every byte-vector field of its exact length. No
`runtime.growslice` directive is stepped: each capacity test is decided from the premise. Not covered: the
growslice branches, the length rejects, the morestack path. Not a complete encoder result.
FAST-PATH-JSON: {"type": "BuilderPendingWithdrawal", "const": "marshalSSZTo", "prefix": "Encode.generated", "size": 36, "frame": 144, "guard_addend": 24, "runtime_calls": true, "fields": [["FeeRecipient", "b", 20], ["Amount", "u", 8], ["BuilderIndex", "u", 8]], "boundaries": [9, 38, 67, 86], "layout": "Prysm.BuilderPendingWithdrawal.Encode.generated_layout", "assembly_sha256": "21b29973838e97486071c5f739fa47da7d84913a761c950e5258837d0b29c8ec", "ir_sha256": "59b783f53a4aef9ca94860df8776154d571310937304ba29b9329ce80c7a29b0", "statement_check": "kind instance only", "assembly": "prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.MarshalSSZTo.S", "ir": "prysm/ir/ir-mainnet.json", "ir_type": "v1alpha1.BuilderPendingWithdrawal", "kinds": [{"theorem": "Encode.generated_head", "kind": "encodeHeadKindAnyFrame"}, {"theorem": "Encode.generated_field_0", "kind": "encodeFieldKindAnyFrame"}, {"theorem": "Encode.generated_field_1", "kind": "encodeFieldKindAnyFrame"}, {"theorem": "Encode.generated_field_2", "kind": "encodeFieldKindAnyFrame"}, {"theorem": "Encode.generated_epilogue", "kind": "encodeEpilogueKindAnyFrame"}, {"theorem": "Encode.generated_fast", "kind": "encodeFastPathKindAnyFrame"}]}
-/

open Machine Runtime Codec Prysm.BuilderPendingWithdrawal.Code
variable [Host]

namespace Prysm.BuilderPendingWithdrawal

/-- The frame facts of `marshalSSZTo` (read from the `.S` file by the walk): frame `0x90`, stack chunks
`fp s1 s2 l96 l104 l24 t56 t40 t88 t72 rslot`. -/
def Encode.generated_layout : EncoderFrameLayout where
  stateWord := true
  frame := 144
  guardAddend := 24
  callsMemmove := true
  stackChunkCount := 11
  stackChunkLengths := [(0, 8), (1, 8), (2, 8), (3, 8), (4, 8), (5, 8), (6, 16), (7, 16), (8, 16), (9, 16), (10, 8)]
  pre := [.at (.below 8) (.original 0), .at (.above 8) (.original 1), .at (.above 16) (.original 2), .at (.below 96) (.original 3), .at (.below 104) (.original 4), .at (.below 24) (.original 5), .at (.below 56) (.original 6), .at (.below 40) (.original 7), .at (.below 88) (.original 8), .at (.below 72) (.original 9), .at (.below 160) (.original 10), .low .scratch]
  existentials := [.low, .fixed 8, .fixed 16, .fixed 8, .fixed 16]
  post := [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 96) (.reg .rdi), .at (.below 104) (.len 20), .at (.below 24) (.reg .rbx), .at (.below 56) (.field 1), .at (.below 48) (.existential 1), .at (.below 40) (.existential 2), .at (.below 88) (.field 2), .at (.below 80) (.existential 3), .at (.below 72) (.existential 4), .at (.below 160) (.ret 38), .low (.existential 0)]


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Head: directives 0–8 (stack guard, frame, spills); entry → boundary state 0. -/
theorem Encode.generated_head : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v1 v2 c0 b0 pre d0 d1 d2 : List UInt8) (hast : ast.length = 8) (hv1 : v1.length = 8) (hv2 : v2.length = 8) (hc0 : c0.length = 8) (hb0 : b0.length = 20) (hd0 : d0.length = 20) (hd1 : d1.length = 8) (hd2 : d2.length = 8)
    (p0 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l96 l104 l24 t56 t40 t88 t72 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl96 : l96.length = 8) (hl104 : l104.length = 8) (hl24 : l24.length = 8) (ht56 : t56.length = 16) (ht40 : t40.length = 16) (ht88 : t88.length = 16) (ht72 : t72.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l96.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (l104.At (s.regs.rsp.toBitVec - 104))
      ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (t56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (t88.At (s.regs.rsp.toBitVec - 88))
      ⋆ Eq (t72.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 160))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 160 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (v1.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (v2.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (b0.At p0)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 20))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 28))
      ⋆ R)
    (hguard : guard.toNat + 24 < s.regs.rsp.toNat) (hsp : 160 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 36 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 9)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 152 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.get64 Reg64.rax = s.regs.rax.toBitVec
        ∧ st.data.regs.get64 Reg64.rbx = s.regs.rbx.toBitVec
        ∧ st.data.regs.get64 Reg64.rcx = s.regs.rcx.toBitVec
        ∧ st.data.regs.get64 Reg64.rdi = s.regs.rdi.toBitVec ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (l96.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (l104.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (t56.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (t88.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (t72.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 160 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 20))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 28))
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf ast v1 v2 c0 b0 pre d0 d1 d2 hast hv1 hv2 hc0 hb0 hd0 hd1 hd2 p0 s ra guard hpre fp s1 s2 l96 l104 l24 t56 t40 t88 t72 rslot hfp hs1 hs2 hl96 hl104 hl24 ht56 ht40 ht88 ht72 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hcap hcap63 hpre ⊢
  have hcap' : rcx.toBitVec.toNat + 36 ≤ rdi.toBitVec.toNat := hcap
  apply encoder_prologue_large_frame _ _ _ (-24) 24 _ k (k + 7) (window_infix_at hk 0 7) (by rfl) (by rfl) (by rfl) guard fp hfp _ _ _ (by dsimp only; ecancel) hguard
  intro m1 H1 fl1; normalize_registers; dsimp only at H1
  apply step_sub_immediate Reg64.rsp 144 _ (k + 7) (k + 8) (window_infix_at hk 7 1) (by rfl) (by rfl)
  intro fl; normalize_registers
  apply register_value_rewrite Reg64.rsp (rsp.toBitVec - 152) _ _ _ (by show ((rsp.toBitVec - 8) - 144 : BitVec 64) = (rsp.toBitVec - 152); bv_omega)
  normalize_registers
  apply step_store Reg64.rbx Reg64.rsp 168 _ (k + 8) (k + 9) (window_infix_at hk 8 1) (by rfl) (by rfl)
    (rsp.toBitVec - 152) (rsp.toBitVec + 16) (by encoder_address_equation) s2 hs2 _ _ _ (by rfl) (by ecancel)
  intro m2 H2; normalize_registers; simp only [Reg64s.get64] at H2
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem Encode.generated_head_kind : ∀ (h : Host), type_of% (@Encode.generated_head h)
    = @Codec.encodeHeadKindAnyFrame h marshalSSZTo Prysm.BuilderPendingWithdrawal.Encode.generated_layout [.bytes 20, .uint64, .uint64]
    ⟨9, 0, [(.rax, .receiver), (.rbx, .ptr), (.rcx, .len 0), (.rdi, .cap)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.original 1), .at (.above 16) (.reg .rbx), .at (.below 96) (.original 3), .at (.below 104) (.original 4), .at (.below 24) (.original 5), .at (.below 56) (.original 6), .at (.below 40) (.original 7), .at (.below 88) (.original 8), .at (.below 72) (.original 9), .at (.below 160) (.original 10), .low .scratch],
      []⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 0 `FeeRecipient` (20 bytes): directives 9–37; boundary state 0 → 1. -/
theorem Encode.generated_field_0 : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v1 v2 c0 b0 pre d0 d1 d2 : List UInt8) (hast : ast.length = 8) (hv1 : v1.length = 8) (hv2 : v2.length = 8) (hc0 : c0.length = 8) (hb0 : b0.length = 20) (hd0 : d0.length = 20) (hd1 : d1.length = 8) (hd2 : d2.length = 8)
    (p0 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l96 l104 l24 t56 t40 t88 t72 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl96 : l96.length = 8) (hl104 : l104.length = 8) (hl24 : l24.length = 8) (ht56 : t56.length = 16) (ht40 : t40.length = 16) (ht88 : t88.length = 16) (ht72 : t72.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 160 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 36 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 9)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 152 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14
        ∧ st0.data.regs.get64 Reg64.rax = s.regs.rax.toBitVec
        ∧ st0.data.regs.get64 Reg64.rbx = s.regs.rbx.toBitVec
        ∧ st0.data.regs.get64 Reg64.rcx = s.regs.rcx.toBitVec
        ∧ st0.data.regs.get64 Reg64.rdi = s.regs.rdi.toBitVec ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (l96.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (l104.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (t56.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (t88.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (t72.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 160 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 20))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 28))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 38)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 152 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 : List UInt8), x0.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 20).toInt).At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (t56.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (t88.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (t72.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 38)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 160 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 20))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 28))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v1 v2 c0 b0 pre d0 d1 d2 hast hv1 hv2 hc0 hb0 hd0 hd1 hd2 p0 s ra guard hpre fp s1 s2 l96 l104 l24 t56 t40 t88 t72 rslot hfp hs1 hs2 hl96 hl104 hl24 ht56 ht40 ht88 ht72 hrslot R S scratch hsc hsp hcap hcap63 hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hsp hcap hcap63 hpre ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, hrrax, hrrbx, hrrcx, hrrdi, Hm⟩
  dsimp only at hpc hrsp hrbp hr14 hrrax hrrbx hrrcx hrrdi Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14 hrrax hrrbx hrrcx hrrdi Hm
  subst rsp1 rbp1 r141
  obtain rfl : rax = rax1 := (UInt64.toBitVec_inj.mp hrrax).symm
  obtain rfl : rbx = rbx1 := (UInt64.toBitVec_inj.mp hrrbx).symm
  obtain rfl : rcx = rcx1 := (UInt64.toBitVec_inj.mp hrrcx).symm
  obtain rfl : rdi = rdi1 := (UInt64.toBitVec_inj.mp hrrdi).symm
  have hcap' : rcx.toBitVec.toNat + 36 ≤ rdi.toBitVec.toNat := hcap
  apply step_load_value Reg64.rdx Reg64.rax 8 _ (k + 9) (k + 10) (window_infix_at hk 9 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 8) p0 (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_length_check Reg64.rax 16 20 _ _ (k + 10) (k + 12) (window_infix_at hk 10 2) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 16) (by encoder_address_equation) (Int.toBytes 8 20) (by rfl) (by decide) _ _ _ (by rfl) (by ecancel)
  intro fl; normalize_registers
  apply step_store Reg64.rax Reg64.rsp 160 _ (k + 12) (k + 13) (window_infix_at hk 12 1) (by rfl) (by rfl)
    (rsp.toBitVec - 152) (rsp.toBitVec + 8) (by encoder_address_equation) s1 hs1 _ _ _ (by rfl) (by ecancel)
  intro m3 H3; normalize_registers; simp only [Reg64s.get64] at H3
  apply step_lea Reg64.r8 Reg64.rcx 20 _ (k + 13) (k + 14) (window_infix_at hk 13 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.r8 (rcx.toBitVec + 20) _ _ _ (by show (rcx.toBitVec + 20 : BitVec 64) = (rcx.toBitVec + 20); bv_omega)
  normalize_registers
  have hl30 := Machine.label_at' hk hf (j := 30)
    (by simp only [marshalSSZTo, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply step_cmp_jae_taken Reg64.rdi Reg64.r8 _ _ (k + 14) (k + 30) (window_infix_at hk 14 3) (by rfl) hl30 _ _ (by show ((rcx.toBitVec + 20) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; normalize_registers
  apply step_label _ _ (k + 30) (k + 31) (window_infix_at hk 30 1) (by rfl) (by rfl)
  apply step_store Reg64.rdi Reg64.rsp 56 _ (k + 31) (k + 32) (window_infix_at hk 31 1) (by rfl) (by rfl)
    (rsp.toBitVec - 152) (rsp.toBitVec - 96) (by encoder_address_equation) l96 hl96 _ _ _ (by rfl) (by ecancel)
  intro m4 H4; normalize_registers; simp only [Reg64s.get64] at H4
  apply step_store Reg64.r8 Reg64.rsp 48 _ (k + 32) (k + 33) (window_infix_at hk 32 1) (by rfl) (by rfl)
    (rsp.toBitVec - 152) (rsp.toBitVec - 104) (by encoder_address_equation) l104 hl104 _ _ _ (by rfl) (by ecancel)
  intro m5 H5; normalize_registers; simp only [Reg64s.get64] at H5
  apply step_store Reg64.rbx Reg64.rsp 128 _ (k + 33) (k + 34) (window_infix_at hk 33 1) (by rfl) (by rfl)
    (rsp.toBitVec - 152) (rsp.toBitVec - 24) (by encoder_address_equation) l24 hl24 _ _ _ (by rfl) (by ecancel)
  intro m6 H6; normalize_registers; simp only [Reg64s.get64] at H6
  apply step_lea_indexed Reg64.rax Reg64.rbx Reg64.rcx _ (k + 34) (k + 35) (window_infix_at hk 34 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.rax (rbx.toBitVec + rcx.toBitVec) _ _ _ (by show (rbx.toBitVec + rcx.toBitVec : BitVec 64) = (rbx.toBitVec + rcx.toBitVec); bv_omega)
  normalize_registers
  apply step_move_register Reg64.rbx Reg64.rdx _ (k + 35) (k + 36) (window_infix_at hk 35 1) (by rfl) (by rfl)
  normalize_registers
  apply step_move_immediate Reg64.rcx 20 _ (k + 36) (k + 37) (window_infix_at hk 36 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.rcx 20 _ _ _ (by show (BitVec.zeroExtend 64 (BitVec.truncate 32 (20 : BitVec 64)) : BitVec 64) = 20; decide)
  normalize_registers
  refine eventually_trans _ _ _ _ (encode_memmove_call (k + 37) (window_infix_at hk 37 1) (rsp.toBitVec - 152) (rbx.toBitVec + rcx.toBitVec) p0
    (rsp.toBitVec - 160) (rsp.toBitVec - 160 - BitVec.ofNat 64 S) S (by bv_omega) (Codec.frame_low_address_without_calls rsp.toBitVec 152 160 S (by decide))
    b0 d0 rslot scratch (by rw [hd0, hb0]) hrslot hsc
    _ _ (by rfl) (by rfl) (by rfl) (by rw [hb0]; rfl) (by first | ecancel | (dsimp only; ecancel)) hmm) ?_
  rintro ⟨e1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, scr1, hscr1, Hc1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 Hc1
  subst hpc1
  obtain ⟨⟨raxc1, rbxc1, rcxc1, rdxc1, rsic1, rdic1, rspc1, rbpc1, r8c1, r9c1, r10c1, r11c1, r12c1, r13c1, r14c1, r15c1⟩, zmmsc1, flagsc1, memc1⟩ := e1
  simp only at hrsp1 hrbp1 hr141 Hc1
  subst rspc1 rbpc1 r14c1
  rw [show k + 37 + 1 = k + 38 from rfl] at Hc1
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, scr1, hscr1, ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem Encode.generated_field_0_kind : ∀ (h : Host), type_of% (@Encode.generated_field_0 h)
    = @Codec.encodeFieldKindAnyFrame h marshalSSZTo Prysm.BuilderPendingWithdrawal.Encode.generated_layout [.bytes 20, .uint64, .uint64]
    ⟨9, 0, [(.rax, .receiver), (.rbx, .ptr), (.rcx, .len 0), (.rdi, .cap)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.original 1), .at (.above 16) (.reg .rbx), .at (.below 96) (.original 3), .at (.below 104) (.original 4), .at (.below 24) (.original 5), .at (.below 56) (.original 6), .at (.below 40) (.original 7), .at (.below 88) (.original 8), .at (.below 72) (.original 9), .at (.below 160) (.original 10), .low .scratch],
      []⟩
    ⟨38, 1, [],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 96) (.reg .rdi), .at (.below 104) (.len 20), .at (.below 24) (.reg .rbx), .at (.below 56) (.original 6), .at (.below 40) (.original 7), .at (.below 88) (.original 8), .at (.below 72) (.original 9), .at (.below 160) (.ret 38), .low (.existential 0)],
      [.low]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 1 `Amount` (uint64): directives 38–66; boundary state 1 → 2. -/
theorem Encode.generated_field_1 : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v1 v2 c0 b0 pre d0 d1 d2 : List UInt8) (hast : ast.length = 8) (hv1 : v1.length = 8) (hv2 : v2.length = 8) (hc0 : c0.length = 8) (hb0 : b0.length = 20) (hd0 : d0.length = 20) (hd1 : d1.length = 8) (hd2 : d2.length = 8)
    (p0 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l96 l104 l24 t56 t40 t88 t72 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl96 : l96.length = 8) (hl104 : l104.length = 8) (hl24 : l24.length = 8) (ht56 : t56.length = 16) (ht40 : t40.length = 16) (ht88 : t88.length = 16) (ht72 : t72.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 160 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 36 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 38)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 152 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 : List UInt8), x0.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 20).toInt).At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (t56.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (t88.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (t72.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 38)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 160 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 20))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 28))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 67)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 152 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.get64 Reg64.rax = s.regs.rbx.toBitVec
        ∧ st.data.regs.get64 Reg64.rcx = s.regs.rdi.toBitVec
        ∧ st.data.regs.get64 Reg64.rdx = s.regs.rcx.toBitVec + 28
        ∧ st.data.regs.get64 Reg64.rsi = s.regs.rax.toBitVec ∧
        ∃ (x0 x1 x2 : List UInt8), x0.length = S ∧ x1.length = 8 ∧ x2.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 20).toInt).At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (v1.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (t88.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (t72.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 38)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 160 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 20))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 28))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v1 v2 c0 b0 pre d0 d1 d2 hast hv1 hv2 hc0 hb0 hd0 hd1 hd2 p0 s ra guard hpre fp s1 s2 l96 l104 l24 t56 t40 t88 t72 rslot hfp hs1 hs2 hl96 hl104 hl24 ht56 ht40 ht88 ht72 hrslot R S scratch hsc hsp hcap hcap63 hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hsp hcap hcap63 hpre ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, x0, hx0, Hm⟩
  dsimp only at hpc hrsp hrbp hr14  Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14  Hm
  subst rsp1 rbp1 r141
  have hcap' : rcx.toBitVec.toNat + 36 ≤ rdi.toBitVec.toNat := hcap
  apply step_load_value Reg64.rbx Reg64.rsp 48 _ (k + 38) (k + 39) (window_infix_at hk 38 1) (by rfl) (by rfl)
    (rsp.toBitVec - 152) (rsp.toBitVec - 104) (rcx.toBitVec + 20) (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_lea Reg64.rdx Reg64.rbx 8 _ (k + 39) (k + 40) (window_infix_at hk 39 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.rdx (rcx.toBitVec + 28) _ _ _ (by show ((rcx.toBitVec + 20) + 8 : BitVec 64) = (rcx.toBitVec + 28); bv_omega)
  normalize_registers
  apply step_load_value Reg64.rsi Reg64.rsp 160 _ (k + 40) (k + 41) (window_infix_at hk 40 1) (by rfl) (by rfl)
    (rsp.toBitVec - 152) (rsp.toBitVec + 8) rax.toBitVec (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_load_bytes Reg64.rdi Reg64.rsi 32 _ (k + 41) (k + 42) (window_infix_at hk 41 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 32) (by encoder_address_equation) v1 hv1 _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_lea Reg64.r8 Reg64.rsp 96 _ (k + 42) (k + 46) (window_infix_at hk 42 4) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.r8 (rsp.toBitVec - 56) _ _ _ (by show ((rsp.toBitVec - 152) + 96 : BitVec 64) = (rsp.toBitVec - 56); bv_omega)
  normalize_registers
  apply step_store_xmm15 Reg64.r8 0 _ (k + 46) (k + 47) (window_infix_at hk 46 1) (by rfl) (by rfl)
    (rsp.toBitVec - 56) (rsp.toBitVec - 56) (by encoder_address_equation) t56 ht56 _ _ _ (by rfl) (by ecancel)
  intro m7 H7; normalize_registers; try dsimp only at H7
  apply step_store_xmm15 Reg64.r8 16 _ (k + 47) (k + 48) (window_infix_at hk 47 1) (by rfl) (by rfl)
    (rsp.toBitVec - 56) (rsp.toBitVec - 40) (by encoder_address_equation) t40 ht40 _ _ _ (by rfl) (by ecancel)
  intro m8 H8; normalize_registers; try dsimp only at H8
  rw [Machine.at_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 56), show (rsp.toBitVec - 56) + 8 = (rsp.toBitVec - 48) by bv_omega] at H8
  apply step_store Reg64.rdi Reg64.rsp 96 _ (k + 48) (k + 49) (window_infix_at hk 48 1) (by rfl) (by rfl)
    (rsp.toBitVec - 152) (rsp.toBitVec - 56) (by encoder_address_equation) ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).take 8) (by rw [List.length_take, Int.toBytes_length]; rfl) _ _ _ (by rfl) (by ecancel)
  intro m9 H9; normalize_registers; simp only [Reg64s.get64] at H9
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v1 hv1] at H9
  apply step_load_value Reg64.rcx Reg64.rsp 56 _ (k + 49) (k + 50) (window_infix_at hk 49 1) (by rfl) (by rfl)
    (rsp.toBitVec - 152) (rsp.toBitVec - 96) rdi.toBitVec (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_cmp_jb_not_taken Reg64.rcx Reg64.rdx _ _ (k + 50) (k + 53) (window_infix_at hk 50 3) (by rfl) (by rfl) _ _ (by show ((rcx.toBitVec + 28) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; normalize_registers
  apply step_load_value Reg64.rax Reg64.rsp 128 _ (k + 53) (k + 54) (window_infix_at hk 53 1) (by rfl) (by rfl)
    (rsp.toBitVec - 152) (rsp.toBitVec - 24) rbx.toBitVec (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  have hl64 := Machine.label_at' hk hf (j := 64)
    (by simp only [marshalSSZTo, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply step_jump _ _ (k + 54) (k + 64) (window_infix_at hk 54 1) (by rfl) hl64
  apply step_label _ _ (k + 64) (k + 65) (window_infix_at hk 64 1) (by rfl) (by rfl)
  apply step_load_bytes Reg64.r8 Reg64.rsp 96 _ (k + 65) (k + 66) (window_infix_at hk 65 1) (by rfl) (by rfl)
    (rsp.toBitVec - 152) (rsp.toBitVec - 56) (by encoder_address_equation) v1 hv1 _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_store_indexed Reg64.r8 Reg64.rax Reg64.rbx 0 _ (k + 66) (k + 67) (window_infix_at hk 66 1) (by rfl) (by rfl)
    rbx.toBitVec (rcx.toBitVec + 20) (rbx.toBitVec + rcx.toBitVec + 20) (by encoder_address_equation) d1 hd1 _ _ _ (by rfl) (by rfl) (by ecancel)
  intro m10 H10; normalize_registers; simp only [Reg64s.get64] at H10
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v1 hv1] at H10
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, x0, ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8), (Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt), hx0, (by rw [List.length_drop, Int.toBytes_length]), (Int.toBytes_length 16 _), ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem Encode.generated_field_1_kind : ∀ (h : Host), type_of% (@Encode.generated_field_1 h)
    = @Codec.encodeFieldKindAnyFrame h marshalSSZTo Prysm.BuilderPendingWithdrawal.Encode.generated_layout [.bytes 20, .uint64, .uint64]
    ⟨38, 1, [],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 96) (.reg .rdi), .at (.below 104) (.len 20), .at (.below 24) (.reg .rbx), .at (.below 56) (.original 6), .at (.below 40) (.original 7), .at (.below 88) (.original 8), .at (.below 72) (.original 9), .at (.below 160) (.ret 38), .low (.existential 0)],
      [.low]⟩
    ⟨67, 2, [(.rax, .ptr), (.rcx, .cap), (.rdx, .len 28), (.rsi, .receiver)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 96) (.reg .rdi), .at (.below 104) (.len 20), .at (.below 24) (.reg .rbx), .at (.below 56) (.field 1), .at (.below 48) (.existential 1), .at (.below 40) (.existential 2), .at (.below 88) (.original 8), .at (.below 72) (.original 9), .at (.below 160) (.ret 38), .low (.existential 0)],
      [.low, .fixed 8, .fixed 16]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 2 `BuilderIndex` (uint64): directives 67–85; boundary state 2 → 3. -/
theorem Encode.generated_field_2 : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v1 v2 c0 b0 pre d0 d1 d2 : List UInt8) (hast : ast.length = 8) (hv1 : v1.length = 8) (hv2 : v2.length = 8) (hc0 : c0.length = 8) (hb0 : b0.length = 20) (hd0 : d0.length = 20) (hd1 : d1.length = 8) (hd2 : d2.length = 8)
    (p0 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l96 l104 l24 t56 t40 t88 t72 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl96 : l96.length = 8) (hl104 : l104.length = 8) (hl24 : l24.length = 8) (ht56 : t56.length = 16) (ht40 : t40.length = 16) (ht88 : t88.length = 16) (ht72 : t72.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 160 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 36 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 67)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 152 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14
        ∧ st0.data.regs.get64 Reg64.rax = s.regs.rbx.toBitVec
        ∧ st0.data.regs.get64 Reg64.rcx = s.regs.rdi.toBitVec
        ∧ st0.data.regs.get64 Reg64.rdx = s.regs.rcx.toBitVec + 28
        ∧ st0.data.regs.get64 Reg64.rsi = s.regs.rax.toBitVec ∧
        ∃ (x0 x1 x2 : List UInt8), x0.length = S ∧ x1.length = 8 ∧ x2.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 20).toInt).At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (v1.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (t88.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (t72.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 38)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 160 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 20))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 28))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 86)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 152 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.get64 Reg64.rax = s.regs.rbx.toBitVec
        ∧ st.data.regs.get64 Reg64.rbx = s.regs.rcx.toBitVec + 36
        ∧ st.data.regs.get64 Reg64.rcx = s.regs.rdi.toBitVec ∧
        ∃ (x0 x1 x2 x3 x4 : List UInt8), x0.length = S ∧ x1.length = 8 ∧ x2.length = 16 ∧ x3.length = 8 ∧ x4.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 20).toInt).At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (v1.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (v2.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x4.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 38)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 160 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 20))
          ⋆ Eq (v2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 28))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v1 v2 c0 b0 pre d0 d1 d2 hast hv1 hv2 hc0 hb0 hd0 hd1 hd2 p0 s ra guard hpre fp s1 s2 l96 l104 l24 t56 t40 t88 t72 rslot hfp hs1 hs2 hl96 hl104 hl24 ht56 ht40 ht88 ht72 hrslot R S scratch hsc hsp hcap hcap63 hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hsp hcap hcap63 hpre ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, hrrax, hrrcx, hrrdx, hrrsi, x0, x1, x2, hx0, hx1, hx2, Hm⟩
  dsimp only at hpc hrsp hrbp hr14 hrrax hrrcx hrrdx hrrsi Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14 hrrax hrrcx hrrdx hrrsi Hm
  subst rsp1 rbp1 r141
  obtain rfl : rbx = rax1 := (UInt64.toBitVec_inj.mp hrrax).symm
  obtain rfl : rdi = rcx1 := (UInt64.toBitVec_inj.mp hrrcx).symm
  obtain rfl : rdx1 = { toBitVec := rcx.toBitVec + 28 } := UInt64.toBitVec_inj.mp hrrdx
  obtain rfl : rax = rsi1 := (UInt64.toBitVec_inj.mp hrrsi).symm
  have hcap' : rcx.toBitVec.toNat + 36 ≤ rdi.toBitVec.toNat := hcap
  apply step_lea Reg64.rbx Reg64.rdx 8 _ (k + 67) (k + 68) (window_infix_at hk 67 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.rbx (rcx.toBitVec + 36) _ _ _ (by show ((rcx.toBitVec + 28) + 8 : BitVec 64) = (rcx.toBitVec + 36); bv_omega)
  normalize_registers
  apply step_load_bytes Reg64.r8 Reg64.rsi 40 _ (k + 68) (k + 69) (window_infix_at hk 68 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 40) (by encoder_address_equation) v2 hv2 _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_lea Reg64.r9 Reg64.rsp 64 _ (k + 69) (k + 73) (window_infix_at hk 69 4) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.r9 (rsp.toBitVec - 88) _ _ _ (by show ((rsp.toBitVec - 152) + 64 : BitVec 64) = (rsp.toBitVec - 88); bv_omega)
  normalize_registers
  apply step_store_xmm15 Reg64.r9 0 _ (k + 73) (k + 74) (window_infix_at hk 73 1) (by rfl) (by rfl)
    (rsp.toBitVec - 88) (rsp.toBitVec - 88) (by encoder_address_equation) t88 ht88 _ _ _ (by rfl) (by ecancel)
  intro m11 H11; normalize_registers; try dsimp only at H11
  apply step_store_xmm15 Reg64.r9 16 _ (k + 74) (k + 75) (window_infix_at hk 74 1) (by rfl) (by rfl)
    (rsp.toBitVec - 88) (rsp.toBitVec - 72) (by encoder_address_equation) t72 ht72 _ _ _ (by rfl) (by ecancel)
  intro m12 H12; normalize_registers; try dsimp only at H12
  rw [Machine.at_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 88), show (rsp.toBitVec - 88) + 8 = (rsp.toBitVec - 80) by bv_omega] at H12
  apply step_store Reg64.r8 Reg64.rsp 64 _ (k + 75) (k + 76) (window_infix_at hk 75 1) (by rfl) (by rfl)
    (rsp.toBitVec - 152) (rsp.toBitVec - 88) (by encoder_address_equation) ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).take 8) (by rw [List.length_take, Int.toBytes_length]; rfl) _ _ _ (by rfl) (by ecancel)
  intro m13 H13; normalize_registers; simp only [Reg64s.get64] at H13
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v2 hv2] at H13
  have hl83 := Machine.label_at' hk hf (j := 83)
    (by simp only [marshalSSZTo, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply step_cmp_jae_taken Reg64.rcx Reg64.rbx _ _ (k + 76) (k + 83) (window_infix_at hk 76 2) (by rfl) hl83 _ _ (by show ((rcx.toBitVec + 36) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; normalize_registers
  apply step_label _ _ (k + 83) (k + 84) (window_infix_at hk 83 1) (by rfl) (by rfl)
  apply step_load_bytes Reg64.r8 Reg64.rsp 64 _ (k + 84) (k + 85) (window_infix_at hk 84 1) (by rfl) (by rfl)
    (rsp.toBitVec - 152) (rsp.toBitVec - 88) (by encoder_address_equation) v2 hv2 _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_store_indexed Reg64.r8 Reg64.rax Reg64.rdx 0 _ (k + 85) (k + 86) (window_infix_at hk 85 1) (by rfl) (by rfl)
    rbx.toBitVec (rcx.toBitVec + 28) (rbx.toBitVec + rcx.toBitVec + 28) (by encoder_address_equation) d2 hd2 _ _ _ (by rfl) (by rfl) (by ecancel)
  intro m14 H14; normalize_registers; simp only [Reg64s.get64] at H14
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v2 hv2] at H14
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, x0, x1, x2, ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8), (Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt), hx0, hx1, hx2, (by rw [List.length_drop, Int.toBytes_length]), (Int.toBytes_length 16 _), ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem Encode.generated_field_2_kind : ∀ (h : Host), type_of% (@Encode.generated_field_2 h)
    = @Codec.encodeFieldKindAnyFrame h marshalSSZTo Prysm.BuilderPendingWithdrawal.Encode.generated_layout [.bytes 20, .uint64, .uint64]
    ⟨67, 2, [(.rax, .ptr), (.rcx, .cap), (.rdx, .len 28), (.rsi, .receiver)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 96) (.reg .rdi), .at (.below 104) (.len 20), .at (.below 24) (.reg .rbx), .at (.below 56) (.field 1), .at (.below 48) (.existential 1), .at (.below 40) (.existential 2), .at (.below 88) (.original 8), .at (.below 72) (.original 9), .at (.below 160) (.ret 38), .low (.existential 0)],
      [.low, .fixed 8, .fixed 16]⟩
    ⟨86, 3, [(.rax, .ptr), (.rbx, .len 36), (.rcx, .cap)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 96) (.reg .rdi), .at (.below 104) (.len 20), .at (.below 24) (.reg .rbx), .at (.below 56) (.field 1), .at (.below 48) (.existential 1), .at (.below 40) (.existential 2), .at (.below 88) (.field 2), .at (.below 80) (.existential 3), .at (.below 72) (.existential 4), .at (.below 160) (.ret 38), .low (.existential 0)],
      [.low, .fixed 8, .fixed 16, .fixed 8, .fixed 16]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Epilogue: directives 86–return; boundary state 3 → the fast-path post-state. -/
theorem Encode.generated_epilogue : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v1 v2 c0 b0 pre d0 d1 d2 : List UInt8) (hast : ast.length = 8) (hv1 : v1.length = 8) (hv2 : v2.length = 8) (hc0 : c0.length = 8) (hb0 : b0.length = 20) (hd0 : d0.length = 20) (hd1 : d1.length = 8) (hd2 : d2.length = 8)
    (p0 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l96 l104 l24 t56 t40 t88 t72 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl96 : l96.length = 8) (hl104 : l104.length = 8) (hl24 : l24.length = 8) (ht56 : t56.length = 16) (ht40 : t40.length = 16) (ht88 : t88.length = 16) (ht72 : t72.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 160 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 36 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 86)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 152 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14
        ∧ st0.data.regs.get64 Reg64.rax = s.regs.rbx.toBitVec
        ∧ st0.data.regs.get64 Reg64.rbx = s.regs.rcx.toBitVec + 36
        ∧ st0.data.regs.get64 Reg64.rcx = s.regs.rdi.toBitVec ∧
        ∃ (x0 x1 x2 x3 x4 : List UInt8), x0.length = S ∧ x1.length = 8 ∧ x2.length = 16 ∧ x3.length = 8 ∧ x4.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 20).toInt).At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (v1.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (v2.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x4.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 38)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 160 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 20))
          ⋆ Eq (v2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 28))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec
        ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 36
        ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0
        ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8
        ∧ st.data.regs.rbp = s.regs.rbp
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 x2 x3 x4 : List UInt8), x0.length = S ∧ x1.length = 8 ∧ x2.length = 16 ∧ x3.length = 8 ∧ x4.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 20).toInt).At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (v1.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (v2.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x4.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 38)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 160 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 20))
          ⋆ Eq (v2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 28))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v1 v2 c0 b0 pre d0 d1 d2 hast hv1 hv2 hc0 hb0 hd0 hd1 hd2 p0 s ra guard hpre fp s1 s2 l96 l104 l24 t56 t40 t88 t72 rslot hfp hs1 hs2 hl96 hl104 hl24 ht56 ht40 ht88 ht72 hrslot R S scratch hsc hsp hcap hcap63
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hsp hcap hcap63 hpre ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, hrrax, hrrbx, hrrcx, x0, x1, x2, x3, x4, hx0, hx1, hx2, hx3, hx4, Hm⟩
  dsimp only at hpc hrsp hrbp hr14 hrrax hrrbx hrrcx Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14 hrrax hrrbx hrrcx Hm
  subst rsp1 rbp1 r141
  obtain rfl : rbx = rax1 := (UInt64.toBitVec_inj.mp hrrax).symm
  obtain rfl : rbx1 = { toBitVec := rcx.toBitVec + 36 } := UInt64.toBitVec_inj.mp hrrbx
  obtain rfl : rdi = rcx1 := (UInt64.toBitVec_inj.mp hrrcx).symm
  have hcap' : rcx.toBitVec.toNat + 36 ≤ rdi.toBitVec.toNat := hcap
  apply step_xor32 Reg64.rdi _ (k + 86) (k + 87) (window_infix_at hk 86 1) (by rfl) (by rfl)
  intro fl; normalize_registers
  apply step_xor32 Reg64.rsi _ (k + 87) (k + 88) (window_infix_at hk 87 1) (by rfl) (by rfl)
  intro fl; normalize_registers
  apply step_add_immediate Reg64.rsp 144 _ (k + 88) (k + 89) (window_infix_at hk 88 1) (by rfl) (by rfl)
  intro fl; normalize_registers
  apply register_value_rewrite Reg64.rsp (rsp.toBitVec - 8) _ _ _ (by show ((rsp.toBitVec - 152) + 144 : BitVec 64) = (rsp.toBitVec - 8); bv_omega)
  normalize_registers
  refine eventually_trans _ _ _ _ (decode_return_segment _ (k + 89) (window_infix_at hk 89 2) (by rfl) (rsp.toBitVec - 8) rsp.toBitVec (by bv_omega) rbp ra _ _ (by rfl) (by ecancel)) ?_
  rintro ⟨d', pc'⟩ ⟨hpc', hrsp', hrbp', hreg', hmem'⟩
  dsimp only at hpc' hrsp' hrbp' hreg' hmem'
  apply Eventually.done
  refine ⟨hpc', ?_, ?_, ?_, ?_, ?_, ?_, hrbp', ?_, x0, x1, x2, x3, x4, hx0, hx1, hx2, hx3, hx4, ?_⟩
  · exact UInt64.toBitVec_inj.mp (hreg' Reg64.rax (by decide) (by decide))
  · show d'.regs.rbx.toBitVec.toNat = rcx.toBitVec.toNat + 36
    rw [show d'.regs.rbx.toBitVec = rcx.toBitVec + 36 from hreg' Reg64.rbx (by decide) (by decide)]
    bv_omega
  · exact UInt64.toBitVec_inj.mp (hreg' Reg64.rcx (by decide) (by decide))
  · exact UInt64.toBitVec_inj.mp (hreg' Reg64.rdi (by decide) (by decide))
  · exact UInt64.toBitVec_inj.mp (hreg' Reg64.rsi (by decide) (by decide))
  · rw [hrsp']; apply UInt64.toBitVec_inj.mp
    first
      | (simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; done)
      | (simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega)
  · exact UInt64.toBitVec_inj.mp (hreg' Reg64.r14 (by decide) (by decide))
  · first | (rw [hmem']; ecancel) | (dsimp only; rw [hmem']; ecancel)
theorem Encode.generated_epilogue_kind : ∀ (h : Host), type_of% (@Encode.generated_epilogue h)
    = @Codec.encodeEpilogueKindAnyFrame h marshalSSZTo Prysm.BuilderPendingWithdrawal.Encode.generated_layout [.bytes 20, .uint64, .uint64]
    ⟨86, 3, [(.rax, .ptr), (.rbx, .len 36), (.rcx, .cap)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 96) (.reg .rdi), .at (.below 104) (.len 20), .at (.below 24) (.reg .rbx), .at (.below 56) (.field 1), .at (.below 48) (.existential 1), .at (.below 40) (.existential 2), .at (.below 88) (.field 2), .at (.below 80) (.existential 3), .at (.below 72) (.existential 4), .at (.below 160) (.ret 38), .low (.existential 0)],
      [.low, .fixed 8, .fixed 16, .fixed 8, .fixed 16]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Encoder fast path of `(*v1alpha1.BuilderPendingWithdrawal).MarshalSSZTo` (Go 1.26.10), generated** (`encoder --fast-path`):
head, one theorem per field, epilogue, chained by `eventually_trans`. Premises: `len + 36 ≤ cap`,
every byte-vector field of its exact length. Statement = the kind instance (`_kind`). Fast path only. -/
theorem Encode.generated_fast : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v1 v2 c0 b0 pre d0 d1 d2 : List UInt8) (hast : ast.length = 8) (hv1 : v1.length = 8) (hv2 : v2.length = 8) (hc0 : c0.length = 8) (hb0 : b0.length = 20) (hd0 : d0.length = 20) (hd1 : d1.length = 8) (hd2 : d2.length = 8)
    (p0 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l96 l104 l24 t56 t40 t88 t72 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl96 : l96.length = 8) (hl104 : l104.length = 8) (hl24 : l24.length = 8) (ht56 : t56.length = 16) (ht40 : t40.length = 16) (ht88 : t88.length = 16) (ht72 : t72.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l96.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (l104.At (s.regs.rsp.toBitVec - 104))
      ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (t56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (t88.At (s.regs.rsp.toBitVec - 88))
      ⋆ Eq (t72.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 160))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 160 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (v1.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (v2.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (b0.At p0)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 20))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 28))
      ⋆ R)
    (hguard : guard.toNat + 24 < s.regs.rsp.toNat) (hsp : 160 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 36 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec
        ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 36
        ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0
        ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8
        ∧ st.data.regs.rbp = s.regs.rbp
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 x2 x3 x4 : List UInt8), x0.length = S ∧ x1.length = 8 ∧ x2.length = 16 ∧ x3.length = 8 ∧ x4.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 20).toInt).At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (v1.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (v2.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x4.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 38)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 160 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 20))
          ⋆ Eq (v2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 28))
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf ast v1 v2 c0 b0 pre d0 d1 d2 hast hv1 hv2 hc0 hb0 hd0 hd1 hd2 p0 s ra guard hpre fp s1 s2 l96 l104 l24 t56 t40 t88 t72 rslot hfp hs1 hs2 hl96 hl104 hl24 ht56 ht40 ht88 ht72 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm
  refine eventually_trans _ _ _ _ (Encode.generated_head k hk hf ast v1 v2 c0 b0 pre d0 d1 d2 hast hv1 hv2 hc0 hb0 hd0 hd1 hd2 p0 s ra guard hpre fp s1 s2 l96 l104 l24 t56 t40 t88 t72 rslot hfp hs1 hs2 hl96 hl104 hl24 ht56 ht40 ht88 ht72 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm) ?_
  intro st0 h0
  refine eventually_trans _ _ _ _ (Encode.generated_field_0 k hk hf ast v1 v2 c0 b0 pre d0 d1 d2 hast hv1 hv2 hc0 hb0 hd0 hd1 hd2 p0 s ra guard hpre fp s1 s2 l96 l104 l24 t56 t40 t88 t72 rslot hfp hs1 hs2 hl96 hl104 hl24 ht56 ht40 ht88 ht72 hrslot R S scratch hsc hsp hcap hcap63 hmm st0 h0) ?_
  intro st1 h1
  refine eventually_trans _ _ _ _ (Encode.generated_field_1 k hk hf ast v1 v2 c0 b0 pre d0 d1 d2 hast hv1 hv2 hc0 hb0 hd0 hd1 hd2 p0 s ra guard hpre fp s1 s2 l96 l104 l24 t56 t40 t88 t72 rslot hfp hs1 hs2 hl96 hl104 hl24 ht56 ht40 ht88 ht72 hrslot R S scratch hsc hsp hcap hcap63 hmm st1 h1) ?_
  intro st2 h2
  refine eventually_trans _ _ _ _ (Encode.generated_field_2 k hk hf ast v1 v2 c0 b0 pre d0 d1 d2 hast hv1 hv2 hc0 hb0 hd0 hd1 hd2 p0 s ra guard hpre fp s1 s2 l96 l104 l24 t56 t40 t88 t72 rslot hfp hs1 hs2 hl96 hl104 hl24 ht56 ht40 ht88 ht72 hrslot R S scratch hsc hsp hcap hcap63 hmm st2 h2) ?_
  intro st3 h3
  exact Encode.generated_epilogue k hk hf ast v1 v2 c0 b0 pre d0 d1 d2 hast hv1 hv2 hc0 hb0 hd0 hd1 hd2 p0 s ra guard hpre fp s1 s2 l96 l104 l24 t56 t40 t88 t72 rslot hfp hs1 hs2 hl96 hl104 hl24 ht56 ht40 ht88 ht72 hrslot R S scratch hsc hsp hcap hcap63 st3 h3
theorem Encode.generated_fast_kind : ∀ (h : Host), type_of% (@Encode.generated_fast h)
    = @Codec.encodeFastPathKindAnyFrame h marshalSSZTo Prysm.BuilderPendingWithdrawal.Encode.generated_layout [.bytes 20, .uint64, .uint64] := by
  intro h; rfl

end Prysm.BuilderPendingWithdrawal
