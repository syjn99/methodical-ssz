import Codec.Kind.EncodeFastPathAnyFrame
import Codec.EncodeFrameTest
import Codec.EncodeInlineCopy
import Prysm.Status.Code

/-!
# Fast path (`encoder --fast-path`): encoder fast path of `(*v1alpha1.Status).MarshalSSZTo`

Generated from the `.S` file and the IR: a symbolic dataflow walk of the fast path, one application of a
step lemma per directive (windows with the nops erased), boundary states between the fields. Every theorem
has a `_kind` line (`encodeHeadKindAnyFrame`, `encodeFieldKindAnyFrame`, `encodeEpilogueKindAnyFrame`, `encodeFastPathKindAnyFrame`).
**Fast path only**: `len(dst) + 84 ≤ cap(dst)` and every byte-vector field of its exact length. No
`runtime.growslice` directive is stepped: each capacity test is decided from the premise. Not covered: the
growslice branches, the length rejects, the morestack path. Not a complete encoder result.
FAST-PATH-JSON: {"type": "Status", "const": "marshalSSZTo", "prefix": "Encode.generated", "size": 84, "frame": 176, "guard_addend": 56, "runtime_calls": true, "fields": [["ForkDigest", "b", 4], ["FinalizedRoot", "b", 32], ["FinalizedEpoch", "u", 8], ["HeadRoot", "b", 32], ["HeadSlot", "u", 8]], "boundaries": [9, 34, 62, 91, 113, 141], "layout": "Prysm.Status.Encode.generated_layout", "assembly_sha256": "7dc2617991d9358707041f16fc60e0eccf0b7d583d0bba0f0dc8be9e555c74c6", "ir_sha256": "59b783f53a4aef9ca94860df8776154d571310937304ba29b9329ce80c7a29b0", "statement_check": "kind instance only", "assembly": "prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo.S", "ir": "prysm/ir/ir-mainnet.json", "ir_type": "v1alpha1.Status", "kinds": [{"theorem": "Encode.generated_head", "kind": "encodeHeadKindAnyFrame"}, {"theorem": "Encode.generated_field_0", "kind": "encodeFieldKindAnyFrame"}, {"theorem": "Encode.generated_field_1", "kind": "encodeFieldKindAnyFrame"}, {"theorem": "Encode.generated_field_2", "kind": "encodeFieldKindAnyFrame"}, {"theorem": "Encode.generated_field_3", "kind": "encodeFieldKindAnyFrame"}, {"theorem": "Encode.generated_field_4", "kind": "encodeFieldKindAnyFrame"}, {"theorem": "Encode.generated_epilogue", "kind": "encodeEpilogueKindAnyFrame"}, {"theorem": "Encode.generated_fast", "kind": "encodeFastPathKindAnyFrame"}]}
-/

open Machine Runtime Codec Prysm.Status.Code
variable [Host]

namespace Prysm.Status

/-- The frame facts of `marshalSSZTo` (read from the `.S` file by the walk): frame `0xb0`, stack chunks
`fp s1 s2 l112 l128 l24 t64 t48 l136 l120 l32 t96 t80 rslot`. -/
def Encode.generated_layout : EncoderFrameLayout where
  stateWord := true
  frame := 176
  guardAddend := 56
  callsMemmove := true
  stackChunkCount := 14
  stackChunkLengths := [(0, 8), (1, 8), (2, 8), (3, 8), (4, 8), (5, 8), (6, 16), (7, 16), (8, 8), (9, 8), (10, 8), (11, 16), (12, 16), (13, 8)]
  pre := [.at (.below 8) (.original 0), .at (.above 8) (.original 1), .at (.above 16) (.original 2), .at (.below 112) (.original 3), .at (.below 128) (.original 4), .at (.below 24) (.original 5), .at (.below 64) (.original 6), .at (.below 48) (.original 7), .at (.below 136) (.original 8), .at (.below 120) (.original 9), .at (.below 32) (.original 10), .at (.below 96) (.original 11), .at (.below 80) (.original 12), .at (.below 192) (.original 13), .low .scratch]
  existentials := [.low, .fixed 8, .fixed 16, .fixed 8, .fixed 16]
  post := [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 112) (.reg .rdi), .at (.below 128) (.len 36), .at (.below 24) (.reg .rbx), .at (.below 64) (.field 2), .at (.below 56) (.existential 1), .at (.below 48) (.existential 2), .at (.below 136) (.len 76), .at (.below 120) (.reg .rdi), .at (.below 32) (.reg .rbx), .at (.below 96) (.field 4), .at (.below 88) (.existential 3), .at (.below 80) (.existential 4), .at (.below 192) (.ret 113), .low (.existential 0)]


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Head: directives 0–8 (stack guard, frame, spills); entry → boundary state 0. -/
theorem Encode.generated_head : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 : List UInt8) (hast : ast.length = 8) (hv2 : v2.length = 8) (hv4 : v4.length = 8) (hc0 : c0.length = 8) (hc1 : c1.length = 8) (hc3 : c3.length = 8) (hb0 : b0.length = 4) (hb1 : b1.length = 32) (hb3 : b3.length = 32) (hd0 : d0.length = 4) (hd1 : d1.length = 32) (hd2 : d2.length = 8) (hd3 : d3.length = 32) (hd4 : d4.length = 8)
    (p0 p1 p3 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l112 l128 l24 t64 t48 l136 l120 l32 t96 t80 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl112 : l112.length = 8) (hl128 : l128.length = 8) (hl24 : l24.length = 8) (ht64 : t64.length = 16) (ht48 : t48.length = 16) (hl136 : l136.length = 8) (hl120 : l120.length = 8) (hl32 : l32.length = 8) (ht96 : t96.length = 16) (ht80 : t80.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l112.At (s.regs.rsp.toBitVec - 112))
      ⋆ Eq (l128.At (s.regs.rsp.toBitVec - 128))
      ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (t64.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (t48.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (l136.At (s.regs.rsp.toBitVec - 136))
      ⋆ Eq (l120.At (s.regs.rsp.toBitVec - 120))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (t96.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (t80.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 192))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 192 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 4).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq (v2.At (s.regs.rax.toBitVec + 56))
      ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 72))
      ⋆ Eq (c3.At (s.regs.rax.toBitVec + 80))
      ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
      ⋆ Eq (b0.At p0)
      ⋆ Eq (b1.At p1)
      ⋆ Eq (b3.At p3)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 4))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 36))
      ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 44))
      ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 76))
      ⋆ R)
    (hguard : guard.toNat + 56 < s.regs.rsp.toNat) (hsp : 192 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 84 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 9)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 184 }
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
          ⋆ Eq (l112.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq (l128.At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (t64.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (t48.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (l136.At (s.regs.rsp.toBitVec - 136))
          ⋆ Eq (l120.At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (t96.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (t80.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 192))
          ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 192 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 4).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 4))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 36))
          ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 44))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 76))
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 hast hv2 hv4 hc0 hc1 hc3 hb0 hb1 hb3 hd0 hd1 hd2 hd3 hd4 p0 p1 p3 s ra guard hpre fp s1 s2 l112 l128 l24 t64 t48 l136 l120 l32 t96 t80 rslot hfp hs1 hs2 hl112 hl128 hl24 ht64 ht48 hl136 hl120 hl32 ht96 ht80 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hcap hcap63 hpre ⊢
  have hcap' : rcx.toBitVec.toNat + 84 ≤ rdi.toBitVec.toNat := hcap
  apply encoder_prologue_large_frame _ _ _ (-56) 56 _ k (k + 7) (window_infix_at hk 0 7) (by rfl) (by rfl) (by rfl) guard fp hfp _ _ _ (by dsimp only; ecancel) hguard
  intro m1 H1 fl1; normalize_registers; dsimp only at H1
  apply step_sub_immediate Reg64.rsp 176 _ (k + 7) (k + 8) (window_infix_at hk 7 1) (by rfl) (by rfl)
  intro fl; normalize_registers
  apply register_value_rewrite Reg64.rsp (rsp.toBitVec - 184) _ _ _ (by show ((rsp.toBitVec - 8) - 176 : BitVec 64) = (rsp.toBitVec - 184); bv_omega)
  normalize_registers
  apply step_store Reg64.rbx Reg64.rsp 200 _ (k + 8) (k + 9) (window_infix_at hk 8 1) (by rfl) (by rfl)
    (rsp.toBitVec - 184) (rsp.toBitVec + 16) (by encoder_address_equation) s2 hs2 _ _ _ (by rfl) (by ecancel)
  intro m2 H2; normalize_registers; simp only [Reg64s.get64] at H2
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem Encode.generated_head_kind : ∀ (h : Host), type_of% (@Encode.generated_head h)
    = @Codec.encodeHeadKindAnyFrame h marshalSSZTo Prysm.Status.Encode.generated_layout [.bytes 4, .bytes 32, .uint64, .bytes 32, .uint64]
    ⟨9, 0, [(.rax, .receiver), (.rbx, .ptr), (.rcx, .len 0), (.rdi, .cap)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.original 1), .at (.above 16) (.reg .rbx), .at (.below 112) (.original 3), .at (.below 128) (.original 4), .at (.below 24) (.original 5), .at (.below 64) (.original 6), .at (.below 48) (.original 7), .at (.below 136) (.original 8), .at (.below 120) (.original 9), .at (.below 32) (.original 10), .at (.below 96) (.original 11), .at (.below 80) (.original 12), .at (.below 192) (.original 13), .low .scratch],
      []⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 0 `ForkDigest` (4 bytes): directives 9–33; boundary state 0 → 1. -/
theorem Encode.generated_field_0 : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 : List UInt8) (hast : ast.length = 8) (hv2 : v2.length = 8) (hv4 : v4.length = 8) (hc0 : c0.length = 8) (hc1 : c1.length = 8) (hc3 : c3.length = 8) (hb0 : b0.length = 4) (hb1 : b1.length = 32) (hb3 : b3.length = 32) (hd0 : d0.length = 4) (hd1 : d1.length = 32) (hd2 : d2.length = 8) (hd3 : d3.length = 32) (hd4 : d4.length = 8)
    (p0 p1 p3 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l112 l128 l24 t64 t48 l136 l120 l32 t96 t80 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl112 : l112.length = 8) (hl128 : l128.length = 8) (hl24 : l24.length = 8) (ht64 : t64.length = 16) (ht48 : t48.length = 16) (hl136 : l136.length = 8) (hl120 : l120.length = 8) (hl32 : l32.length = 8) (ht96 : t96.length = 16) (ht80 : t80.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 192 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 84 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 9)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 184 }
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
          ⋆ Eq (l112.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq (l128.At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (t64.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (t48.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (l136.At (s.regs.rsp.toBitVec - 136))
          ⋆ Eq (l120.At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (t96.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (t80.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 192))
          ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 192 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 4).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 4))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 36))
          ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 44))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 76))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 34)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 184 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.get64 Reg64.rax = s.regs.rax.toBitVec
        ∧ st.data.regs.get64 Reg64.rbx = s.regs.rbx.toBitVec
        ∧ st.data.regs.get64 Reg64.rdi = s.regs.rdi.toBitVec
        ∧ st.data.regs.get64 Reg64.r8 = s.regs.rcx.toBitVec + 4 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (l112.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq (l128.At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (t64.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (t48.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (l136.At (s.regs.rsp.toBitVec - 136))
          ⋆ Eq (l120.At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (t96.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (t80.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 192))
          ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 192 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 4).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 4))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 36))
          ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 44))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 76))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 hast hv2 hv4 hc0 hc1 hc3 hb0 hb1 hb3 hd0 hd1 hd2 hd3 hd4 p0 p1 p3 s ra guard hpre fp s1 s2 l112 l128 l24 t64 t48 l136 l120 l32 t96 t80 rslot hfp hs1 hs2 hl112 hl128 hl24 ht64 ht48 hl136 hl120 hl32 ht96 ht80 hrslot R S scratch hsc hsp hcap hcap63 hmm
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
  have hcap' : rcx.toBitVec.toNat + 84 ≤ rdi.toBitVec.toNat := hcap
  apply step_load_value Reg64.rdx Reg64.rax 8 _ (k + 9) (k + 10) (window_infix_at hk 9 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 8) p0 (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_length_check Reg64.rax 16 4 _ _ (k + 10) (k + 12) (window_infix_at hk 10 2) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 16) (by encoder_address_equation) (Int.toBytes 8 4) (by rfl) (by decide) _ _ _ (by rfl) (by ecancel)
  intro fl; normalize_registers
  apply step_store Reg64.rax Reg64.rsp 192 _ (k + 12) (k + 13) (window_infix_at hk 12 1) (by rfl) (by rfl)
    (rsp.toBitVec - 184) (rsp.toBitVec + 8) (by encoder_address_equation) s1 hs1 _ _ _ (by rfl) (by ecancel)
  intro m3 H3; normalize_registers; simp only [Reg64s.get64] at H3
  apply step_lea Reg64.r8 Reg64.rcx 4 _ (k + 13) (k + 14) (window_infix_at hk 13 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.r8 (rcx.toBitVec + 4) _ _ _ (by show (rcx.toBitVec + 4 : BitVec 64) = (rcx.toBitVec + 4); bv_omega)
  normalize_registers
  have hl31 := Machine.label_at' hk hf (j := 31)
    (by simp only [marshalSSZTo, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply step_cmp_jae_taken Reg64.rdi Reg64.r8 _ _ (k + 14) (k + 31) (window_infix_at hk 14 3) (by rfl) hl31 _ _ (by show ((rcx.toBitVec + 4) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; normalize_registers
  apply step_label _ _ (k + 31) (k + 32) (window_infix_at hk 31 1) (by rfl) (by rfl)
  apply step_load_bytes32 Reg64.rdx Reg64.rdx 0 _ (k + 32) (k + 33) (window_infix_at hk 32 1) (by rfl) (by rfl)
    p0 p0 (by encoder_address_equation) b0 hb0 _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_store_indexed32 Reg64.rdx Reg64.rbx Reg64.rcx 0 _ (k + 33) (k + 34) (window_infix_at hk 33 1) (by rfl) (by rfl)
    rbx.toBitVec rcx.toBitVec (rbx.toBitVec + rcx.toBitVec) (by encoder_address_equation) d0 hd0 _ _ _ (by rfl) (by rfl) (by ecancel)
  intro m4 H4; normalize_registers; simp only [Reg64s.get64] at H4
  simp only [Machine.zx32, toBytes_ofInt_ofBytes 32 4 rfl b0 hb0] at H4
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem Encode.generated_field_0_kind : ∀ (h : Host), type_of% (@Encode.generated_field_0 h)
    = @Codec.encodeFieldKindAnyFrame h marshalSSZTo Prysm.Status.Encode.generated_layout [.bytes 4, .bytes 32, .uint64, .bytes 32, .uint64]
    ⟨9, 0, [(.rax, .receiver), (.rbx, .ptr), (.rcx, .len 0), (.rdi, .cap)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.original 1), .at (.above 16) (.reg .rbx), .at (.below 112) (.original 3), .at (.below 128) (.original 4), .at (.below 24) (.original 5), .at (.below 64) (.original 6), .at (.below 48) (.original 7), .at (.below 136) (.original 8), .at (.below 120) (.original 9), .at (.below 32) (.original 10), .at (.below 96) (.original 11), .at (.below 80) (.original 12), .at (.below 192) (.original 13), .low .scratch],
      []⟩
    ⟨34, 1, [(.rax, .receiver), (.rbx, .ptr), (.rdi, .cap), (.r8, .len 4)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 112) (.original 3), .at (.below 128) (.original 4), .at (.below 24) (.original 5), .at (.below 64) (.original 6), .at (.below 48) (.original 7), .at (.below 136) (.original 8), .at (.below 120) (.original 9), .at (.below 32) (.original 10), .at (.below 96) (.original 11), .at (.below 80) (.original 12), .at (.below 192) (.original 13), .low .scratch],
      []⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 1 `FinalizedRoot` (32 bytes): directives 34–61; boundary state 1 → 2. -/
theorem Encode.generated_field_1 : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 : List UInt8) (hast : ast.length = 8) (hv2 : v2.length = 8) (hv4 : v4.length = 8) (hc0 : c0.length = 8) (hc1 : c1.length = 8) (hc3 : c3.length = 8) (hb0 : b0.length = 4) (hb1 : b1.length = 32) (hb3 : b3.length = 32) (hd0 : d0.length = 4) (hd1 : d1.length = 32) (hd2 : d2.length = 8) (hd3 : d3.length = 32) (hd4 : d4.length = 8)
    (p0 p1 p3 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l112 l128 l24 t64 t48 l136 l120 l32 t96 t80 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl112 : l112.length = 8) (hl128 : l128.length = 8) (hl24 : l24.length = 8) (ht64 : t64.length = 16) (ht48 : t48.length = 16) (hl136 : l136.length = 8) (hl120 : l120.length = 8) (hl32 : l32.length = 8) (ht96 : t96.length = 16) (ht80 : t80.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 192 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 84 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 34)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 184 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14
        ∧ st0.data.regs.get64 Reg64.rax = s.regs.rax.toBitVec
        ∧ st0.data.regs.get64 Reg64.rbx = s.regs.rbx.toBitVec
        ∧ st0.data.regs.get64 Reg64.rdi = s.regs.rdi.toBitVec
        ∧ st0.data.regs.get64 Reg64.r8 = s.regs.rcx.toBitVec + 4 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (l112.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq (l128.At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (t64.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (t48.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (l136.At (s.regs.rsp.toBitVec - 136))
          ⋆ Eq (l120.At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (t96.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (t80.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 192))
          ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 192 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 4).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 4))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 36))
          ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 44))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 76))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 62)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 184 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 : List UInt8), x0.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 36).toInt).At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (t64.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (t48.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (l136.At (s.regs.rsp.toBitVec - 136))
          ⋆ Eq (l120.At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (t96.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (t80.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 62)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 192))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 192 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 4).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 4))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 36))
          ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 44))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 76))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 hast hv2 hv4 hc0 hc1 hc3 hb0 hb1 hb3 hd0 hd1 hd2 hd3 hd4 p0 p1 p3 s ra guard hpre fp s1 s2 l112 l128 l24 t64 t48 l136 l120 l32 t96 t80 rslot hfp hs1 hs2 hl112 hl128 hl24 ht64 ht48 hl136 hl120 hl32 ht96 ht80 hrslot R S scratch hsc hsp hcap hcap63 hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hsp hcap hcap63 hpre ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, hrrax, hrrbx, hrrdi, hrr8, Hm⟩
  dsimp only at hpc hrsp hrbp hr14 hrrax hrrbx hrrdi hrr8 Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14 hrrax hrrbx hrrdi hrr8 Hm
  subst rsp1 rbp1 r141
  obtain rfl : rax = rax1 := (UInt64.toBitVec_inj.mp hrrax).symm
  obtain rfl : rbx = rbx1 := (UInt64.toBitVec_inj.mp hrrbx).symm
  obtain rfl : rdi = rdi1 := (UInt64.toBitVec_inj.mp hrrdi).symm
  obtain rfl : r81 = { toBitVec := rcx.toBitVec + 4 } := UInt64.toBitVec_inj.mp hrr8
  have hcap' : rcx.toBitVec.toNat + 84 ≤ rdi.toBitVec.toNat := hcap
  apply step_load_value Reg64.rdx Reg64.rax 32 _ (k + 34) (k + 35) (window_infix_at hk 34 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 32) p1 (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_length_check Reg64.rax 40 32 _ _ (k + 35) (k + 38) (window_infix_at hk 35 3) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 40) (by encoder_address_equation) (Int.toBytes 8 32) (by rfl) (by decide) _ _ _ (by rfl) (by ecancel)
  intro fl; normalize_registers
  apply step_lea Reg64.r9 Reg64.r8 32 _ (k + 38) (k + 39) (window_infix_at hk 38 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.r9 (rcx.toBitVec + 36) _ _ _ (by show ((rcx.toBitVec + 4) + 32 : BitVec 64) = (rcx.toBitVec + 36); bv_omega)
  normalize_registers
  have hl54 := Machine.label_at' hk hf (j := 54)
    (by simp only [marshalSSZTo, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply step_cmp_jae_taken Reg64.rdi Reg64.r9 _ _ (k + 39) (k + 54) (window_infix_at hk 39 2) (by rfl) hl54 _ _ (by show ((rcx.toBitVec + 36) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; normalize_registers
  apply step_label _ _ (k + 54) (k + 55) (window_infix_at hk 54 1) (by rfl) (by rfl)
  apply step_store Reg64.rdi Reg64.rsp 72 _ (k + 55) (k + 56) (window_infix_at hk 55 1) (by rfl) (by rfl)
    (rsp.toBitVec - 184) (rsp.toBitVec - 112) (by encoder_address_equation) l112 hl112 _ _ _ (by rfl) (by ecancel)
  intro m5 H5; normalize_registers; simp only [Reg64s.get64] at H5
  apply step_store Reg64.r9 Reg64.rsp 56 _ (k + 56) (k + 57) (window_infix_at hk 56 1) (by rfl) (by rfl)
    (rsp.toBitVec - 184) (rsp.toBitVec - 128) (by encoder_address_equation) l128 hl128 _ _ _ (by rfl) (by ecancel)
  intro m6 H6; normalize_registers; simp only [Reg64s.get64] at H6
  apply step_store Reg64.rbx Reg64.rsp 160 _ (k + 57) (k + 58) (window_infix_at hk 57 1) (by rfl) (by rfl)
    (rsp.toBitVec - 184) (rsp.toBitVec - 24) (by encoder_address_equation) l24 hl24 _ _ _ (by rfl) (by ecancel)
  intro m7 H7; normalize_registers; simp only [Reg64s.get64] at H7
  apply step_lea_indexed Reg64.rax Reg64.rbx Reg64.r8 _ (k + 58) (k + 59) (window_infix_at hk 58 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.rax (rbx.toBitVec + rcx.toBitVec + 4) _ _ _ (by show (rbx.toBitVec + (rcx.toBitVec + 4) : BitVec 64) = (rbx.toBitVec + rcx.toBitVec + 4); bv_omega)
  normalize_registers
  apply step_move_register Reg64.rbx Reg64.rdx _ (k + 59) (k + 60) (window_infix_at hk 59 1) (by rfl) (by rfl)
  normalize_registers
  apply step_move_immediate Reg64.rcx 32 _ (k + 60) (k + 61) (window_infix_at hk 60 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.rcx 32 _ _ _ (by show (BitVec.zeroExtend 64 (BitVec.truncate 32 (32 : BitVec 64)) : BitVec 64) = 32; decide)
  normalize_registers
  refine eventually_trans _ _ _ _ (encode_memmove_call (k + 61) (window_infix_at hk 61 1) (rsp.toBitVec - 184) (rbx.toBitVec + rcx.toBitVec + 4) p1
    (rsp.toBitVec - 192) (rsp.toBitVec - 192 - BitVec.ofNat 64 S) S (by bv_omega) (Codec.frame_low_address_without_calls rsp.toBitVec 184 192 S (by decide))
    b1 d1 rslot scratch (by rw [hd1, hb1]) hrslot hsc
    _ _ (by rfl) (by rfl) (by rfl) (by rw [hb1]; rfl) (by first | ecancel | (dsimp only; ecancel)) hmm) ?_
  rintro ⟨e1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, scr1, hscr1, Hc1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 Hc1
  subst hpc1
  obtain ⟨⟨raxc1, rbxc1, rcxc1, rdxc1, rsic1, rdic1, rspc1, rbpc1, r8c1, r9c1, r10c1, r11c1, r12c1, r13c1, r14c1, r15c1⟩, zmmsc1, flagsc1, memc1⟩ := e1
  simp only at hrsp1 hrbp1 hr141 Hc1
  subst rspc1 rbpc1 r14c1
  rw [show k + 61 + 1 = k + 62 from rfl] at Hc1
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, scr1, hscr1, ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem Encode.generated_field_1_kind : ∀ (h : Host), type_of% (@Encode.generated_field_1 h)
    = @Codec.encodeFieldKindAnyFrame h marshalSSZTo Prysm.Status.Encode.generated_layout [.bytes 4, .bytes 32, .uint64, .bytes 32, .uint64]
    ⟨34, 1, [(.rax, .receiver), (.rbx, .ptr), (.rdi, .cap), (.r8, .len 4)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 112) (.original 3), .at (.below 128) (.original 4), .at (.below 24) (.original 5), .at (.below 64) (.original 6), .at (.below 48) (.original 7), .at (.below 136) (.original 8), .at (.below 120) (.original 9), .at (.below 32) (.original 10), .at (.below 96) (.original 11), .at (.below 80) (.original 12), .at (.below 192) (.original 13), .low .scratch],
      []⟩
    ⟨62, 2, [],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 112) (.reg .rdi), .at (.below 128) (.len 36), .at (.below 24) (.reg .rbx), .at (.below 64) (.original 6), .at (.below 48) (.original 7), .at (.below 136) (.original 8), .at (.below 120) (.original 9), .at (.below 32) (.original 10), .at (.below 96) (.original 11), .at (.below 80) (.original 12), .at (.below 192) (.ret 62), .low (.existential 0)],
      [.low]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 2 `FinalizedEpoch` (uint64): directives 62–90; boundary state 2 → 3. -/
theorem Encode.generated_field_2 : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 : List UInt8) (hast : ast.length = 8) (hv2 : v2.length = 8) (hv4 : v4.length = 8) (hc0 : c0.length = 8) (hc1 : c1.length = 8) (hc3 : c3.length = 8) (hb0 : b0.length = 4) (hb1 : b1.length = 32) (hb3 : b3.length = 32) (hd0 : d0.length = 4) (hd1 : d1.length = 32) (hd2 : d2.length = 8) (hd3 : d3.length = 32) (hd4 : d4.length = 8)
    (p0 p1 p3 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l112 l128 l24 t64 t48 l136 l120 l32 t96 t80 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl112 : l112.length = 8) (hl128 : l128.length = 8) (hl24 : l24.length = 8) (ht64 : t64.length = 16) (ht48 : t48.length = 16) (hl136 : l136.length = 8) (hl120 : l120.length = 8) (hl32 : l32.length = 8) (ht96 : t96.length = 16) (ht80 : t80.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 192 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 84 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 62)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 184 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 : List UInt8), x0.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 36).toInt).At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (t64.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (t48.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (l136.At (s.regs.rsp.toBitVec - 136))
          ⋆ Eq (l120.At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (t96.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (t80.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 62)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 192))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 192 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 4).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 4))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 36))
          ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 44))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 76))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 91)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 184 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.get64 Reg64.rax = s.regs.rbx.toBitVec
        ∧ st.data.regs.get64 Reg64.rcx = s.regs.rdi.toBitVec
        ∧ st.data.regs.get64 Reg64.rdx = s.regs.rcx.toBitVec + 44
        ∧ st.data.regs.get64 Reg64.rsi = s.regs.rax.toBitVec ∧
        ∃ (x0 x1 x2 : List UInt8), x0.length = S ∧ x1.length = 8 ∧ x2.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 36).toInt).At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (v2.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (l136.At (s.regs.rsp.toBitVec - 136))
          ⋆ Eq (l120.At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (t96.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (t80.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 62)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 192))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 192 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 4).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 4))
          ⋆ Eq (v2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 36))
          ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 44))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 76))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 hast hv2 hv4 hc0 hc1 hc3 hb0 hb1 hb3 hd0 hd1 hd2 hd3 hd4 p0 p1 p3 s ra guard hpre fp s1 s2 l112 l128 l24 t64 t48 l136 l120 l32 t96 t80 rslot hfp hs1 hs2 hl112 hl128 hl24 ht64 ht48 hl136 hl120 hl32 ht96 ht80 hrslot R S scratch hsc hsp hcap hcap63 hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hsp hcap hcap63 hpre ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, x0, hx0, Hm⟩
  dsimp only at hpc hrsp hrbp hr14  Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14  Hm
  subst rsp1 rbp1 r141
  have hcap' : rcx.toBitVec.toNat + 84 ≤ rdi.toBitVec.toNat := hcap
  apply step_load_value Reg64.rbx Reg64.rsp 56 _ (k + 62) (k + 63) (window_infix_at hk 62 1) (by rfl) (by rfl)
    (rsp.toBitVec - 184) (rsp.toBitVec - 128) (rcx.toBitVec + 36) (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_lea Reg64.rdx Reg64.rbx 8 _ (k + 63) (k + 64) (window_infix_at hk 63 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.rdx (rcx.toBitVec + 44) _ _ _ (by show ((rcx.toBitVec + 36) + 8 : BitVec 64) = (rcx.toBitVec + 44); bv_omega)
  normalize_registers
  apply step_load_value Reg64.rsi Reg64.rsp 192 _ (k + 64) (k + 65) (window_infix_at hk 64 1) (by rfl) (by rfl)
    (rsp.toBitVec - 184) (rsp.toBitVec + 8) rax.toBitVec (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_load_bytes Reg64.rdi Reg64.rsi 56 _ (k + 65) (k + 66) (window_infix_at hk 65 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 56) (by encoder_address_equation) v2 hv2 _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_lea Reg64.r8 Reg64.rsp 120 _ (k + 66) (k + 70) (window_infix_at hk 66 4) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.r8 (rsp.toBitVec - 64) _ _ _ (by show ((rsp.toBitVec - 184) + 120 : BitVec 64) = (rsp.toBitVec - 64); bv_omega)
  normalize_registers
  apply step_store_xmm15 Reg64.r8 0 _ (k + 70) (k + 71) (window_infix_at hk 70 1) (by rfl) (by rfl)
    (rsp.toBitVec - 64) (rsp.toBitVec - 64) (by encoder_address_equation) t64 ht64 _ _ _ (by rfl) (by ecancel)
  intro m8 H8; normalize_registers; try dsimp only at H8
  apply step_store_xmm15 Reg64.r8 16 _ (k + 71) (k + 72) (window_infix_at hk 71 1) (by rfl) (by rfl)
    (rsp.toBitVec - 64) (rsp.toBitVec - 48) (by encoder_address_equation) t48 ht48 _ _ _ (by rfl) (by ecancel)
  intro m9 H9; normalize_registers; try dsimp only at H9
  rw [Machine.at_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 64), show (rsp.toBitVec - 64) + 8 = (rsp.toBitVec - 56) by bv_omega] at H9
  apply step_store Reg64.rdi Reg64.rsp 120 _ (k + 72) (k + 73) (window_infix_at hk 72 1) (by rfl) (by rfl)
    (rsp.toBitVec - 184) (rsp.toBitVec - 64) (by encoder_address_equation) ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).take 8) (by rw [List.length_take, Int.toBytes_length]; rfl) _ _ _ (by rfl) (by ecancel)
  intro m10 H10; normalize_registers; simp only [Reg64s.get64] at H10
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v2 hv2] at H10
  apply step_load_value Reg64.rcx Reg64.rsp 72 _ (k + 73) (k + 74) (window_infix_at hk 73 1) (by rfl) (by rfl)
    (rsp.toBitVec - 184) (rsp.toBitVec - 112) rdi.toBitVec (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_cmp_jb_not_taken Reg64.rcx Reg64.rdx _ _ (k + 74) (k + 77) (window_infix_at hk 74 3) (by rfl) (by rfl) _ _ (by show ((rcx.toBitVec + 44) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; normalize_registers
  apply step_load_value Reg64.rax Reg64.rsp 160 _ (k + 77) (k + 78) (window_infix_at hk 77 1) (by rfl) (by rfl)
    (rsp.toBitVec - 184) (rsp.toBitVec - 24) rbx.toBitVec (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  have hl88 := Machine.label_at' hk hf (j := 88)
    (by simp only [marshalSSZTo, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply step_jump _ _ (k + 78) (k + 88) (window_infix_at hk 78 1) (by rfl) hl88
  apply step_label _ _ (k + 88) (k + 89) (window_infix_at hk 88 1) (by rfl) (by rfl)
  apply step_load_bytes Reg64.r8 Reg64.rsp 120 _ (k + 89) (k + 90) (window_infix_at hk 89 1) (by rfl) (by rfl)
    (rsp.toBitVec - 184) (rsp.toBitVec - 64) (by encoder_address_equation) v2 hv2 _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_store_indexed Reg64.r8 Reg64.rax Reg64.rbx 0 _ (k + 90) (k + 91) (window_infix_at hk 90 1) (by rfl) (by rfl)
    rbx.toBitVec (rcx.toBitVec + 36) (rbx.toBitVec + rcx.toBitVec + 36) (by encoder_address_equation) d2 hd2 _ _ _ (by rfl) (by rfl) (by ecancel)
  intro m11 H11; normalize_registers; simp only [Reg64s.get64] at H11
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v2 hv2] at H11
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, x0, ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8), (Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt), hx0, (by rw [List.length_drop, Int.toBytes_length]), (Int.toBytes_length 16 _), ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem Encode.generated_field_2_kind : ∀ (h : Host), type_of% (@Encode.generated_field_2 h)
    = @Codec.encodeFieldKindAnyFrame h marshalSSZTo Prysm.Status.Encode.generated_layout [.bytes 4, .bytes 32, .uint64, .bytes 32, .uint64]
    ⟨62, 2, [],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 112) (.reg .rdi), .at (.below 128) (.len 36), .at (.below 24) (.reg .rbx), .at (.below 64) (.original 6), .at (.below 48) (.original 7), .at (.below 136) (.original 8), .at (.below 120) (.original 9), .at (.below 32) (.original 10), .at (.below 96) (.original 11), .at (.below 80) (.original 12), .at (.below 192) (.ret 62), .low (.existential 0)],
      [.low]⟩
    ⟨91, 3, [(.rax, .ptr), (.rcx, .cap), (.rdx, .len 44), (.rsi, .receiver)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 112) (.reg .rdi), .at (.below 128) (.len 36), .at (.below 24) (.reg .rbx), .at (.below 64) (.field 2), .at (.below 56) (.existential 1), .at (.below 48) (.existential 2), .at (.below 136) (.original 8), .at (.below 120) (.original 9), .at (.below 32) (.original 10), .at (.below 96) (.original 11), .at (.below 80) (.original 12), .at (.below 192) (.ret 62), .low (.existential 0)],
      [.low, .fixed 8, .fixed 16]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 3 `HeadRoot` (32 bytes): directives 91–112; boundary state 3 → 4. -/
theorem Encode.generated_field_3 : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 : List UInt8) (hast : ast.length = 8) (hv2 : v2.length = 8) (hv4 : v4.length = 8) (hc0 : c0.length = 8) (hc1 : c1.length = 8) (hc3 : c3.length = 8) (hb0 : b0.length = 4) (hb1 : b1.length = 32) (hb3 : b3.length = 32) (hd0 : d0.length = 4) (hd1 : d1.length = 32) (hd2 : d2.length = 8) (hd3 : d3.length = 32) (hd4 : d4.length = 8)
    (p0 p1 p3 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l112 l128 l24 t64 t48 l136 l120 l32 t96 t80 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl112 : l112.length = 8) (hl128 : l128.length = 8) (hl24 : l24.length = 8) (ht64 : t64.length = 16) (ht48 : t48.length = 16) (hl136 : l136.length = 8) (hl120 : l120.length = 8) (hl32 : l32.length = 8) (ht96 : t96.length = 16) (ht80 : t80.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 192 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 84 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 91)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 184 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14
        ∧ st0.data.regs.get64 Reg64.rax = s.regs.rbx.toBitVec
        ∧ st0.data.regs.get64 Reg64.rcx = s.regs.rdi.toBitVec
        ∧ st0.data.regs.get64 Reg64.rdx = s.regs.rcx.toBitVec + 44
        ∧ st0.data.regs.get64 Reg64.rsi = s.regs.rax.toBitVec ∧
        ∃ (x0 x1 x2 : List UInt8), x0.length = S ∧ x1.length = 8 ∧ x2.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 36).toInt).At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (v2.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (l136.At (s.regs.rsp.toBitVec - 136))
          ⋆ Eq (l120.At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (t96.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (t80.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 62)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 192))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 192 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 4).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 4))
          ⋆ Eq (v2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 36))
          ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 44))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 76))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 113)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 184 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 x2 : List UInt8), x0.length = S ∧ x1.length = 8 ∧ x2.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 36).toInt).At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (v2.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 76).toInt).At (s.regs.rsp.toBitVec - 136))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (t96.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (t80.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 113)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 192))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 192 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 4).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 4))
          ⋆ Eq (v2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 36))
          ⋆ Eq (b3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 44))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 76))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 hast hv2 hv4 hc0 hc1 hc3 hb0 hb1 hb3 hd0 hd1 hd2 hd3 hd4 p0 p1 p3 s ra guard hpre fp s1 s2 l112 l128 l24 t64 t48 l136 l120 l32 t96 t80 rslot hfp hs1 hs2 hl112 hl128 hl24 ht64 ht48 hl136 hl120 hl32 ht96 ht80 hrslot R S scratch hsc hsp hcap hcap63 hmm
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
  obtain rfl : rdx1 = { toBitVec := rcx.toBitVec + 44 } := UInt64.toBitVec_inj.mp hrrdx
  obtain rfl : rax = rsi1 := (UInt64.toBitVec_inj.mp hrrsi).symm
  have hcap' : rcx.toBitVec.toNat + 84 ≤ rdi.toBitVec.toNat := hcap
  apply step_load_value Reg64.rbx Reg64.rsi 64 _ (k + 91) (k + 92) (window_infix_at hk 91 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 64) p3 (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_length_check Reg64.rsi 72 32 _ _ (k + 92) (k + 94) (window_infix_at hk 92 2) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 72) (by encoder_address_equation) (Int.toBytes 8 32) (by rfl) (by decide) _ _ _ (by rfl) (by ecancel)
  intro fl; normalize_registers
  apply step_lea Reg64.r8 Reg64.rdx 32 _ (k + 94) (k + 95) (window_infix_at hk 94 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.r8 (rcx.toBitVec + 76) _ _ _ (by show ((rcx.toBitVec + 44) + 32 : BitVec 64) = (rcx.toBitVec + 76); bv_omega)
  normalize_registers
  have hl106 := Machine.label_at' hk hf (j := 106)
    (by simp only [marshalSSZTo, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply step_cmp_jae_taken Reg64.rcx Reg64.r8 _ _ (k + 95) (k + 106) (window_infix_at hk 95 2) (by rfl) hl106 _ _ (by show ((rcx.toBitVec + 76) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; normalize_registers
  apply step_label _ _ (k + 106) (k + 107) (window_infix_at hk 106 1) (by rfl) (by rfl)
  apply step_store Reg64.r8 Reg64.rsp 48 _ (k + 107) (k + 108) (window_infix_at hk 107 1) (by rfl) (by rfl)
    (rsp.toBitVec - 184) (rsp.toBitVec - 136) (by encoder_address_equation) l136 hl136 _ _ _ (by rfl) (by ecancel)
  intro m12 H12; normalize_registers; simp only [Reg64s.get64] at H12
  apply step_store Reg64.rcx Reg64.rsp 64 _ (k + 108) (k + 109) (window_infix_at hk 108 1) (by rfl) (by rfl)
    (rsp.toBitVec - 184) (rsp.toBitVec - 120) (by encoder_address_equation) l120 hl120 _ _ _ (by rfl) (by ecancel)
  intro m13 H13; normalize_registers; simp only [Reg64s.get64] at H13
  apply step_store Reg64.rax Reg64.rsp 152 _ (k + 109) (k + 110) (window_infix_at hk 109 1) (by rfl) (by rfl)
    (rsp.toBitVec - 184) (rsp.toBitVec - 32) (by encoder_address_equation) l32 hl32 _ _ _ (by rfl) (by ecancel)
  intro m14 H14; normalize_registers; simp only [Reg64s.get64] at H14
  apply step_add_registers Reg64.rax Reg64.rdx _ (k + 110) (k + 111) (window_infix_at hk 110 1) (by rfl) (by rfl)
  intro fl; normalize_registers
  apply register_value_rewrite Reg64.rax (rbx.toBitVec + rcx.toBitVec + 44) _ _ _ (by show (rbx.toBitVec + (rcx.toBitVec + 44) : BitVec 64) = (rbx.toBitVec + rcx.toBitVec + 44); bv_omega)
  normalize_registers
  apply step_move_immediate Reg64.rcx 32 _ (k + 111) (k + 112) (window_infix_at hk 111 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.rcx 32 _ _ _ (by show (BitVec.zeroExtend 64 (BitVec.truncate 32 (32 : BitVec 64)) : BitVec 64) = 32; decide)
  normalize_registers
  refine eventually_trans _ _ _ _ (encode_memmove_call (k + 112) (window_infix_at hk 112 1) (rsp.toBitVec - 184) (rbx.toBitVec + rcx.toBitVec + 44) p3
    (rsp.toBitVec - 192) (rsp.toBitVec - 192 - BitVec.ofNat 64 S) S (by bv_omega) (Codec.frame_low_address_without_calls rsp.toBitVec 184 192 S (by decide))
    b3 d3 (Int.toBytes 8 (Host.addrOf (k + 62)).toBitVec.toInt) x0 (by rw [hd3, hb3]) (Int.toBytes_length 8 _) hx0
    _ _ (by rfl) (by rfl) (by rfl) (by rw [hb3]; rfl) (by first | ecancel | (dsimp only; ecancel)) hmm) ?_
  rintro ⟨e2, pc2⟩ ⟨hpc2, hrsp2, hrbp2, hr142, scr2, hscr2, Hc2⟩
  dsimp only at hpc2 hrsp2 hrbp2 hr142 Hc2
  subst hpc2
  obtain ⟨⟨raxc2, rbxc2, rcxc2, rdxc2, rsic2, rdic2, rspc2, rbpc2, r8c2, r9c2, r10c2, r11c2, r12c2, r13c2, r14c2, r15c2⟩, zmmsc2, flagsc2, memc2⟩ := e2
  simp only at hrsp2 hrbp2 hr142 Hc2
  subst rspc2 rbpc2 r14c2
  rw [show k + 112 + 1 = k + 113 from rfl] at Hc2
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, scr2, x1, x2, hscr2, hx1, hx2, ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem Encode.generated_field_3_kind : ∀ (h : Host), type_of% (@Encode.generated_field_3 h)
    = @Codec.encodeFieldKindAnyFrame h marshalSSZTo Prysm.Status.Encode.generated_layout [.bytes 4, .bytes 32, .uint64, .bytes 32, .uint64]
    ⟨91, 3, [(.rax, .ptr), (.rcx, .cap), (.rdx, .len 44), (.rsi, .receiver)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 112) (.reg .rdi), .at (.below 128) (.len 36), .at (.below 24) (.reg .rbx), .at (.below 64) (.field 2), .at (.below 56) (.existential 1), .at (.below 48) (.existential 2), .at (.below 136) (.original 8), .at (.below 120) (.original 9), .at (.below 32) (.original 10), .at (.below 96) (.original 11), .at (.below 80) (.original 12), .at (.below 192) (.ret 62), .low (.existential 0)],
      [.low, .fixed 8, .fixed 16]⟩
    ⟨113, 4, [],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 112) (.reg .rdi), .at (.below 128) (.len 36), .at (.below 24) (.reg .rbx), .at (.below 64) (.field 2), .at (.below 56) (.existential 1), .at (.below 48) (.existential 2), .at (.below 136) (.len 76), .at (.below 120) (.reg .rdi), .at (.below 32) (.reg .rbx), .at (.below 96) (.original 11), .at (.below 80) (.original 12), .at (.below 192) (.ret 113), .low (.existential 0)],
      [.low, .fixed 8, .fixed 16]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 4 `HeadSlot` (uint64): directives 113–140; boundary state 4 → 5. -/
theorem Encode.generated_field_4 : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 : List UInt8) (hast : ast.length = 8) (hv2 : v2.length = 8) (hv4 : v4.length = 8) (hc0 : c0.length = 8) (hc1 : c1.length = 8) (hc3 : c3.length = 8) (hb0 : b0.length = 4) (hb1 : b1.length = 32) (hb3 : b3.length = 32) (hd0 : d0.length = 4) (hd1 : d1.length = 32) (hd2 : d2.length = 8) (hd3 : d3.length = 32) (hd4 : d4.length = 8)
    (p0 p1 p3 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l112 l128 l24 t64 t48 l136 l120 l32 t96 t80 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl112 : l112.length = 8) (hl128 : l128.length = 8) (hl24 : l24.length = 8) (ht64 : t64.length = 16) (ht48 : t48.length = 16) (hl136 : l136.length = 8) (hl120 : l120.length = 8) (hl32 : l32.length = 8) (ht96 : t96.length = 16) (ht80 : t80.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 192 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 84 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 113)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 184 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 x2 : List UInt8), x0.length = S ∧ x1.length = 8 ∧ x2.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 36).toInt).At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (v2.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 76).toInt).At (s.regs.rsp.toBitVec - 136))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (t96.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (t80.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 113)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 192))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 192 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 4).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 4))
          ⋆ Eq (v2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 36))
          ⋆ Eq (b3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 44))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 76))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 141)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 184 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.get64 Reg64.rax = s.regs.rbx.toBitVec
        ∧ st.data.regs.get64 Reg64.rcx = s.regs.rdi.toBitVec
        ∧ st.data.regs.get64 Reg64.rdx = s.regs.rcx.toBitVec + 84 ∧
        ∃ (x0 x1 x2 x3 x4 : List UInt8), x0.length = S ∧ x1.length = 8 ∧ x2.length = 16 ∧ x3.length = 8 ∧ x4.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 36).toInt).At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (v2.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 76).toInt).At (s.regs.rsp.toBitVec - 136))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (v4.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (x4.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 113)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 192))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 192 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 4).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 4))
          ⋆ Eq (v2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 36))
          ⋆ Eq (b3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 44))
          ⋆ Eq (v4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 76))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 hast hv2 hv4 hc0 hc1 hc3 hb0 hb1 hb3 hd0 hd1 hd2 hd3 hd4 p0 p1 p3 s ra guard hpre fp s1 s2 l112 l128 l24 t64 t48 l136 l120 l32 t96 t80 rslot hfp hs1 hs2 hl112 hl128 hl24 ht64 ht48 hl136 hl120 hl32 ht96 ht80 hrslot R S scratch hsc hsp hcap hcap63 hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hsp hcap hcap63 hpre ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, x0, x1, x2, hx0, hx1, hx2, Hm⟩
  dsimp only at hpc hrsp hrbp hr14  Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14  Hm
  subst rsp1 rbp1 r141
  have hcap' : rcx.toBitVec.toNat + 84 ≤ rdi.toBitVec.toNat := hcap
  apply step_load_value Reg64.rbx Reg64.rsp 48 _ (k + 113) (k + 114) (window_infix_at hk 113 1) (by rfl) (by rfl)
    (rsp.toBitVec - 184) (rsp.toBitVec - 136) (rcx.toBitVec + 76) (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_lea Reg64.rdx Reg64.rbx 8 _ (k + 114) (k + 115) (window_infix_at hk 114 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.rdx (rcx.toBitVec + 84) _ _ _ (by show ((rcx.toBitVec + 76) + 8 : BitVec 64) = (rcx.toBitVec + 84); bv_omega)
  normalize_registers
  apply step_load_value Reg64.rsi Reg64.rsp 192 _ (k + 115) (k + 116) (window_infix_at hk 115 1) (by rfl) (by rfl)
    (rsp.toBitVec - 184) (rsp.toBitVec + 8) rax.toBitVec (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_load_bytes Reg64.rsi Reg64.rsi 88 _ (k + 116) (k + 117) (window_infix_at hk 116 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 88) (by encoder_address_equation) v4 hv4 _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_lea Reg64.rdi Reg64.rsp 88 _ (k + 117) (k + 121) (window_infix_at hk 117 4) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.rdi (rsp.toBitVec - 96) _ _ _ (by show ((rsp.toBitVec - 184) + 88 : BitVec 64) = (rsp.toBitVec - 96); bv_omega)
  normalize_registers
  apply step_store_xmm15 Reg64.rdi 0 _ (k + 121) (k + 122) (window_infix_at hk 121 1) (by rfl) (by rfl)
    (rsp.toBitVec - 96) (rsp.toBitVec - 96) (by encoder_address_equation) t96 ht96 _ _ _ (by rfl) (by ecancel)
  intro m15 H15; normalize_registers; try dsimp only at H15
  apply step_store_xmm15 Reg64.rdi 16 _ (k + 122) (k + 123) (window_infix_at hk 122 1) (by rfl) (by rfl)
    (rsp.toBitVec - 96) (rsp.toBitVec - 80) (by encoder_address_equation) t80 ht80 _ _ _ (by rfl) (by ecancel)
  intro m16 H16; normalize_registers; try dsimp only at H16
  rw [Machine.at_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 96), show (rsp.toBitVec - 96) + 8 = (rsp.toBitVec - 88) by bv_omega] at H16
  apply step_store Reg64.rsi Reg64.rsp 88 _ (k + 123) (k + 124) (window_infix_at hk 123 1) (by rfl) (by rfl)
    (rsp.toBitVec - 184) (rsp.toBitVec - 96) (by encoder_address_equation) ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).take 8) (by rw [List.length_take, Int.toBytes_length]; rfl) _ _ _ (by rfl) (by ecancel)
  intro m17 H17; normalize_registers; simp only [Reg64s.get64] at H17
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v4 hv4] at H17
  apply step_load_value Reg64.rcx Reg64.rsp 64 _ (k + 124) (k + 125) (window_infix_at hk 124 1) (by rfl) (by rfl)
    (rsp.toBitVec - 184) (rsp.toBitVec - 120) rdi.toBitVec (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_cmp_jb_not_taken Reg64.rcx Reg64.rdx _ _ (k + 125) (k + 128) (window_infix_at hk 125 3) (by rfl) (by rfl) _ _ (by show ((rcx.toBitVec + 84) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; normalize_registers
  apply step_load_value Reg64.rax Reg64.rsp 152 _ (k + 128) (k + 129) (window_infix_at hk 128 1) (by rfl) (by rfl)
    (rsp.toBitVec - 184) (rsp.toBitVec - 32) rbx.toBitVec (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  have hl138 := Machine.label_at' hk hf (j := 138)
    (by simp only [marshalSSZTo, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply step_jump _ _ (k + 129) (k + 138) (window_infix_at hk 129 1) (by rfl) hl138
  apply step_label _ _ (k + 138) (k + 139) (window_infix_at hk 138 1) (by rfl) (by rfl)
  apply step_load_bytes Reg64.r8 Reg64.rsp 88 _ (k + 139) (k + 140) (window_infix_at hk 139 1) (by rfl) (by rfl)
    (rsp.toBitVec - 184) (rsp.toBitVec - 96) (by encoder_address_equation) v4 hv4 _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_store_indexed Reg64.r8 Reg64.rax Reg64.rbx 0 _ (k + 140) (k + 141) (window_infix_at hk 140 1) (by rfl) (by rfl)
    rbx.toBitVec (rcx.toBitVec + 76) (rbx.toBitVec + rcx.toBitVec + 76) (by encoder_address_equation) d4 hd4 _ _ _ (by rfl) (by rfl) (by ecancel)
  intro m18 H18; normalize_registers; simp only [Reg64s.get64] at H18
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v4 hv4] at H18
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, x0, x1, x2, ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8), (Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt), hx0, hx1, hx2, (by rw [List.length_drop, Int.toBytes_length]), (Int.toBytes_length 16 _), ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem Encode.generated_field_4_kind : ∀ (h : Host), type_of% (@Encode.generated_field_4 h)
    = @Codec.encodeFieldKindAnyFrame h marshalSSZTo Prysm.Status.Encode.generated_layout [.bytes 4, .bytes 32, .uint64, .bytes 32, .uint64]
    ⟨113, 4, [],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 112) (.reg .rdi), .at (.below 128) (.len 36), .at (.below 24) (.reg .rbx), .at (.below 64) (.field 2), .at (.below 56) (.existential 1), .at (.below 48) (.existential 2), .at (.below 136) (.len 76), .at (.below 120) (.reg .rdi), .at (.below 32) (.reg .rbx), .at (.below 96) (.original 11), .at (.below 80) (.original 12), .at (.below 192) (.ret 113), .low (.existential 0)],
      [.low, .fixed 8, .fixed 16]⟩
    ⟨141, 5, [(.rax, .ptr), (.rcx, .cap), (.rdx, .len 84)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 112) (.reg .rdi), .at (.below 128) (.len 36), .at (.below 24) (.reg .rbx), .at (.below 64) (.field 2), .at (.below 56) (.existential 1), .at (.below 48) (.existential 2), .at (.below 136) (.len 76), .at (.below 120) (.reg .rdi), .at (.below 32) (.reg .rbx), .at (.below 96) (.field 4), .at (.below 88) (.existential 3), .at (.below 80) (.existential 4), .at (.below 192) (.ret 113), .low (.existential 0)],
      [.low, .fixed 8, .fixed 16, .fixed 8, .fixed 16]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Epilogue: directives 141–return; boundary state 5 → the fast-path post-state. -/
theorem Encode.generated_epilogue : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 : List UInt8) (hast : ast.length = 8) (hv2 : v2.length = 8) (hv4 : v4.length = 8) (hc0 : c0.length = 8) (hc1 : c1.length = 8) (hc3 : c3.length = 8) (hb0 : b0.length = 4) (hb1 : b1.length = 32) (hb3 : b3.length = 32) (hd0 : d0.length = 4) (hd1 : d1.length = 32) (hd2 : d2.length = 8) (hd3 : d3.length = 32) (hd4 : d4.length = 8)
    (p0 p1 p3 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l112 l128 l24 t64 t48 l136 l120 l32 t96 t80 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl112 : l112.length = 8) (hl128 : l128.length = 8) (hl24 : l24.length = 8) (ht64 : t64.length = 16) (ht48 : t48.length = 16) (hl136 : l136.length = 8) (hl120 : l120.length = 8) (hl32 : l32.length = 8) (ht96 : t96.length = 16) (ht80 : t80.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 192 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 84 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 141)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 184 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14
        ∧ st0.data.regs.get64 Reg64.rax = s.regs.rbx.toBitVec
        ∧ st0.data.regs.get64 Reg64.rcx = s.regs.rdi.toBitVec
        ∧ st0.data.regs.get64 Reg64.rdx = s.regs.rcx.toBitVec + 84 ∧
        ∃ (x0 x1 x2 x3 x4 : List UInt8), x0.length = S ∧ x1.length = 8 ∧ x2.length = 16 ∧ x3.length = 8 ∧ x4.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 36).toInt).At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (v2.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 76).toInt).At (s.regs.rsp.toBitVec - 136))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (v4.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (x4.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 113)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 192))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 192 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 4).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 4))
          ⋆ Eq (v2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 36))
          ⋆ Eq (b3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 44))
          ⋆ Eq (v4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 76))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec
        ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 84
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
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 36).toInt).At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (v2.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 76).toInt).At (s.regs.rsp.toBitVec - 136))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (v4.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (x4.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 113)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 192))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 192 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 4).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 4))
          ⋆ Eq (v2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 36))
          ⋆ Eq (b3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 44))
          ⋆ Eq (v4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 76))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 hast hv2 hv4 hc0 hc1 hc3 hb0 hb1 hb3 hd0 hd1 hd2 hd3 hd4 p0 p1 p3 s ra guard hpre fp s1 s2 l112 l128 l24 t64 t48 l136 l120 l32 t96 t80 rslot hfp hs1 hs2 hl112 hl128 hl24 ht64 ht48 hl136 hl120 hl32 ht96 ht80 hrslot R S scratch hsc hsp hcap hcap63
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hsp hcap hcap63 hpre ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, hrrax, hrrcx, hrrdx, x0, x1, x2, x3, x4, hx0, hx1, hx2, hx3, hx4, Hm⟩
  dsimp only at hpc hrsp hrbp hr14 hrrax hrrcx hrrdx Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14 hrrax hrrcx hrrdx Hm
  subst rsp1 rbp1 r141
  obtain rfl : rbx = rax1 := (UInt64.toBitVec_inj.mp hrrax).symm
  obtain rfl : rdi = rcx1 := (UInt64.toBitVec_inj.mp hrrcx).symm
  obtain rfl : rdx1 = { toBitVec := rcx.toBitVec + 84 } := UInt64.toBitVec_inj.mp hrrdx
  have hcap' : rcx.toBitVec.toNat + 84 ≤ rdi.toBitVec.toNat := hcap
  apply step_move_register Reg64.rbx Reg64.rdx _ (k + 141) (k + 142) (window_infix_at hk 141 1) (by rfl) (by rfl)
  normalize_registers
  apply step_xor32 Reg64.rdi _ (k + 142) (k + 143) (window_infix_at hk 142 1) (by rfl) (by rfl)
  intro fl; normalize_registers
  apply step_xor32 Reg64.rsi _ (k + 143) (k + 144) (window_infix_at hk 143 1) (by rfl) (by rfl)
  intro fl; normalize_registers
  apply step_add_immediate Reg64.rsp 176 _ (k + 144) (k + 145) (window_infix_at hk 144 1) (by rfl) (by rfl)
  intro fl; normalize_registers
  apply register_value_rewrite Reg64.rsp (rsp.toBitVec - 8) _ _ _ (by show ((rsp.toBitVec - 184) + 176 : BitVec 64) = (rsp.toBitVec - 8); bv_omega)
  normalize_registers
  refine eventually_trans _ _ _ _ (decode_return_segment _ (k + 145) (window_infix_at hk 145 2) (by rfl) (rsp.toBitVec - 8) rsp.toBitVec (by bv_omega) rbp ra _ _ (by rfl) (by ecancel)) ?_
  rintro ⟨d', pc'⟩ ⟨hpc', hrsp', hrbp', hreg', hmem'⟩
  dsimp only at hpc' hrsp' hrbp' hreg' hmem'
  apply Eventually.done
  refine ⟨hpc', ?_, ?_, ?_, ?_, ?_, ?_, hrbp', ?_, x0, x1, x2, x3, x4, hx0, hx1, hx2, hx3, hx4, ?_⟩
  · exact UInt64.toBitVec_inj.mp (hreg' Reg64.rax (by decide) (by decide))
  · show d'.regs.rbx.toBitVec.toNat = rcx.toBitVec.toNat + 84
    rw [show d'.regs.rbx.toBitVec = rcx.toBitVec + 84 from hreg' Reg64.rbx (by decide) (by decide)]
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
    = @Codec.encodeEpilogueKindAnyFrame h marshalSSZTo Prysm.Status.Encode.generated_layout [.bytes 4, .bytes 32, .uint64, .bytes 32, .uint64]
    ⟨141, 5, [(.rax, .ptr), (.rcx, .cap), (.rdx, .len 84)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 112) (.reg .rdi), .at (.below 128) (.len 36), .at (.below 24) (.reg .rbx), .at (.below 64) (.field 2), .at (.below 56) (.existential 1), .at (.below 48) (.existential 2), .at (.below 136) (.len 76), .at (.below 120) (.reg .rdi), .at (.below 32) (.reg .rbx), .at (.below 96) (.field 4), .at (.below 88) (.existential 3), .at (.below 80) (.existential 4), .at (.below 192) (.ret 113), .low (.existential 0)],
      [.low, .fixed 8, .fixed 16, .fixed 8, .fixed 16]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Encoder fast path of `(*v1alpha1.Status).MarshalSSZTo` (Go 1.26.10), generated** (`encoder --fast-path`):
head, one theorem per field, epilogue, chained by `eventually_trans`. Premises: `len + 84 ≤ cap`,
every byte-vector field of its exact length. Statement = the kind instance (`_kind`). Fast path only. -/
theorem Encode.generated_fast : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 : List UInt8) (hast : ast.length = 8) (hv2 : v2.length = 8) (hv4 : v4.length = 8) (hc0 : c0.length = 8) (hc1 : c1.length = 8) (hc3 : c3.length = 8) (hb0 : b0.length = 4) (hb1 : b1.length = 32) (hb3 : b3.length = 32) (hd0 : d0.length = 4) (hd1 : d1.length = 32) (hd2 : d2.length = 8) (hd3 : d3.length = 32) (hd4 : d4.length = 8)
    (p0 p1 p3 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l112 l128 l24 t64 t48 l136 l120 l32 t96 t80 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl112 : l112.length = 8) (hl128 : l128.length = 8) (hl24 : l24.length = 8) (ht64 : t64.length = 16) (ht48 : t48.length = 16) (hl136 : l136.length = 8) (hl120 : l120.length = 8) (hl32 : l32.length = 8) (ht96 : t96.length = 16) (ht80 : t80.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l112.At (s.regs.rsp.toBitVec - 112))
      ⋆ Eq (l128.At (s.regs.rsp.toBitVec - 128))
      ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (t64.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (t48.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (l136.At (s.regs.rsp.toBitVec - 136))
      ⋆ Eq (l120.At (s.regs.rsp.toBitVec - 120))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (t96.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (t80.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 192))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 192 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 4).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq (v2.At (s.regs.rax.toBitVec + 56))
      ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 72))
      ⋆ Eq (c3.At (s.regs.rax.toBitVec + 80))
      ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
      ⋆ Eq (b0.At p0)
      ⋆ Eq (b1.At p1)
      ⋆ Eq (b3.At p3)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 4))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 36))
      ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 44))
      ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 76))
      ⋆ R)
    (hguard : guard.toNat + 56 < s.regs.rsp.toNat) (hsp : 192 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 84 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec
        ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 84
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
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 36).toInt).At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (v2.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 76).toInt).At (s.regs.rsp.toBitVec - 136))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (v4.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (x4.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 113)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 192))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 192 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 4).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 4))
          ⋆ Eq (v2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 36))
          ⋆ Eq (b3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 44))
          ⋆ Eq (v4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 76))
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 hast hv2 hv4 hc0 hc1 hc3 hb0 hb1 hb3 hd0 hd1 hd2 hd3 hd4 p0 p1 p3 s ra guard hpre fp s1 s2 l112 l128 l24 t64 t48 l136 l120 l32 t96 t80 rslot hfp hs1 hs2 hl112 hl128 hl24 ht64 ht48 hl136 hl120 hl32 ht96 ht80 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm
  refine eventually_trans _ _ _ _ (Encode.generated_head k hk hf ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 hast hv2 hv4 hc0 hc1 hc3 hb0 hb1 hb3 hd0 hd1 hd2 hd3 hd4 p0 p1 p3 s ra guard hpre fp s1 s2 l112 l128 l24 t64 t48 l136 l120 l32 t96 t80 rslot hfp hs1 hs2 hl112 hl128 hl24 ht64 ht48 hl136 hl120 hl32 ht96 ht80 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm) ?_
  intro st0 h0
  refine eventually_trans _ _ _ _ (Encode.generated_field_0 k hk hf ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 hast hv2 hv4 hc0 hc1 hc3 hb0 hb1 hb3 hd0 hd1 hd2 hd3 hd4 p0 p1 p3 s ra guard hpre fp s1 s2 l112 l128 l24 t64 t48 l136 l120 l32 t96 t80 rslot hfp hs1 hs2 hl112 hl128 hl24 ht64 ht48 hl136 hl120 hl32 ht96 ht80 hrslot R S scratch hsc hsp hcap hcap63 hmm st0 h0) ?_
  intro st1 h1
  refine eventually_trans _ _ _ _ (Encode.generated_field_1 k hk hf ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 hast hv2 hv4 hc0 hc1 hc3 hb0 hb1 hb3 hd0 hd1 hd2 hd3 hd4 p0 p1 p3 s ra guard hpre fp s1 s2 l112 l128 l24 t64 t48 l136 l120 l32 t96 t80 rslot hfp hs1 hs2 hl112 hl128 hl24 ht64 ht48 hl136 hl120 hl32 ht96 ht80 hrslot R S scratch hsc hsp hcap hcap63 hmm st1 h1) ?_
  intro st2 h2
  refine eventually_trans _ _ _ _ (Encode.generated_field_2 k hk hf ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 hast hv2 hv4 hc0 hc1 hc3 hb0 hb1 hb3 hd0 hd1 hd2 hd3 hd4 p0 p1 p3 s ra guard hpre fp s1 s2 l112 l128 l24 t64 t48 l136 l120 l32 t96 t80 rslot hfp hs1 hs2 hl112 hl128 hl24 ht64 ht48 hl136 hl120 hl32 ht96 ht80 hrslot R S scratch hsc hsp hcap hcap63 hmm st2 h2) ?_
  intro st3 h3
  refine eventually_trans _ _ _ _ (Encode.generated_field_3 k hk hf ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 hast hv2 hv4 hc0 hc1 hc3 hb0 hb1 hb3 hd0 hd1 hd2 hd3 hd4 p0 p1 p3 s ra guard hpre fp s1 s2 l112 l128 l24 t64 t48 l136 l120 l32 t96 t80 rslot hfp hs1 hs2 hl112 hl128 hl24 ht64 ht48 hl136 hl120 hl32 ht96 ht80 hrslot R S scratch hsc hsp hcap hcap63 hmm st3 h3) ?_
  intro st4 h4
  refine eventually_trans _ _ _ _ (Encode.generated_field_4 k hk hf ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 hast hv2 hv4 hc0 hc1 hc3 hb0 hb1 hb3 hd0 hd1 hd2 hd3 hd4 p0 p1 p3 s ra guard hpre fp s1 s2 l112 l128 l24 t64 t48 l136 l120 l32 t96 t80 rslot hfp hs1 hs2 hl112 hl128 hl24 ht64 ht48 hl136 hl120 hl32 ht96 ht80 hrslot R S scratch hsc hsp hcap hcap63 hmm st4 h4) ?_
  intro st5 h5
  exact Encode.generated_epilogue k hk hf ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 hast hv2 hv4 hc0 hc1 hc3 hb0 hb1 hb3 hd0 hd1 hd2 hd3 hd4 p0 p1 p3 s ra guard hpre fp s1 s2 l112 l128 l24 t64 t48 l136 l120 l32 t96 t80 rslot hfp hs1 hs2 hl112 hl128 hl24 ht64 ht48 hl136 hl120 hl32 ht96 ht80 hrslot R S scratch hsc hsp hcap hcap63 st5 h5
theorem Encode.generated_fast_kind : ∀ (h : Host), type_of% (@Encode.generated_fast h)
    = @Codec.encodeFastPathKindAnyFrame h marshalSSZTo Prysm.Status.Encode.generated_layout [.bytes 4, .bytes 32, .uint64, .bytes 32, .uint64] := by
  intro h; rfl

end Prysm.Status
