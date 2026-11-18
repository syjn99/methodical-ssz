import Codec.Kind.EncodeFastPathAnyFrame
import Codec.EncodeFrameTest
import Codec.EncodeInlineCopy
import Prysm.Builder.Code

/-!
# Fast path (`encoder --fast-path`): encoder fast path of `(*v1alpha1.Builder).MarshalSSZTo`

Generated from the `.S` file and the IR: a symbolic dataflow walk of the fast path, one application of a
step lemma per directive (windows with the nops erased), boundary states between the fields. Every theorem
has a `_kind` line (`encodeHeadKindAnyFrame`, `encodeFieldKindAnyFrame`, `encodeEpilogueKindAnyFrame`, `encodeFastPathKindAnyFrame`).
**Fast path only**: `len(dst) + 93 ≤ cap(dst)` and every byte-vector field of its exact length. No
`runtime.growslice` directive is stepped: each capacity test is decided from the premise. Not covered: the
growslice branches, the length rejects, the morestack path. Not a complete encoder result.
FAST-PATH-JSON: {"type": "Builder", "const": "marshalSSZTo", "prefix": "Encode.generated", "size": 93, "frame": 208, "guard_addend": 88, "runtime_calls": true, "fields": [["Pubkey", "b", 48], ["Version", "b", 1], ["ExecutionAddress", "b", 20], ["Balance", "u", 8], ["DepositEpoch", "u", 8], ["WithdrawableEpoch", "u", 8]], "boundaries": [9, 38, 64, 87, 115, 135, 157], "layout": "Prysm.Builder.Encode.generated_layout", "assembly_sha256": "856d5e8ad61bceaf2398db9da9014c3d3189a7a322e7812a833d00345754b997", "ir_sha256": "59b783f53a4aef9ca94860df8776154d571310937304ba29b9329ce80c7a29b0", "statement_check": "kind instance only", "assembly": "prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo.S", "ir": "prysm/ir/ir-mainnet.json", "ir_type": "v1alpha1.Builder", "kinds": [{"theorem": "Encode.generated_head", "kind": "encodeHeadKindAnyFrame"}, {"theorem": "Encode.generated_field_0", "kind": "encodeFieldKindAnyFrame"}, {"theorem": "Encode.generated_field_1", "kind": "encodeFieldKindAnyFrame"}, {"theorem": "Encode.generated_field_2", "kind": "encodeFieldKindAnyFrame"}, {"theorem": "Encode.generated_field_3", "kind": "encodeFieldKindAnyFrame"}, {"theorem": "Encode.generated_field_4", "kind": "encodeFieldKindAnyFrame"}, {"theorem": "Encode.generated_field_5", "kind": "encodeFieldKindAnyFrame"}, {"theorem": "Encode.generated_epilogue", "kind": "encodeEpilogueKindAnyFrame"}, {"theorem": "Encode.generated_fast", "kind": "encodeFastPathKindAnyFrame"}]}
-/

open Machine Runtime Codec Prysm.Builder.Code
variable [Host]

namespace Prysm.Builder

/-- The frame facts of `marshalSSZTo` (read from the `.S` file by the walk): frame `0xd0`, stack chunks
`fp s1 s2 l136 l144 l16 l152 l160 l32 t64 t48 t96 t80 t128 t112 rslot`. -/
def Encode.generated_layout : EncoderFrameLayout where
  stateWord := true
  frame := 208
  guardAddend := 88
  callsMemmove := true
  stackChunkCount := 16
  stackChunkLengths := [(0, 8), (1, 8), (2, 8), (3, 8), (4, 8), (5, 8), (6, 8), (7, 8), (8, 8), (9, 16), (10, 16), (11, 16), (12, 16), (13, 16), (14, 16), (15, 8)]
  pre := [.at (.below 8) (.original 0), .at (.above 8) (.original 1), .at (.above 16) (.original 2), .at (.below 136) (.original 3), .at (.below 144) (.original 4), .at (.below 16) (.original 5), .at (.below 152) (.original 6), .at (.below 160) (.original 7), .at (.below 32) (.original 8), .at (.below 64) (.original 9), .at (.below 48) (.original 10), .at (.below 96) (.original 11), .at (.below 80) (.original 12), .at (.below 128) (.original 13), .at (.below 112) (.original 14), .at (.below 224) (.original 15), .low .scratch]
  existentials := [.low, .fixed 8, .fixed 16, .fixed 8, .fixed 16, .fixed 8, .fixed 16]
  post := [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 136) (.reg .rdi), .at (.below 144) (.len 48), .at (.below 16) (.reg .rbx), .at (.below 152) (.reg .rdi), .at (.below 160) (.len 69), .at (.below 32) (.reg .rbx), .at (.below 64) (.field 3), .at (.below 56) (.existential 1), .at (.below 48) (.existential 2), .at (.below 96) (.field 4), .at (.below 88) (.existential 3), .at (.below 80) (.existential 4), .at (.below 128) (.field 5), .at (.below 120) (.existential 5), .at (.below 112) (.existential 6), .at (.below 224) (.ret 87), .low (.existential 0)]


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Head: directives 0–8 (stack guard, frame, spills); entry → boundary state 0. -/
theorem Encode.generated_head : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v3 v4 v5 c0 c1 c2 b0 b1 b2 pre d0 d1 d2 d3 d4 d5 : List UInt8) (hast : ast.length = 8) (hv3 : v3.length = 8) (hv4 : v4.length = 8) (hv5 : v5.length = 8) (hc0 : c0.length = 8) (hc1 : c1.length = 8) (hc2 : c2.length = 8) (hb0 : b0.length = 48) (hb1 : b1.length = 1) (hb2 : b2.length = 20) (hd0 : d0.length = 48) (hd1 : d1.length = 1) (hd2 : d2.length = 20) (hd3 : d3.length = 8) (hd4 : d4.length = 8) (hd5 : d5.length = 8)
    (p0 p1 p2 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l136 l144 l16 l152 l160 l32 t64 t48 t96 t80 t128 t112 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl136 : l136.length = 8) (hl144 : l144.length = 8) (hl16 : l16.length = 8) (hl152 : l152.length = 8) (hl160 : l160.length = 8) (hl32 : l32.length = 8) (ht64 : t64.length = 16) (ht48 : t48.length = 16) (ht96 : t96.length = 16) (ht80 : t80.length = 16) (ht128 : t128.length = 16) (ht112 : t112.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l136.At (s.regs.rsp.toBitVec - 136))
      ⋆ Eq (l144.At (s.regs.rsp.toBitVec - 144))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (l152.At (s.regs.rsp.toBitVec - 152))
      ⋆ Eq (l160.At (s.regs.rsp.toBitVec - 160))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (t64.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (t48.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (t96.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (t80.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (t128.At (s.regs.rsp.toBitVec - 128))
      ⋆ Eq (t112.At (s.regs.rsp.toBitVec - 112))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 224))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 224 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
      ⋆ Eq ((Int.toBytes 8 1).At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 56))
      ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 64))
      ⋆ Eq (c2.At (s.regs.rax.toBitVec + 72))
      ⋆ Eq (v3.At (s.regs.rax.toBitVec + 80))
      ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
      ⋆ Eq (v5.At (s.regs.rax.toBitVec + 96))
      ⋆ Eq (b0.At p0)
      ⋆ Eq (b1.At p1)
      ⋆ Eq (b2.At p2)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 49))
      ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 69))
      ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 77))
      ⋆ Eq (d5.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 85))
      ⋆ R)
    (hguard : guard.toNat + 88 < s.regs.rsp.toNat) (hsp : 224 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 93 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 9)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 216 }
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
          ⋆ Eq (l136.At (s.regs.rsp.toBitVec - 136))
          ⋆ Eq (l144.At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq (l152.At (s.regs.rsp.toBitVec - 152))
          ⋆ Eq (l160.At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (t64.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (t48.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (t96.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (t80.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (t128.At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq (t112.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 224))
          ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 224 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 1).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (c2.At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (v3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (v5.At (s.regs.rax.toBitVec + 96))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b2.At p2)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 49))
          ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 69))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 77))
          ⋆ Eq (d5.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 85))
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf ast v3 v4 v5 c0 c1 c2 b0 b1 b2 pre d0 d1 d2 d3 d4 d5 hast hv3 hv4 hv5 hc0 hc1 hc2 hb0 hb1 hb2 hd0 hd1 hd2 hd3 hd4 hd5 p0 p1 p2 s ra guard hpre fp s1 s2 l136 l144 l16 l152 l160 l32 t64 t48 t96 t80 t128 t112 rslot hfp hs1 hs2 hl136 hl144 hl16 hl152 hl160 hl32 ht64 ht48 ht96 ht80 ht128 ht112 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hcap hcap63 hpre ⊢
  have hcap' : rcx.toBitVec.toNat + 93 ≤ rdi.toBitVec.toNat := hcap
  apply encoder_prologue_large_frame _ _ _ (-88) 88 _ k (k + 7) (window_infix_at hk 0 7) (by rfl) (by rfl) (by rfl) guard fp hfp _ _ _ (by dsimp only; ecancel) hguard
  intro m1 H1 fl1; normalize_registers; dsimp only at H1
  apply step_sub_immediate Reg64.rsp 208 _ (k + 7) (k + 8) (window_infix_at hk 7 1) (by rfl) (by rfl)
  intro fl; normalize_registers
  apply register_value_rewrite Reg64.rsp (rsp.toBitVec - 216) _ _ _ (by show ((rsp.toBitVec - 8) - 208 : BitVec 64) = (rsp.toBitVec - 216); bv_omega)
  normalize_registers
  apply step_store Reg64.rbx Reg64.rsp 232 _ (k + 8) (k + 9) (window_infix_at hk 8 1) (by rfl) (by rfl)
    (rsp.toBitVec - 216) (rsp.toBitVec + 16) (by encoder_address_equation) s2 hs2 _ _ _ (by rfl) (by ecancel)
  intro m2 H2; normalize_registers; simp only [Reg64s.get64] at H2
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem Encode.generated_head_kind : ∀ (h : Host), type_of% (@Encode.generated_head h)
    = @Codec.encodeHeadKindAnyFrame h marshalSSZTo Prysm.Builder.Encode.generated_layout [.bytes 48, .bytes 1, .bytes 20, .uint64, .uint64, .uint64]
    ⟨9, 0, [(.rax, .receiver), (.rbx, .ptr), (.rcx, .len 0), (.rdi, .cap)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.original 1), .at (.above 16) (.reg .rbx), .at (.below 136) (.original 3), .at (.below 144) (.original 4), .at (.below 16) (.original 5), .at (.below 152) (.original 6), .at (.below 160) (.original 7), .at (.below 32) (.original 8), .at (.below 64) (.original 9), .at (.below 48) (.original 10), .at (.below 96) (.original 11), .at (.below 80) (.original 12), .at (.below 128) (.original 13), .at (.below 112) (.original 14), .at (.below 224) (.original 15), .low .scratch],
      []⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 0 `Pubkey` (48 bytes): directives 9–37; boundary state 0 → 1. -/
theorem Encode.generated_field_0 : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v3 v4 v5 c0 c1 c2 b0 b1 b2 pre d0 d1 d2 d3 d4 d5 : List UInt8) (hast : ast.length = 8) (hv3 : v3.length = 8) (hv4 : v4.length = 8) (hv5 : v5.length = 8) (hc0 : c0.length = 8) (hc1 : c1.length = 8) (hc2 : c2.length = 8) (hb0 : b0.length = 48) (hb1 : b1.length = 1) (hb2 : b2.length = 20) (hd0 : d0.length = 48) (hd1 : d1.length = 1) (hd2 : d2.length = 20) (hd3 : d3.length = 8) (hd4 : d4.length = 8) (hd5 : d5.length = 8)
    (p0 p1 p2 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l136 l144 l16 l152 l160 l32 t64 t48 t96 t80 t128 t112 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl136 : l136.length = 8) (hl144 : l144.length = 8) (hl16 : l16.length = 8) (hl152 : l152.length = 8) (hl160 : l160.length = 8) (hl32 : l32.length = 8) (ht64 : t64.length = 16) (ht48 : t48.length = 16) (ht96 : t96.length = 16) (ht80 : t80.length = 16) (ht128 : t128.length = 16) (ht112 : t112.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 224 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 93 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 9)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 216 }
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
          ⋆ Eq (l136.At (s.regs.rsp.toBitVec - 136))
          ⋆ Eq (l144.At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq (l152.At (s.regs.rsp.toBitVec - 152))
          ⋆ Eq (l160.At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (t64.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (t48.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (t96.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (t80.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (t128.At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq (t112.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 224))
          ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 224 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 1).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (c2.At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (v3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (v5.At (s.regs.rax.toBitVec + 96))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b2.At p2)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 49))
          ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 69))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 77))
          ⋆ Eq (d5.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 85))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 38)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 216 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 : List UInt8), x0.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 136))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq (l152.At (s.regs.rsp.toBitVec - 152))
          ⋆ Eq (l160.At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (t64.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (t48.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (t96.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (t80.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (t128.At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq (t112.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 38)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 224))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 224 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 1).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (c2.At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (v3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (v5.At (s.regs.rax.toBitVec + 96))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b2.At p2)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 49))
          ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 69))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 77))
          ⋆ Eq (d5.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 85))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v3 v4 v5 c0 c1 c2 b0 b1 b2 pre d0 d1 d2 d3 d4 d5 hast hv3 hv4 hv5 hc0 hc1 hc2 hb0 hb1 hb2 hd0 hd1 hd2 hd3 hd4 hd5 p0 p1 p2 s ra guard hpre fp s1 s2 l136 l144 l16 l152 l160 l32 t64 t48 t96 t80 t128 t112 rslot hfp hs1 hs2 hl136 hl144 hl16 hl152 hl160 hl32 ht64 ht48 ht96 ht80 ht128 ht112 hrslot R S scratch hsc hsp hcap hcap63 hmm
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
  have hcap' : rcx.toBitVec.toNat + 93 ≤ rdi.toBitVec.toNat := hcap
  apply step_load_value Reg64.rdx Reg64.rax 8 _ (k + 9) (k + 10) (window_infix_at hk 9 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 8) p0 (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_length_check Reg64.rax 16 48 _ _ (k + 10) (k + 12) (window_infix_at hk 10 2) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 16) (by encoder_address_equation) (Int.toBytes 8 48) (by rfl) (by decide) _ _ _ (by rfl) (by ecancel)
  intro fl; normalize_registers
  apply step_store Reg64.rax Reg64.rsp 224 _ (k + 12) (k + 13) (window_infix_at hk 12 1) (by rfl) (by rfl)
    (rsp.toBitVec - 216) (rsp.toBitVec + 8) (by encoder_address_equation) s1 hs1 _ _ _ (by rfl) (by ecancel)
  intro m3 H3; normalize_registers; simp only [Reg64s.get64] at H3
  apply step_lea Reg64.r8 Reg64.rcx 48 _ (k + 13) (k + 14) (window_infix_at hk 13 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.r8 (rcx.toBitVec + 48) _ _ _ (by show (rcx.toBitVec + 48 : BitVec 64) = (rcx.toBitVec + 48); bv_omega)
  normalize_registers
  have hl30 := Machine.label_at' hk hf (j := 30)
    (by simp only [marshalSSZTo, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply step_cmp_jae_taken Reg64.rdi Reg64.r8 _ _ (k + 14) (k + 30) (window_infix_at hk 14 3) (by rfl) hl30 _ _ (by show ((rcx.toBitVec + 48) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; normalize_registers
  apply step_label _ _ (k + 30) (k + 31) (window_infix_at hk 30 1) (by rfl) (by rfl)
  apply step_store Reg64.rdi Reg64.rsp 80 _ (k + 31) (k + 32) (window_infix_at hk 31 1) (by rfl) (by rfl)
    (rsp.toBitVec - 216) (rsp.toBitVec - 136) (by encoder_address_equation) l136 hl136 _ _ _ (by rfl) (by ecancel)
  intro m4 H4; normalize_registers; simp only [Reg64s.get64] at H4
  apply step_store Reg64.r8 Reg64.rsp 72 _ (k + 32) (k + 33) (window_infix_at hk 32 1) (by rfl) (by rfl)
    (rsp.toBitVec - 216) (rsp.toBitVec - 144) (by encoder_address_equation) l144 hl144 _ _ _ (by rfl) (by ecancel)
  intro m5 H5; normalize_registers; simp only [Reg64s.get64] at H5
  apply step_store Reg64.rbx Reg64.rsp 200 _ (k + 33) (k + 34) (window_infix_at hk 33 1) (by rfl) (by rfl)
    (rsp.toBitVec - 216) (rsp.toBitVec - 16) (by encoder_address_equation) l16 hl16 _ _ _ (by rfl) (by ecancel)
  intro m6 H6; normalize_registers; simp only [Reg64s.get64] at H6
  apply step_lea_indexed Reg64.rax Reg64.rbx Reg64.rcx _ (k + 34) (k + 35) (window_infix_at hk 34 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.rax (rbx.toBitVec + rcx.toBitVec) _ _ _ (by show (rbx.toBitVec + rcx.toBitVec : BitVec 64) = (rbx.toBitVec + rcx.toBitVec); bv_omega)
  normalize_registers
  apply step_move_register Reg64.rbx Reg64.rdx _ (k + 35) (k + 36) (window_infix_at hk 35 1) (by rfl) (by rfl)
  normalize_registers
  apply step_move_immediate Reg64.rcx 48 _ (k + 36) (k + 37) (window_infix_at hk 36 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.rcx 48 _ _ _ (by show (BitVec.zeroExtend 64 (BitVec.truncate 32 (48 : BitVec 64)) : BitVec 64) = 48; decide)
  normalize_registers
  refine eventually_trans _ _ _ _ (encode_memmove_call (k + 37) (window_infix_at hk 37 1) (rsp.toBitVec - 216) (rbx.toBitVec + rcx.toBitVec) p0
    (rsp.toBitVec - 224) (rsp.toBitVec - 224 - BitVec.ofNat 64 S) S (by bv_omega) (Codec.frame_low_address_without_calls rsp.toBitVec 216 224 S (by decide))
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
    = @Codec.encodeFieldKindAnyFrame h marshalSSZTo Prysm.Builder.Encode.generated_layout [.bytes 48, .bytes 1, .bytes 20, .uint64, .uint64, .uint64]
    ⟨9, 0, [(.rax, .receiver), (.rbx, .ptr), (.rcx, .len 0), (.rdi, .cap)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.original 1), .at (.above 16) (.reg .rbx), .at (.below 136) (.original 3), .at (.below 144) (.original 4), .at (.below 16) (.original 5), .at (.below 152) (.original 6), .at (.below 160) (.original 7), .at (.below 32) (.original 8), .at (.below 64) (.original 9), .at (.below 48) (.original 10), .at (.below 96) (.original 11), .at (.below 80) (.original 12), .at (.below 128) (.original 13), .at (.below 112) (.original 14), .at (.below 224) (.original 15), .low .scratch],
      []⟩
    ⟨38, 1, [],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 136) (.reg .rdi), .at (.below 144) (.len 48), .at (.below 16) (.reg .rbx), .at (.below 152) (.original 6), .at (.below 160) (.original 7), .at (.below 32) (.original 8), .at (.below 64) (.original 9), .at (.below 48) (.original 10), .at (.below 96) (.original 11), .at (.below 80) (.original 12), .at (.below 128) (.original 13), .at (.below 112) (.original 14), .at (.below 224) (.ret 38), .low (.existential 0)],
      [.low]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 1 `Version` (1 bytes): directives 38–63; boundary state 1 → 2. -/
theorem Encode.generated_field_1 : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v3 v4 v5 c0 c1 c2 b0 b1 b2 pre d0 d1 d2 d3 d4 d5 : List UInt8) (hast : ast.length = 8) (hv3 : v3.length = 8) (hv4 : v4.length = 8) (hv5 : v5.length = 8) (hc0 : c0.length = 8) (hc1 : c1.length = 8) (hc2 : c2.length = 8) (hb0 : b0.length = 48) (hb1 : b1.length = 1) (hb2 : b2.length = 20) (hd0 : d0.length = 48) (hd1 : d1.length = 1) (hd2 : d2.length = 20) (hd3 : d3.length = 8) (hd4 : d4.length = 8) (hd5 : d5.length = 8)
    (p0 p1 p2 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l136 l144 l16 l152 l160 l32 t64 t48 t96 t80 t128 t112 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl136 : l136.length = 8) (hl144 : l144.length = 8) (hl16 : l16.length = 8) (hl152 : l152.length = 8) (hl160 : l160.length = 8) (hl32 : l32.length = 8) (ht64 : t64.length = 16) (ht48 : t48.length = 16) (ht96 : t96.length = 16) (ht80 : t80.length = 16) (ht128 : t128.length = 16) (ht112 : t112.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 224 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 93 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 38)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 216 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 : List UInt8), x0.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 136))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq (l152.At (s.regs.rsp.toBitVec - 152))
          ⋆ Eq (l160.At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (t64.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (t48.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (t96.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (t80.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (t128.At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq (t112.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 38)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 224))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 224 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 1).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (c2.At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (v3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (v5.At (s.regs.rax.toBitVec + 96))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b2.At p2)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 49))
          ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 69))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 77))
          ⋆ Eq (d5.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 85))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 64)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 216 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.get64 Reg64.rax = s.regs.rbx.toBitVec
        ∧ st.data.regs.get64 Reg64.rcx = s.regs.rdi.toBitVec
        ∧ st.data.regs.get64 Reg64.rdx = s.regs.rax.toBitVec
        ∧ st.data.regs.get64 Reg64.r8 = s.regs.rcx.toBitVec + 49 ∧
        ∃ (x0 : List UInt8), x0.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 136))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq (l152.At (s.regs.rsp.toBitVec - 152))
          ⋆ Eq (l160.At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (t64.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (t48.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (t96.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (t80.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (t128.At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq (t112.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 38)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 224))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 224 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 1).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (c2.At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (v3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (v5.At (s.regs.rax.toBitVec + 96))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b2.At p2)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 49))
          ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 69))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 77))
          ⋆ Eq (d5.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 85))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v3 v4 v5 c0 c1 c2 b0 b1 b2 pre d0 d1 d2 d3 d4 d5 hast hv3 hv4 hv5 hc0 hc1 hc2 hb0 hb1 hb2 hd0 hd1 hd2 hd3 hd4 hd5 p0 p1 p2 s ra guard hpre fp s1 s2 l136 l144 l16 l152 l160 l32 t64 t48 t96 t80 t128 t112 rslot hfp hs1 hs2 hl136 hl144 hl16 hl152 hl160 hl32 ht64 ht48 ht96 ht80 ht128 ht112 hrslot R S scratch hsc hsp hcap hcap63 hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hsp hcap hcap63 hpre ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, x0, hx0, Hm⟩
  dsimp only at hpc hrsp hrbp hr14  Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14  Hm
  subst rsp1 rbp1 r141
  have hcap' : rcx.toBitVec.toNat + 93 ≤ rdi.toBitVec.toNat := hcap
  apply step_load_value Reg64.rdx Reg64.rsp 224 _ (k + 38) (k + 39) (window_infix_at hk 38 1) (by rfl) (by rfl)
    (rsp.toBitVec - 216) (rsp.toBitVec + 8) rax.toBitVec (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_load_value Reg64.rsi Reg64.rdx 32 _ (k + 39) (k + 40) (window_infix_at hk 39 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 32) p1 (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_length_check Reg64.rdx 40 1 _ _ (k + 40) (k + 43) (window_infix_at hk 40 3) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 40) (by encoder_address_equation) (Int.toBytes 8 1) (by rfl) (by decide) _ _ _ (by rfl) (by ecancel)
  intro fl; normalize_registers
  apply step_load_value Reg64.rbx Reg64.rsp 72 _ (k + 43) (k + 44) (window_infix_at hk 43 1) (by rfl) (by rfl)
    (rsp.toBitVec - 216) (rsp.toBitVec - 144) (rcx.toBitVec + 48) (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_lea Reg64.r8 Reg64.rbx 1 _ (k + 44) (k + 45) (window_infix_at hk 44 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.r8 (rcx.toBitVec + 49) _ _ _ (by show ((rcx.toBitVec + 48) + 1 : BitVec 64) = (rcx.toBitVec + 49); bv_omega)
  normalize_registers
  apply step_load_value Reg64.rcx Reg64.rsp 80 _ (k + 45) (k + 46) (window_infix_at hk 45 1) (by rfl) (by rfl)
    (rsp.toBitVec - 216) (rsp.toBitVec - 136) rdi.toBitVec (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_cmp_jb_not_taken Reg64.rcx Reg64.r8 _ _ (k + 46) (k + 48) (window_infix_at hk 46 2) (by rfl) (by rfl) _ _ (by show ((rcx.toBitVec + 49) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; normalize_registers
  apply step_load_value Reg64.rax Reg64.rsp 200 _ (k + 48) (k + 49) (window_infix_at hk 48 1) (by rfl) (by rfl)
    (rsp.toBitVec - 216) (rsp.toBitVec - 16) rbx.toBitVec (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  have hl61 := Machine.label_at' hk hf (j := 61)
    (by simp only [marshalSSZTo, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply step_jump _ _ (k + 49) (k + 61) (window_infix_at hk 49 1) (by rfl) hl61
  apply step_label _ _ (k + 61) (k + 62) (window_infix_at hk 61 1) (by rfl) (by rfl)
  apply step_load_byte8 Reg64.r9 Reg64.rsi 0 _ (k + 62) (k + 63) (window_infix_at hk 62 1) (by rfl) (by rfl)
    p1 p1 (by encoder_address_equation) b1 hb1 _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_store_indexed8 Reg64.r9 Reg64.rax Reg64.rbx 0 _ (k + 63) (k + 64) (window_infix_at hk 63 1) (by rfl) (by rfl)
    rbx.toBitVec (rcx.toBitVec + 48) (rbx.toBitVec + rcx.toBitVec + 48) (by encoder_address_equation) d1 hd1 _ _ _ (by rfl) (by rfl) (by ecancel)
  intro m7 H7; normalize_registers; simp only [Reg64s.get64] at H7
  simp only [extractLsb'_zeroExtend_byte, toBytes_ofInt_ofBytes 8 1 rfl b1 hb1] at H7
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, x0, hx0, ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem Encode.generated_field_1_kind : ∀ (h : Host), type_of% (@Encode.generated_field_1 h)
    = @Codec.encodeFieldKindAnyFrame h marshalSSZTo Prysm.Builder.Encode.generated_layout [.bytes 48, .bytes 1, .bytes 20, .uint64, .uint64, .uint64]
    ⟨38, 1, [],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 136) (.reg .rdi), .at (.below 144) (.len 48), .at (.below 16) (.reg .rbx), .at (.below 152) (.original 6), .at (.below 160) (.original 7), .at (.below 32) (.original 8), .at (.below 64) (.original 9), .at (.below 48) (.original 10), .at (.below 96) (.original 11), .at (.below 80) (.original 12), .at (.below 128) (.original 13), .at (.below 112) (.original 14), .at (.below 224) (.ret 38), .low (.existential 0)],
      [.low]⟩
    ⟨64, 2, [(.rax, .ptr), (.rcx, .cap), (.rdx, .receiver), (.r8, .len 49)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 136) (.reg .rdi), .at (.below 144) (.len 48), .at (.below 16) (.reg .rbx), .at (.below 152) (.original 6), .at (.below 160) (.original 7), .at (.below 32) (.original 8), .at (.below 64) (.original 9), .at (.below 48) (.original 10), .at (.below 96) (.original 11), .at (.below 80) (.original 12), .at (.below 128) (.original 13), .at (.below 112) (.original 14), .at (.below 224) (.ret 38), .low (.existential 0)],
      [.low]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 2 `ExecutionAddress` (20 bytes): directives 64–86; boundary state 2 → 3. -/
theorem Encode.generated_field_2 : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v3 v4 v5 c0 c1 c2 b0 b1 b2 pre d0 d1 d2 d3 d4 d5 : List UInt8) (hast : ast.length = 8) (hv3 : v3.length = 8) (hv4 : v4.length = 8) (hv5 : v5.length = 8) (hc0 : c0.length = 8) (hc1 : c1.length = 8) (hc2 : c2.length = 8) (hb0 : b0.length = 48) (hb1 : b1.length = 1) (hb2 : b2.length = 20) (hd0 : d0.length = 48) (hd1 : d1.length = 1) (hd2 : d2.length = 20) (hd3 : d3.length = 8) (hd4 : d4.length = 8) (hd5 : d5.length = 8)
    (p0 p1 p2 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l136 l144 l16 l152 l160 l32 t64 t48 t96 t80 t128 t112 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl136 : l136.length = 8) (hl144 : l144.length = 8) (hl16 : l16.length = 8) (hl152 : l152.length = 8) (hl160 : l160.length = 8) (hl32 : l32.length = 8) (ht64 : t64.length = 16) (ht48 : t48.length = 16) (ht96 : t96.length = 16) (ht80 : t80.length = 16) (ht128 : t128.length = 16) (ht112 : t112.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 224 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 93 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 64)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 216 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14
        ∧ st0.data.regs.get64 Reg64.rax = s.regs.rbx.toBitVec
        ∧ st0.data.regs.get64 Reg64.rcx = s.regs.rdi.toBitVec
        ∧ st0.data.regs.get64 Reg64.rdx = s.regs.rax.toBitVec
        ∧ st0.data.regs.get64 Reg64.r8 = s.regs.rcx.toBitVec + 49 ∧
        ∃ (x0 : List UInt8), x0.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 136))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq (l152.At (s.regs.rsp.toBitVec - 152))
          ⋆ Eq (l160.At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (t64.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (t48.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (t96.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (t80.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (t128.At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq (t112.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 38)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 224))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 224 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 1).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (c2.At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (v3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (v5.At (s.regs.rax.toBitVec + 96))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b2.At p2)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 49))
          ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 69))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 77))
          ⋆ Eq (d5.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 85))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 87)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 216 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 : List UInt8), x0.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 136))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 152))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 69).toInt).At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (t64.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (t48.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (t96.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (t80.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (t128.At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq (t112.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 87)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 224))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 224 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 1).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (c2.At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (v3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (v5.At (s.regs.rax.toBitVec + 96))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b2.At p2)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (b2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 49))
          ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 69))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 77))
          ⋆ Eq (d5.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 85))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v3 v4 v5 c0 c1 c2 b0 b1 b2 pre d0 d1 d2 d3 d4 d5 hast hv3 hv4 hv5 hc0 hc1 hc2 hb0 hb1 hb2 hd0 hd1 hd2 hd3 hd4 hd5 p0 p1 p2 s ra guard hpre fp s1 s2 l136 l144 l16 l152 l160 l32 t64 t48 t96 t80 t128 t112 rslot hfp hs1 hs2 hl136 hl144 hl16 hl152 hl160 hl32 ht64 ht48 ht96 ht80 ht128 ht112 hrslot R S scratch hsc hsp hcap hcap63 hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hsp hcap hcap63 hpre ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, hrrax, hrrcx, hrrdx, hrr8, x0, hx0, Hm⟩
  dsimp only at hpc hrsp hrbp hr14 hrrax hrrcx hrrdx hrr8 Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14 hrrax hrrcx hrrdx hrr8 Hm
  subst rsp1 rbp1 r141
  obtain rfl : rbx = rax1 := (UInt64.toBitVec_inj.mp hrrax).symm
  obtain rfl : rdi = rcx1 := (UInt64.toBitVec_inj.mp hrrcx).symm
  obtain rfl : rax = rdx1 := (UInt64.toBitVec_inj.mp hrrdx).symm
  obtain rfl : r81 = { toBitVec := rcx.toBitVec + 49 } := UInt64.toBitVec_inj.mp hrr8
  have hcap' : rcx.toBitVec.toNat + 93 ≤ rdi.toBitVec.toNat := hcap
  apply step_load_value Reg64.rbx Reg64.rdx 56 _ (k + 64) (k + 65) (window_infix_at hk 64 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 56) p2 (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_length_check Reg64.rdx 64 20 _ _ (k + 65) (k + 67) (window_infix_at hk 65 2) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 64) (by encoder_address_equation) (Int.toBytes 8 20) (by rfl) (by decide) _ _ _ (by rfl) (by ecancel)
  intro fl; normalize_registers
  apply step_lea Reg64.r9 Reg64.r8 20 _ (k + 67) (k + 68) (window_infix_at hk 67 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.r9 (rcx.toBitVec + 69) _ _ _ (by show ((rcx.toBitVec + 49) + 20 : BitVec 64) = (rcx.toBitVec + 69); bv_omega)
  normalize_registers
  have hl80 := Machine.label_at' hk hf (j := 80)
    (by simp only [marshalSSZTo, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply step_cmp_jae_taken Reg64.rcx Reg64.r9 _ _ (k + 68) (k + 80) (window_infix_at hk 68 2) (by rfl) hl80 _ _ (by show ((rcx.toBitVec + 69) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; normalize_registers
  apply step_label _ _ (k + 80) (k + 81) (window_infix_at hk 80 1) (by rfl) (by rfl)
  apply step_store Reg64.rcx Reg64.rsp 64 _ (k + 81) (k + 82) (window_infix_at hk 81 1) (by rfl) (by rfl)
    (rsp.toBitVec - 216) (rsp.toBitVec - 152) (by encoder_address_equation) l152 hl152 _ _ _ (by rfl) (by ecancel)
  intro m8 H8; normalize_registers; simp only [Reg64s.get64] at H8
  apply step_store Reg64.r9 Reg64.rsp 56 _ (k + 82) (k + 83) (window_infix_at hk 82 1) (by rfl) (by rfl)
    (rsp.toBitVec - 216) (rsp.toBitVec - 160) (by encoder_address_equation) l160 hl160 _ _ _ (by rfl) (by ecancel)
  intro m9 H9; normalize_registers; simp only [Reg64s.get64] at H9
  apply step_store Reg64.rax Reg64.rsp 184 _ (k + 83) (k + 84) (window_infix_at hk 83 1) (by rfl) (by rfl)
    (rsp.toBitVec - 216) (rsp.toBitVec - 32) (by encoder_address_equation) l32 hl32 _ _ _ (by rfl) (by ecancel)
  intro m10 H10; normalize_registers; simp only [Reg64s.get64] at H10
  apply step_add_registers Reg64.rax Reg64.r8 _ (k + 84) (k + 85) (window_infix_at hk 84 1) (by rfl) (by rfl)
  intro fl; normalize_registers
  apply register_value_rewrite Reg64.rax (rbx.toBitVec + rcx.toBitVec + 49) _ _ _ (by show (rbx.toBitVec + (rcx.toBitVec + 49) : BitVec 64) = (rbx.toBitVec + rcx.toBitVec + 49); bv_omega)
  normalize_registers
  apply step_move_immediate Reg64.rcx 20 _ (k + 85) (k + 86) (window_infix_at hk 85 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.rcx 20 _ _ _ (by show (BitVec.zeroExtend 64 (BitVec.truncate 32 (20 : BitVec 64)) : BitVec 64) = 20; decide)
  normalize_registers
  refine eventually_trans _ _ _ _ (encode_memmove_call (k + 86) (window_infix_at hk 86 1) (rsp.toBitVec - 216) (rbx.toBitVec + rcx.toBitVec + 49) p2
    (rsp.toBitVec - 224) (rsp.toBitVec - 224 - BitVec.ofNat 64 S) S (by bv_omega) (Codec.frame_low_address_without_calls rsp.toBitVec 216 224 S (by decide))
    b2 d2 (Int.toBytes 8 (Host.addrOf (k + 38)).toBitVec.toInt) x0 (by rw [hd2, hb2]) (Int.toBytes_length 8 _) hx0
    _ _ (by rfl) (by rfl) (by rfl) (by rw [hb2]; rfl) (by first | ecancel | (dsimp only; ecancel)) hmm) ?_
  rintro ⟨e2, pc2⟩ ⟨hpc2, hrsp2, hrbp2, hr142, scr2, hscr2, Hc2⟩
  dsimp only at hpc2 hrsp2 hrbp2 hr142 Hc2
  subst hpc2
  obtain ⟨⟨raxc2, rbxc2, rcxc2, rdxc2, rsic2, rdic2, rspc2, rbpc2, r8c2, r9c2, r10c2, r11c2, r12c2, r13c2, r14c2, r15c2⟩, zmmsc2, flagsc2, memc2⟩ := e2
  simp only at hrsp2 hrbp2 hr142 Hc2
  subst rspc2 rbpc2 r14c2
  rw [show k + 86 + 1 = k + 87 from rfl] at Hc2
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, scr2, hscr2, ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem Encode.generated_field_2_kind : ∀ (h : Host), type_of% (@Encode.generated_field_2 h)
    = @Codec.encodeFieldKindAnyFrame h marshalSSZTo Prysm.Builder.Encode.generated_layout [.bytes 48, .bytes 1, .bytes 20, .uint64, .uint64, .uint64]
    ⟨64, 2, [(.rax, .ptr), (.rcx, .cap), (.rdx, .receiver), (.r8, .len 49)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 136) (.reg .rdi), .at (.below 144) (.len 48), .at (.below 16) (.reg .rbx), .at (.below 152) (.original 6), .at (.below 160) (.original 7), .at (.below 32) (.original 8), .at (.below 64) (.original 9), .at (.below 48) (.original 10), .at (.below 96) (.original 11), .at (.below 80) (.original 12), .at (.below 128) (.original 13), .at (.below 112) (.original 14), .at (.below 224) (.ret 38), .low (.existential 0)],
      [.low]⟩
    ⟨87, 3, [],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 136) (.reg .rdi), .at (.below 144) (.len 48), .at (.below 16) (.reg .rbx), .at (.below 152) (.reg .rdi), .at (.below 160) (.len 69), .at (.below 32) (.reg .rbx), .at (.below 64) (.original 9), .at (.below 48) (.original 10), .at (.below 96) (.original 11), .at (.below 80) (.original 12), .at (.below 128) (.original 13), .at (.below 112) (.original 14), .at (.below 224) (.ret 87), .low (.existential 0)],
      [.low]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 3 `Balance` (uint64): directives 87–114; boundary state 3 → 4. -/
theorem Encode.generated_field_3 : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v3 v4 v5 c0 c1 c2 b0 b1 b2 pre d0 d1 d2 d3 d4 d5 : List UInt8) (hast : ast.length = 8) (hv3 : v3.length = 8) (hv4 : v4.length = 8) (hv5 : v5.length = 8) (hc0 : c0.length = 8) (hc1 : c1.length = 8) (hc2 : c2.length = 8) (hb0 : b0.length = 48) (hb1 : b1.length = 1) (hb2 : b2.length = 20) (hd0 : d0.length = 48) (hd1 : d1.length = 1) (hd2 : d2.length = 20) (hd3 : d3.length = 8) (hd4 : d4.length = 8) (hd5 : d5.length = 8)
    (p0 p1 p2 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l136 l144 l16 l152 l160 l32 t64 t48 t96 t80 t128 t112 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl136 : l136.length = 8) (hl144 : l144.length = 8) (hl16 : l16.length = 8) (hl152 : l152.length = 8) (hl160 : l160.length = 8) (hl32 : l32.length = 8) (ht64 : t64.length = 16) (ht48 : t48.length = 16) (ht96 : t96.length = 16) (ht80 : t80.length = 16) (ht128 : t128.length = 16) (ht112 : t112.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 224 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 93 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 87)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 216 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 : List UInt8), x0.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 136))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 152))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 69).toInt).At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (t64.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (t48.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (t96.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (t80.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (t128.At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq (t112.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 87)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 224))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 224 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 1).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (c2.At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (v3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (v5.At (s.regs.rax.toBitVec + 96))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b2.At p2)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (b2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 49))
          ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 69))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 77))
          ⋆ Eq (d5.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 85))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 115)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 216 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.get64 Reg64.rax = s.regs.rbx.toBitVec
        ∧ st.data.regs.get64 Reg64.rcx = s.regs.rdi.toBitVec
        ∧ st.data.regs.get64 Reg64.rdx = s.regs.rcx.toBitVec + 77
        ∧ st.data.regs.get64 Reg64.rsi = s.regs.rax.toBitVec ∧
        ∃ (x0 x1 x2 : List UInt8), x0.length = S ∧ x1.length = 8 ∧ x2.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 136))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 152))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 69).toInt).At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (v3.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (t96.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (t80.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (t128.At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq (t112.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 87)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 224))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 224 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 1).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (c2.At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (v3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (v5.At (s.regs.rax.toBitVec + 96))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b2.At p2)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (b2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 49))
          ⋆ Eq (v3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 69))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 77))
          ⋆ Eq (d5.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 85))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v3 v4 v5 c0 c1 c2 b0 b1 b2 pre d0 d1 d2 d3 d4 d5 hast hv3 hv4 hv5 hc0 hc1 hc2 hb0 hb1 hb2 hd0 hd1 hd2 hd3 hd4 hd5 p0 p1 p2 s ra guard hpre fp s1 s2 l136 l144 l16 l152 l160 l32 t64 t48 t96 t80 t128 t112 rslot hfp hs1 hs2 hl136 hl144 hl16 hl152 hl160 hl32 ht64 ht48 ht96 ht80 ht128 ht112 hrslot R S scratch hsc hsp hcap hcap63 hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hsp hcap hcap63 hpre ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, x0, hx0, Hm⟩
  dsimp only at hpc hrsp hrbp hr14  Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14  Hm
  subst rsp1 rbp1 r141
  have hcap' : rcx.toBitVec.toNat + 93 ≤ rdi.toBitVec.toNat := hcap
  apply step_load_value Reg64.rbx Reg64.rsp 56 _ (k + 87) (k + 88) (window_infix_at hk 87 1) (by rfl) (by rfl)
    (rsp.toBitVec - 216) (rsp.toBitVec - 160) (rcx.toBitVec + 69) (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_lea Reg64.rdx Reg64.rbx 8 _ (k + 88) (k + 89) (window_infix_at hk 88 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.rdx (rcx.toBitVec + 77) _ _ _ (by show ((rcx.toBitVec + 69) + 8 : BitVec 64) = (rcx.toBitVec + 77); bv_omega)
  normalize_registers
  apply step_load_value Reg64.rsi Reg64.rsp 224 _ (k + 89) (k + 90) (window_infix_at hk 89 1) (by rfl) (by rfl)
    (rsp.toBitVec - 216) (rsp.toBitVec + 8) rax.toBitVec (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_load_bytes Reg64.rdi Reg64.rsi 80 _ (k + 90) (k + 91) (window_infix_at hk 90 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 80) (by encoder_address_equation) v3 hv3 _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_lea Reg64.r8 Reg64.rsp 152 _ (k + 91) (k + 95) (window_infix_at hk 91 4) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.r8 (rsp.toBitVec - 64) _ _ _ (by show ((rsp.toBitVec - 216) + 152 : BitVec 64) = (rsp.toBitVec - 64); bv_omega)
  normalize_registers
  apply step_store_xmm15 Reg64.r8 0 _ (k + 95) (k + 96) (window_infix_at hk 95 1) (by rfl) (by rfl)
    (rsp.toBitVec - 64) (rsp.toBitVec - 64) (by encoder_address_equation) t64 ht64 _ _ _ (by rfl) (by ecancel)
  intro m11 H11; normalize_registers; try dsimp only at H11
  apply step_store_xmm15 Reg64.r8 16 _ (k + 96) (k + 97) (window_infix_at hk 96 1) (by rfl) (by rfl)
    (rsp.toBitVec - 64) (rsp.toBitVec - 48) (by encoder_address_equation) t48 ht48 _ _ _ (by rfl) (by ecancel)
  intro m12 H12; normalize_registers; try dsimp only at H12
  rw [Machine.at_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 64), show (rsp.toBitVec - 64) + 8 = (rsp.toBitVec - 56) by bv_omega] at H12
  apply step_store Reg64.rdi Reg64.rsp 152 _ (k + 97) (k + 98) (window_infix_at hk 97 1) (by rfl) (by rfl)
    (rsp.toBitVec - 216) (rsp.toBitVec - 64) (by encoder_address_equation) ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).take 8) (by rw [List.length_take, Int.toBytes_length]; rfl) _ _ _ (by rfl) (by ecancel)
  intro m13 H13; normalize_registers; simp only [Reg64s.get64] at H13
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v3 hv3] at H13
  apply step_load_value Reg64.rcx Reg64.rsp 64 _ (k + 98) (k + 99) (window_infix_at hk 98 1) (by rfl) (by rfl)
    (rsp.toBitVec - 216) (rsp.toBitVec - 152) rdi.toBitVec (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_cmp_jb_not_taken Reg64.rcx Reg64.rdx _ _ (k + 99) (k + 101) (window_infix_at hk 99 2) (by rfl) (by rfl) _ _ (by show ((rcx.toBitVec + 77) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; normalize_registers
  apply step_load_value Reg64.rax Reg64.rsp 184 _ (k + 101) (k + 102) (window_infix_at hk 101 1) (by rfl) (by rfl)
    (rsp.toBitVec - 216) (rsp.toBitVec - 32) rbx.toBitVec (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  have hl112 := Machine.label_at' hk hf (j := 112)
    (by simp only [marshalSSZTo, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply step_jump _ _ (k + 102) (k + 112) (window_infix_at hk 102 1) (by rfl) hl112
  apply step_label _ _ (k + 112) (k + 113) (window_infix_at hk 112 1) (by rfl) (by rfl)
  apply step_load_bytes Reg64.r8 Reg64.rsp 152 _ (k + 113) (k + 114) (window_infix_at hk 113 1) (by rfl) (by rfl)
    (rsp.toBitVec - 216) (rsp.toBitVec - 64) (by encoder_address_equation) v3 hv3 _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_store_indexed Reg64.r8 Reg64.rax Reg64.rbx 0 _ (k + 114) (k + 115) (window_infix_at hk 114 1) (by rfl) (by rfl)
    rbx.toBitVec (rcx.toBitVec + 69) (rbx.toBitVec + rcx.toBitVec + 69) (by encoder_address_equation) d3 hd3 _ _ _ (by rfl) (by rfl) (by ecancel)
  intro m14 H14; normalize_registers; simp only [Reg64s.get64] at H14
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v3 hv3] at H14
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, x0, ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8), (Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt), hx0, (by rw [List.length_drop, Int.toBytes_length]), (Int.toBytes_length 16 _), ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem Encode.generated_field_3_kind : ∀ (h : Host), type_of% (@Encode.generated_field_3 h)
    = @Codec.encodeFieldKindAnyFrame h marshalSSZTo Prysm.Builder.Encode.generated_layout [.bytes 48, .bytes 1, .bytes 20, .uint64, .uint64, .uint64]
    ⟨87, 3, [],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 136) (.reg .rdi), .at (.below 144) (.len 48), .at (.below 16) (.reg .rbx), .at (.below 152) (.reg .rdi), .at (.below 160) (.len 69), .at (.below 32) (.reg .rbx), .at (.below 64) (.original 9), .at (.below 48) (.original 10), .at (.below 96) (.original 11), .at (.below 80) (.original 12), .at (.below 128) (.original 13), .at (.below 112) (.original 14), .at (.below 224) (.ret 87), .low (.existential 0)],
      [.low]⟩
    ⟨115, 4, [(.rax, .ptr), (.rcx, .cap), (.rdx, .len 77), (.rsi, .receiver)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 136) (.reg .rdi), .at (.below 144) (.len 48), .at (.below 16) (.reg .rbx), .at (.below 152) (.reg .rdi), .at (.below 160) (.len 69), .at (.below 32) (.reg .rbx), .at (.below 64) (.field 3), .at (.below 56) (.existential 1), .at (.below 48) (.existential 2), .at (.below 96) (.original 11), .at (.below 80) (.original 12), .at (.below 128) (.original 13), .at (.below 112) (.original 14), .at (.below 224) (.ret 87), .low (.existential 0)],
      [.low, .fixed 8, .fixed 16]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 4 `DepositEpoch` (uint64): directives 115–134; boundary state 4 → 5. -/
theorem Encode.generated_field_4 : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v3 v4 v5 c0 c1 c2 b0 b1 b2 pre d0 d1 d2 d3 d4 d5 : List UInt8) (hast : ast.length = 8) (hv3 : v3.length = 8) (hv4 : v4.length = 8) (hv5 : v5.length = 8) (hc0 : c0.length = 8) (hc1 : c1.length = 8) (hc2 : c2.length = 8) (hb0 : b0.length = 48) (hb1 : b1.length = 1) (hb2 : b2.length = 20) (hd0 : d0.length = 48) (hd1 : d1.length = 1) (hd2 : d2.length = 20) (hd3 : d3.length = 8) (hd4 : d4.length = 8) (hd5 : d5.length = 8)
    (p0 p1 p2 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l136 l144 l16 l152 l160 l32 t64 t48 t96 t80 t128 t112 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl136 : l136.length = 8) (hl144 : l144.length = 8) (hl16 : l16.length = 8) (hl152 : l152.length = 8) (hl160 : l160.length = 8) (hl32 : l32.length = 8) (ht64 : t64.length = 16) (ht48 : t48.length = 16) (ht96 : t96.length = 16) (ht80 : t80.length = 16) (ht128 : t128.length = 16) (ht112 : t112.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 224 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 93 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 115)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 216 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14
        ∧ st0.data.regs.get64 Reg64.rax = s.regs.rbx.toBitVec
        ∧ st0.data.regs.get64 Reg64.rcx = s.regs.rdi.toBitVec
        ∧ st0.data.regs.get64 Reg64.rdx = s.regs.rcx.toBitVec + 77
        ∧ st0.data.regs.get64 Reg64.rsi = s.regs.rax.toBitVec ∧
        ∃ (x0 x1 x2 : List UInt8), x0.length = S ∧ x1.length = 8 ∧ x2.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 136))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 152))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 69).toInt).At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (v3.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (t96.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (t80.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (t128.At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq (t112.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 87)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 224))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 224 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 1).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (c2.At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (v3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (v5.At (s.regs.rax.toBitVec + 96))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b2.At p2)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (b2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 49))
          ⋆ Eq (v3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 69))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 77))
          ⋆ Eq (d5.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 85))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 135)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 216 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.get64 Reg64.rax = s.regs.rbx.toBitVec
        ∧ st.data.regs.get64 Reg64.rbx = s.regs.rcx.toBitVec + 85
        ∧ st.data.regs.get64 Reg64.rcx = s.regs.rdi.toBitVec
        ∧ st.data.regs.get64 Reg64.rsi = s.regs.rax.toBitVec ∧
        ∃ (x0 x1 x2 x3 x4 : List UInt8), x0.length = S ∧ x1.length = 8 ∧ x2.length = 16 ∧ x3.length = 8 ∧ x4.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 136))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 152))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 69).toInt).At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (v3.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (v4.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (x4.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (t128.At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq (t112.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 87)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 224))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 224 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 1).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (c2.At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (v3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (v5.At (s.regs.rax.toBitVec + 96))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b2.At p2)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (b2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 49))
          ⋆ Eq (v3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 69))
          ⋆ Eq (v4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 77))
          ⋆ Eq (d5.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 85))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v3 v4 v5 c0 c1 c2 b0 b1 b2 pre d0 d1 d2 d3 d4 d5 hast hv3 hv4 hv5 hc0 hc1 hc2 hb0 hb1 hb2 hd0 hd1 hd2 hd3 hd4 hd5 p0 p1 p2 s ra guard hpre fp s1 s2 l136 l144 l16 l152 l160 l32 t64 t48 t96 t80 t128 t112 rslot hfp hs1 hs2 hl136 hl144 hl16 hl152 hl160 hl32 ht64 ht48 ht96 ht80 ht128 ht112 hrslot R S scratch hsc hsp hcap hcap63 hmm
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
  obtain rfl : rdx1 = { toBitVec := rcx.toBitVec + 77 } := UInt64.toBitVec_inj.mp hrrdx
  obtain rfl : rax = rsi1 := (UInt64.toBitVec_inj.mp hrrsi).symm
  have hcap' : rcx.toBitVec.toNat + 93 ≤ rdi.toBitVec.toNat := hcap
  apply step_lea Reg64.rbx Reg64.rdx 8 _ (k + 115) (k + 116) (window_infix_at hk 115 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.rbx (rcx.toBitVec + 85) _ _ _ (by show ((rcx.toBitVec + 77) + 8 : BitVec 64) = (rcx.toBitVec + 85); bv_omega)
  normalize_registers
  apply step_load_bytes Reg64.r8 Reg64.rsi 88 _ (k + 116) (k + 117) (window_infix_at hk 116 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 88) (by encoder_address_equation) v4 hv4 _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_lea Reg64.r9 Reg64.rsp 120 _ (k + 117) (k + 121) (window_infix_at hk 117 4) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.r9 (rsp.toBitVec - 96) _ _ _ (by show ((rsp.toBitVec - 216) + 120 : BitVec 64) = (rsp.toBitVec - 96); bv_omega)
  normalize_registers
  apply step_store_xmm15 Reg64.r9 0 _ (k + 121) (k + 122) (window_infix_at hk 121 1) (by rfl) (by rfl)
    (rsp.toBitVec - 96) (rsp.toBitVec - 96) (by encoder_address_equation) t96 ht96 _ _ _ (by rfl) (by ecancel)
  intro m15 H15; normalize_registers; try dsimp only at H15
  apply step_store_xmm15 Reg64.r9 16 _ (k + 122) (k + 123) (window_infix_at hk 122 1) (by rfl) (by rfl)
    (rsp.toBitVec - 96) (rsp.toBitVec - 80) (by encoder_address_equation) t80 ht80 _ _ _ (by rfl) (by ecancel)
  intro m16 H16; normalize_registers; try dsimp only at H16
  rw [Machine.at_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 96), show (rsp.toBitVec - 96) + 8 = (rsp.toBitVec - 88) by bv_omega] at H16
  apply step_store Reg64.r8 Reg64.rsp 120 _ (k + 123) (k + 124) (window_infix_at hk 123 1) (by rfl) (by rfl)
    (rsp.toBitVec - 216) (rsp.toBitVec - 96) (by encoder_address_equation) ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).take 8) (by rw [List.length_take, Int.toBytes_length]; rfl) _ _ _ (by rfl) (by ecancel)
  intro m17 H17; normalize_registers; simp only [Reg64s.get64] at H17
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v4 hv4] at H17
  have hl132 := Machine.label_at' hk hf (j := 132)
    (by simp only [marshalSSZTo, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply step_cmp_jae_taken Reg64.rcx Reg64.rbx _ _ (k + 124) (k + 132) (window_infix_at hk 124 2) (by rfl) hl132 _ _ (by show ((rcx.toBitVec + 85) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; normalize_registers
  apply step_label _ _ (k + 132) (k + 133) (window_infix_at hk 132 1) (by rfl) (by rfl)
  apply step_load_bytes Reg64.r8 Reg64.rsp 120 _ (k + 133) (k + 134) (window_infix_at hk 133 1) (by rfl) (by rfl)
    (rsp.toBitVec - 216) (rsp.toBitVec - 96) (by encoder_address_equation) v4 hv4 _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_store_indexed Reg64.r8 Reg64.rax Reg64.rdx 0 _ (k + 134) (k + 135) (window_infix_at hk 134 1) (by rfl) (by rfl)
    rbx.toBitVec (rcx.toBitVec + 77) (rbx.toBitVec + rcx.toBitVec + 77) (by encoder_address_equation) d4 hd4 _ _ _ (by rfl) (by rfl) (by ecancel)
  intro m18 H18; normalize_registers; simp only [Reg64s.get64] at H18
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v4 hv4] at H18
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, x0, x1, x2, ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8), (Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt), hx0, hx1, hx2, (by rw [List.length_drop, Int.toBytes_length]), (Int.toBytes_length 16 _), ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem Encode.generated_field_4_kind : ∀ (h : Host), type_of% (@Encode.generated_field_4 h)
    = @Codec.encodeFieldKindAnyFrame h marshalSSZTo Prysm.Builder.Encode.generated_layout [.bytes 48, .bytes 1, .bytes 20, .uint64, .uint64, .uint64]
    ⟨115, 4, [(.rax, .ptr), (.rcx, .cap), (.rdx, .len 77), (.rsi, .receiver)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 136) (.reg .rdi), .at (.below 144) (.len 48), .at (.below 16) (.reg .rbx), .at (.below 152) (.reg .rdi), .at (.below 160) (.len 69), .at (.below 32) (.reg .rbx), .at (.below 64) (.field 3), .at (.below 56) (.existential 1), .at (.below 48) (.existential 2), .at (.below 96) (.original 11), .at (.below 80) (.original 12), .at (.below 128) (.original 13), .at (.below 112) (.original 14), .at (.below 224) (.ret 87), .low (.existential 0)],
      [.low, .fixed 8, .fixed 16]⟩
    ⟨135, 5, [(.rax, .ptr), (.rbx, .len 85), (.rcx, .cap), (.rsi, .receiver)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 136) (.reg .rdi), .at (.below 144) (.len 48), .at (.below 16) (.reg .rbx), .at (.below 152) (.reg .rdi), .at (.below 160) (.len 69), .at (.below 32) (.reg .rbx), .at (.below 64) (.field 3), .at (.below 56) (.existential 1), .at (.below 48) (.existential 2), .at (.below 96) (.field 4), .at (.below 88) (.existential 3), .at (.below 80) (.existential 4), .at (.below 128) (.original 13), .at (.below 112) (.original 14), .at (.below 224) (.ret 87), .low (.existential 0)],
      [.low, .fixed 8, .fixed 16, .fixed 8, .fixed 16]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 5 `WithdrawableEpoch` (uint64): directives 135–156; boundary state 5 → 6. -/
theorem Encode.generated_field_5 : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v3 v4 v5 c0 c1 c2 b0 b1 b2 pre d0 d1 d2 d3 d4 d5 : List UInt8) (hast : ast.length = 8) (hv3 : v3.length = 8) (hv4 : v4.length = 8) (hv5 : v5.length = 8) (hc0 : c0.length = 8) (hc1 : c1.length = 8) (hc2 : c2.length = 8) (hb0 : b0.length = 48) (hb1 : b1.length = 1) (hb2 : b2.length = 20) (hd0 : d0.length = 48) (hd1 : d1.length = 1) (hd2 : d2.length = 20) (hd3 : d3.length = 8) (hd4 : d4.length = 8) (hd5 : d5.length = 8)
    (p0 p1 p2 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l136 l144 l16 l152 l160 l32 t64 t48 t96 t80 t128 t112 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl136 : l136.length = 8) (hl144 : l144.length = 8) (hl16 : l16.length = 8) (hl152 : l152.length = 8) (hl160 : l160.length = 8) (hl32 : l32.length = 8) (ht64 : t64.length = 16) (ht48 : t48.length = 16) (ht96 : t96.length = 16) (ht80 : t80.length = 16) (ht128 : t128.length = 16) (ht112 : t112.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 224 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 93 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 135)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 216 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14
        ∧ st0.data.regs.get64 Reg64.rax = s.regs.rbx.toBitVec
        ∧ st0.data.regs.get64 Reg64.rbx = s.regs.rcx.toBitVec + 85
        ∧ st0.data.regs.get64 Reg64.rcx = s.regs.rdi.toBitVec
        ∧ st0.data.regs.get64 Reg64.rsi = s.regs.rax.toBitVec ∧
        ∃ (x0 x1 x2 x3 x4 : List UInt8), x0.length = S ∧ x1.length = 8 ∧ x2.length = 16 ∧ x3.length = 8 ∧ x4.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 136))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 152))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 69).toInt).At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (v3.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (v4.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (x4.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (t128.At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq (t112.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 87)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 224))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 224 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 1).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (c2.At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (v3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (v5.At (s.regs.rax.toBitVec + 96))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b2.At p2)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (b2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 49))
          ⋆ Eq (v3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 69))
          ⋆ Eq (v4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 77))
          ⋆ Eq (d5.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 85))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 157)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 216 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.get64 Reg64.rax = s.regs.rbx.toBitVec
        ∧ st.data.regs.get64 Reg64.rcx = s.regs.rdi.toBitVec
        ∧ st.data.regs.get64 Reg64.rdx = s.regs.rcx.toBitVec + 93 ∧
        ∃ (x0 x1 x2 x3 x4 x5 x6 : List UInt8), x0.length = S ∧ x1.length = 8 ∧ x2.length = 16 ∧ x3.length = 8 ∧ x4.length = 16 ∧ x5.length = 8 ∧ x6.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 136))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 152))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 69).toInt).At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (v3.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (v4.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (x4.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (v5.At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq (x5.At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq (x6.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 87)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 224))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 224 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 1).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (c2.At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (v3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (v5.At (s.regs.rax.toBitVec + 96))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b2.At p2)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (b2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 49))
          ⋆ Eq (v3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 69))
          ⋆ Eq (v4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 77))
          ⋆ Eq (v5.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 85))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v3 v4 v5 c0 c1 c2 b0 b1 b2 pre d0 d1 d2 d3 d4 d5 hast hv3 hv4 hv5 hc0 hc1 hc2 hb0 hb1 hb2 hd0 hd1 hd2 hd3 hd4 hd5 p0 p1 p2 s ra guard hpre fp s1 s2 l136 l144 l16 l152 l160 l32 t64 t48 t96 t80 t128 t112 rslot hfp hs1 hs2 hl136 hl144 hl16 hl152 hl160 hl32 ht64 ht48 ht96 ht80 ht128 ht112 hrslot R S scratch hsc hsp hcap hcap63 hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hsp hcap hcap63 hpre ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, hrrax, hrrbx, hrrcx, hrrsi, x0, x1, x2, x3, x4, hx0, hx1, hx2, hx3, hx4, Hm⟩
  dsimp only at hpc hrsp hrbp hr14 hrrax hrrbx hrrcx hrrsi Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14 hrrax hrrbx hrrcx hrrsi Hm
  subst rsp1 rbp1 r141
  obtain rfl : rbx = rax1 := (UInt64.toBitVec_inj.mp hrrax).symm
  obtain rfl : rbx1 = { toBitVec := rcx.toBitVec + 85 } := UInt64.toBitVec_inj.mp hrrbx
  obtain rfl : rdi = rcx1 := (UInt64.toBitVec_inj.mp hrrcx).symm
  obtain rfl : rax = rsi1 := (UInt64.toBitVec_inj.mp hrrsi).symm
  have hcap' : rcx.toBitVec.toNat + 93 ≤ rdi.toBitVec.toNat := hcap
  apply step_lea Reg64.rdx Reg64.rbx 8 _ (k + 135) (k + 136) (window_infix_at hk 135 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.rdx (rcx.toBitVec + 93) _ _ _ (by show ((rcx.toBitVec + 85) + 8 : BitVec 64) = (rcx.toBitVec + 93); bv_omega)
  normalize_registers
  apply step_load_bytes Reg64.r8 Reg64.rsi 96 _ (k + 136) (k + 137) (window_infix_at hk 136 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 96) (by encoder_address_equation) v5 hv5 _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_lea Reg64.r9 Reg64.rsp 88 _ (k + 137) (k + 141) (window_infix_at hk 137 4) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.r9 (rsp.toBitVec - 128) _ _ _ (by show ((rsp.toBitVec - 216) + 88 : BitVec 64) = (rsp.toBitVec - 128); bv_omega)
  normalize_registers
  apply step_store_xmm15 Reg64.r9 0 _ (k + 141) (k + 142) (window_infix_at hk 141 1) (by rfl) (by rfl)
    (rsp.toBitVec - 128) (rsp.toBitVec - 128) (by encoder_address_equation) t128 ht128 _ _ _ (by rfl) (by ecancel)
  intro m19 H19; normalize_registers; try dsimp only at H19
  apply step_store_xmm15 Reg64.r9 16 _ (k + 142) (k + 143) (window_infix_at hk 142 1) (by rfl) (by rfl)
    (rsp.toBitVec - 128) (rsp.toBitVec - 112) (by encoder_address_equation) t112 ht112 _ _ _ (by rfl) (by ecancel)
  intro m20 H20; normalize_registers; try dsimp only at H20
  rw [Machine.at_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 128), show (rsp.toBitVec - 128) + 8 = (rsp.toBitVec - 120) by bv_omega] at H20
  apply step_store Reg64.r8 Reg64.rsp 88 _ (k + 143) (k + 144) (window_infix_at hk 143 1) (by rfl) (by rfl)
    (rsp.toBitVec - 216) (rsp.toBitVec - 128) (by encoder_address_equation) ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).take 8) (by rw [List.length_take, Int.toBytes_length]; rfl) _ _ _ (by rfl) (by ecancel)
  intro m21 H21; normalize_registers; simp only [Reg64s.get64] at H21
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v5 hv5] at H21
  have hl154 := Machine.label_at' hk hf (j := 154)
    (by simp only [marshalSSZTo, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply step_cmp_jae_taken Reg64.rcx Reg64.rdx _ _ (k + 144) (k + 154) (window_infix_at hk 144 3) (by rfl) hl154 _ _ (by show ((rcx.toBitVec + 93) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; normalize_registers
  apply step_label _ _ (k + 154) (k + 155) (window_infix_at hk 154 1) (by rfl) (by rfl)
  apply step_load_bytes Reg64.r8 Reg64.rsp 88 _ (k + 155) (k + 156) (window_infix_at hk 155 1) (by rfl) (by rfl)
    (rsp.toBitVec - 216) (rsp.toBitVec - 128) (by encoder_address_equation) v5 hv5 _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_store_indexed Reg64.r8 Reg64.rax Reg64.rbx 0 _ (k + 156) (k + 157) (window_infix_at hk 156 1) (by rfl) (by rfl)
    rbx.toBitVec (rcx.toBitVec + 85) (rbx.toBitVec + rcx.toBitVec + 85) (by encoder_address_equation) d5 hd5 _ _ _ (by rfl) (by rfl) (by ecancel)
  intro m22 H22; normalize_registers; simp only [Reg64s.get64] at H22
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v5 hv5] at H22
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, x0, x1, x2, x3, x4, ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8), (Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt), hx0, hx1, hx2, hx3, hx4, (by rw [List.length_drop, Int.toBytes_length]), (Int.toBytes_length 16 _), ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem Encode.generated_field_5_kind : ∀ (h : Host), type_of% (@Encode.generated_field_5 h)
    = @Codec.encodeFieldKindAnyFrame h marshalSSZTo Prysm.Builder.Encode.generated_layout [.bytes 48, .bytes 1, .bytes 20, .uint64, .uint64, .uint64]
    ⟨135, 5, [(.rax, .ptr), (.rbx, .len 85), (.rcx, .cap), (.rsi, .receiver)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 136) (.reg .rdi), .at (.below 144) (.len 48), .at (.below 16) (.reg .rbx), .at (.below 152) (.reg .rdi), .at (.below 160) (.len 69), .at (.below 32) (.reg .rbx), .at (.below 64) (.field 3), .at (.below 56) (.existential 1), .at (.below 48) (.existential 2), .at (.below 96) (.field 4), .at (.below 88) (.existential 3), .at (.below 80) (.existential 4), .at (.below 128) (.original 13), .at (.below 112) (.original 14), .at (.below 224) (.ret 87), .low (.existential 0)],
      [.low, .fixed 8, .fixed 16, .fixed 8, .fixed 16]⟩
    ⟨157, 6, [(.rax, .ptr), (.rcx, .cap), (.rdx, .len 93)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 136) (.reg .rdi), .at (.below 144) (.len 48), .at (.below 16) (.reg .rbx), .at (.below 152) (.reg .rdi), .at (.below 160) (.len 69), .at (.below 32) (.reg .rbx), .at (.below 64) (.field 3), .at (.below 56) (.existential 1), .at (.below 48) (.existential 2), .at (.below 96) (.field 4), .at (.below 88) (.existential 3), .at (.below 80) (.existential 4), .at (.below 128) (.field 5), .at (.below 120) (.existential 5), .at (.below 112) (.existential 6), .at (.below 224) (.ret 87), .low (.existential 0)],
      [.low, .fixed 8, .fixed 16, .fixed 8, .fixed 16, .fixed 8, .fixed 16]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Epilogue: directives 157–return; boundary state 6 → the fast-path post-state. -/
theorem Encode.generated_epilogue : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v3 v4 v5 c0 c1 c2 b0 b1 b2 pre d0 d1 d2 d3 d4 d5 : List UInt8) (hast : ast.length = 8) (hv3 : v3.length = 8) (hv4 : v4.length = 8) (hv5 : v5.length = 8) (hc0 : c0.length = 8) (hc1 : c1.length = 8) (hc2 : c2.length = 8) (hb0 : b0.length = 48) (hb1 : b1.length = 1) (hb2 : b2.length = 20) (hd0 : d0.length = 48) (hd1 : d1.length = 1) (hd2 : d2.length = 20) (hd3 : d3.length = 8) (hd4 : d4.length = 8) (hd5 : d5.length = 8)
    (p0 p1 p2 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l136 l144 l16 l152 l160 l32 t64 t48 t96 t80 t128 t112 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl136 : l136.length = 8) (hl144 : l144.length = 8) (hl16 : l16.length = 8) (hl152 : l152.length = 8) (hl160 : l160.length = 8) (hl32 : l32.length = 8) (ht64 : t64.length = 16) (ht48 : t48.length = 16) (ht96 : t96.length = 16) (ht80 : t80.length = 16) (ht128 : t128.length = 16) (ht112 : t112.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 224 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 93 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 157)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 216 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14
        ∧ st0.data.regs.get64 Reg64.rax = s.regs.rbx.toBitVec
        ∧ st0.data.regs.get64 Reg64.rcx = s.regs.rdi.toBitVec
        ∧ st0.data.regs.get64 Reg64.rdx = s.regs.rcx.toBitVec + 93 ∧
        ∃ (x0 x1 x2 x3 x4 x5 x6 : List UInt8), x0.length = S ∧ x1.length = 8 ∧ x2.length = 16 ∧ x3.length = 8 ∧ x4.length = 16 ∧ x5.length = 8 ∧ x6.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 136))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 152))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 69).toInt).At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (v3.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (v4.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (x4.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (v5.At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq (x5.At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq (x6.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 87)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 224))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 224 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 1).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (c2.At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (v3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (v5.At (s.regs.rax.toBitVec + 96))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b2.At p2)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (b2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 49))
          ⋆ Eq (v3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 69))
          ⋆ Eq (v4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 77))
          ⋆ Eq (v5.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 85))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec
        ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 93
        ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0
        ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8
        ∧ st.data.regs.rbp = s.regs.rbp
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 x2 x3 x4 x5 x6 : List UInt8), x0.length = S ∧ x1.length = 8 ∧ x2.length = 16 ∧ x3.length = 8 ∧ x4.length = 16 ∧ x5.length = 8 ∧ x6.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 136))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 152))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 69).toInt).At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (v3.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (v4.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (x4.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (v5.At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq (x5.At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq (x6.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 87)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 224))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 224 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 1).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (c2.At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (v3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (v5.At (s.regs.rax.toBitVec + 96))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b2.At p2)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (b2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 49))
          ⋆ Eq (v3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 69))
          ⋆ Eq (v4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 77))
          ⋆ Eq (v5.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 85))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v3 v4 v5 c0 c1 c2 b0 b1 b2 pre d0 d1 d2 d3 d4 d5 hast hv3 hv4 hv5 hc0 hc1 hc2 hb0 hb1 hb2 hd0 hd1 hd2 hd3 hd4 hd5 p0 p1 p2 s ra guard hpre fp s1 s2 l136 l144 l16 l152 l160 l32 t64 t48 t96 t80 t128 t112 rslot hfp hs1 hs2 hl136 hl144 hl16 hl152 hl160 hl32 ht64 ht48 ht96 ht80 ht128 ht112 hrslot R S scratch hsc hsp hcap hcap63
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hsp hcap hcap63 hpre ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, hrrax, hrrcx, hrrdx, x0, x1, x2, x3, x4, x5, x6, hx0, hx1, hx2, hx3, hx4, hx5, hx6, Hm⟩
  dsimp only at hpc hrsp hrbp hr14 hrrax hrrcx hrrdx Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14 hrrax hrrcx hrrdx Hm
  subst rsp1 rbp1 r141
  obtain rfl : rbx = rax1 := (UInt64.toBitVec_inj.mp hrrax).symm
  obtain rfl : rdi = rcx1 := (UInt64.toBitVec_inj.mp hrrcx).symm
  obtain rfl : rdx1 = { toBitVec := rcx.toBitVec + 93 } := UInt64.toBitVec_inj.mp hrrdx
  have hcap' : rcx.toBitVec.toNat + 93 ≤ rdi.toBitVec.toNat := hcap
  apply step_move_register Reg64.rbx Reg64.rdx _ (k + 157) (k + 158) (window_infix_at hk 157 1) (by rfl) (by rfl)
  normalize_registers
  apply step_xor32 Reg64.rdi _ (k + 158) (k + 159) (window_infix_at hk 158 1) (by rfl) (by rfl)
  intro fl; normalize_registers
  apply step_xor32 Reg64.rsi _ (k + 159) (k + 160) (window_infix_at hk 159 1) (by rfl) (by rfl)
  intro fl; normalize_registers
  apply step_add_immediate Reg64.rsp 208 _ (k + 160) (k + 161) (window_infix_at hk 160 1) (by rfl) (by rfl)
  intro fl; normalize_registers
  apply register_value_rewrite Reg64.rsp (rsp.toBitVec - 8) _ _ _ (by show ((rsp.toBitVec - 216) + 208 : BitVec 64) = (rsp.toBitVec - 8); bv_omega)
  normalize_registers
  refine eventually_trans _ _ _ _ (decode_return_segment _ (k + 161) (window_infix_at hk 161 2) (by rfl) (rsp.toBitVec - 8) rsp.toBitVec (by bv_omega) rbp ra _ _ (by rfl) (by ecancel)) ?_
  rintro ⟨d', pc'⟩ ⟨hpc', hrsp', hrbp', hreg', hmem'⟩
  dsimp only at hpc' hrsp' hrbp' hreg' hmem'
  apply Eventually.done
  refine ⟨hpc', ?_, ?_, ?_, ?_, ?_, ?_, hrbp', ?_, x0, x1, x2, x3, x4, x5, x6, hx0, hx1, hx2, hx3, hx4, hx5, hx6, ?_⟩
  · exact UInt64.toBitVec_inj.mp (hreg' Reg64.rax (by decide) (by decide))
  · show d'.regs.rbx.toBitVec.toNat = rcx.toBitVec.toNat + 93
    rw [show d'.regs.rbx.toBitVec = rcx.toBitVec + 93 from hreg' Reg64.rbx (by decide) (by decide)]
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
    = @Codec.encodeEpilogueKindAnyFrame h marshalSSZTo Prysm.Builder.Encode.generated_layout [.bytes 48, .bytes 1, .bytes 20, .uint64, .uint64, .uint64]
    ⟨157, 6, [(.rax, .ptr), (.rcx, .cap), (.rdx, .len 93)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 136) (.reg .rdi), .at (.below 144) (.len 48), .at (.below 16) (.reg .rbx), .at (.below 152) (.reg .rdi), .at (.below 160) (.len 69), .at (.below 32) (.reg .rbx), .at (.below 64) (.field 3), .at (.below 56) (.existential 1), .at (.below 48) (.existential 2), .at (.below 96) (.field 4), .at (.below 88) (.existential 3), .at (.below 80) (.existential 4), .at (.below 128) (.field 5), .at (.below 120) (.existential 5), .at (.below 112) (.existential 6), .at (.below 224) (.ret 87), .low (.existential 0)],
      [.low, .fixed 8, .fixed 16, .fixed 8, .fixed 16, .fixed 8, .fixed 16]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Encoder fast path of `(*v1alpha1.Builder).MarshalSSZTo` (Go 1.26.10), generated** (`encoder --fast-path`):
head, one theorem per field, epilogue, chained by `eventually_trans`. Premises: `len + 93 ≤ cap`,
every byte-vector field of its exact length. Statement = the kind instance (`_kind`). Fast path only. -/
theorem Encode.generated_fast : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v3 v4 v5 c0 c1 c2 b0 b1 b2 pre d0 d1 d2 d3 d4 d5 : List UInt8) (hast : ast.length = 8) (hv3 : v3.length = 8) (hv4 : v4.length = 8) (hv5 : v5.length = 8) (hc0 : c0.length = 8) (hc1 : c1.length = 8) (hc2 : c2.length = 8) (hb0 : b0.length = 48) (hb1 : b1.length = 1) (hb2 : b2.length = 20) (hd0 : d0.length = 48) (hd1 : d1.length = 1) (hd2 : d2.length = 20) (hd3 : d3.length = 8) (hd4 : d4.length = 8) (hd5 : d5.length = 8)
    (p0 p1 p2 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l136 l144 l16 l152 l160 l32 t64 t48 t96 t80 t128 t112 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl136 : l136.length = 8) (hl144 : l144.length = 8) (hl16 : l16.length = 8) (hl152 : l152.length = 8) (hl160 : l160.length = 8) (hl32 : l32.length = 8) (ht64 : t64.length = 16) (ht48 : t48.length = 16) (ht96 : t96.length = 16) (ht80 : t80.length = 16) (ht128 : t128.length = 16) (ht112 : t112.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l136.At (s.regs.rsp.toBitVec - 136))
      ⋆ Eq (l144.At (s.regs.rsp.toBitVec - 144))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (l152.At (s.regs.rsp.toBitVec - 152))
      ⋆ Eq (l160.At (s.regs.rsp.toBitVec - 160))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (t64.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (t48.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (t96.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (t80.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (t128.At (s.regs.rsp.toBitVec - 128))
      ⋆ Eq (t112.At (s.regs.rsp.toBitVec - 112))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 224))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 224 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
      ⋆ Eq ((Int.toBytes 8 1).At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 56))
      ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 64))
      ⋆ Eq (c2.At (s.regs.rax.toBitVec + 72))
      ⋆ Eq (v3.At (s.regs.rax.toBitVec + 80))
      ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
      ⋆ Eq (v5.At (s.regs.rax.toBitVec + 96))
      ⋆ Eq (b0.At p0)
      ⋆ Eq (b1.At p1)
      ⋆ Eq (b2.At p2)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 49))
      ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 69))
      ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 77))
      ⋆ Eq (d5.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 85))
      ⋆ R)
    (hguard : guard.toNat + 88 < s.regs.rsp.toNat) (hsp : 224 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 93 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec
        ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 93
        ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0
        ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8
        ∧ st.data.regs.rbp = s.regs.rbp
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 x2 x3 x4 x5 x6 : List UInt8), x0.length = S ∧ x1.length = 8 ∧ x2.length = 16 ∧ x3.length = 8 ∧ x4.length = 16 ∧ x5.length = 8 ∧ x6.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 136))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 152))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 69).toInt).At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (v3.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (v4.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (x4.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (v5.At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq (x5.At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq (x6.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 87)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 224))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 224 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 1).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 20).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (c2.At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (v3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (v5.At (s.regs.rax.toBitVec + 96))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b2.At p2)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (b2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 49))
          ⋆ Eq (v3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 69))
          ⋆ Eq (v4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 77))
          ⋆ Eq (v5.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 85))
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf ast v3 v4 v5 c0 c1 c2 b0 b1 b2 pre d0 d1 d2 d3 d4 d5 hast hv3 hv4 hv5 hc0 hc1 hc2 hb0 hb1 hb2 hd0 hd1 hd2 hd3 hd4 hd5 p0 p1 p2 s ra guard hpre fp s1 s2 l136 l144 l16 l152 l160 l32 t64 t48 t96 t80 t128 t112 rslot hfp hs1 hs2 hl136 hl144 hl16 hl152 hl160 hl32 ht64 ht48 ht96 ht80 ht128 ht112 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm
  refine eventually_trans _ _ _ _ (Encode.generated_head k hk hf ast v3 v4 v5 c0 c1 c2 b0 b1 b2 pre d0 d1 d2 d3 d4 d5 hast hv3 hv4 hv5 hc0 hc1 hc2 hb0 hb1 hb2 hd0 hd1 hd2 hd3 hd4 hd5 p0 p1 p2 s ra guard hpre fp s1 s2 l136 l144 l16 l152 l160 l32 t64 t48 t96 t80 t128 t112 rslot hfp hs1 hs2 hl136 hl144 hl16 hl152 hl160 hl32 ht64 ht48 ht96 ht80 ht128 ht112 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm) ?_
  intro st0 h0
  refine eventually_trans _ _ _ _ (Encode.generated_field_0 k hk hf ast v3 v4 v5 c0 c1 c2 b0 b1 b2 pre d0 d1 d2 d3 d4 d5 hast hv3 hv4 hv5 hc0 hc1 hc2 hb0 hb1 hb2 hd0 hd1 hd2 hd3 hd4 hd5 p0 p1 p2 s ra guard hpre fp s1 s2 l136 l144 l16 l152 l160 l32 t64 t48 t96 t80 t128 t112 rslot hfp hs1 hs2 hl136 hl144 hl16 hl152 hl160 hl32 ht64 ht48 ht96 ht80 ht128 ht112 hrslot R S scratch hsc hsp hcap hcap63 hmm st0 h0) ?_
  intro st1 h1
  refine eventually_trans _ _ _ _ (Encode.generated_field_1 k hk hf ast v3 v4 v5 c0 c1 c2 b0 b1 b2 pre d0 d1 d2 d3 d4 d5 hast hv3 hv4 hv5 hc0 hc1 hc2 hb0 hb1 hb2 hd0 hd1 hd2 hd3 hd4 hd5 p0 p1 p2 s ra guard hpre fp s1 s2 l136 l144 l16 l152 l160 l32 t64 t48 t96 t80 t128 t112 rslot hfp hs1 hs2 hl136 hl144 hl16 hl152 hl160 hl32 ht64 ht48 ht96 ht80 ht128 ht112 hrslot R S scratch hsc hsp hcap hcap63 hmm st1 h1) ?_
  intro st2 h2
  refine eventually_trans _ _ _ _ (Encode.generated_field_2 k hk hf ast v3 v4 v5 c0 c1 c2 b0 b1 b2 pre d0 d1 d2 d3 d4 d5 hast hv3 hv4 hv5 hc0 hc1 hc2 hb0 hb1 hb2 hd0 hd1 hd2 hd3 hd4 hd5 p0 p1 p2 s ra guard hpre fp s1 s2 l136 l144 l16 l152 l160 l32 t64 t48 t96 t80 t128 t112 rslot hfp hs1 hs2 hl136 hl144 hl16 hl152 hl160 hl32 ht64 ht48 ht96 ht80 ht128 ht112 hrslot R S scratch hsc hsp hcap hcap63 hmm st2 h2) ?_
  intro st3 h3
  refine eventually_trans _ _ _ _ (Encode.generated_field_3 k hk hf ast v3 v4 v5 c0 c1 c2 b0 b1 b2 pre d0 d1 d2 d3 d4 d5 hast hv3 hv4 hv5 hc0 hc1 hc2 hb0 hb1 hb2 hd0 hd1 hd2 hd3 hd4 hd5 p0 p1 p2 s ra guard hpre fp s1 s2 l136 l144 l16 l152 l160 l32 t64 t48 t96 t80 t128 t112 rslot hfp hs1 hs2 hl136 hl144 hl16 hl152 hl160 hl32 ht64 ht48 ht96 ht80 ht128 ht112 hrslot R S scratch hsc hsp hcap hcap63 hmm st3 h3) ?_
  intro st4 h4
  refine eventually_trans _ _ _ _ (Encode.generated_field_4 k hk hf ast v3 v4 v5 c0 c1 c2 b0 b1 b2 pre d0 d1 d2 d3 d4 d5 hast hv3 hv4 hv5 hc0 hc1 hc2 hb0 hb1 hb2 hd0 hd1 hd2 hd3 hd4 hd5 p0 p1 p2 s ra guard hpre fp s1 s2 l136 l144 l16 l152 l160 l32 t64 t48 t96 t80 t128 t112 rslot hfp hs1 hs2 hl136 hl144 hl16 hl152 hl160 hl32 ht64 ht48 ht96 ht80 ht128 ht112 hrslot R S scratch hsc hsp hcap hcap63 hmm st4 h4) ?_
  intro st5 h5
  refine eventually_trans _ _ _ _ (Encode.generated_field_5 k hk hf ast v3 v4 v5 c0 c1 c2 b0 b1 b2 pre d0 d1 d2 d3 d4 d5 hast hv3 hv4 hv5 hc0 hc1 hc2 hb0 hb1 hb2 hd0 hd1 hd2 hd3 hd4 hd5 p0 p1 p2 s ra guard hpre fp s1 s2 l136 l144 l16 l152 l160 l32 t64 t48 t96 t80 t128 t112 rslot hfp hs1 hs2 hl136 hl144 hl16 hl152 hl160 hl32 ht64 ht48 ht96 ht80 ht128 ht112 hrslot R S scratch hsc hsp hcap hcap63 hmm st5 h5) ?_
  intro st6 h6
  exact Encode.generated_epilogue k hk hf ast v3 v4 v5 c0 c1 c2 b0 b1 b2 pre d0 d1 d2 d3 d4 d5 hast hv3 hv4 hv5 hc0 hc1 hc2 hb0 hb1 hb2 hd0 hd1 hd2 hd3 hd4 hd5 p0 p1 p2 s ra guard hpre fp s1 s2 l136 l144 l16 l152 l160 l32 t64 t48 t96 t80 t128 t112 rslot hfp hs1 hs2 hl136 hl144 hl16 hl152 hl160 hl32 ht64 ht48 ht96 ht80 ht128 ht112 hrslot R S scratch hsc hsp hcap hcap63 st6 h6
theorem Encode.generated_fast_kind : ∀ (h : Host), type_of% (@Encode.generated_fast h)
    = @Codec.encodeFastPathKindAnyFrame h marshalSSZTo Prysm.Builder.Encode.generated_layout [.bytes 48, .bytes 1, .bytes 20, .uint64, .uint64, .uint64] := by
  intro h; rfl

end Prysm.Builder
