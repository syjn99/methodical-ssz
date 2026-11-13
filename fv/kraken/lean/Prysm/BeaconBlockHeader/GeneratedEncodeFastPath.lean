import Prysm.BeaconBlockHeader.EncodeFastPathKindInstances
import Codec.EncodeFrameTest
import Prysm.BeaconBlockHeader.Code

/-!
# Fast path (`encoder --fast-path`): encoder fast path of `(*v1alpha1.BeaconBlockHeader).MarshalSSZTo`

Generated from the `.S` file and the IR: a symbolic dataflow walk of the fast path, one application of a
step lemma per directive (windows with the nops erased), boundary states between the fields. Every theorem
has a `_kind` line (`encHeadKindAnyFrame`, `encFieldKindAnyFrame`, `encEpilogueKindAnyFrame`, `encFastPathKindAnyFrame`).
**Fast path only**: `len(dst) + 112 ≤ cap(dst)` and every byte-vector field of its exact length. No
`runtime.growslice` directive is stepped: each capacity test is decided from the premise. Not covered: the
growslice branches, the length rejects, the morestack path. Not a complete encoder result.
The statement is the declared type of the committed hand theorem `Prysm.BeaconBlockHeader.Encode.fast_path`.
FAST-PATH-JSON: {"type": "BeaconBlockHeader", "const": "marshalSSZTo", "prefix": "Encode.generated", "size": 112, "frame": 152, "guard_addend": 32, "runtime_calls": true, "fields": [["Slot", "u", 8], ["ProposerIndex", "u", 8], ["ParentRoot", "b", 32], ["StateRoot", "b", 32], ["BodyRoot", "b", 32]], "boundaries": [10, 36, 62, 90, 118, 148], "layout": "Prysm.BeaconBlockHeader.encodeLayout", "S_sha256": "c76a57703af0f5d5889921baf6b3844b81d043b466b5e17df02a8b5d218124f3", "ir_sha256": "c1586d32018abd182c16d50f6a7a76e38814cab08cf4a7a42105fe30342a5d2a", "statement_check": "same Prysm.BeaconBlockHeader.Encode.fast_path", "S": "prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo.S", "ir": "prysm/ir/ir-mainnet.json", "ir_type": "v1alpha1.BeaconBlockHeader", "kinds": [{"theorem": "Encode.generated_head", "kind": "encHeadKindAnyFrame"}, {"theorem": "Encode.generated_field_0", "kind": "encFieldKindAnyFrame"}, {"theorem": "Encode.generated_field_1", "kind": "encFieldKindAnyFrame"}, {"theorem": "Encode.generated_field_2", "kind": "encFieldKindAnyFrame"}, {"theorem": "Encode.generated_field_3", "kind": "encFieldKindAnyFrame"}, {"theorem": "Encode.generated_field_4", "kind": "encFieldKindAnyFrame"}, {"theorem": "Encode.generated_epilogue", "kind": "encEpilogueKindAnyFrame"}, {"theorem": "Encode.generated_fast", "kind": "encFastPathKindAnyFrame"}]}
-/

open Machine Runtime Codec Prysm.BeaconBlockHeader.Code
variable [Host]

namespace Prysm.BeaconBlockHeader

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Head: directives 0–9 (stack guard, frame, spills); entry → boundary state 0. -/
theorem Encode.generated_head : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v0 v1 c2 c3 c4 b2 b3 b4 pre d0 d1 d2 d3 d4 : List UInt8) (hast : ast.length = 8) (hv0 : v0.length = 8) (hv1 : v1.length = 8) (hc2 : c2.length = 8) (hc3 : c3.length = 8) (hc4 : c4.length = 8) (hb2 : b2.length = 32) (hb3 : b3.length = 32) (hb4 : b4.length = 32) (hd0 : d0.length = 8) (hd1 : d1.length = 8) (hd2 : d2.length = 32) (hd3 : d3.length = 32) (hd4 : d4.length = 32)
    (p2 p3 p4 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l96 l104 t56 t40 t88 t72 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8) (hl96 : l96.length = 8) (hl104 : l104.length = 8) (ht56 : t56.length = 16) (ht40 : t40.length = 16) (ht88 : t88.length = 16) (ht72 : t72.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (l96.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (l104.At (s.regs.rsp.toBitVec - 104))
      ⋆ Eq (t56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (t88.At (s.regs.rsp.toBitVec - 88))
      ⋆ Eq (t72.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 168))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 168 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (c2.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 56))
      ⋆ Eq (c3.At (s.regs.rax.toBitVec + 64))
      ⋆ Eq ((Int.toBytes 8 p4.toInt).At (s.regs.rax.toBitVec + 72))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 80))
      ⋆ Eq (c4.At (s.regs.rax.toBitVec + 88))
      ⋆ Eq (b2.At p2)
      ⋆ Eq (b3.At p3)
      ⋆ Eq (b4.At p4)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
      ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
      ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
      ⋆ R)
    (hguard : guard.toNat + 32 < s.regs.rsp.toNat) (hsp : 168 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 112 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 10)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 160 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.get64 Reg64.rax = s.regs.rax.toBitVec
        ∧ st.data.regs.get64 Reg64.rbx = s.regs.rbx.toBitVec
        ∧ st.data.regs.get64 Reg64.rcx = s.regs.rcx.toBitVec
        ∧ st.data.regs.get64 Reg64.rdi = s.regs.rdi.toBitVec ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq (l96.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (l104.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (t56.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (t88.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (t72.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 168))
          ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 168 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (c2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 p4.toInt).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (c4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b2.At p2)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (b4.At p4)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
          ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf ast v0 v1 c2 c3 c4 b2 b3 b4 pre d0 d1 d2 d3 d4 hast hv0 hv1 hc2 hc3 hc4 hb2 hb3 hb4 hd0 hd1 hd2 hd3 hd4 p2 p3 p4 s ra guard hpre fp s1 s2 l16 l96 l104 t56 t40 t88 t72 rslot hfp hs1 hs2 hl16 hl96 hl104 ht56 ht40 ht88 ht72 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hcap hcap63 hpre ⊢
  have hcap' : rcx.toBitVec.toNat + 112 ≤ rdi.toBitVec.toNat := hcap
  apply encoder_prologue_large_frame _ _ _ (-32) 32 _ k (k + 7) (window_infix_at hk 0 7) (by rfl) (by rfl) (by rfl) guard fp hfp _ _ _ (by dsimp only; ecancel) hguard
  intro m1 H1 fl1; normalize_registers; dsimp only at H1
  apply step_sub_immediate Reg64.rsp 152 _ (k + 7) (k + 8) (window_infix_at hk 7 1) (by rfl) (by rfl)
  intro fl; normalize_registers
  apply register_value_rewrite Reg64.rsp (rsp.toBitVec - 160) _ _ _ (by show ((rsp.toBitVec - 8) - 152 : BitVec 64) = (rsp.toBitVec - 160); bv_omega)
  normalize_registers
  apply step_store Reg64.rbx Reg64.rsp 176 _ (k + 8) (k + 9) (window_infix_at hk 8 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec + 16) (by encoder_address_equation) s2 hs2 _ _ _ (by rfl) (by ecancel)
  intro m2 H2; normalize_registers; simp only [Reg64s.get64] at H2
  apply step_store Reg64.rax Reg64.rsp 168 _ (k + 9) (k + 10) (window_infix_at hk 9 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec + 8) (by encoder_address_equation) s1 hs1 _ _ _ (by rfl) (by ecancel)
  intro m3 H3; normalize_registers; simp only [Reg64s.get64] at H3
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem Encode.generated_head_kind : ∀ (h : Host), type_of% (@Encode.generated_head h)
    = @Codec.encHeadKindAnyFrame h marshalSSZTo Prysm.BeaconBlockHeader.encodeLayout [.u64, .u64, .bytes 32, .bytes 32, .bytes 32]
    ⟨10, 0, [(.rax, .receiver), (.rbx, .ptr), (.rcx, .len 0), (.rdi, .cap)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 16) (.original 3), .at (.below 96) (.original 4), .at (.below 104) (.original 5), .at (.below 56) (.original 6), .at (.below 40) (.original 7), .at (.below 88) (.original 8), .at (.below 72) (.original 9), .at (.below 168) (.original 10), .low .scratch],
      []⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 0 `Slot` (uint64): directives 10–35; boundary state 0 → 1. -/
theorem Encode.generated_field_0 : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v0 v1 c2 c3 c4 b2 b3 b4 pre d0 d1 d2 d3 d4 : List UInt8) (hast : ast.length = 8) (hv0 : v0.length = 8) (hv1 : v1.length = 8) (hc2 : c2.length = 8) (hc3 : c3.length = 8) (hc4 : c4.length = 8) (hb2 : b2.length = 32) (hb3 : b3.length = 32) (hb4 : b4.length = 32) (hd0 : d0.length = 8) (hd1 : d1.length = 8) (hd2 : d2.length = 32) (hd3 : d3.length = 32) (hd4 : d4.length = 32)
    (p2 p3 p4 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l96 l104 t56 t40 t88 t72 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8) (hl96 : l96.length = 8) (hl104 : l104.length = 8) (ht56 : t56.length = 16) (ht40 : t40.length = 16) (ht88 : t88.length = 16) (ht72 : t72.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 168 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 112 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 10)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 160 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14
        ∧ st0.data.regs.get64 Reg64.rax = s.regs.rax.toBitVec
        ∧ st0.data.regs.get64 Reg64.rbx = s.regs.rbx.toBitVec
        ∧ st0.data.regs.get64 Reg64.rcx = s.regs.rcx.toBitVec
        ∧ st0.data.regs.get64 Reg64.rdi = s.regs.rdi.toBitVec ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq (l96.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (l104.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (t56.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (t88.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (t72.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 168))
          ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 168 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (c2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 p4.toInt).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (c4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b2.At p2)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (b4.At p4)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
          ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 36)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 160 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.get64 Reg64.rax = s.regs.rax.toBitVec
        ∧ st.data.regs.get64 Reg64.rbx = s.regs.rbx.toBitVec
        ∧ st.data.regs.get64 Reg64.rdx = s.regs.rcx.toBitVec + 8
        ∧ st.data.regs.get64 Reg64.rdi = s.regs.rdi.toBitVec ∧
        ∃ (x0 x1 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq (l96.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (l104.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (t88.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (t72.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 168))
          ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 168 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (c2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 p4.toInt).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (c4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b2.At p2)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (b4.At p4)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
          ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v0 v1 c2 c3 c4 b2 b3 b4 pre d0 d1 d2 d3 d4 hast hv0 hv1 hc2 hc3 hc4 hb2 hb3 hb4 hd0 hd1 hd2 hd3 hd4 p2 p3 p4 s ra guard hpre fp s1 s2 l16 l96 l104 t56 t40 t88 t72 rslot hfp hs1 hs2 hl16 hl96 hl104 ht56 ht40 ht88 ht72 hrslot R S scratch hsc hsp hcap hcap63 hmm
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
  have hcap' : rcx.toBitVec.toNat + 112 ≤ rdi.toBitVec.toNat := hcap
  apply step_lea Reg64.rdx Reg64.rcx 8 _ (k + 10) (k + 11) (window_infix_at hk 10 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.rdx (rcx.toBitVec + 8) _ _ _ (by show (rcx.toBitVec + 8 : BitVec 64) = (rcx.toBitVec + 8); bv_omega)
  normalize_registers
  apply step_load_bytes Reg64.r8 Reg64.rax 8 _ (k + 11) (k + 12) (window_infix_at hk 11 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 8) (by encoder_address_equation) v0 hv0 _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_lea Reg64.r9 Reg64.rsp 104 _ (k + 12) (k + 16) (window_infix_at hk 12 4) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.r9 (rsp.toBitVec - 56) _ _ _ (by show ((rsp.toBitVec - 160) + 104 : BitVec 64) = (rsp.toBitVec - 56); bv_omega)
  normalize_registers
  apply step_store_xmm15 Reg64.r9 0 _ (k + 16) (k + 17) (window_infix_at hk 16 1) (by rfl) (by rfl)
    (rsp.toBitVec - 56) (rsp.toBitVec - 56) (by encoder_address_equation) t56 ht56 _ _ _ (by rfl) (by ecancel)
  intro m4 H4; normalize_registers; try dsimp only at H4
  apply step_store_xmm15 Reg64.r9 16 _ (k + 17) (k + 18) (window_infix_at hk 17 1) (by rfl) (by rfl)
    (rsp.toBitVec - 56) (rsp.toBitVec - 40) (by encoder_address_equation) t40 ht40 _ _ _ (by rfl) (by ecancel)
  intro m5 H5; normalize_registers; try dsimp only at H5
  rw [Machine.at_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 56), show (rsp.toBitVec - 56) + 8 = (rsp.toBitVec - 48) by bv_omega] at H5
  apply step_store Reg64.r8 Reg64.rsp 104 _ (k + 18) (k + 19) (window_infix_at hk 18 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 56) (by encoder_address_equation) ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).take 8) (by rw [List.length_take, Int.toBytes_length]; rfl) _ _ _ (by rfl) (by ecancel)
  intro m6 H6; normalize_registers; simp only [Reg64s.get64] at H6
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v0 hv0] at H6
  have hl33 := Machine.label_at' hk hf (j := 33)
    (by simp only [marshalSSZTo, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply step_cmp_jae_taken Reg64.rdi Reg64.rdx _ _ (k + 19) (k + 33) (window_infix_at hk 19 2) (by rfl) hl33 _ _ (by show ((rcx.toBitVec + 8) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; normalize_registers
  apply step_label _ _ (k + 33) (k + 34) (window_infix_at hk 33 1) (by rfl) (by rfl)
  apply step_load_bytes Reg64.r8 Reg64.rsp 104 _ (k + 34) (k + 35) (window_infix_at hk 34 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 56) (by encoder_address_equation) v0 hv0 _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_store_indexed Reg64.r8 Reg64.rbx Reg64.rcx 0 _ (k + 35) (k + 36) (window_infix_at hk 35 1) (by rfl) (by rfl)
    rbx.toBitVec rcx.toBitVec (rbx.toBitVec + rcx.toBitVec) (by encoder_address_equation) d0 hd0 _ _ _ (by rfl) (by rfl) (by ecancel)
  intro m7 H7; normalize_registers; simp only [Reg64s.get64] at H7
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v0 hv0] at H7
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8), (Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt), (by rw [List.length_drop, Int.toBytes_length]), (Int.toBytes_length 16 _), ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem Encode.generated_field_0_kind : ∀ (h : Host), type_of% (@Encode.generated_field_0 h)
    = @Codec.encFieldKindAnyFrame h marshalSSZTo Prysm.BeaconBlockHeader.encodeLayout [.u64, .u64, .bytes 32, .bytes 32, .bytes 32]
    ⟨10, 0, [(.rax, .receiver), (.rbx, .ptr), (.rcx, .len 0), (.rdi, .cap)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 16) (.original 3), .at (.below 96) (.original 4), .at (.below 104) (.original 5), .at (.below 56) (.original 6), .at (.below 40) (.original 7), .at (.below 88) (.original 8), .at (.below 72) (.original 9), .at (.below 168) (.original 10), .low .scratch],
      []⟩
    ⟨36, 1, [(.rax, .receiver), (.rbx, .ptr), (.rdx, .len 8), (.rdi, .cap)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 16) (.original 3), .at (.below 96) (.original 4), .at (.below 104) (.original 5), .at (.below 56) (.field 0), .at (.below 48) (.existential 0), .at (.below 40) (.existential 1), .at (.below 88) (.original 8), .at (.below 72) (.original 9), .at (.below 168) (.original 10), .low .scratch],
      [.fixed 8, .fixed 16]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 1 `ProposerIndex` (uint64): directives 36–61; boundary state 1 → 2. -/
theorem Encode.generated_field_1 : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v0 v1 c2 c3 c4 b2 b3 b4 pre d0 d1 d2 d3 d4 : List UInt8) (hast : ast.length = 8) (hv0 : v0.length = 8) (hv1 : v1.length = 8) (hc2 : c2.length = 8) (hc3 : c3.length = 8) (hc4 : c4.length = 8) (hb2 : b2.length = 32) (hb3 : b3.length = 32) (hb4 : b4.length = 32) (hd0 : d0.length = 8) (hd1 : d1.length = 8) (hd2 : d2.length = 32) (hd3 : d3.length = 32) (hd4 : d4.length = 32)
    (p2 p3 p4 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l96 l104 t56 t40 t88 t72 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8) (hl96 : l96.length = 8) (hl104 : l104.length = 8) (ht56 : t56.length = 16) (ht40 : t40.length = 16) (ht88 : t88.length = 16) (ht72 : t72.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 168 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 112 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 36)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 160 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14
        ∧ st0.data.regs.get64 Reg64.rax = s.regs.rax.toBitVec
        ∧ st0.data.regs.get64 Reg64.rbx = s.regs.rbx.toBitVec
        ∧ st0.data.regs.get64 Reg64.rdx = s.regs.rcx.toBitVec + 8
        ∧ st0.data.regs.get64 Reg64.rdi = s.regs.rdi.toBitVec ∧
        ∃ (x0 x1 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq (l96.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (l104.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (t88.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (t72.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 168))
          ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 168 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (c2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 p4.toInt).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (c4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b2.At p2)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (b4.At p4)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
          ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 62)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 160 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.get64 Reg64.rax = s.regs.rax.toBitVec
        ∧ st.data.regs.get64 Reg64.rbx = s.regs.rbx.toBitVec
        ∧ st.data.regs.get64 Reg64.rdi = s.regs.rdi.toBitVec
        ∧ st.data.regs.get64 Reg64.r8 = s.regs.rcx.toBitVec + 16 ∧
        ∃ (x0 x1 x2 x3 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧ x2.length = 8 ∧ x3.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq (l96.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (l104.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (v1.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 168))
          ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 168 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (c2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 p4.toInt).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (c4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b2.At p2)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (b4.At p4)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
          ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v0 v1 c2 c3 c4 b2 b3 b4 pre d0 d1 d2 d3 d4 hast hv0 hv1 hc2 hc3 hc4 hb2 hb3 hb4 hd0 hd1 hd2 hd3 hd4 p2 p3 p4 s ra guard hpre fp s1 s2 l16 l96 l104 t56 t40 t88 t72 rslot hfp hs1 hs2 hl16 hl96 hl104 ht56 ht40 ht88 ht72 hrslot R S scratch hsc hsp hcap hcap63 hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hsp hcap hcap63 hpre ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, hrrax, hrrbx, hrrdx, hrrdi, x0, x1, hx0, hx1, Hm⟩
  dsimp only at hpc hrsp hrbp hr14 hrrax hrrbx hrrdx hrrdi Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14 hrrax hrrbx hrrdx hrrdi Hm
  subst rsp1 rbp1 r141
  obtain rfl : rax = rax1 := (UInt64.toBitVec_inj.mp hrrax).symm
  obtain rfl : rbx = rbx1 := (UInt64.toBitVec_inj.mp hrrbx).symm
  obtain rfl : rdx1 = { toBitVec := rcx.toBitVec + 8 } := UInt64.toBitVec_inj.mp hrrdx
  obtain rfl : rdi = rdi1 := (UInt64.toBitVec_inj.mp hrrdi).symm
  have hcap' : rcx.toBitVec.toNat + 112 ≤ rdi.toBitVec.toNat := hcap
  apply step_lea Reg64.r8 Reg64.rdx 8 _ (k + 36) (k + 37) (window_infix_at hk 36 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.r8 (rcx.toBitVec + 16) _ _ _ (by show ((rcx.toBitVec + 8) + 8 : BitVec 64) = (rcx.toBitVec + 16); bv_omega)
  normalize_registers
  apply step_load_bytes Reg64.r9 Reg64.rax 16 _ (k + 37) (k + 38) (window_infix_at hk 37 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 16) (by encoder_address_equation) v1 hv1 _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_lea Reg64.r10 Reg64.rsp 72 _ (k + 38) (k + 42) (window_infix_at hk 38 4) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.r10 (rsp.toBitVec - 88) _ _ _ (by show ((rsp.toBitVec - 160) + 72 : BitVec 64) = (rsp.toBitVec - 88); bv_omega)
  normalize_registers
  apply step_store_xmm15 Reg64.r10 0 _ (k + 42) (k + 43) (window_infix_at hk 42 1) (by rfl) (by rfl)
    (rsp.toBitVec - 88) (rsp.toBitVec - 88) (by encoder_address_equation) t88 ht88 _ _ _ (by rfl) (by ecancel)
  intro m8 H8; normalize_registers; try dsimp only at H8
  apply step_store_xmm15 Reg64.r10 16 _ (k + 43) (k + 44) (window_infix_at hk 43 1) (by rfl) (by rfl)
    (rsp.toBitVec - 88) (rsp.toBitVec - 72) (by encoder_address_equation) t72 ht72 _ _ _ (by rfl) (by ecancel)
  intro m9 H9; normalize_registers; try dsimp only at H9
  rw [Machine.at_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 88), show (rsp.toBitVec - 88) + 8 = (rsp.toBitVec - 80) by bv_omega] at H9
  apply step_store Reg64.r9 Reg64.rsp 72 _ (k + 44) (k + 45) (window_infix_at hk 44 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 88) (by encoder_address_equation) ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).take 8) (by rw [List.length_take, Int.toBytes_length]; rfl) _ _ _ (by rfl) (by ecancel)
  intro m10 H10; normalize_registers; simp only [Reg64s.get64] at H10
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v1 hv1] at H10
  have hl59 := Machine.label_at' hk hf (j := 59)
    (by simp only [marshalSSZTo, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply step_cmp_jae_taken Reg64.rdi Reg64.r8 _ _ (k + 45) (k + 59) (window_infix_at hk 45 2) (by rfl) hl59 _ _ (by show ((rcx.toBitVec + 16) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; normalize_registers
  apply step_label _ _ (k + 59) (k + 60) (window_infix_at hk 59 1) (by rfl) (by rfl)
  apply step_load_bytes Reg64.r9 Reg64.rsp 72 _ (k + 60) (k + 61) (window_infix_at hk 60 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 88) (by encoder_address_equation) v1 hv1 _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_store_indexed Reg64.r9 Reg64.rbx Reg64.rdx 0 _ (k + 61) (k + 62) (window_infix_at hk 61 1) (by rfl) (by rfl)
    rbx.toBitVec (rcx.toBitVec + 8) (rbx.toBitVec + rcx.toBitVec + 8) (by encoder_address_equation) d1 hd1 _ _ _ (by rfl) (by rfl) (by ecancel)
  intro m11 H11; normalize_registers; simp only [Reg64s.get64] at H11
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v1 hv1] at H11
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, x0, x1, ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8), (Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt), hx0, hx1, (by rw [List.length_drop, Int.toBytes_length]), (Int.toBytes_length 16 _), ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem Encode.generated_field_1_kind : ∀ (h : Host), type_of% (@Encode.generated_field_1 h)
    = @Codec.encFieldKindAnyFrame h marshalSSZTo Prysm.BeaconBlockHeader.encodeLayout [.u64, .u64, .bytes 32, .bytes 32, .bytes 32]
    ⟨36, 1, [(.rax, .receiver), (.rbx, .ptr), (.rdx, .len 8), (.rdi, .cap)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 16) (.original 3), .at (.below 96) (.original 4), .at (.below 104) (.original 5), .at (.below 56) (.field 0), .at (.below 48) (.existential 0), .at (.below 40) (.existential 1), .at (.below 88) (.original 8), .at (.below 72) (.original 9), .at (.below 168) (.original 10), .low .scratch],
      [.fixed 8, .fixed 16]⟩
    ⟨62, 2, [(.rax, .receiver), (.rbx, .ptr), (.rdi, .cap), (.r8, .len 16)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 16) (.original 3), .at (.below 96) (.original 4), .at (.below 104) (.original 5), .at (.below 56) (.field 0), .at (.below 48) (.existential 0), .at (.below 40) (.existential 1), .at (.below 88) (.field 1), .at (.below 80) (.existential 2), .at (.below 72) (.existential 3), .at (.below 168) (.original 10), .low .scratch],
      [.fixed 8, .fixed 16, .fixed 8, .fixed 16]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 2 `ParentRoot` (32 bytes): directives 62–89; boundary state 2 → 3. -/
theorem Encode.generated_field_2 : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v0 v1 c2 c3 c4 b2 b3 b4 pre d0 d1 d2 d3 d4 : List UInt8) (hast : ast.length = 8) (hv0 : v0.length = 8) (hv1 : v1.length = 8) (hc2 : c2.length = 8) (hc3 : c3.length = 8) (hc4 : c4.length = 8) (hb2 : b2.length = 32) (hb3 : b3.length = 32) (hb4 : b4.length = 32) (hd0 : d0.length = 8) (hd1 : d1.length = 8) (hd2 : d2.length = 32) (hd3 : d3.length = 32) (hd4 : d4.length = 32)
    (p2 p3 p4 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l96 l104 t56 t40 t88 t72 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8) (hl96 : l96.length = 8) (hl104 : l104.length = 8) (ht56 : t56.length = 16) (ht40 : t40.length = 16) (ht88 : t88.length = 16) (ht72 : t72.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 168 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 112 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 62)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 160 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14
        ∧ st0.data.regs.get64 Reg64.rax = s.regs.rax.toBitVec
        ∧ st0.data.regs.get64 Reg64.rbx = s.regs.rbx.toBitVec
        ∧ st0.data.regs.get64 Reg64.rdi = s.regs.rdi.toBitVec
        ∧ st0.data.regs.get64 Reg64.r8 = s.regs.rcx.toBitVec + 16 ∧
        ∃ (x0 x1 x2 x3 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧ x2.length = 8 ∧ x3.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq (l96.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (l104.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (v1.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 168))
          ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 168 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (c2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 p4.toInt).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (c4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b2.At p2)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (b4.At p4)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
          ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 90)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 160 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 x2 x3 x4 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧ x2.length = 8 ∧ x3.length = 16 ∧ x4.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (v1.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 90)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 168))
          ⋆ Eq (x4.At (s.regs.rsp.toBitVec - 168 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (c2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 p4.toInt).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (c4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b2.At p2)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (b4.At p4)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (b2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
          ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v0 v1 c2 c3 c4 b2 b3 b4 pre d0 d1 d2 d3 d4 hast hv0 hv1 hc2 hc3 hc4 hb2 hb3 hb4 hd0 hd1 hd2 hd3 hd4 p2 p3 p4 s ra guard hpre fp s1 s2 l16 l96 l104 t56 t40 t88 t72 rslot hfp hs1 hs2 hl16 hl96 hl104 ht56 ht40 ht88 ht72 hrslot R S scratch hsc hsp hcap hcap63 hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hsp hcap hcap63 hpre ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, hrrax, hrrbx, hrrdi, hrr8, x0, x1, x2, x3, hx0, hx1, hx2, hx3, Hm⟩
  dsimp only at hpc hrsp hrbp hr14 hrrax hrrbx hrrdi hrr8 Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14 hrrax hrrbx hrrdi hrr8 Hm
  subst rsp1 rbp1 r141
  obtain rfl : rax = rax1 := (UInt64.toBitVec_inj.mp hrrax).symm
  obtain rfl : rbx = rbx1 := (UInt64.toBitVec_inj.mp hrrbx).symm
  obtain rfl : rdi = rdi1 := (UInt64.toBitVec_inj.mp hrrdi).symm
  obtain rfl : r81 = { toBitVec := rcx.toBitVec + 16 } := UInt64.toBitVec_inj.mp hrr8
  have hcap' : rcx.toBitVec.toNat + 112 ≤ rdi.toBitVec.toNat := hcap
  apply step_load_value Reg64.rdx Reg64.rax 24 _ (k + 62) (k + 63) (window_infix_at hk 62 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 24) p2 (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_length_check Reg64.rax 32 32 _ _ (k + 63) (k + 66) (window_infix_at hk 63 3) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 32) (by encoder_address_equation) (Int.toBytes 8 32) (by rfl) (by decide) _ _ _ (by rfl) (by ecancel)
  intro fl; normalize_registers
  apply step_lea Reg64.r9 Reg64.r8 32 _ (k + 66) (k + 67) (window_infix_at hk 66 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.r9 (rcx.toBitVec + 48) _ _ _ (by show ((rcx.toBitVec + 16) + 32 : BitVec 64) = (rcx.toBitVec + 48); bv_omega)
  normalize_registers
  have hl82 := Machine.label_at' hk hf (j := 82)
    (by simp only [marshalSSZTo, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply step_cmp_jae_taken Reg64.rdi Reg64.r9 _ _ (k + 67) (k + 82) (window_infix_at hk 67 2) (by rfl) hl82 _ _ (by show ((rcx.toBitVec + 48) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; normalize_registers
  apply step_label _ _ (k + 82) (k + 83) (window_infix_at hk 82 1) (by rfl) (by rfl)
  apply step_store Reg64.rbx Reg64.rsp 144 _ (k + 83) (k + 84) (window_infix_at hk 83 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 16) (by encoder_address_equation) l16 hl16 _ _ _ (by rfl) (by ecancel)
  intro m12 H12; normalize_registers; simp only [Reg64s.get64] at H12
  apply step_store Reg64.r9 Reg64.rsp 64 _ (k + 84) (k + 85) (window_infix_at hk 84 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 96) (by encoder_address_equation) l96 hl96 _ _ _ (by rfl) (by ecancel)
  intro m13 H13; normalize_registers; simp only [Reg64s.get64] at H13
  apply step_store Reg64.rdi Reg64.rsp 56 _ (k + 85) (k + 86) (window_infix_at hk 85 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 104) (by encoder_address_equation) l104 hl104 _ _ _ (by rfl) (by ecancel)
  intro m14 H14; normalize_registers; simp only [Reg64s.get64] at H14
  apply step_lea_indexed Reg64.rax Reg64.rbx Reg64.r8 _ (k + 86) (k + 87) (window_infix_at hk 86 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.rax (rbx.toBitVec + rcx.toBitVec + 16) _ _ _ (by show (rbx.toBitVec + (rcx.toBitVec + 16) : BitVec 64) = (rbx.toBitVec + rcx.toBitVec + 16); bv_omega)
  normalize_registers
  apply step_move_register Reg64.rbx Reg64.rdx _ (k + 87) (k + 88) (window_infix_at hk 87 1) (by rfl) (by rfl)
  normalize_registers
  apply step_move_immediate Reg64.rcx 32 _ (k + 88) (k + 89) (window_infix_at hk 88 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.rcx 32 _ _ _ (by show (BitVec.zeroExtend 64 (BitVec.truncate 32 (32 : BitVec 64)) : BitVec 64) = 32; decide)
  normalize_registers
  refine eventually_trans _ _ _ _ (encode_memmove_call (k + 89) (window_infix_at hk 89 1) (rsp.toBitVec - 160) (rbx.toBitVec + rcx.toBitVec + 16) p2
    (rsp.toBitVec - 168) (rsp.toBitVec - 168 - BitVec.ofNat 64 S) S (by bv_omega) (Codec.frame_low_address_without_calls rsp.toBitVec 160 168 S (by decide))
    b2 d2 rslot scratch (by rw [hd2, hb2]) hrslot hsc
    _ _ (by rfl) (by rfl) (by rfl) (by rw [hb2]; rfl) (by first | ecancel | (dsimp only; ecancel)) hmm) ?_
  rintro ⟨e1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, scr1, hscr1, Hc1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 Hc1
  subst hpc1
  obtain ⟨⟨raxc1, rbxc1, rcxc1, rdxc1, rsic1, rdic1, rspc1, rbpc1, r8c1, r9c1, r10c1, r11c1, r12c1, r13c1, r14c1, r15c1⟩, zmmsc1, flagsc1, memc1⟩ := e1
  simp only at hrsp1 hrbp1 hr141 Hc1
  subst rspc1 rbpc1 r14c1
  rw [show k + 89 + 1 = k + 90 from rfl] at Hc1
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, x0, x1, x2, x3, scr1, hx0, hx1, hx2, hx3, hscr1, ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem Encode.generated_field_2_kind : ∀ (h : Host), type_of% (@Encode.generated_field_2 h)
    = @Codec.encFieldKindAnyFrame h marshalSSZTo Prysm.BeaconBlockHeader.encodeLayout [.u64, .u64, .bytes 32, .bytes 32, .bytes 32]
    ⟨62, 2, [(.rax, .receiver), (.rbx, .ptr), (.rdi, .cap), (.r8, .len 16)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 16) (.original 3), .at (.below 96) (.original 4), .at (.below 104) (.original 5), .at (.below 56) (.field 0), .at (.below 48) (.existential 0), .at (.below 40) (.existential 1), .at (.below 88) (.field 1), .at (.below 80) (.existential 2), .at (.below 72) (.existential 3), .at (.below 168) (.original 10), .low .scratch],
      [.fixed 8, .fixed 16, .fixed 8, .fixed 16]⟩
    ⟨90, 3, [],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 16) (.reg .rbx), .at (.below 96) (.len 48), .at (.below 104) (.reg .rdi), .at (.below 56) (.field 0), .at (.below 48) (.existential 0), .at (.below 40) (.existential 1), .at (.below 88) (.field 1), .at (.below 80) (.existential 2), .at (.below 72) (.existential 3), .at (.below 168) (.ret 90), .low (.existential 4)],
      [.fixed 8, .fixed 16, .fixed 8, .fixed 16, .low]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 3 `StateRoot` (32 bytes): directives 90–117; boundary state 3 → 4. -/
theorem Encode.generated_field_3 : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v0 v1 c2 c3 c4 b2 b3 b4 pre d0 d1 d2 d3 d4 : List UInt8) (hast : ast.length = 8) (hv0 : v0.length = 8) (hv1 : v1.length = 8) (hc2 : c2.length = 8) (hc3 : c3.length = 8) (hc4 : c4.length = 8) (hb2 : b2.length = 32) (hb3 : b3.length = 32) (hb4 : b4.length = 32) (hd0 : d0.length = 8) (hd1 : d1.length = 8) (hd2 : d2.length = 32) (hd3 : d3.length = 32) (hd4 : d4.length = 32)
    (p2 p3 p4 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l96 l104 t56 t40 t88 t72 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8) (hl96 : l96.length = 8) (hl104 : l104.length = 8) (ht56 : t56.length = 16) (ht40 : t40.length = 16) (ht88 : t88.length = 16) (ht72 : t72.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 168 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 112 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 90)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 160 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 x2 x3 x4 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧ x2.length = 8 ∧ x3.length = 16 ∧ x4.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (v1.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 90)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 168))
          ⋆ Eq (x4.At (s.regs.rsp.toBitVec - 168 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (c2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 p4.toInt).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (c4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b2.At p2)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (b4.At p4)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (b2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
          ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 118)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 160 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 x2 x3 x4 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧ x2.length = 8 ∧ x3.length = 16 ∧ x4.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 80).toInt).At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (v1.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 118)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 168))
          ⋆ Eq (x4.At (s.regs.rsp.toBitVec - 168 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (c2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 p4.toInt).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (c4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b2.At p2)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (b4.At p4)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (b2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
          ⋆ Eq (b3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v0 v1 c2 c3 c4 b2 b3 b4 pre d0 d1 d2 d3 d4 hast hv0 hv1 hc2 hc3 hc4 hb2 hb3 hb4 hd0 hd1 hd2 hd3 hd4 p2 p3 p4 s ra guard hpre fp s1 s2 l16 l96 l104 t56 t40 t88 t72 rslot hfp hs1 hs2 hl16 hl96 hl104 ht56 ht40 ht88 ht72 hrslot R S scratch hsc hsp hcap hcap63 hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hsp hcap hcap63 hpre ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, x0, x1, x2, x3, x4, hx0, hx1, hx2, hx3, hx4, Hm⟩
  dsimp only at hpc hrsp hrbp hr14  Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14  Hm
  subst rsp1 rbp1 r141
  have hcap' : rcx.toBitVec.toNat + 112 ≤ rdi.toBitVec.toNat := hcap
  apply step_load_value Reg64.rdx Reg64.rsp 168 _ (k + 90) (k + 91) (window_infix_at hk 90 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec + 8) rax.toBitVec (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_load_value Reg64.rbx Reg64.rdx 48 _ (k + 91) (k + 92) (window_infix_at hk 91 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 48) p3 (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_length_check Reg64.rdx 56 32 _ _ (k + 92) (k + 94) (window_infix_at hk 92 2) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 56) (by encoder_address_equation) (Int.toBytes 8 32) (by rfl) (by decide) _ _ _ (by rfl) (by ecancel)
  intro fl; normalize_registers
  apply step_load_value Reg64.r8 Reg64.rsp 64 _ (k + 94) (k + 95) (window_infix_at hk 94 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 96) (rcx.toBitVec + 48) (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_lea Reg64.r9 Reg64.r8 32 _ (k + 95) (k + 96) (window_infix_at hk 95 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.r9 (rcx.toBitVec + 80) _ _ _ (by show ((rcx.toBitVec + 48) + 32 : BitVec 64) = (rcx.toBitVec + 80); bv_omega)
  normalize_registers
  apply step_load_value Reg64.rcx Reg64.rsp 56 _ (k + 96) (k + 97) (window_infix_at hk 96 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 104) rdi.toBitVec (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_cmp_jb_not_taken Reg64.rcx Reg64.r9 _ _ (k + 97) (k + 99) (window_infix_at hk 97 2) (by rfl) (by rfl) _ _ (by show ((rcx.toBitVec + 80) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; normalize_registers
  apply step_load_value Reg64.rax Reg64.rsp 144 _ (k + 99) (k + 100) (window_infix_at hk 99 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 16) rbx.toBitVec (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  have hl111 := Machine.label_at' hk hf (j := 111)
    (by simp only [marshalSSZTo, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply step_jump _ _ (k + 100) (k + 111) (window_infix_at hk 100 1) (by rfl) hl111
  apply step_label _ _ (k + 111) (k + 112) (window_infix_at hk 111 1) (by rfl) (by rfl)
  apply step_store Reg64.rcx Reg64.rsp 64 _ (k + 112) (k + 113) (window_infix_at hk 112 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 96) (by encoder_address_equation) (Int.toBytes 8 (rcx.toBitVec + 48).toInt) (Int.toBytes_length 8 _) _ _ _ (by rfl) (by ecancel)
  intro m15 H15; normalize_registers; simp only [Reg64s.get64] at H15
  apply step_store Reg64.r9 Reg64.rsp 56 _ (k + 113) (k + 114) (window_infix_at hk 113 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 104) (by encoder_address_equation) (Int.toBytes 8 rdi.toBitVec.toInt) (Int.toBytes_length 8 _) _ _ _ (by rfl) (by ecancel)
  intro m16 H16; normalize_registers; simp only [Reg64s.get64] at H16
  apply step_store Reg64.rax Reg64.rsp 144 _ (k + 114) (k + 115) (window_infix_at hk 114 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 16) (by encoder_address_equation) (Int.toBytes 8 rbx.toBitVec.toInt) (Int.toBytes_length 8 _) _ _ _ (by rfl) (by ecancel)
  intro m17 H17; normalize_registers; simp only [Reg64s.get64] at H17
  apply step_add_registers Reg64.rax Reg64.r8 _ (k + 115) (k + 116) (window_infix_at hk 115 1) (by rfl) (by rfl)
  intro fl; normalize_registers
  apply register_value_rewrite Reg64.rax (rbx.toBitVec + rcx.toBitVec + 48) _ _ _ (by show (rbx.toBitVec + (rcx.toBitVec + 48) : BitVec 64) = (rbx.toBitVec + rcx.toBitVec + 48); bv_omega)
  normalize_registers
  apply step_move_immediate Reg64.rcx 32 _ (k + 116) (k + 117) (window_infix_at hk 116 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.rcx 32 _ _ _ (by show (BitVec.zeroExtend 64 (BitVec.truncate 32 (32 : BitVec 64)) : BitVec 64) = 32; decide)
  normalize_registers
  refine eventually_trans _ _ _ _ (encode_memmove_call (k + 117) (window_infix_at hk 117 1) (rsp.toBitVec - 160) (rbx.toBitVec + rcx.toBitVec + 48) p3
    (rsp.toBitVec - 168) (rsp.toBitVec - 168 - BitVec.ofNat 64 S) S (by bv_omega) (Codec.frame_low_address_without_calls rsp.toBitVec 160 168 S (by decide))
    b3 d3 (Int.toBytes 8 (Host.addrOf (k + 90)).toBitVec.toInt) x4 (by rw [hd3, hb3]) (Int.toBytes_length 8 _) hx4
    _ _ (by rfl) (by rfl) (by rfl) (by rw [hb3]; rfl) (by first | ecancel | (dsimp only; ecancel)) hmm) ?_
  rintro ⟨e2, pc2⟩ ⟨hpc2, hrsp2, hrbp2, hr142, scr2, hscr2, Hc2⟩
  dsimp only at hpc2 hrsp2 hrbp2 hr142 Hc2
  subst hpc2
  obtain ⟨⟨raxc2, rbxc2, rcxc2, rdxc2, rsic2, rdic2, rspc2, rbpc2, r8c2, r9c2, r10c2, r11c2, r12c2, r13c2, r14c2, r15c2⟩, zmmsc2, flagsc2, memc2⟩ := e2
  simp only at hrsp2 hrbp2 hr142 Hc2
  subst rspc2 rbpc2 r14c2
  rw [show k + 117 + 1 = k + 118 from rfl] at Hc2
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, x0, x1, x2, x3, scr2, hx0, hx1, hx2, hx3, hscr2, ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem Encode.generated_field_3_kind : ∀ (h : Host), type_of% (@Encode.generated_field_3 h)
    = @Codec.encFieldKindAnyFrame h marshalSSZTo Prysm.BeaconBlockHeader.encodeLayout [.u64, .u64, .bytes 32, .bytes 32, .bytes 32]
    ⟨90, 3, [],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 16) (.reg .rbx), .at (.below 96) (.len 48), .at (.below 104) (.reg .rdi), .at (.below 56) (.field 0), .at (.below 48) (.existential 0), .at (.below 40) (.existential 1), .at (.below 88) (.field 1), .at (.below 80) (.existential 2), .at (.below 72) (.existential 3), .at (.below 168) (.ret 90), .low (.existential 4)],
      [.fixed 8, .fixed 16, .fixed 8, .fixed 16, .low]⟩
    ⟨118, 4, [],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 16) (.reg .rbx), .at (.below 96) (.reg .rdi), .at (.below 104) (.len 80), .at (.below 56) (.field 0), .at (.below 48) (.existential 0), .at (.below 40) (.existential 1), .at (.below 88) (.field 1), .at (.below 80) (.existential 2), .at (.below 72) (.existential 3), .at (.below 168) (.ret 118), .low (.existential 4)],
      [.fixed 8, .fixed 16, .fixed 8, .fixed 16, .low]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 4 `BodyRoot` (32 bytes): directives 118–147; boundary state 4 → 5. -/
theorem Encode.generated_field_4 : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v0 v1 c2 c3 c4 b2 b3 b4 pre d0 d1 d2 d3 d4 : List UInt8) (hast : ast.length = 8) (hv0 : v0.length = 8) (hv1 : v1.length = 8) (hc2 : c2.length = 8) (hc3 : c3.length = 8) (hc4 : c4.length = 8) (hb2 : b2.length = 32) (hb3 : b3.length = 32) (hb4 : b4.length = 32) (hd0 : d0.length = 8) (hd1 : d1.length = 8) (hd2 : d2.length = 32) (hd3 : d3.length = 32) (hd4 : d4.length = 32)
    (p2 p3 p4 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l96 l104 t56 t40 t88 t72 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8) (hl96 : l96.length = 8) (hl104 : l104.length = 8) (ht56 : t56.length = 16) (ht40 : t40.length = 16) (ht88 : t88.length = 16) (ht72 : t72.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 168 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 112 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 118)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 160 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 x2 x3 x4 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧ x2.length = 8 ∧ x3.length = 16 ∧ x4.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 80).toInt).At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (v1.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 118)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 168))
          ⋆ Eq (x4.At (s.regs.rsp.toBitVec - 168 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (c2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 p4.toInt).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (c4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b2.At p2)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (b4.At p4)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (b2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
          ⋆ Eq (b3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 148)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 160 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 x2 x3 x4 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧ x2.length = 8 ∧ x3.length = 16 ∧ x4.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 112).toInt).At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (v1.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 148)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 168))
          ⋆ Eq (x4.At (s.regs.rsp.toBitVec - 168 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (c2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 p4.toInt).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (c4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b2.At p2)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (b4.At p4)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (b2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
          ⋆ Eq (b3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (b4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v0 v1 c2 c3 c4 b2 b3 b4 pre d0 d1 d2 d3 d4 hast hv0 hv1 hc2 hc3 hc4 hb2 hb3 hb4 hd0 hd1 hd2 hd3 hd4 p2 p3 p4 s ra guard hpre fp s1 s2 l16 l96 l104 t56 t40 t88 t72 rslot hfp hs1 hs2 hl16 hl96 hl104 ht56 ht40 ht88 ht72 hrslot R S scratch hsc hsp hcap hcap63 hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hsp hcap hcap63 hpre ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, x0, x1, x2, x3, x4, hx0, hx1, hx2, hx3, hx4, Hm⟩
  dsimp only at hpc hrsp hrbp hr14  Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14  Hm
  subst rsp1 rbp1 r141
  have hcap' : rcx.toBitVec.toNat + 112 ≤ rdi.toBitVec.toNat := hcap
  apply step_load_value Reg64.rdx Reg64.rsp 168 _ (k + 118) (k + 119) (window_infix_at hk 118 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec + 8) rax.toBitVec (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_load_value Reg64.rbx Reg64.rdx 72 _ (k + 119) (k + 120) (window_infix_at hk 119 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 72) p4 (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_length_check Reg64.rdx 80 32 _ _ (k + 120) (k + 122) (window_infix_at hk 120 2) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 80) (by encoder_address_equation) (Int.toBytes 8 32) (by rfl) (by decide) _ _ _ (by rfl) (by ecancel)
  intro fl; normalize_registers
  apply step_load_value Reg64.rdx Reg64.rsp 56 _ (k + 122) (k + 123) (window_infix_at hk 122 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 104) (rcx.toBitVec + 80) (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_lea Reg64.r8 Reg64.rdx 32 _ (k + 123) (k + 124) (window_infix_at hk 123 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.r8 (rcx.toBitVec + 112) _ _ _ (by show ((rcx.toBitVec + 80) + 32 : BitVec 64) = (rcx.toBitVec + 112); bv_omega)
  normalize_registers
  apply step_load_value Reg64.rcx Reg64.rsp 64 _ (k + 124) (k + 125) (window_infix_at hk 124 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 96) rdi.toBitVec (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_cmp_jb_not_taken Reg64.rcx Reg64.r8 _ _ (k + 125) (k + 128) (window_infix_at hk 125 3) (by rfl) (by rfl) _ _ (by show ((rcx.toBitVec + 112) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; normalize_registers
  apply step_load_value Reg64.rax Reg64.rsp 144 _ (k + 128) (k + 129) (window_infix_at hk 128 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 16) rbx.toBitVec (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  have hl140 := Machine.label_at' hk hf (j := 140)
    (by simp only [marshalSSZTo, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply step_jump _ _ (k + 129) (k + 140) (window_infix_at hk 129 1) (by rfl) hl140
  apply step_label _ _ (k + 140) (k + 141) (window_infix_at hk 140 1) (by rfl) (by rfl)
  apply step_store Reg64.rcx Reg64.rsp 64 _ (k + 141) (k + 142) (window_infix_at hk 141 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 96) (by encoder_address_equation) (Int.toBytes 8 rdi.toBitVec.toInt) (Int.toBytes_length 8 _) _ _ _ (by rfl) (by ecancel)
  intro m18 H18; normalize_registers; simp only [Reg64s.get64] at H18
  apply step_store Reg64.r8 Reg64.rsp 56 _ (k + 142) (k + 143) (window_infix_at hk 142 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 104) (by encoder_address_equation) (Int.toBytes 8 (rcx.toBitVec + 80).toInt) (Int.toBytes_length 8 _) _ _ _ (by rfl) (by ecancel)
  intro m19 H19; normalize_registers; simp only [Reg64s.get64] at H19
  apply step_store Reg64.rax Reg64.rsp 144 _ (k + 143) (k + 144) (window_infix_at hk 143 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 16) (by encoder_address_equation) (Int.toBytes 8 rbx.toBitVec.toInt) (Int.toBytes_length 8 _) _ _ _ (by rfl) (by ecancel)
  intro m20 H20; normalize_registers; simp only [Reg64s.get64] at H20
  apply step_add_registers Reg64.rax Reg64.rdx _ (k + 144) (k + 145) (window_infix_at hk 144 1) (by rfl) (by rfl)
  intro fl; normalize_registers
  apply register_value_rewrite Reg64.rax (rbx.toBitVec + rcx.toBitVec + 80) _ _ _ (by show (rbx.toBitVec + (rcx.toBitVec + 80) : BitVec 64) = (rbx.toBitVec + rcx.toBitVec + 80); bv_omega)
  normalize_registers
  apply step_move_immediate Reg64.rcx 32 _ (k + 145) (k + 146) (window_infix_at hk 145 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.rcx 32 _ _ _ (by show (BitVec.zeroExtend 64 (BitVec.truncate 32 (32 : BitVec 64)) : BitVec 64) = 32; decide)
  normalize_registers
  apply step_nops _ (k + 146) (k + 147) (window_infix_at hk 146 1) (by rfl) (by rfl)
  refine eventually_trans _ _ _ _ (encode_memmove_call (k + 147) (window_infix_at hk 147 1) (rsp.toBitVec - 160) (rbx.toBitVec + rcx.toBitVec + 80) p4
    (rsp.toBitVec - 168) (rsp.toBitVec - 168 - BitVec.ofNat 64 S) S (by bv_omega) (Codec.frame_low_address_without_calls rsp.toBitVec 160 168 S (by decide))
    b4 d4 (Int.toBytes 8 (Host.addrOf (k + 118)).toBitVec.toInt) x4 (by rw [hd4, hb4]) (Int.toBytes_length 8 _) hx4
    _ _ (by rfl) (by rfl) (by rfl) (by rw [hb4]; rfl) (by first | ecancel | (dsimp only; ecancel)) hmm) ?_
  rintro ⟨e3, pc3⟩ ⟨hpc3, hrsp3, hrbp3, hr143, scr3, hscr3, Hc3⟩
  dsimp only at hpc3 hrsp3 hrbp3 hr143 Hc3
  subst hpc3
  obtain ⟨⟨raxc3, rbxc3, rcxc3, rdxc3, rsic3, rdic3, rspc3, rbpc3, r8c3, r9c3, r10c3, r11c3, r12c3, r13c3, r14c3, r15c3⟩, zmmsc3, flagsc3, memc3⟩ := e3
  simp only at hrsp3 hrbp3 hr143 Hc3
  subst rspc3 rbpc3 r14c3
  rw [show k + 147 + 1 = k + 148 from rfl] at Hc3
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, x0, x1, x2, x3, scr3, hx0, hx1, hx2, hx3, hscr3, ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem Encode.generated_field_4_kind : ∀ (h : Host), type_of% (@Encode.generated_field_4 h)
    = @Codec.encFieldKindAnyFrame h marshalSSZTo Prysm.BeaconBlockHeader.encodeLayout [.u64, .u64, .bytes 32, .bytes 32, .bytes 32]
    ⟨118, 4, [],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 16) (.reg .rbx), .at (.below 96) (.reg .rdi), .at (.below 104) (.len 80), .at (.below 56) (.field 0), .at (.below 48) (.existential 0), .at (.below 40) (.existential 1), .at (.below 88) (.field 1), .at (.below 80) (.existential 2), .at (.below 72) (.existential 3), .at (.below 168) (.ret 118), .low (.existential 4)],
      [.fixed 8, .fixed 16, .fixed 8, .fixed 16, .low]⟩
    ⟨148, 5, [],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 16) (.reg .rbx), .at (.below 96) (.reg .rdi), .at (.below 104) (.len 112), .at (.below 56) (.field 0), .at (.below 48) (.existential 0), .at (.below 40) (.existential 1), .at (.below 88) (.field 1), .at (.below 80) (.existential 2), .at (.below 72) (.existential 3), .at (.below 168) (.ret 148), .low (.existential 4)],
      [.fixed 8, .fixed 16, .fixed 8, .fixed 16, .low]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Epilogue: directives 148–return; boundary state 5 → the fast-path post-state. -/
theorem Encode.generated_epilogue : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v0 v1 c2 c3 c4 b2 b3 b4 pre d0 d1 d2 d3 d4 : List UInt8) (hast : ast.length = 8) (hv0 : v0.length = 8) (hv1 : v1.length = 8) (hc2 : c2.length = 8) (hc3 : c3.length = 8) (hc4 : c4.length = 8) (hb2 : b2.length = 32) (hb3 : b3.length = 32) (hb4 : b4.length = 32) (hd0 : d0.length = 8) (hd1 : d1.length = 8) (hd2 : d2.length = 32) (hd3 : d3.length = 32) (hd4 : d4.length = 32)
    (p2 p3 p4 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l96 l104 t56 t40 t88 t72 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8) (hl96 : l96.length = 8) (hl104 : l104.length = 8) (ht56 : t56.length = 16) (ht40 : t40.length = 16) (ht88 : t88.length = 16) (ht72 : t72.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 168 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 112 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 148)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 160 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 x2 x3 x4 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧ x2.length = 8 ∧ x3.length = 16 ∧ x4.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 112).toInt).At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (v1.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 148)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 168))
          ⋆ Eq (x4.At (s.regs.rsp.toBitVec - 168 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (c2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 p4.toInt).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (c4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b2.At p2)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (b4.At p4)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (b2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
          ⋆ Eq (b3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (b4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec
        ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 112
        ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0
        ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8
        ∧ st.data.regs.rbp = s.regs.rbp
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 x2 x3 x4 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧ x2.length = 8 ∧ x3.length = 16 ∧ x4.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 112).toInt).At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (v1.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 148)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 168))
          ⋆ Eq (x4.At (s.regs.rsp.toBitVec - 168 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (c2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 p4.toInt).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (c4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b2.At p2)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (b4.At p4)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (b2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
          ⋆ Eq (b3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (b4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v0 v1 c2 c3 c4 b2 b3 b4 pre d0 d1 d2 d3 d4 hast hv0 hv1 hc2 hc3 hc4 hb2 hb3 hb4 hd0 hd1 hd2 hd3 hd4 p2 p3 p4 s ra guard hpre fp s1 s2 l16 l96 l104 t56 t40 t88 t72 rslot hfp hs1 hs2 hl16 hl96 hl104 ht56 ht40 ht88 ht72 hrslot R S scratch hsc hsp hcap hcap63
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hsp hcap hcap63 hpre ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, x0, x1, x2, x3, x4, hx0, hx1, hx2, hx3, hx4, Hm⟩
  dsimp only at hpc hrsp hrbp hr14  Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14  Hm
  subst rsp1 rbp1 r141
  have hcap' : rcx.toBitVec.toNat + 112 ≤ rdi.toBitVec.toNat := hcap
  apply step_load_value Reg64.rax Reg64.rsp 144 _ (k + 148) (k + 149) (window_infix_at hk 148 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 16) rbx.toBitVec (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_load_value Reg64.rbx Reg64.rsp 56 _ (k + 149) (k + 150) (window_infix_at hk 149 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 104) (rcx.toBitVec + 112) (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_load_value Reg64.rcx Reg64.rsp 64 _ (k + 150) (k + 151) (window_infix_at hk 150 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 96) rdi.toBitVec (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_xor32 Reg64.rdi _ (k + 151) (k + 152) (window_infix_at hk 151 1) (by rfl) (by rfl)
  intro fl; normalize_registers
  apply step_xor32 Reg64.rsi _ (k + 152) (k + 153) (window_infix_at hk 152 1) (by rfl) (by rfl)
  intro fl; normalize_registers
  apply step_add_immediate Reg64.rsp 152 _ (k + 153) (k + 154) (window_infix_at hk 153 1) (by rfl) (by rfl)
  intro fl; normalize_registers
  apply register_value_rewrite Reg64.rsp (rsp.toBitVec - 8) _ _ _ (by show ((rsp.toBitVec - 160) + 152 : BitVec 64) = (rsp.toBitVec - 8); bv_omega)
  normalize_registers
  refine eventually_trans _ _ _ _ (dec_return_seg _ (k + 154) (window_infix_at hk 154 2) (by rfl) (rsp.toBitVec - 8) rsp.toBitVec (by bv_omega) rbp ra _ _ (by rfl) (by ecancel)) ?_
  rintro ⟨d', pc'⟩ ⟨hpc', hrsp', hrbp', hreg', hmem'⟩
  dsimp only at hpc' hrsp' hrbp' hreg' hmem'
  apply Eventually.done
  refine ⟨hpc', ?_, ?_, ?_, ?_, ?_, ?_, hrbp', ?_, x0, x1, x2, x3, x4, hx0, hx1, hx2, hx3, hx4, ?_⟩
  · exact UInt64.toBitVec_inj.mp (hreg' Reg64.rax (by decide) (by decide))
  · show d'.regs.rbx.toBitVec.toNat = rcx.toBitVec.toNat + 112
    rw [show d'.regs.rbx.toBitVec = rcx.toBitVec + 112 from hreg' Reg64.rbx (by decide) (by decide)]
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
    = @Codec.encEpilogueKindAnyFrame h marshalSSZTo Prysm.BeaconBlockHeader.encodeLayout [.u64, .u64, .bytes 32, .bytes 32, .bytes 32]
    ⟨148, 5, [],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 16) (.reg .rbx), .at (.below 96) (.reg .rdi), .at (.below 104) (.len 112), .at (.below 56) (.field 0), .at (.below 48) (.existential 0), .at (.below 40) (.existential 1), .at (.below 88) (.field 1), .at (.below 80) (.existential 2), .at (.below 72) (.existential 3), .at (.below 168) (.ret 148), .low (.existential 4)],
      [.fixed 8, .fixed 16, .fixed 8, .fixed 16, .low]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Encoder fast path of `(*v1alpha1.BeaconBlockHeader).MarshalSSZTo` (Go 1.26.10), generated** (`encoder --fast-path`):
head, one theorem per field, epilogue, chained by `eventually_trans`. Premises: `len + 112 ≤ cap`,
every byte-vector field of its exact length. Statement = the kind instance (`_kind`). Fast path only. -/
theorem Encode.generated_fast : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v0 v1 c2 c3 c4 b2 b3 b4 pre d0 d1 d2 d3 d4 : List UInt8) (hast : ast.length = 8) (hv0 : v0.length = 8) (hv1 : v1.length = 8) (hc2 : c2.length = 8) (hc3 : c3.length = 8) (hc4 : c4.length = 8) (hb2 : b2.length = 32) (hb3 : b3.length = 32) (hb4 : b4.length = 32) (hd0 : d0.length = 8) (hd1 : d1.length = 8) (hd2 : d2.length = 32) (hd3 : d3.length = 32) (hd4 : d4.length = 32)
    (p2 p3 p4 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l96 l104 t56 t40 t88 t72 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8) (hl96 : l96.length = 8) (hl104 : l104.length = 8) (ht56 : t56.length = 16) (ht40 : t40.length = 16) (ht88 : t88.length = 16) (ht72 : t72.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (l96.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (l104.At (s.regs.rsp.toBitVec - 104))
      ⋆ Eq (t56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (t88.At (s.regs.rsp.toBitVec - 88))
      ⋆ Eq (t72.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 168))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 168 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (c2.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 56))
      ⋆ Eq (c3.At (s.regs.rax.toBitVec + 64))
      ⋆ Eq ((Int.toBytes 8 p4.toInt).At (s.regs.rax.toBitVec + 72))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 80))
      ⋆ Eq (c4.At (s.regs.rax.toBitVec + 88))
      ⋆ Eq (b2.At p2)
      ⋆ Eq (b3.At p3)
      ⋆ Eq (b4.At p4)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
      ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
      ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
      ⋆ R)
    (hguard : guard.toNat + 32 < s.regs.rsp.toNat) (hsp : 168 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 112 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec
        ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 112
        ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0
        ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8
        ∧ st.data.regs.rbp = s.regs.rbp
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 x2 x3 x4 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧ x2.length = 8 ∧ x3.length = 16 ∧ x4.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 112).toInt).At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (v1.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 148)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 168))
          ⋆ Eq (x4.At (s.regs.rsp.toBitVec - 168 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (c2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 p4.toInt).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (c4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b2.At p2)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (b4.At p4)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (b2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
          ⋆ Eq (b3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (b4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf ast v0 v1 c2 c3 c4 b2 b3 b4 pre d0 d1 d2 d3 d4 hast hv0 hv1 hc2 hc3 hc4 hb2 hb3 hb4 hd0 hd1 hd2 hd3 hd4 p2 p3 p4 s ra guard hpre fp s1 s2 l16 l96 l104 t56 t40 t88 t72 rslot hfp hs1 hs2 hl16 hl96 hl104 ht56 ht40 ht88 ht72 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm
  refine eventually_trans _ _ _ _ (Encode.generated_head k hk hf ast v0 v1 c2 c3 c4 b2 b3 b4 pre d0 d1 d2 d3 d4 hast hv0 hv1 hc2 hc3 hc4 hb2 hb3 hb4 hd0 hd1 hd2 hd3 hd4 p2 p3 p4 s ra guard hpre fp s1 s2 l16 l96 l104 t56 t40 t88 t72 rslot hfp hs1 hs2 hl16 hl96 hl104 ht56 ht40 ht88 ht72 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm) ?_
  intro st0 h0
  refine eventually_trans _ _ _ _ (Encode.generated_field_0 k hk hf ast v0 v1 c2 c3 c4 b2 b3 b4 pre d0 d1 d2 d3 d4 hast hv0 hv1 hc2 hc3 hc4 hb2 hb3 hb4 hd0 hd1 hd2 hd3 hd4 p2 p3 p4 s ra guard hpre fp s1 s2 l16 l96 l104 t56 t40 t88 t72 rslot hfp hs1 hs2 hl16 hl96 hl104 ht56 ht40 ht88 ht72 hrslot R S scratch hsc hsp hcap hcap63 hmm st0 h0) ?_
  intro st1 h1
  refine eventually_trans _ _ _ _ (Encode.generated_field_1 k hk hf ast v0 v1 c2 c3 c4 b2 b3 b4 pre d0 d1 d2 d3 d4 hast hv0 hv1 hc2 hc3 hc4 hb2 hb3 hb4 hd0 hd1 hd2 hd3 hd4 p2 p3 p4 s ra guard hpre fp s1 s2 l16 l96 l104 t56 t40 t88 t72 rslot hfp hs1 hs2 hl16 hl96 hl104 ht56 ht40 ht88 ht72 hrslot R S scratch hsc hsp hcap hcap63 hmm st1 h1) ?_
  intro st2 h2
  refine eventually_trans _ _ _ _ (Encode.generated_field_2 k hk hf ast v0 v1 c2 c3 c4 b2 b3 b4 pre d0 d1 d2 d3 d4 hast hv0 hv1 hc2 hc3 hc4 hb2 hb3 hb4 hd0 hd1 hd2 hd3 hd4 p2 p3 p4 s ra guard hpre fp s1 s2 l16 l96 l104 t56 t40 t88 t72 rslot hfp hs1 hs2 hl16 hl96 hl104 ht56 ht40 ht88 ht72 hrslot R S scratch hsc hsp hcap hcap63 hmm st2 h2) ?_
  intro st3 h3
  refine eventually_trans _ _ _ _ (Encode.generated_field_3 k hk hf ast v0 v1 c2 c3 c4 b2 b3 b4 pre d0 d1 d2 d3 d4 hast hv0 hv1 hc2 hc3 hc4 hb2 hb3 hb4 hd0 hd1 hd2 hd3 hd4 p2 p3 p4 s ra guard hpre fp s1 s2 l16 l96 l104 t56 t40 t88 t72 rslot hfp hs1 hs2 hl16 hl96 hl104 ht56 ht40 ht88 ht72 hrslot R S scratch hsc hsp hcap hcap63 hmm st3 h3) ?_
  intro st4 h4
  refine eventually_trans _ _ _ _ (Encode.generated_field_4 k hk hf ast v0 v1 c2 c3 c4 b2 b3 b4 pre d0 d1 d2 d3 d4 hast hv0 hv1 hc2 hc3 hc4 hb2 hb3 hb4 hd0 hd1 hd2 hd3 hd4 p2 p3 p4 s ra guard hpre fp s1 s2 l16 l96 l104 t56 t40 t88 t72 rslot hfp hs1 hs2 hl16 hl96 hl104 ht56 ht40 ht88 ht72 hrslot R S scratch hsc hsp hcap hcap63 hmm st4 h4) ?_
  intro st5 h5
  exact Encode.generated_epilogue k hk hf ast v0 v1 c2 c3 c4 b2 b3 b4 pre d0 d1 d2 d3 d4 hast hv0 hv1 hc2 hc3 hc4 hb2 hb3 hb4 hd0 hd1 hd2 hd3 hd4 p2 p3 p4 s ra guard hpre fp s1 s2 l16 l96 l104 t56 t40 t88 t72 rslot hfp hs1 hs2 hl16 hl96 hl104 ht56 ht40 ht88 ht72 hrslot R S scratch hsc hsp hcap hcap63 st5 h5
theorem Encode.generated_fast_kind : ∀ (h : Host), type_of% (@Encode.generated_fast h)
    = @Codec.encFastPathKindAnyFrame h marshalSSZTo Prysm.BeaconBlockHeader.encodeLayout [.u64, .u64, .bytes 32, .bytes 32, .bytes 32] := by
  intro h; rfl

/-- Statement check: the generated theorem proves the committed hand statement. -/
theorem Encode.generated_statement : type_of% (@Prysm.BeaconBlockHeader.Encode.fast_path ‹Host›) :=
  Encode.generated_fast

end Prysm.BeaconBlockHeader
