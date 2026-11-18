import Codec.Kind.EncodeFastPathAnyFrame
import Codec.EncodeFrameTest
import Codec.Kind.EncodeFastPathNestedAnyFrame
import Codec.EncodeNestedCheckpoint
import Prysm.Checkpoint.Code
import Prysm.Checkpoint.FunctionSpecsAsNestedField
import Prysm.AttestationData.Code

/-!
# Fast path (`encoder --fast-path`): encoder fast path of `(*v1alpha1.AttestationData).MarshalSSZTo`

Generated from the `.S` file and the IR: a symbolic dataflow walk of the fast path, one application of a
step lemma per directive (windows with the nops erased), boundary states between the fields. Every theorem
has a `_kind` line (`encodeHeadNestedKindAnyFrame`, `encodeFieldNestedKindAnyFrame`, `encodeEpilogueNestedKindAnyFrame`, `encodeFastPathNestedKindAnyFrame`).
**Fast path only**: `len(dst) + 128 ≤ cap(dst)` and every byte-vector field of its exact length. No
`runtime.growslice` directive is stepped: each capacity test is decided from the premise. Not covered: the
growslice branches, the length rejects, the morestack path. Not a complete encoder result.
Each nested pointer is not nil, and each nested call uses the function specification of its callee
(`Prysm.Checkpoint.Encode.fast_path_function_spec_holds`). Not covered: the `newobject` branch of a nil pointer and the
error wrap of a nested call.
FAST-PATH-JSON: {"type": "AttestationData", "const": "marshalSSZTo", "prefix": "Encode.generated", "size": 128, "frame": 176, "guard_addend": 56, "runtime_calls": true, "fields": [["Slot", "u", 8], ["CommitteeIndex", "u", 8], ["BeaconBlockRoot", "b", 32], ["Source", "n", 40], ["Target", "n", 40]], "boundaries": [10, 36, 62, 90, 147, 212], "layout": "Prysm.AttestationData.Encode.generated_layout", "assembly_sha256": "c065f7da72dd010c7716cae3f14a143d5f2d663ad75e205c612f9d5fe6178ba2", "ir_sha256": "59b783f53a4aef9ca94860df8776154d571310937304ba29b9329ce80c7a29b0", "statement_check": "kind instance only", "assembly": "prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo.S", "ir": "prysm/ir/ir-mainnet.json", "ir_type": "v1alpha1.AttestationData", "kinds": [{"theorem": "Encode.generated_head", "kind": "encodeHeadNestedKindAnyFrame"}, {"theorem": "Encode.generated_field_0", "kind": "encodeFieldNestedKindAnyFrame"}, {"theorem": "Encode.generated_field_1", "kind": "encodeFieldNestedKindAnyFrame"}, {"theorem": "Encode.generated_field_2", "kind": "encodeFieldNestedKindAnyFrame"}, {"theorem": "Encode.generated_field_3", "kind": "encodeFieldNestedKindAnyFrame"}, {"theorem": "Encode.generated_field_4", "kind": "encodeFieldNestedKindAnyFrame"}, {"theorem": "Encode.generated_epilogue", "kind": "encodeEpilogueNestedKindAnyFrame"}, {"theorem": "Encode.generated_fast", "kind": "encodeFastPathNestedKindAnyFrame"}]}
-/

open Machine Runtime Codec Prysm.AttestationData.Code
variable [Host]

namespace Prysm.AttestationData

/-- The frame facts of `marshalSSZTo` (read from the `.S` file by the walk): frame `0xb0`, stack chunks
`fp s1 s2 t80 t64 t112 t96 l48 l120 l128 l176 rslot`, the callee `Prysm.Checkpoint.Code.marshalSSZTo`. -/
def Encode.generated_layout : EncoderNestedFrameLayout where
  callees := [Prysm.Checkpoint.Code.marshalSSZTo]
  goStart := 8
  frame := 176
  guardAddend := 312
  lowExtra := 120
  stackChunkCount := 12
  stackChunkLengths := [(0, 8), (1, 8), (2, 8), (3, 16), (4, 16), (5, 16), (6, 16), (7, 8), (8, 8), (9, 8), (10, 8), (11, 8)]
  pre := [.at (.below 8) (.original 0), .at (.above 8) (.original 1), .at (.above 16) (.original 2), .at (.below 80) (.original 3), .at (.below 64) (.original 4), .at (.below 112) (.original 5), .at (.below 96) (.original 6), .at (.below 48) (.original 7), .at (.below 120) (.original 8), .at (.below 128) (.original 9), .at (.below 176) (.original 10), .at (.below 192) (.original 11), .low .scratch]
  existentials := [.fixed 8, .fixed 16, .fixed 8, .fixed 16, .fixed 48, .fixed 16, .fixed 8, .fixed 8, .low]
  post := [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 80) (.field 0), .at (.below 72) (.existential 0), .at (.below 64) (.existential 1), .at (.below 112) (.field 1), .at (.below 104) (.existential 2), .at (.below 96) (.existential 3), .at (.below 48) (.reg .rbx), .at (.below 120) (.len 48), .at (.below 128) (.reg .rdi), .at (.below 176) (.reg .rbx), .at (.below 192) (.ret 178), .at (.below 200) (.framePointer), .at (.below 208) (.reg .rbx), .at (.below 216) (.reg .rdi), .at (.below 224) (.len 128), .at (.below 240) (.existential 5), .at (.below 256) (.field 5), .at (.below 248) (.existential 6), .at (.below 304) (.existential 4), .at (.below 312) (.existential 7), .low (.existential 8)]


/-- Head: directives 0–9 (stack guard, frame, spills); entry → boundary state 0. -/
theorem Encode.generated_head : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (kC : Nat) (hkC : Prysm.Checkpoint.Code.marshalSSZTo.IsInfixAt Host.prog kC) (hfC : LabelsFresh Prysm.Checkpoint.Code.marshalSSZTo kC)
    (v0 v1 b2 ep3 rt3 ep4 rt4 ob3 oc3 ot3 ob4 oc4 ot4 pre d0 d1 d2 d3 dr3 d4 dr4 : List UInt8) (hv0 : v0.length = 8) (hv1 : v1.length = 8) (hb2 : b2.length = 32) (hep3 : ep3.length = 8) (hrt3 : rt3.length = 32) (hep4 : ep4.length = 8) (hrt4 : rt4.length = 32) (hob3 : ob3.length = 8) (hoc3 : oc3.length = 8) (hot3 : ot3.length = 32) (hob4 : ob4.length = 8) (hoc4 : oc4.length = 8) (hot4 : ot4.length = 32) (hd0 : d0.length = 8) (hd1 : d1.length = 8) (hd2 : d2.length = 32) (hd3 : d3.length = 8) (hdr3 : dr3.length = 32) (hd4 : d4.length = 8) (hdr4 : dr4.length = 32)
    (p2 p3 pr3 p4 pr4 : BitVec 64) (hp3 : p3 ≠ 0) (hp4 : p4 ≠ 0) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 t80 t64 t112 t96 l48 l120 l128 l176 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (ht80 : t80.length = 16) (ht64 : t64.length = 16) (ht112 : t112.length = 16) (ht96 : t96.length = 16) (hl48 : l48.length = 8) (hl120 : l120.length = 8) (hl128 : l128.length = 8) (hl176 : l176.length = 8) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (hS : S < 2 ^ 60) (scratch : List UInt8) (hsc : scratch.length = S + 120)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (t80.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (t64.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (t112.At (s.regs.rsp.toBitVec - 112))
      ⋆ Eq (t96.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (l120.At (s.regs.rsp.toBitVec - 120))
      ⋆ Eq (l128.At (s.regs.rsp.toBitVec - 128))
      ⋆ Eq (l176.At (s.regs.rsp.toBitVec - 176))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 192))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 312 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
      ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
      ⋆ Eq ((Int.toBytes 8 p4.toInt).At (s.regs.rax.toBitVec + 56))
      ⋆ Eq (b2.At p2)
      ⋆ Eq (ob3.At p3)
      ⋆ Eq (ep3.At (p3 + 8))
      ⋆ Eq ((Int.toBytes 8 pr3.toInt).At (p3 + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (p3 + 24))
      ⋆ Eq (oc3.At (p3 + 32))
      ⋆ Eq (ot3.At (p3 + 40))
      ⋆ Eq (rt3.At pr3)
      ⋆ Eq (ob4.At p4)
      ⋆ Eq (ep4.At (p4 + 8))
      ⋆ Eq ((Int.toBytes 8 pr4.toInt).At (p4 + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (p4 + 24))
      ⋆ Eq (oc4.At (p4 + 32))
      ⋆ Eq (ot4.At (p4 + 40))
      ⋆ Eq (rt4.At pr4)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
      ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
      ⋆ Eq (dr3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56))
      ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
      ⋆ Eq (dr4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 96))
      ⋆ R)
    (hguard : guard.toNat + 312 < s.regs.rsp.toNat) (hcap : s.regs.rcx.toNat + 128 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 10)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 184 }
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
          ⋆ Eq (t80.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (t64.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (t112.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq (t96.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (l120.At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq (l128.At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq (l176.At (s.regs.rsp.toBitVec - 176))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 192))
          ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 312 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 p4.toInt).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (b2.At p2)
          ⋆ Eq (ob3.At p3)
          ⋆ Eq (ep3.At (p3 + 8))
          ⋆ Eq ((Int.toBytes 8 pr3.toInt).At (p3 + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (p3 + 24))
          ⋆ Eq (oc3.At (p3 + 32))
          ⋆ Eq (ot3.At (p3 + 40))
          ⋆ Eq (rt3.At pr3)
          ⋆ Eq (ob4.At p4)
          ⋆ Eq (ep4.At (p4 + 8))
          ⋆ Eq ((Int.toBytes 8 pr4.toInt).At (p4 + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (p4 + 24))
          ⋆ Eq (oc4.At (p4 + 32))
          ⋆ Eq (ot4.At (p4 + 40))
          ⋆ Eq (rt4.At pr4)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
          ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (dr3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
          ⋆ Eq (dr4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 96))
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf kC hkC hfC v0 v1 b2 ep3 rt3 ep4 rt4 ob3 oc3 ot3 ob4 oc4 ot4 pre d0 d1 d2 d3 dr3 d4 dr4 hv0 hv1 hb2 hep3 hrt3 hep4 hrt4 hob3 hoc3 hot3 hob4 hoc4 hot4 hd0 hd1 hd2 hd3 hdr3 hd4 hdr4 p2 p3 pr3 p4 pr4 hp3 hp4 s ra guard hpre fp s1 s2 t80 t64 t112 t96 l48 l120 l128 l176 rslot hfp hs1 hs2 ht80 ht64 ht112 ht96 hl48 hl120 hl128 hl176 hrslot R S hS scratch hsc h_mem hguard hcap hcap63 hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hcap hcap63 hpre ⊢
  have hcap' : rcx.toBitVec.toNat + 128 ≤ rdi.toBitVec.toNat := hcap
  apply encoder_prologue_large_frame _ _ _ (-56) 56 _ k (k + 7) (window_infix_at hk 0 7) (by rfl) (by rfl) (by rfl) guard fp hfp _ _ _ (by dsimp only; ecancel) (by dsimp only; omega)
  intro m1 H1 fl1; normalize_registers; dsimp only at H1
  apply step_sub_immediate Reg64.rsp 176 _ (k + 7) (k + 8) (window_infix_at hk 7 1) (by rfl) (by rfl)
  intro fl; normalize_registers
  apply register_value_rewrite Reg64.rsp (rsp.toBitVec - 184) _ _ _ (by show ((rsp.toBitVec - 8) - 176 : BitVec 64) = (rsp.toBitVec - 184); bv_omega)
  normalize_registers
  apply step_store Reg64.rbx Reg64.rsp 200 _ (k + 8) (k + 9) (window_infix_at hk 8 1) (by rfl) (by rfl)
    (rsp.toBitVec - 184) (rsp.toBitVec + 16) (by encoder_address_equation) s2 hs2 _ _ _ (by rfl) (by ecancel)
  intro m2 H2; normalize_registers; simp only [Reg64s.get64] at H2
  apply step_store Reg64.rax Reg64.rsp 192 _ (k + 9) (k + 10) (window_infix_at hk 9 1) (by rfl) (by rfl)
    (rsp.toBitVec - 184) (rsp.toBitVec + 8) (by encoder_address_equation) s1 hs1 _ _ _ (by rfl) (by ecancel)
  intro m3 H3; normalize_registers; simp only [Reg64s.get64] at H3
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem Encode.generated_head_kind : ∀ (h : Host), type_of% (@Encode.generated_head h)
    = @Codec.encodeHeadNestedKindAnyFrame h marshalSSZTo Prysm.AttestationData.Encode.generated_layout [.flat .uint64, .flat .uint64, .flat (.bytes 32), .checkpoint, .checkpoint]
    ⟨10, 0, [(.rax, .receiver), (.rbx, .ptr), (.rcx, .len 0), (.rdi, .cap)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 80) (.original 3), .at (.below 64) (.original 4), .at (.below 112) (.original 5), .at (.below 96) (.original 6), .at (.below 48) (.original 7), .at (.below 120) (.original 8), .at (.below 128) (.original 9), .at (.below 176) (.original 10), .at (.below 192) (.original 11), .low .scratch],
      []⟩ := by
  intro h; rfl

-- Measured cause: with the default maxRecDepth (512), the `simp only` of a label fact (`Machine.label_at'`)
-- fails with "maximum recursion depth has been reached"; 1000 passes. The default maxHeartbeats passes.
set_option maxRecDepth 1000 in
/-- Field 0 `Slot` (uint64): directives 10–35; boundary state 0 → 1. -/
theorem Encode.generated_field_0 : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (kC : Nat) (hkC : Prysm.Checkpoint.Code.marshalSSZTo.IsInfixAt Host.prog kC) (hfC : LabelsFresh Prysm.Checkpoint.Code.marshalSSZTo kC)
    (v0 v1 b2 ep3 rt3 ep4 rt4 ob3 oc3 ot3 ob4 oc4 ot4 pre d0 d1 d2 d3 dr3 d4 dr4 : List UInt8) (hv0 : v0.length = 8) (hv1 : v1.length = 8) (hb2 : b2.length = 32) (hep3 : ep3.length = 8) (hrt3 : rt3.length = 32) (hep4 : ep4.length = 8) (hrt4 : rt4.length = 32) (hob3 : ob3.length = 8) (hoc3 : oc3.length = 8) (hot3 : ot3.length = 32) (hob4 : ob4.length = 8) (hoc4 : oc4.length = 8) (hot4 : ot4.length = 32) (hd0 : d0.length = 8) (hd1 : d1.length = 8) (hd2 : d2.length = 32) (hd3 : d3.length = 8) (hdr3 : dr3.length = 32) (hd4 : d4.length = 8) (hdr4 : dr4.length = 32)
    (p2 p3 pr3 p4 pr4 : BitVec 64) (hp3 : p3 ≠ 0) (hp4 : p4 ≠ 0) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 t80 t64 t112 t96 l48 l120 l128 l176 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (ht80 : t80.length = 16) (ht64 : t64.length = 16) (ht112 : t112.length = 16) (ht96 : t96.length = 16) (hl48 : l48.length = 8) (hl120 : l120.length = 8) (hl128 : l128.length = 8) (hl176 : l176.length = 8) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (hS : S < 2 ^ 60) (scratch : List UInt8) (hsc : scratch.length = S + 120)
    (hguard : guard.toNat + 312 < s.regs.rsp.toNat) (hcap : s.regs.rcx.toNat + 128 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 10)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 184 }
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
          ⋆ Eq (t80.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (t64.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (t112.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq (t96.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (l120.At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq (l128.At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq (l176.At (s.regs.rsp.toBitVec - 176))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 192))
          ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 312 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 p4.toInt).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (b2.At p2)
          ⋆ Eq (ob3.At p3)
          ⋆ Eq (ep3.At (p3 + 8))
          ⋆ Eq ((Int.toBytes 8 pr3.toInt).At (p3 + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (p3 + 24))
          ⋆ Eq (oc3.At (p3 + 32))
          ⋆ Eq (ot3.At (p3 + 40))
          ⋆ Eq (rt3.At pr3)
          ⋆ Eq (ob4.At p4)
          ⋆ Eq (ep4.At (p4 + 8))
          ⋆ Eq ((Int.toBytes 8 pr4.toInt).At (p4 + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (p4 + 24))
          ⋆ Eq (oc4.At (p4 + 32))
          ⋆ Eq (ot4.At (p4 + 40))
          ⋆ Eq (rt4.At pr4)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
          ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (dr3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
          ⋆ Eq (dr4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 96))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 36)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 184 }
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
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (t112.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq (t96.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (l120.At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq (l128.At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq (l176.At (s.regs.rsp.toBitVec - 176))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 192))
          ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 312 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 p4.toInt).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (b2.At p2)
          ⋆ Eq (ob3.At p3)
          ⋆ Eq (ep3.At (p3 + 8))
          ⋆ Eq ((Int.toBytes 8 pr3.toInt).At (p3 + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (p3 + 24))
          ⋆ Eq (oc3.At (p3 + 32))
          ⋆ Eq (ot3.At (p3 + 40))
          ⋆ Eq (rt3.At pr3)
          ⋆ Eq (ob4.At p4)
          ⋆ Eq (ep4.At (p4 + 8))
          ⋆ Eq ((Int.toBytes 8 pr4.toInt).At (p4 + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (p4 + 24))
          ⋆ Eq (oc4.At (p4 + 32))
          ⋆ Eq (ot4.At (p4 + 40))
          ⋆ Eq (rt4.At pr4)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
          ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (dr3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
          ⋆ Eq (dr4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 96))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf kC hkC hfC v0 v1 b2 ep3 rt3 ep4 rt4 ob3 oc3 ot3 ob4 oc4 ot4 pre d0 d1 d2 d3 dr3 d4 dr4 hv0 hv1 hb2 hep3 hrt3 hep4 hrt4 hob3 hoc3 hot3 hob4 hoc4 hot4 hd0 hd1 hd2 hd3 hdr3 hd4 hdr4 p2 p3 pr3 p4 pr4 hp3 hp4 s ra guard hpre fp s1 s2 t80 t64 t112 t96 l48 l120 l128 l176 rslot hfp hs1 hs2 ht80 ht64 ht112 ht96 hl48 hl120 hl128 hl176 hrslot R S hS scratch hsc hguard hcap hcap63 hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hguard hcap hcap63 hpre ⊢
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
  have hcap' : rcx.toBitVec.toNat + 128 ≤ rdi.toBitVec.toNat := hcap
  apply step_lea Reg64.rdx Reg64.rcx 8 _ (k + 10) (k + 11) (window_infix_at hk 10 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.rdx (rcx.toBitVec + 8) _ _ _ (by show (rcx.toBitVec + 8 : BitVec 64) = (rcx.toBitVec + 8); bv_omega)
  normalize_registers
  apply step_load_bytes Reg64.r8 Reg64.rax 8 _ (k + 11) (k + 12) (window_infix_at hk 11 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 8) (by encoder_address_equation) v0 hv0 _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_lea Reg64.r9 Reg64.rsp 104 _ (k + 12) (k + 16) (window_infix_at hk 12 4) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.r9 (rsp.toBitVec - 80) _ _ _ (by show ((rsp.toBitVec - 184) + 104 : BitVec 64) = (rsp.toBitVec - 80); bv_omega)
  normalize_registers
  apply step_store_xmm15 Reg64.r9 0 _ (k + 16) (k + 17) (window_infix_at hk 16 1) (by rfl) (by rfl)
    (rsp.toBitVec - 80) (rsp.toBitVec - 80) (by encoder_address_equation) t80 ht80 _ _ _ (by rfl) (by ecancel)
  intro m4 H4; normalize_registers; try dsimp only at H4
  apply step_store_xmm15 Reg64.r9 16 _ (k + 17) (k + 18) (window_infix_at hk 17 1) (by rfl) (by rfl)
    (rsp.toBitVec - 80) (rsp.toBitVec - 64) (by encoder_address_equation) t64 ht64 _ _ _ (by rfl) (by ecancel)
  intro m5 H5; normalize_registers; try dsimp only at H5
  rw [Machine.at_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 80), show (rsp.toBitVec - 80) + 8 = (rsp.toBitVec - 72) by bv_omega] at H5
  apply step_store Reg64.r8 Reg64.rsp 104 _ (k + 18) (k + 19) (window_infix_at hk 18 1) (by rfl) (by rfl)
    (rsp.toBitVec - 184) (rsp.toBitVec - 80) (by encoder_address_equation) ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).take 8) (by rw [List.length_take, Int.toBytes_length]; rfl) _ _ _ (by rfl) (by ecancel)
  intro m6 H6; normalize_registers; simp only [Reg64s.get64] at H6
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v0 hv0] at H6
  have hl33 := Machine.label_at' hk hf (j := 33)
    (by simp only [marshalSSZTo, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply step_cmp_jae_taken Reg64.rdi Reg64.rdx _ _ (k + 19) (k + 33) (window_infix_at hk 19 2) (by rfl) hl33 _ _ (by show ((rcx.toBitVec + 8) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; normalize_registers
  apply step_label _ _ (k + 33) (k + 34) (window_infix_at hk 33 1) (by rfl) (by rfl)
  apply step_load_bytes Reg64.r8 Reg64.rsp 104 _ (k + 34) (k + 35) (window_infix_at hk 34 1) (by rfl) (by rfl)
    (rsp.toBitVec - 184) (rsp.toBitVec - 80) (by encoder_address_equation) v0 hv0 _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_store_indexed Reg64.r8 Reg64.rbx Reg64.rcx 0 _ (k + 35) (k + 36) (window_infix_at hk 35 1) (by rfl) (by rfl)
    rbx.toBitVec rcx.toBitVec (rbx.toBitVec + rcx.toBitVec) (by encoder_address_equation) d0 hd0 _ _ _ (by rfl) (by rfl) (by ecancel)
  intro m7 H7; normalize_registers; simp only [Reg64s.get64] at H7
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v0 hv0] at H7
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8), (Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt), (by rw [List.length_drop, Int.toBytes_length]), (Int.toBytes_length 16 _), ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem Encode.generated_field_0_kind : ∀ (h : Host), type_of% (@Encode.generated_field_0 h)
    = @Codec.encodeFieldNestedKindAnyFrame h marshalSSZTo Prysm.AttestationData.Encode.generated_layout [.flat .uint64, .flat .uint64, .flat (.bytes 32), .checkpoint, .checkpoint]
    ⟨10, 0, [(.rax, .receiver), (.rbx, .ptr), (.rcx, .len 0), (.rdi, .cap)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 80) (.original 3), .at (.below 64) (.original 4), .at (.below 112) (.original 5), .at (.below 96) (.original 6), .at (.below 48) (.original 7), .at (.below 120) (.original 8), .at (.below 128) (.original 9), .at (.below 176) (.original 10), .at (.below 192) (.original 11), .low .scratch],
      []⟩
    ⟨36, 1, [(.rax, .receiver), (.rbx, .ptr), (.rdx, .len 8), (.rdi, .cap)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 80) (.field 0), .at (.below 72) (.existential 0), .at (.below 64) (.existential 1), .at (.below 112) (.original 5), .at (.below 96) (.original 6), .at (.below 48) (.original 7), .at (.below 120) (.original 8), .at (.below 128) (.original 9), .at (.below 176) (.original 10), .at (.below 192) (.original 11), .low .scratch],
      [.fixed 8, .fixed 16]⟩ := by
  intro h; rfl

-- Measured cause: with the default maxRecDepth (512), the `simp only` of a label fact (`Machine.label_at'`)
-- fails with "maximum recursion depth has been reached"; 1000 passes. The default maxHeartbeats passes.
set_option maxRecDepth 1000 in
/-- Field 1 `CommitteeIndex` (uint64): directives 36–61; boundary state 1 → 2. -/
theorem Encode.generated_field_1 : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (kC : Nat) (hkC : Prysm.Checkpoint.Code.marshalSSZTo.IsInfixAt Host.prog kC) (hfC : LabelsFresh Prysm.Checkpoint.Code.marshalSSZTo kC)
    (v0 v1 b2 ep3 rt3 ep4 rt4 ob3 oc3 ot3 ob4 oc4 ot4 pre d0 d1 d2 d3 dr3 d4 dr4 : List UInt8) (hv0 : v0.length = 8) (hv1 : v1.length = 8) (hb2 : b2.length = 32) (hep3 : ep3.length = 8) (hrt3 : rt3.length = 32) (hep4 : ep4.length = 8) (hrt4 : rt4.length = 32) (hob3 : ob3.length = 8) (hoc3 : oc3.length = 8) (hot3 : ot3.length = 32) (hob4 : ob4.length = 8) (hoc4 : oc4.length = 8) (hot4 : ot4.length = 32) (hd0 : d0.length = 8) (hd1 : d1.length = 8) (hd2 : d2.length = 32) (hd3 : d3.length = 8) (hdr3 : dr3.length = 32) (hd4 : d4.length = 8) (hdr4 : dr4.length = 32)
    (p2 p3 pr3 p4 pr4 : BitVec 64) (hp3 : p3 ≠ 0) (hp4 : p4 ≠ 0) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 t80 t64 t112 t96 l48 l120 l128 l176 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (ht80 : t80.length = 16) (ht64 : t64.length = 16) (ht112 : t112.length = 16) (ht96 : t96.length = 16) (hl48 : l48.length = 8) (hl120 : l120.length = 8) (hl128 : l128.length = 8) (hl176 : l176.length = 8) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (hS : S < 2 ^ 60) (scratch : List UInt8) (hsc : scratch.length = S + 120)
    (hguard : guard.toNat + 312 < s.regs.rsp.toNat) (hcap : s.regs.rcx.toNat + 128 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 36)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 184 }
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
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (t112.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq (t96.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (l120.At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq (l128.At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq (l176.At (s.regs.rsp.toBitVec - 176))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 192))
          ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 312 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 p4.toInt).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (b2.At p2)
          ⋆ Eq (ob3.At p3)
          ⋆ Eq (ep3.At (p3 + 8))
          ⋆ Eq ((Int.toBytes 8 pr3.toInt).At (p3 + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (p3 + 24))
          ⋆ Eq (oc3.At (p3 + 32))
          ⋆ Eq (ot3.At (p3 + 40))
          ⋆ Eq (rt3.At pr3)
          ⋆ Eq (ob4.At p4)
          ⋆ Eq (ep4.At (p4 + 8))
          ⋆ Eq ((Int.toBytes 8 pr4.toInt).At (p4 + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (p4 + 24))
          ⋆ Eq (oc4.At (p4 + 32))
          ⋆ Eq (ot4.At (p4 + 40))
          ⋆ Eq (rt4.At pr4)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
          ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (dr3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
          ⋆ Eq (dr4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 96))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 62)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 184 }
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
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (v1.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (l120.At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq (l128.At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq (l176.At (s.regs.rsp.toBitVec - 176))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 192))
          ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 312 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 p4.toInt).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (b2.At p2)
          ⋆ Eq (ob3.At p3)
          ⋆ Eq (ep3.At (p3 + 8))
          ⋆ Eq ((Int.toBytes 8 pr3.toInt).At (p3 + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (p3 + 24))
          ⋆ Eq (oc3.At (p3 + 32))
          ⋆ Eq (ot3.At (p3 + 40))
          ⋆ Eq (rt3.At pr3)
          ⋆ Eq (ob4.At p4)
          ⋆ Eq (ep4.At (p4 + 8))
          ⋆ Eq ((Int.toBytes 8 pr4.toInt).At (p4 + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (p4 + 24))
          ⋆ Eq (oc4.At (p4 + 32))
          ⋆ Eq (ot4.At (p4 + 40))
          ⋆ Eq (rt4.At pr4)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
          ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (dr3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
          ⋆ Eq (dr4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 96))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf kC hkC hfC v0 v1 b2 ep3 rt3 ep4 rt4 ob3 oc3 ot3 ob4 oc4 ot4 pre d0 d1 d2 d3 dr3 d4 dr4 hv0 hv1 hb2 hep3 hrt3 hep4 hrt4 hob3 hoc3 hot3 hob4 hoc4 hot4 hd0 hd1 hd2 hd3 hdr3 hd4 hdr4 p2 p3 pr3 p4 pr4 hp3 hp4 s ra guard hpre fp s1 s2 t80 t64 t112 t96 l48 l120 l128 l176 rslot hfp hs1 hs2 ht80 ht64 ht112 ht96 hl48 hl120 hl128 hl176 hrslot R S hS scratch hsc hguard hcap hcap63 hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hguard hcap hcap63 hpre ⊢
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
  have hcap' : rcx.toBitVec.toNat + 128 ≤ rdi.toBitVec.toNat := hcap
  apply step_lea Reg64.r8 Reg64.rdx 8 _ (k + 36) (k + 37) (window_infix_at hk 36 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.r8 (rcx.toBitVec + 16) _ _ _ (by show ((rcx.toBitVec + 8) + 8 : BitVec 64) = (rcx.toBitVec + 16); bv_omega)
  normalize_registers
  apply step_load_bytes Reg64.r9 Reg64.rax 16 _ (k + 37) (k + 38) (window_infix_at hk 37 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 16) (by encoder_address_equation) v1 hv1 _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_lea Reg64.r10 Reg64.rsp 72 _ (k + 38) (k + 42) (window_infix_at hk 38 4) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.r10 (rsp.toBitVec - 112) _ _ _ (by show ((rsp.toBitVec - 184) + 72 : BitVec 64) = (rsp.toBitVec - 112); bv_omega)
  normalize_registers
  apply step_store_xmm15 Reg64.r10 0 _ (k + 42) (k + 43) (window_infix_at hk 42 1) (by rfl) (by rfl)
    (rsp.toBitVec - 112) (rsp.toBitVec - 112) (by encoder_address_equation) t112 ht112 _ _ _ (by rfl) (by ecancel)
  intro m8 H8; normalize_registers; try dsimp only at H8
  apply step_store_xmm15 Reg64.r10 16 _ (k + 43) (k + 44) (window_infix_at hk 43 1) (by rfl) (by rfl)
    (rsp.toBitVec - 112) (rsp.toBitVec - 96) (by encoder_address_equation) t96 ht96 _ _ _ (by rfl) (by ecancel)
  intro m9 H9; normalize_registers; try dsimp only at H9
  rw [Machine.at_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 112), show (rsp.toBitVec - 112) + 8 = (rsp.toBitVec - 104) by bv_omega] at H9
  apply step_store Reg64.r9 Reg64.rsp 72 _ (k + 44) (k + 45) (window_infix_at hk 44 1) (by rfl) (by rfl)
    (rsp.toBitVec - 184) (rsp.toBitVec - 112) (by encoder_address_equation) ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).take 8) (by rw [List.length_take, Int.toBytes_length]; rfl) _ _ _ (by rfl) (by ecancel)
  intro m10 H10; normalize_registers; simp only [Reg64s.get64] at H10
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v1 hv1] at H10
  have hl59 := Machine.label_at' hk hf (j := 59)
    (by simp only [marshalSSZTo, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply step_cmp_jae_taken Reg64.rdi Reg64.r8 _ _ (k + 45) (k + 59) (window_infix_at hk 45 2) (by rfl) hl59 _ _ (by show ((rcx.toBitVec + 16) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; normalize_registers
  apply step_label _ _ (k + 59) (k + 60) (window_infix_at hk 59 1) (by rfl) (by rfl)
  apply step_load_bytes Reg64.r9 Reg64.rsp 72 _ (k + 60) (k + 61) (window_infix_at hk 60 1) (by rfl) (by rfl)
    (rsp.toBitVec - 184) (rsp.toBitVec - 112) (by encoder_address_equation) v1 hv1 _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_store_indexed Reg64.r9 Reg64.rbx Reg64.rdx 0 _ (k + 61) (k + 62) (window_infix_at hk 61 1) (by rfl) (by rfl)
    rbx.toBitVec (rcx.toBitVec + 8) (rbx.toBitVec + rcx.toBitVec + 8) (by encoder_address_equation) d1 hd1 _ _ _ (by rfl) (by rfl) (by ecancel)
  intro m11 H11; normalize_registers; simp only [Reg64s.get64] at H11
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v1 hv1] at H11
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, x0, x1, ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8), (Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt), hx0, hx1, (by rw [List.length_drop, Int.toBytes_length]), (Int.toBytes_length 16 _), ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem Encode.generated_field_1_kind : ∀ (h : Host), type_of% (@Encode.generated_field_1 h)
    = @Codec.encodeFieldNestedKindAnyFrame h marshalSSZTo Prysm.AttestationData.Encode.generated_layout [.flat .uint64, .flat .uint64, .flat (.bytes 32), .checkpoint, .checkpoint]
    ⟨36, 1, [(.rax, .receiver), (.rbx, .ptr), (.rdx, .len 8), (.rdi, .cap)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 80) (.field 0), .at (.below 72) (.existential 0), .at (.below 64) (.existential 1), .at (.below 112) (.original 5), .at (.below 96) (.original 6), .at (.below 48) (.original 7), .at (.below 120) (.original 8), .at (.below 128) (.original 9), .at (.below 176) (.original 10), .at (.below 192) (.original 11), .low .scratch],
      [.fixed 8, .fixed 16]⟩
    ⟨62, 2, [(.rax, .receiver), (.rbx, .ptr), (.rdi, .cap), (.r8, .len 16)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 80) (.field 0), .at (.below 72) (.existential 0), .at (.below 64) (.existential 1), .at (.below 112) (.field 1), .at (.below 104) (.existential 2), .at (.below 96) (.existential 3), .at (.below 48) (.original 7), .at (.below 120) (.original 8), .at (.below 128) (.original 9), .at (.below 176) (.original 10), .at (.below 192) (.original 11), .low .scratch],
      [.fixed 8, .fixed 16, .fixed 8, .fixed 16]⟩ := by
  intro h; rfl

-- Measured cause: with the default maxRecDepth (512), the `simp only` of a label fact (`Machine.label_at'`)
-- fails with "maximum recursion depth has been reached"; 1000 passes. The default maxHeartbeats passes.
set_option maxRecDepth 1000 in
/-- Field 2 `BeaconBlockRoot` (32 bytes): directives 62–89; boundary state 2 → 3. -/
theorem Encode.generated_field_2 : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (kC : Nat) (hkC : Prysm.Checkpoint.Code.marshalSSZTo.IsInfixAt Host.prog kC) (hfC : LabelsFresh Prysm.Checkpoint.Code.marshalSSZTo kC)
    (v0 v1 b2 ep3 rt3 ep4 rt4 ob3 oc3 ot3 ob4 oc4 ot4 pre d0 d1 d2 d3 dr3 d4 dr4 : List UInt8) (hv0 : v0.length = 8) (hv1 : v1.length = 8) (hb2 : b2.length = 32) (hep3 : ep3.length = 8) (hrt3 : rt3.length = 32) (hep4 : ep4.length = 8) (hrt4 : rt4.length = 32) (hob3 : ob3.length = 8) (hoc3 : oc3.length = 8) (hot3 : ot3.length = 32) (hob4 : ob4.length = 8) (hoc4 : oc4.length = 8) (hot4 : ot4.length = 32) (hd0 : d0.length = 8) (hd1 : d1.length = 8) (hd2 : d2.length = 32) (hd3 : d3.length = 8) (hdr3 : dr3.length = 32) (hd4 : d4.length = 8) (hdr4 : dr4.length = 32)
    (p2 p3 pr3 p4 pr4 : BitVec 64) (hp3 : p3 ≠ 0) (hp4 : p4 ≠ 0) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 t80 t64 t112 t96 l48 l120 l128 l176 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (ht80 : t80.length = 16) (ht64 : t64.length = 16) (ht112 : t112.length = 16) (ht96 : t96.length = 16) (hl48 : l48.length = 8) (hl120 : l120.length = 8) (hl128 : l128.length = 8) (hl176 : l176.length = 8) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (hS : S < 2 ^ 60) (scratch : List UInt8) (hsc : scratch.length = S + 120)
    (hguard : guard.toNat + 312 < s.regs.rsp.toNat) (hcap : s.regs.rcx.toNat + 128 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 62)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 184 }
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
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (v1.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (l120.At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq (l128.At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq (l176.At (s.regs.rsp.toBitVec - 176))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 192))
          ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 312 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 p4.toInt).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (b2.At p2)
          ⋆ Eq (ob3.At p3)
          ⋆ Eq (ep3.At (p3 + 8))
          ⋆ Eq ((Int.toBytes 8 pr3.toInt).At (p3 + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (p3 + 24))
          ⋆ Eq (oc3.At (p3 + 32))
          ⋆ Eq (ot3.At (p3 + 40))
          ⋆ Eq (rt3.At pr3)
          ⋆ Eq (ob4.At p4)
          ⋆ Eq (ep4.At (p4 + 8))
          ⋆ Eq ((Int.toBytes 8 pr4.toInt).At (p4 + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (p4 + 24))
          ⋆ Eq (oc4.At (p4 + 32))
          ⋆ Eq (ot4.At (p4 + 40))
          ⋆ Eq (rt4.At pr4)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
          ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (dr3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
          ⋆ Eq (dr4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 96))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 90)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 184 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 x2 x3 x4 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧ x2.length = 8 ∧ x3.length = 16 ∧ x4.length = S + 120 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (v1.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq (l176.At (s.regs.rsp.toBitVec - 176))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 90)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 192))
          ⋆ Eq (x4.At (s.regs.rsp.toBitVec - 312 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 p4.toInt).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (b2.At p2)
          ⋆ Eq (ob3.At p3)
          ⋆ Eq (ep3.At (p3 + 8))
          ⋆ Eq ((Int.toBytes 8 pr3.toInt).At (p3 + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (p3 + 24))
          ⋆ Eq (oc3.At (p3 + 32))
          ⋆ Eq (ot3.At (p3 + 40))
          ⋆ Eq (rt3.At pr3)
          ⋆ Eq (ob4.At p4)
          ⋆ Eq (ep4.At (p4 + 8))
          ⋆ Eq ((Int.toBytes 8 pr4.toInt).At (p4 + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (p4 + 24))
          ⋆ Eq (oc4.At (p4 + 32))
          ⋆ Eq (ot4.At (p4 + 40))
          ⋆ Eq (rt4.At pr4)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (b2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
          ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (dr3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
          ⋆ Eq (dr4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 96))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf kC hkC hfC v0 v1 b2 ep3 rt3 ep4 rt4 ob3 oc3 ot3 ob4 oc4 ot4 pre d0 d1 d2 d3 dr3 d4 dr4 hv0 hv1 hb2 hep3 hrt3 hep4 hrt4 hob3 hoc3 hot3 hob4 hoc4 hot4 hd0 hd1 hd2 hd3 hdr3 hd4 hdr4 p2 p3 pr3 p4 pr4 hp3 hp4 s ra guard hpre fp s1 s2 t80 t64 t112 t96 l48 l120 l128 l176 rslot hfp hs1 hs2 ht80 ht64 ht112 ht96 hl48 hl120 hl128 hl176 hrslot R S hS scratch hsc hguard hcap hcap63 hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hguard hcap hcap63 hpre ⊢
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
  have hcap' : rcx.toBitVec.toNat + 128 ≤ rdi.toBitVec.toNat := hcap
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
  apply step_store Reg64.rbx Reg64.rsp 136 _ (k + 83) (k + 84) (window_infix_at hk 83 1) (by rfl) (by rfl)
    (rsp.toBitVec - 184) (rsp.toBitVec - 48) (by encoder_address_equation) l48 hl48 _ _ _ (by rfl) (by ecancel)
  intro m12 H12; normalize_registers; simp only [Reg64s.get64] at H12
  apply step_store Reg64.r9 Reg64.rsp 64 _ (k + 84) (k + 85) (window_infix_at hk 84 1) (by rfl) (by rfl)
    (rsp.toBitVec - 184) (rsp.toBitVec - 120) (by encoder_address_equation) l120 hl120 _ _ _ (by rfl) (by ecancel)
  intro m13 H13; normalize_registers; simp only [Reg64s.get64] at H13
  apply step_store Reg64.rdi Reg64.rsp 56 _ (k + 85) (k + 86) (window_infix_at hk 85 1) (by rfl) (by rfl)
    (rsp.toBitVec - 184) (rsp.toBitVec - 128) (by encoder_address_equation) l128 hl128 _ _ _ (by rfl) (by ecancel)
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
  obtain ⟨lm1, sm1, hlm1, hsm1, Hm1⟩ := low_block_memmove_split (rsp.toBitVec - 312) (rsp.toBitVec - 192) S 120
    hS (by decide) (by bv_omega) scratch hsc _ _ (by first | ecancel | (dsimp only; ecancel))
  clear H14
  refine eventually_trans _ _ _ _ (encode_memmove_call (k + 89) (window_infix_at hk 89 1) (rsp.toBitVec - 184) (rbx.toBitVec + rcx.toBitVec + 16) p2
    (rsp.toBitVec - 192) (rsp.toBitVec - 192 - BitVec.ofNat 64 S) S (by bv_omega) (Codec.frame_low_address_without_calls rsp.toBitVec 184 192 S (by decide))
    b2 d2 rslot sm1 (by rw [hd2, hb2]) hrslot hsm1
    _ _ (by rfl) (by rfl) (by rfl) (by rw [hb2]; rfl) (by first | ecancel | (dsimp only; ecancel)) hmm) ?_
  rintro ⟨e1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, scr1, hscr1, Hc1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 Hc1
  subst hpc1
  obtain ⟨⟨raxc1, rbxc1, rcxc1, rdxc1, rsic1, rdic1, rspc1, rbpc1, r8c1, r9c1, r10c1, r11c1, r12c1, r13c1, r14c1, r15c1⟩, zmmsc1, flagsc1, memc1⟩ := e1
  simp only at hrsp1 hrbp1 hr141 Hc1
  subst rspc1 rbpc1 r14c1
  rw [show k + 89 + 1 = k + 90 from rfl] at Hc1
  obtain ⟨hj1, Hj1⟩ := low_block_join (rsp.toBitVec - 312) (rsp.toBitVec - 192) S 120 hS (by decide) (by bv_omega)
    lm1 scr1 hlm1 hscr1 _ _ (by first | ecancel | (dsimp only; ecancel))
  clear Hc1
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, x0, x1, x2, x3, (lm1 ++ scr1), hx0, hx1, hx2, hx3, hj1, ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem Encode.generated_field_2_kind : ∀ (h : Host), type_of% (@Encode.generated_field_2 h)
    = @Codec.encodeFieldNestedKindAnyFrame h marshalSSZTo Prysm.AttestationData.Encode.generated_layout [.flat .uint64, .flat .uint64, .flat (.bytes 32), .checkpoint, .checkpoint]
    ⟨62, 2, [(.rax, .receiver), (.rbx, .ptr), (.rdi, .cap), (.r8, .len 16)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 80) (.field 0), .at (.below 72) (.existential 0), .at (.below 64) (.existential 1), .at (.below 112) (.field 1), .at (.below 104) (.existential 2), .at (.below 96) (.existential 3), .at (.below 48) (.original 7), .at (.below 120) (.original 8), .at (.below 128) (.original 9), .at (.below 176) (.original 10), .at (.below 192) (.original 11), .low .scratch],
      [.fixed 8, .fixed 16, .fixed 8, .fixed 16]⟩
    ⟨90, 3, [],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 80) (.field 0), .at (.below 72) (.existential 0), .at (.below 64) (.existential 1), .at (.below 112) (.field 1), .at (.below 104) (.existential 2), .at (.below 96) (.existential 3), .at (.below 48) (.reg .rbx), .at (.below 120) (.len 48), .at (.below 128) (.reg .rdi), .at (.below 176) (.original 10), .at (.below 192) (.ret 90), .low (.existential 4)],
      [.fixed 8, .fixed 16, .fixed 8, .fixed 16, .lowBlock]⟩ := by
  intro h; rfl

-- Measured cause: with the default maxRecDepth (512), the `simp only` of a label fact (`Machine.label_at'`)
-- fails with "maximum recursion depth has been reached"; 1000 passes. The default maxHeartbeats passes.
set_option maxRecDepth 1000 in
/-- Field 3 `Source` (nested Checkpoint): directives 90–146; boundary state 3 → 4. -/
theorem Encode.generated_field_3 : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (kC : Nat) (hkC : Prysm.Checkpoint.Code.marshalSSZTo.IsInfixAt Host.prog kC) (hfC : LabelsFresh Prysm.Checkpoint.Code.marshalSSZTo kC)
    (v0 v1 b2 ep3 rt3 ep4 rt4 ob3 oc3 ot3 ob4 oc4 ot4 pre d0 d1 d2 d3 dr3 d4 dr4 : List UInt8) (hv0 : v0.length = 8) (hv1 : v1.length = 8) (hb2 : b2.length = 32) (hep3 : ep3.length = 8) (hrt3 : rt3.length = 32) (hep4 : ep4.length = 8) (hrt4 : rt4.length = 32) (hob3 : ob3.length = 8) (hoc3 : oc3.length = 8) (hot3 : ot3.length = 32) (hob4 : ob4.length = 8) (hoc4 : oc4.length = 8) (hot4 : ot4.length = 32) (hd0 : d0.length = 8) (hd1 : d1.length = 8) (hd2 : d2.length = 32) (hd3 : d3.length = 8) (hdr3 : dr3.length = 32) (hd4 : d4.length = 8) (hdr4 : dr4.length = 32)
    (p2 p3 pr3 p4 pr4 : BitVec 64) (hp3 : p3 ≠ 0) (hp4 : p4 ≠ 0) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 t80 t64 t112 t96 l48 l120 l128 l176 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (ht80 : t80.length = 16) (ht64 : t64.length = 16) (ht112 : t112.length = 16) (ht96 : t96.length = 16) (hl48 : l48.length = 8) (hl120 : l120.length = 8) (hl128 : l128.length = 8) (hl176 : l176.length = 8) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (hS : S < 2 ^ 60) (scratch : List UInt8) (hsc : scratch.length = S + 120)
    (hguard : guard.toNat + 312 < s.regs.rsp.toNat) (hcap : s.regs.rcx.toNat + 128 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 90)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 184 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 x2 x3 x4 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧ x2.length = 8 ∧ x3.length = 16 ∧ x4.length = S + 120 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (v1.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq (l176.At (s.regs.rsp.toBitVec - 176))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 90)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 192))
          ⋆ Eq (x4.At (s.regs.rsp.toBitVec - 312 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 p4.toInt).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (b2.At p2)
          ⋆ Eq (ob3.At p3)
          ⋆ Eq (ep3.At (p3 + 8))
          ⋆ Eq ((Int.toBytes 8 pr3.toInt).At (p3 + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (p3 + 24))
          ⋆ Eq (oc3.At (p3 + 32))
          ⋆ Eq (ot3.At (p3 + 40))
          ⋆ Eq (rt3.At pr3)
          ⋆ Eq (ob4.At p4)
          ⋆ Eq (ep4.At (p4 + 8))
          ⋆ Eq ((Int.toBytes 8 pr4.toInt).At (p4 + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (p4 + 24))
          ⋆ Eq (oc4.At (p4 + 32))
          ⋆ Eq (ot4.At (p4 + 40))
          ⋆ Eq (rt4.At pr4)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (b2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
          ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (dr3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
          ⋆ Eq (dr4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 96))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 147)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 184 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.get64 Reg64.rax = s.regs.rbx.toBitVec
        ∧ st.data.regs.get64 Reg64.rbx = s.regs.rcx.toBitVec + 88
        ∧ st.data.regs.get64 Reg64.rcx = s.regs.rdi.toBitVec ∧
        ∃ (x0 x1 x2 x3 x4 x5 x6 x7 x8 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧ x2.length = 8 ∧ x3.length = 16 ∧ x4.length = 16 ∧ x5.length = 8 ∧ x6.length = 48 ∧ x7.length = 8 ∧ x8.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (v1.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 176))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 113)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 192))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rsp.toBitVec - 8).toInt).At (s.regs.rsp.toBitVec - 200))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 208))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 216))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 88).toInt).At (s.regs.rsp.toBitVec - 224))
          ⋆ Eq (x4.At (s.regs.rsp.toBitVec - 240))
          ⋆ Eq (ep3.At (s.regs.rsp.toBitVec - 256))
          ⋆ Eq (x5.At (s.regs.rsp.toBitVec - 248))
          ⋆ Eq (x6.At (s.regs.rsp.toBitVec - 304))
          ⋆ Eq (x7.At (s.regs.rsp.toBitVec - 312))
          ⋆ Eq (x8.At (s.regs.rsp.toBitVec - 312 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 p4.toInt).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (b2.At p2)
          ⋆ Eq (ob3.At p3)
          ⋆ Eq (ep3.At (p3 + 8))
          ⋆ Eq ((Int.toBytes 8 pr3.toInt).At (p3 + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (p3 + 24))
          ⋆ Eq (oc3.At (p3 + 32))
          ⋆ Eq (ot3.At (p3 + 40))
          ⋆ Eq (rt3.At pr3)
          ⋆ Eq (ob4.At p4)
          ⋆ Eq (ep4.At (p4 + 8))
          ⋆ Eq ((Int.toBytes 8 pr4.toInt).At (p4 + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (p4 + 24))
          ⋆ Eq (oc4.At (p4 + 32))
          ⋆ Eq (ot4.At (p4 + 40))
          ⋆ Eq (rt4.At pr4)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (b2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
          ⋆ Eq (ep3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (rt3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
          ⋆ Eq (dr4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 96))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf kC hkC hfC v0 v1 b2 ep3 rt3 ep4 rt4 ob3 oc3 ot3 ob4 oc4 ot4 pre d0 d1 d2 d3 dr3 d4 dr4 hv0 hv1 hb2 hep3 hrt3 hep4 hrt4 hob3 hoc3 hot3 hob4 hoc4 hot4 hd0 hd1 hd2 hd3 hdr3 hd4 hdr4 p2 p3 pr3 p4 pr4 hp3 hp4 s ra guard hpre fp s1 s2 t80 t64 t112 t96 l48 l120 l128 l176 rslot hfp hs1 hs2 ht80 ht64 ht112 ht96 hl48 hl120 hl128 hl176 hrslot R S hS scratch hsc hguard hcap hcap63 hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hguard hcap hcap63 hpre ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, x0, x1, x2, x3, x4, hx0, hx1, hx2, hx3, hx4, Hm⟩
  dsimp only at hpc hrsp hrbp hr14  Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14  Hm
  subst rsp1 rbp1 r141
  have hcap' : rcx.toBitVec.toNat + 128 ≤ rdi.toBitVec.toNat := hcap
  apply step_load_value Reg64.rdx Reg64.rsp 192 _ (k + 90) (k + 91) (window_infix_at hk 90 1) (by rfl) (by rfl)
    (rsp.toBitVec - 184) (rsp.toBitVec + 8) rax.toBitVec (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  have hl107 := Machine.label_at' hk hf (j := 107)
    (by simp only [marshalSSZTo, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply step_nil_check_taken Reg64.rdx 48 _ _ (k + 91) (k + 107) (window_infix_at hk 91 2) (by rfl) hl107
    rax.toBitVec (rax.toBitVec + 48) p3 (by encoder_address_equation) hp3 _ _ _ (by rfl) (by ecancel)
  intro fl; normalize_registers
  apply step_label _ _ (k + 107) (k + 108) (window_infix_at hk 107 1) (by rfl) (by rfl)
  apply step_load_value Reg64.rax Reg64.rdx 48 _ (k + 108) (k + 109) (window_infix_at hk 108 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 48) p3 (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_load_value Reg64.rbx Reg64.rsp 136 _ (k + 109) (k + 110) (window_infix_at hk 109 1) (by rfl) (by rfl)
    (rsp.toBitVec - 184) (rsp.toBitVec - 48) rbx.toBitVec (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_load_value Reg64.rcx Reg64.rsp 64 _ (k + 110) (k + 111) (window_infix_at hk 110 1) (by rfl) (by rfl)
    (rsp.toBitVec - 184) (rsp.toBitVec - 120) (rcx.toBitVec + 48) (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_load_value Reg64.rdi Reg64.rsp 56 _ (k + 111) (k + 112) (window_infix_at hk 111 1) (by rfl) (by rfl)
    (rsp.toBitVec - 184) (rsp.toBitVec - 128) rdi.toBitVec (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  have hC : NestedCheckpointCalleeEncode "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo" S := Prysm.Checkpoint.Encode.fast_path_function_spec_holds kC hkC hfC S hmm
  obtain ⟨sc2, rs2, gp2, ta2, tb2, la2, lb2, lc2, fq2, hsc2, hrs2, hgp2, hta2, htb2, hla2, hlb2, hlc2, hfq2, Hs2⟩ :=
    low_block_callee_frame_split (rsp.toBitVec - 312) (rsp.toBitVec - 304) (rsp.toBitVec - 256) (rsp.toBitVec - 240) (rsp.toBitVec - 224) (rsp.toBitVec - 216) (rsp.toBitVec - 208) (rsp.toBitVec - 200) S hS
    (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
    x4 hx4 _ _ (by first | ecancel | (dsimp only; ecancel))
  clear Hm
  have hrdi := rdi.toBitVec.isLt
  have hP2 : Eq ((pre ++ (v0 ++ (v1 ++ b2))).At rbx.toBitVec) = Eq (pre.At rbx.toBitVec) ⋆ (Eq (v0.At (rbx.toBitVec + rcx.toBitVec)) ⋆ (Eq (v1.At (rbx.toBitVec + rcx.toBitVec + 8)) ⋆ Eq (b2.At (rbx.toBitVec + rcx.toBitVec + 16)))) := by
    rw [at_app pre (v0 ++ (v1 ++ (b2))) (b := rbx.toBitVec + rcx.toBitVec)
      (by rw [hpre]; show _ = _ + BitVec.ofNat 64 rcx.toBitVec.toNat; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
      (by simp only [List.length_append, hv0, hv1, hb2]; omega),
    at_app v0 (v1 ++ (b2)) (b := rbx.toBitVec + rcx.toBitVec + 8)
      (by rw [hv0] <;> bv_omega) (by simp only [List.length_append, hv0, hv1, hb2] <;> omega),
    at_app v1 b2 (b := rbx.toBitVec + rcx.toBitVec + 16)
      (by rw [hv1] <;> bv_omega) (by simp only [List.length_append, hv0, hv1, hb2] <;> omega)]
  have hPl2 : (pre ++ (v0 ++ (v1 ++ b2))).length = (rcx.toBitVec + 48).toNat :=
    nested_prefix_length rcx rdi 48 _ (by simp only [List.length_append, hpre, hv0, hv1, hb2] <;> omega) (by omega)
  refine eventually_trans _ _ _ _ (encode_nested_checkpoint_call "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo" S hC (k + 112) (window_infix_at hk 112 1)
    (rsp.toBitVec - 184) p3 pr3 rbx.toBitVec (rcx.toBitVec + 48) rdi.toBitVec (rcx.toBitVec + 88) (by bv_omega)
    (rsp.toBitVec - 192) (rsp.toBitVec - 200) (rsp.toBitVec - 176) (rsp.toBitVec - 208) (rsp.toBitVec - 216) (rsp.toBitVec - 224) (rsp.toBitVec - 240) (rsp.toBitVec - 256) (rsp.toBitVec - 248) (rsp.toBitVec - 312) (rsp.toBitVec - 312 - BitVec.ofNat 64 S)
    (rbx.toBitVec + rcx.toBitVec + 48) (rbx.toBitVec + rcx.toBitVec + 56)
    (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
    (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
    guard (nested_call_stack rsp guard.toNat 184 312 hguard (by decide)).1 (nested_call_stack rsp guard.toNat 184 312 hguard (by decide)).2
    (nested_call_capacity rcx rdi 48 (by omega) hcap63) hcap63
    ob3 ep3 oc3 ot3 rt3 (pre ++ (v0 ++ (v1 ++ b2))) d3 dr3 (Int.toBytes 8 (Host.addrOf (k + 90)).toBitVec.toInt) fq2 l176 lc2 lb2 la2 tb2 ta2 rs2 sc2
    hob3 hep3 hoc3 hot3 hrt3 hPl2 hd3 hdr3 (Int.toBytes_length 8 _) hfq2 hl176 hlc2 hlb2 hla2 htb2 hta2 hrs2 hsc2
    _ _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rw [hP2]; first | ecancel | (dsimp only; ecancel))) ?_
  clear Hs2
  rintro ⟨e2, pc2⟩ ⟨hpc2, hxa2, hxb2, hxc2, hxd2, hxs2, hrsp2, hrbp2, hr142, tt2, uu2, ss2, rr2, htt2, huu2, hss2, hrr2, Hc2⟩
  dsimp only at hpc2 hxa2 hxb2 hxc2 hxd2 hxs2 hrsp2 hrbp2 hr142 Hc2
  subst hpc2
  obtain ⟨⟨raxc2, rbxc2, rcxc2, rdxc2, rsic2, rdic2, rspc2, rbpc2, r8c2, r9c2, r10c2, r11c2, r12c2, r13c2, r14c2, r15c2⟩, zmmsc2, flagsc2, memc2⟩ := e2
  simp only at hxa2 hxb2 hxc2 hxd2 hxs2 hrsp2 hrbp2 hr142 Hc2
  subst rspc2 rbpc2 r14c2 rdic2 rsic2
  obtain rfl : rbx = raxc2 := (UInt64.toBitVec_inj.mp hxa2).symm
  obtain rfl : rdi = rcxc2 := (UInt64.toBitVec_inj.mp hxc2).symm
  rw [show k + 112 + 1 = k + 113 from rfl, hP2] at Hc2
  apply register_value_rewrite Reg64.rbx (rcx.toBitVec + 88) _ _ _ (by exact hxb2)
  normalize_registers
  have hl147 := Machine.label_at' hk hf (j := 147)
    (by simp only [marshalSSZTo, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply step_test_je_taken Reg64.rdi _ _ (k + 113) (k + 147) (window_infix_at hk 113 2) (by rfl) hl147 _ _ (by rfl)
  intro fl; normalize_registers
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, x0, x1, x2, x3, uu2, tt2, gp2, rr2, ss2, hx0, hx1, hx2, hx3, huu2, htt2, hgp2, hrr2, hss2, ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem Encode.generated_field_3_kind : ∀ (h : Host), type_of% (@Encode.generated_field_3 h)
    = @Codec.encodeFieldNestedKindAnyFrame h marshalSSZTo Prysm.AttestationData.Encode.generated_layout [.flat .uint64, .flat .uint64, .flat (.bytes 32), .checkpoint, .checkpoint]
    ⟨90, 3, [],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 80) (.field 0), .at (.below 72) (.existential 0), .at (.below 64) (.existential 1), .at (.below 112) (.field 1), .at (.below 104) (.existential 2), .at (.below 96) (.existential 3), .at (.below 48) (.reg .rbx), .at (.below 120) (.len 48), .at (.below 128) (.reg .rdi), .at (.below 176) (.original 10), .at (.below 192) (.ret 90), .low (.existential 4)],
      [.fixed 8, .fixed 16, .fixed 8, .fixed 16, .lowBlock]⟩
    ⟨147, 4, [(.rax, .ptr), (.rbx, .len 88), (.rcx, .cap)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 80) (.field 0), .at (.below 72) (.existential 0), .at (.below 64) (.existential 1), .at (.below 112) (.field 1), .at (.below 104) (.existential 2), .at (.below 96) (.existential 3), .at (.below 48) (.reg .rbx), .at (.below 120) (.len 48), .at (.below 128) (.reg .rdi), .at (.below 176) (.reg .rbx), .at (.below 192) (.ret 113), .at (.below 200) (.framePointer), .at (.below 208) (.reg .rbx), .at (.below 216) (.reg .rdi), .at (.below 224) (.len 88), .at (.below 240) (.existential 4), .at (.below 256) (.field 3), .at (.below 248) (.existential 5), .at (.below 304) (.existential 6), .at (.below 312) (.existential 7), .low (.existential 8)],
      [.fixed 8, .fixed 16, .fixed 8, .fixed 16, .fixed 16, .fixed 8, .fixed 48, .fixed 8, .low]⟩ := by
  intro h; rfl

-- Measured cause: with the default maxRecDepth (512), the `simp only` of a label fact (`Machine.label_at'`)
-- fails with "maximum recursion depth has been reached"; 1000 passes. The default maxHeartbeats passes.
set_option maxRecDepth 1000 in
/-- Field 4 `Target` (nested Checkpoint): directives 147–211; boundary state 4 → 5. -/
theorem Encode.generated_field_4 : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (kC : Nat) (hkC : Prysm.Checkpoint.Code.marshalSSZTo.IsInfixAt Host.prog kC) (hfC : LabelsFresh Prysm.Checkpoint.Code.marshalSSZTo kC)
    (v0 v1 b2 ep3 rt3 ep4 rt4 ob3 oc3 ot3 ob4 oc4 ot4 pre d0 d1 d2 d3 dr3 d4 dr4 : List UInt8) (hv0 : v0.length = 8) (hv1 : v1.length = 8) (hb2 : b2.length = 32) (hep3 : ep3.length = 8) (hrt3 : rt3.length = 32) (hep4 : ep4.length = 8) (hrt4 : rt4.length = 32) (hob3 : ob3.length = 8) (hoc3 : oc3.length = 8) (hot3 : ot3.length = 32) (hob4 : ob4.length = 8) (hoc4 : oc4.length = 8) (hot4 : ot4.length = 32) (hd0 : d0.length = 8) (hd1 : d1.length = 8) (hd2 : d2.length = 32) (hd3 : d3.length = 8) (hdr3 : dr3.length = 32) (hd4 : d4.length = 8) (hdr4 : dr4.length = 32)
    (p2 p3 pr3 p4 pr4 : BitVec 64) (hp3 : p3 ≠ 0) (hp4 : p4 ≠ 0) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 t80 t64 t112 t96 l48 l120 l128 l176 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (ht80 : t80.length = 16) (ht64 : t64.length = 16) (ht112 : t112.length = 16) (ht96 : t96.length = 16) (hl48 : l48.length = 8) (hl120 : l120.length = 8) (hl128 : l128.length = 8) (hl176 : l176.length = 8) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (hS : S < 2 ^ 60) (scratch : List UInt8) (hsc : scratch.length = S + 120)
    (hguard : guard.toNat + 312 < s.regs.rsp.toNat) (hcap : s.regs.rcx.toNat + 128 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 147)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 184 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14
        ∧ st0.data.regs.get64 Reg64.rax = s.regs.rbx.toBitVec
        ∧ st0.data.regs.get64 Reg64.rbx = s.regs.rcx.toBitVec + 88
        ∧ st0.data.regs.get64 Reg64.rcx = s.regs.rdi.toBitVec ∧
        ∃ (x0 x1 x2 x3 x4 x5 x6 x7 x8 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧ x2.length = 8 ∧ x3.length = 16 ∧ x4.length = 16 ∧ x5.length = 8 ∧ x6.length = 48 ∧ x7.length = 8 ∧ x8.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (v1.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 176))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 113)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 192))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rsp.toBitVec - 8).toInt).At (s.regs.rsp.toBitVec - 200))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 208))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 216))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 88).toInt).At (s.regs.rsp.toBitVec - 224))
          ⋆ Eq (x4.At (s.regs.rsp.toBitVec - 240))
          ⋆ Eq (ep3.At (s.regs.rsp.toBitVec - 256))
          ⋆ Eq (x5.At (s.regs.rsp.toBitVec - 248))
          ⋆ Eq (x6.At (s.regs.rsp.toBitVec - 304))
          ⋆ Eq (x7.At (s.regs.rsp.toBitVec - 312))
          ⋆ Eq (x8.At (s.regs.rsp.toBitVec - 312 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 p4.toInt).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (b2.At p2)
          ⋆ Eq (ob3.At p3)
          ⋆ Eq (ep3.At (p3 + 8))
          ⋆ Eq ((Int.toBytes 8 pr3.toInt).At (p3 + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (p3 + 24))
          ⋆ Eq (oc3.At (p3 + 32))
          ⋆ Eq (ot3.At (p3 + 40))
          ⋆ Eq (rt3.At pr3)
          ⋆ Eq (ob4.At p4)
          ⋆ Eq (ep4.At (p4 + 8))
          ⋆ Eq ((Int.toBytes 8 pr4.toInt).At (p4 + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (p4 + 24))
          ⋆ Eq (oc4.At (p4 + 32))
          ⋆ Eq (ot4.At (p4 + 40))
          ⋆ Eq (rt4.At pr4)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (b2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
          ⋆ Eq (ep3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (rt3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
          ⋆ Eq (dr4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 96))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 212)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 184 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.get64 Reg64.rax = s.regs.rbx.toBitVec
        ∧ st.data.regs.get64 Reg64.rbx = s.regs.rcx.toBitVec + 128
        ∧ st.data.regs.get64 Reg64.rcx = s.regs.rdi.toBitVec
        ∧ st.data.regs.get64 Reg64.rsi = 0
        ∧ st.data.regs.get64 Reg64.rdi = 0 ∧
        ∃ (x0 x1 x2 x3 x4 x5 x6 x7 x8 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧ x2.length = 8 ∧ x3.length = 16 ∧ x4.length = 48 ∧ x5.length = 16 ∧ x6.length = 8 ∧ x7.length = 8 ∧ x8.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (v1.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 176))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 178)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 192))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rsp.toBitVec - 8).toInt).At (s.regs.rsp.toBitVec - 200))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 208))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 216))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 128).toInt).At (s.regs.rsp.toBitVec - 224))
          ⋆ Eq (x5.At (s.regs.rsp.toBitVec - 240))
          ⋆ Eq (ep4.At (s.regs.rsp.toBitVec - 256))
          ⋆ Eq (x6.At (s.regs.rsp.toBitVec - 248))
          ⋆ Eq (x4.At (s.regs.rsp.toBitVec - 304))
          ⋆ Eq (x7.At (s.regs.rsp.toBitVec - 312))
          ⋆ Eq (x8.At (s.regs.rsp.toBitVec - 312 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 p4.toInt).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (b2.At p2)
          ⋆ Eq (ob3.At p3)
          ⋆ Eq (ep3.At (p3 + 8))
          ⋆ Eq ((Int.toBytes 8 pr3.toInt).At (p3 + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (p3 + 24))
          ⋆ Eq (oc3.At (p3 + 32))
          ⋆ Eq (ot3.At (p3 + 40))
          ⋆ Eq (rt3.At pr3)
          ⋆ Eq (ob4.At p4)
          ⋆ Eq (ep4.At (p4 + 8))
          ⋆ Eq ((Int.toBytes 8 pr4.toInt).At (p4 + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (p4 + 24))
          ⋆ Eq (oc4.At (p4 + 32))
          ⋆ Eq (ot4.At (p4 + 40))
          ⋆ Eq (rt4.At pr4)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (b2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
          ⋆ Eq (ep3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (rt3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56))
          ⋆ Eq (ep4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
          ⋆ Eq (rt4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 96))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf kC hkC hfC v0 v1 b2 ep3 rt3 ep4 rt4 ob3 oc3 ot3 ob4 oc4 ot4 pre d0 d1 d2 d3 dr3 d4 dr4 hv0 hv1 hb2 hep3 hrt3 hep4 hrt4 hob3 hoc3 hot3 hob4 hoc4 hot4 hd0 hd1 hd2 hd3 hdr3 hd4 hdr4 p2 p3 pr3 p4 pr4 hp3 hp4 s ra guard hpre fp s1 s2 t80 t64 t112 t96 l48 l120 l128 l176 rslot hfp hs1 hs2 ht80 ht64 ht112 ht96 hl48 hl120 hl128 hl176 hrslot R S hS scratch hsc hguard hcap hcap63 hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hguard hcap hcap63 hpre ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, hrrax, hrrbx, hrrcx, x0, x1, x2, x3, x4, x5, x6, x7, x8, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, Hm⟩
  dsimp only at hpc hrsp hrbp hr14 hrrax hrrbx hrrcx Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14 hrrax hrrbx hrrcx Hm
  subst rsp1 rbp1 r141
  obtain rfl : rbx = rax1 := (UInt64.toBitVec_inj.mp hrrax).symm
  obtain rfl : rbx1 = { toBitVec := rcx.toBitVec + 88 } := UInt64.toBitVec_inj.mp hrrbx
  obtain rfl : rdi = rcx1 := (UInt64.toBitVec_inj.mp hrrcx).symm
  have hcap' : rcx.toBitVec.toNat + 128 ≤ rdi.toBitVec.toNat := hcap
  apply step_label _ _ (k + 147) (k + 148) (window_infix_at hk 147 1) (by rfl) (by rfl)
  apply step_load_value Reg64.rdx Reg64.rsp 192 _ (k + 148) (k + 149) (window_infix_at hk 148 1) (by rfl) (by rfl)
    (rsp.toBitVec - 184) (rsp.toBitVec + 8) rax.toBitVec (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  have hl171 := Machine.label_at' hk hf (j := 171)
    (by simp only [marshalSSZTo, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply step_nil_check_taken Reg64.rdx 56 _ _ (k + 149) (k + 171) (window_infix_at hk 149 2) (by rfl) hl171
    rax.toBitVec (rax.toBitVec + 56) p4 (by encoder_address_equation) hp4 _ _ _ (by rfl) (by ecancel)
  intro fl; normalize_registers
  apply step_label _ _ (k + 171) (k + 172) (window_infix_at hk 171 1) (by rfl) (by rfl)
  apply step_load_value Reg64.rdx Reg64.rdx 56 _ (k + 172) (k + 173) (window_infix_at hk 172 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 56) p4 (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_move_register Reg64.rdi Reg64.rcx _ (k + 173) (k + 174) (window_infix_at hk 173 1) (by rfl) (by rfl)
  normalize_registers
  apply step_move_register Reg64.rcx Reg64.rbx _ (k + 174) (k + 175) (window_infix_at hk 174 1) (by rfl) (by rfl)
  normalize_registers
  apply step_move_register Reg64.rbx Reg64.rax _ (k + 175) (k + 176) (window_infix_at hk 175 1) (by rfl) (by rfl)
  normalize_registers
  apply step_move_register Reg64.rax Reg64.rdx _ (k + 176) (k + 177) (window_infix_at hk 176 1) (by rfl) (by rfl)
  normalize_registers
  have hC : NestedCheckpointCalleeEncode "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo" S := Prysm.Checkpoint.Encode.fast_path_function_spec_holds kC hkC hfC S hmm
  have hrdi := rdi.toBitVec.isLt
  have hP3 : Eq ((pre ++ (v0 ++ (v1 ++ (b2 ++ (ep3 ++ rt3))))).At rbx.toBitVec) = Eq (pre.At rbx.toBitVec) ⋆ (Eq (v0.At (rbx.toBitVec + rcx.toBitVec)) ⋆ (Eq (v1.At (rbx.toBitVec + rcx.toBitVec + 8)) ⋆ (Eq (b2.At (rbx.toBitVec + rcx.toBitVec + 16)) ⋆ (Eq (ep3.At (rbx.toBitVec + rcx.toBitVec + 48)) ⋆ Eq (rt3.At (rbx.toBitVec + rcx.toBitVec + 56)))))) := by
    rw [at_app pre (v0 ++ (v1 ++ (b2 ++ (ep3 ++ (rt3))))) (b := rbx.toBitVec + rcx.toBitVec)
      (by rw [hpre]; show _ = _ + BitVec.ofNat 64 rcx.toBitVec.toNat; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
      (by simp only [List.length_append, hv0, hv1, hb2, hep3, hrt3]; omega),
    at_app v0 (v1 ++ (b2 ++ (ep3 ++ (rt3)))) (b := rbx.toBitVec + rcx.toBitVec + 8)
      (by rw [hv0] <;> bv_omega) (by simp only [List.length_append, hv0, hv1, hb2, hep3, hrt3] <;> omega),
    at_app v1 (b2 ++ (ep3 ++ (rt3))) (b := rbx.toBitVec + rcx.toBitVec + 16)
      (by rw [hv1] <;> bv_omega) (by simp only [List.length_append, hv0, hv1, hb2, hep3, hrt3] <;> omega),
    at_app b2 (ep3 ++ (rt3)) (b := rbx.toBitVec + rcx.toBitVec + 48)
      (by rw [hb2] <;> bv_omega) (by simp only [List.length_append, hv0, hv1, hb2, hep3, hrt3] <;> omega),
    at_app ep3 rt3 (b := rbx.toBitVec + rcx.toBitVec + 56)
      (by rw [hep3] <;> bv_omega) (by simp only [List.length_append, hv0, hv1, hb2, hep3, hrt3] <;> omega)]
  have hPl3 : (pre ++ (v0 ++ (v1 ++ (b2 ++ (ep3 ++ rt3))))).length = (rcx.toBitVec + 88).toNat :=
    nested_prefix_length rcx rdi 88 _ (by simp only [List.length_append, hpre, hv0, hv1, hb2, hep3, hrt3] <;> omega) (by omega)
  refine eventually_trans _ _ _ _ (encode_nested_checkpoint_call "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo" S hC (k + 177) (window_infix_at hk 177 1)
    (rsp.toBitVec - 184) p4 pr4 rbx.toBitVec (rcx.toBitVec + 88) rdi.toBitVec (rcx.toBitVec + 128) (by bv_omega)
    (rsp.toBitVec - 192) (rsp.toBitVec - 200) (rsp.toBitVec - 176) (rsp.toBitVec - 208) (rsp.toBitVec - 216) (rsp.toBitVec - 224) (rsp.toBitVec - 240) (rsp.toBitVec - 256) (rsp.toBitVec - 248) (rsp.toBitVec - 312) (rsp.toBitVec - 312 - BitVec.ofNat 64 S)
    (rbx.toBitVec + rcx.toBitVec + 88) (rbx.toBitVec + rcx.toBitVec + 96)
    (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
    (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
    guard (nested_call_stack rsp guard.toNat 184 312 hguard (by decide)).1 (nested_call_stack rsp guard.toNat 184 312 hguard (by decide)).2
    (nested_call_capacity rcx rdi 88 (by omega) hcap63) hcap63
    ob4 ep4 oc4 ot4 rt4 (pre ++ (v0 ++ (v1 ++ (b2 ++ (ep3 ++ rt3))))) d4 dr4 (Int.toBytes 8 (Host.addrOf (k + 113)).toBitVec.toInt) (Int.toBytes 8 (rsp.toBitVec - 8).toInt) (Int.toBytes 8 rbx.toBitVec.toInt) (Int.toBytes 8 rbx.toBitVec.toInt) (Int.toBytes 8 rdi.toBitVec.toInt) (Int.toBytes 8 (rcx.toBitVec + 88).toInt) x4 (ep3 ++ x5) x7 x8
    hob4 hep4 hoc4 hot4 hrt4 hPl3 hd4 hdr4 (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) hx4 (by rw [List.length_append, hep3, hx5]) hx7 hx8
    _ _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rw [at_app ep3 x5 (b := rsp.toBitVec - 248) (by rw [hep3]; bv_omega) (by rw [hep3, hx5]; omega)]; rw [hP3]; first | ecancel | (dsimp only; ecancel))) ?_
  clear Hm
  rintro ⟨e3, pc3⟩ ⟨hpc3, hxa3, hxb3, hxc3, hxd3, hxs3, hrsp3, hrbp3, hr143, tt3, uu3, ss3, rr3, htt3, huu3, hss3, hrr3, Hc3⟩
  dsimp only at hpc3 hxa3 hxb3 hxc3 hxd3 hxs3 hrsp3 hrbp3 hr143 Hc3
  subst hpc3
  obtain ⟨⟨raxc3, rbxc3, rcxc3, rdxc3, rsic3, rdic3, rspc3, rbpc3, r8c3, r9c3, r10c3, r11c3, r12c3, r13c3, r14c3, r15c3⟩, zmmsc3, flagsc3, memc3⟩ := e3
  simp only at hxa3 hxb3 hxc3 hxd3 hxs3 hrsp3 hrbp3 hr143 Hc3
  subst rspc3 rbpc3 r14c3 rdic3 rsic3
  obtain rfl : rbx = raxc3 := (UInt64.toBitVec_inj.mp hxa3).symm
  obtain rfl : rdi = rcxc3 := (UInt64.toBitVec_inj.mp hxc3).symm
  rw [show k + 177 + 1 = k + 178 from rfl, hP3] at Hc3
  apply register_value_rewrite Reg64.rbx (rcx.toBitVec + 128) _ _ _ (by exact hxb3)
  normalize_registers
  have hl212 := Machine.label_at' hk hf (j := 212)
    (by simp only [marshalSSZTo, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply step_test_je_taken Reg64.rdi _ _ (k + 178) (k + 212) (window_infix_at hk 178 2) (by rfl) hl212 _ _ (by rfl)
  intro fl; normalize_registers
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, x0, x1, x2, x3, x6, uu3, tt3, rr3, ss3, hx0, hx1, hx2, hx3, hx6, huu3, htt3, hrr3, hss3, ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem Encode.generated_field_4_kind : ∀ (h : Host), type_of% (@Encode.generated_field_4 h)
    = @Codec.encodeFieldNestedKindAnyFrame h marshalSSZTo Prysm.AttestationData.Encode.generated_layout [.flat .uint64, .flat .uint64, .flat (.bytes 32), .checkpoint, .checkpoint]
    ⟨147, 4, [(.rax, .ptr), (.rbx, .len 88), (.rcx, .cap)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 80) (.field 0), .at (.below 72) (.existential 0), .at (.below 64) (.existential 1), .at (.below 112) (.field 1), .at (.below 104) (.existential 2), .at (.below 96) (.existential 3), .at (.below 48) (.reg .rbx), .at (.below 120) (.len 48), .at (.below 128) (.reg .rdi), .at (.below 176) (.reg .rbx), .at (.below 192) (.ret 113), .at (.below 200) (.framePointer), .at (.below 208) (.reg .rbx), .at (.below 216) (.reg .rdi), .at (.below 224) (.len 88), .at (.below 240) (.existential 4), .at (.below 256) (.field 3), .at (.below 248) (.existential 5), .at (.below 304) (.existential 6), .at (.below 312) (.existential 7), .low (.existential 8)],
      [.fixed 8, .fixed 16, .fixed 8, .fixed 16, .fixed 16, .fixed 8, .fixed 48, .fixed 8, .low]⟩
    ⟨212, 5, [(.rax, .ptr), (.rbx, .len 128), (.rcx, .cap), (.rsi, .zero), (.rdi, .zero)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 80) (.field 0), .at (.below 72) (.existential 0), .at (.below 64) (.existential 1), .at (.below 112) (.field 1), .at (.below 104) (.existential 2), .at (.below 96) (.existential 3), .at (.below 48) (.reg .rbx), .at (.below 120) (.len 48), .at (.below 128) (.reg .rdi), .at (.below 176) (.reg .rbx), .at (.below 192) (.ret 178), .at (.below 200) (.framePointer), .at (.below 208) (.reg .rbx), .at (.below 216) (.reg .rdi), .at (.below 224) (.len 128), .at (.below 240) (.existential 5), .at (.below 256) (.field 5), .at (.below 248) (.existential 6), .at (.below 304) (.existential 4), .at (.below 312) (.existential 7), .low (.existential 8)],
      [.fixed 8, .fixed 16, .fixed 8, .fixed 16, .fixed 48, .fixed 16, .fixed 8, .fixed 8, .low]⟩ := by
  intro h; rfl

/-- Epilogue: directives 212–return; boundary state 5 → the fast-path post-state. -/
theorem Encode.generated_epilogue : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (kC : Nat) (hkC : Prysm.Checkpoint.Code.marshalSSZTo.IsInfixAt Host.prog kC) (hfC : LabelsFresh Prysm.Checkpoint.Code.marshalSSZTo kC)
    (v0 v1 b2 ep3 rt3 ep4 rt4 ob3 oc3 ot3 ob4 oc4 ot4 pre d0 d1 d2 d3 dr3 d4 dr4 : List UInt8) (hv0 : v0.length = 8) (hv1 : v1.length = 8) (hb2 : b2.length = 32) (hep3 : ep3.length = 8) (hrt3 : rt3.length = 32) (hep4 : ep4.length = 8) (hrt4 : rt4.length = 32) (hob3 : ob3.length = 8) (hoc3 : oc3.length = 8) (hot3 : ot3.length = 32) (hob4 : ob4.length = 8) (hoc4 : oc4.length = 8) (hot4 : ot4.length = 32) (hd0 : d0.length = 8) (hd1 : d1.length = 8) (hd2 : d2.length = 32) (hd3 : d3.length = 8) (hdr3 : dr3.length = 32) (hd4 : d4.length = 8) (hdr4 : dr4.length = 32)
    (p2 p3 pr3 p4 pr4 : BitVec 64) (hp3 : p3 ≠ 0) (hp4 : p4 ≠ 0) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 t80 t64 t112 t96 l48 l120 l128 l176 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (ht80 : t80.length = 16) (ht64 : t64.length = 16) (ht112 : t112.length = 16) (ht96 : t96.length = 16) (hl48 : l48.length = 8) (hl120 : l120.length = 8) (hl128 : l128.length = 8) (hl176 : l176.length = 8) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (hS : S < 2 ^ 60) (scratch : List UInt8) (hsc : scratch.length = S + 120)
    (hguard : guard.toNat + 312 < s.regs.rsp.toNat) (hcap : s.regs.rcx.toNat + 128 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 212)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 184 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14
        ∧ st0.data.regs.get64 Reg64.rax = s.regs.rbx.toBitVec
        ∧ st0.data.regs.get64 Reg64.rbx = s.regs.rcx.toBitVec + 128
        ∧ st0.data.regs.get64 Reg64.rcx = s.regs.rdi.toBitVec
        ∧ st0.data.regs.get64 Reg64.rsi = 0
        ∧ st0.data.regs.get64 Reg64.rdi = 0 ∧
        ∃ (x0 x1 x2 x3 x4 x5 x6 x7 x8 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧ x2.length = 8 ∧ x3.length = 16 ∧ x4.length = 48 ∧ x5.length = 16 ∧ x6.length = 8 ∧ x7.length = 8 ∧ x8.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (v1.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 176))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 178)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 192))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rsp.toBitVec - 8).toInt).At (s.regs.rsp.toBitVec - 200))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 208))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 216))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 128).toInt).At (s.regs.rsp.toBitVec - 224))
          ⋆ Eq (x5.At (s.regs.rsp.toBitVec - 240))
          ⋆ Eq (ep4.At (s.regs.rsp.toBitVec - 256))
          ⋆ Eq (x6.At (s.regs.rsp.toBitVec - 248))
          ⋆ Eq (x4.At (s.regs.rsp.toBitVec - 304))
          ⋆ Eq (x7.At (s.regs.rsp.toBitVec - 312))
          ⋆ Eq (x8.At (s.regs.rsp.toBitVec - 312 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 p4.toInt).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (b2.At p2)
          ⋆ Eq (ob3.At p3)
          ⋆ Eq (ep3.At (p3 + 8))
          ⋆ Eq ((Int.toBytes 8 pr3.toInt).At (p3 + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (p3 + 24))
          ⋆ Eq (oc3.At (p3 + 32))
          ⋆ Eq (ot3.At (p3 + 40))
          ⋆ Eq (rt3.At pr3)
          ⋆ Eq (ob4.At p4)
          ⋆ Eq (ep4.At (p4 + 8))
          ⋆ Eq ((Int.toBytes 8 pr4.toInt).At (p4 + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (p4 + 24))
          ⋆ Eq (oc4.At (p4 + 32))
          ⋆ Eq (ot4.At (p4 + 40))
          ⋆ Eq (rt4.At pr4)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (b2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
          ⋆ Eq (ep3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (rt3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56))
          ⋆ Eq (ep4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
          ⋆ Eq (rt4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 96))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec
        ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 128
        ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0
        ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8
        ∧ st.data.regs.rbp = s.regs.rbp
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 x2 x3 x4 x5 x6 x7 x8 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧ x2.length = 8 ∧ x3.length = 16 ∧ x4.length = 48 ∧ x5.length = 16 ∧ x6.length = 8 ∧ x7.length = 8 ∧ x8.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (v1.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 176))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 178)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 192))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rsp.toBitVec - 8).toInt).At (s.regs.rsp.toBitVec - 200))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 208))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 216))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 128).toInt).At (s.regs.rsp.toBitVec - 224))
          ⋆ Eq (x5.At (s.regs.rsp.toBitVec - 240))
          ⋆ Eq (ep4.At (s.regs.rsp.toBitVec - 256))
          ⋆ Eq (x6.At (s.regs.rsp.toBitVec - 248))
          ⋆ Eq (x4.At (s.regs.rsp.toBitVec - 304))
          ⋆ Eq (x7.At (s.regs.rsp.toBitVec - 312))
          ⋆ Eq (x8.At (s.regs.rsp.toBitVec - 312 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 p4.toInt).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (b2.At p2)
          ⋆ Eq (ob3.At p3)
          ⋆ Eq (ep3.At (p3 + 8))
          ⋆ Eq ((Int.toBytes 8 pr3.toInt).At (p3 + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (p3 + 24))
          ⋆ Eq (oc3.At (p3 + 32))
          ⋆ Eq (ot3.At (p3 + 40))
          ⋆ Eq (rt3.At pr3)
          ⋆ Eq (ob4.At p4)
          ⋆ Eq (ep4.At (p4 + 8))
          ⋆ Eq ((Int.toBytes 8 pr4.toInt).At (p4 + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (p4 + 24))
          ⋆ Eq (oc4.At (p4 + 32))
          ⋆ Eq (ot4.At (p4 + 40))
          ⋆ Eq (rt4.At pr4)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (b2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
          ⋆ Eq (ep3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (rt3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56))
          ⋆ Eq (ep4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
          ⋆ Eq (rt4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 96))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf kC hkC hfC v0 v1 b2 ep3 rt3 ep4 rt4 ob3 oc3 ot3 ob4 oc4 ot4 pre d0 d1 d2 d3 dr3 d4 dr4 hv0 hv1 hb2 hep3 hrt3 hep4 hrt4 hob3 hoc3 hot3 hob4 hoc4 hot4 hd0 hd1 hd2 hd3 hdr3 hd4 hdr4 p2 p3 pr3 p4 pr4 hp3 hp4 s ra guard hpre fp s1 s2 t80 t64 t112 t96 l48 l120 l128 l176 rslot hfp hs1 hs2 ht80 ht64 ht112 ht96 hl48 hl120 hl128 hl176 hrslot R S hS scratch hsc hguard hcap hcap63
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hguard hcap hcap63 hpre ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, hrrax, hrrbx, hrrcx, hrrsi, hrrdi, x0, x1, x2, x3, x4, x5, x6, x7, x8, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, Hm⟩
  dsimp only at hpc hrsp hrbp hr14 hrrax hrrbx hrrcx hrrsi hrrdi Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14 hrrax hrrbx hrrcx hrrsi hrrdi Hm
  subst rsp1 rbp1 r141
  obtain rfl : rbx = rax1 := (UInt64.toBitVec_inj.mp hrrax).symm
  obtain rfl : rbx1 = { toBitVec := rcx.toBitVec + 128 } := UInt64.toBitVec_inj.mp hrrbx
  obtain rfl : rdi = rcx1 := (UInt64.toBitVec_inj.mp hrrcx).symm
  obtain rfl : rsi1 = 0 := UInt64.toBitVec_inj.mp hrrsi
  obtain rfl : rdi1 = 0 := UInt64.toBitVec_inj.mp hrrdi
  have hcap' : rcx.toBitVec.toNat + 128 ≤ rdi.toBitVec.toNat := hcap
  apply step_label _ _ (k + 212) (k + 213) (window_infix_at hk 212 1) (by rfl) (by rfl)
  apply step_add_immediate Reg64.rsp 176 _ (k + 213) (k + 214) (window_infix_at hk 213 1) (by rfl) (by rfl)
  intro fl; normalize_registers
  apply register_value_rewrite Reg64.rsp (rsp.toBitVec - 8) _ _ _ (by show ((rsp.toBitVec - 184) + 176 : BitVec 64) = (rsp.toBitVec - 8); bv_omega)
  normalize_registers
  refine eventually_trans _ _ _ _ (decode_return_segment _ (k + 214) (window_infix_at hk 214 3) (by rfl) (rsp.toBitVec - 8) rsp.toBitVec (by bv_omega) rbp ra _ _ (by rfl) (by ecancel)) ?_
  rintro ⟨d', pc'⟩ ⟨hpc', hrsp', hrbp', hreg', hmem'⟩
  dsimp only at hpc' hrsp' hrbp' hreg' hmem'
  apply Eventually.done
  refine ⟨hpc', ?_, ?_, ?_, ?_, ?_, ?_, hrbp', ?_, x0, x1, x2, x3, x4, x5, x6, x7, x8, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, ?_⟩
  · exact UInt64.toBitVec_inj.mp (hreg' Reg64.rax (by decide) (by decide))
  · show d'.regs.rbx.toBitVec.toNat = rcx.toBitVec.toNat + 128
    rw [show d'.regs.rbx.toBitVec = rcx.toBitVec + 128 from hreg' Reg64.rbx (by decide) (by decide)]
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
    = @Codec.encodeEpilogueNestedKindAnyFrame h marshalSSZTo Prysm.AttestationData.Encode.generated_layout [.flat .uint64, .flat .uint64, .flat (.bytes 32), .checkpoint, .checkpoint]
    ⟨212, 5, [(.rax, .ptr), (.rbx, .len 128), (.rcx, .cap), (.rsi, .zero), (.rdi, .zero)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 80) (.field 0), .at (.below 72) (.existential 0), .at (.below 64) (.existential 1), .at (.below 112) (.field 1), .at (.below 104) (.existential 2), .at (.below 96) (.existential 3), .at (.below 48) (.reg .rbx), .at (.below 120) (.len 48), .at (.below 128) (.reg .rdi), .at (.below 176) (.reg .rbx), .at (.below 192) (.ret 178), .at (.below 200) (.framePointer), .at (.below 208) (.reg .rbx), .at (.below 216) (.reg .rdi), .at (.below 224) (.len 128), .at (.below 240) (.existential 5), .at (.below 256) (.field 5), .at (.below 248) (.existential 6), .at (.below 304) (.existential 4), .at (.below 312) (.existential 7), .low (.existential 8)],
      [.fixed 8, .fixed 16, .fixed 8, .fixed 16, .fixed 48, .fixed 16, .fixed 8, .fixed 8, .low]⟩ := by
  intro h; rfl

/-- **Encoder fast path of `(*v1alpha1.AttestationData).MarshalSSZTo` (Go 1.26.10), generated** (`encoder --fast-path`):
head, one theorem per field, epilogue, chained by `eventually_trans`. Premises: `len + 128 ≤ cap`,
every byte-vector field of its exact length, every nested pointer not nil, the callee placed.
Statement = the kind instance (`_kind`). Fast path only. -/
theorem Encode.generated_fast : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (kC : Nat) (hkC : Prysm.Checkpoint.Code.marshalSSZTo.IsInfixAt Host.prog kC) (hfC : LabelsFresh Prysm.Checkpoint.Code.marshalSSZTo kC)
    (v0 v1 b2 ep3 rt3 ep4 rt4 ob3 oc3 ot3 ob4 oc4 ot4 pre d0 d1 d2 d3 dr3 d4 dr4 : List UInt8) (hv0 : v0.length = 8) (hv1 : v1.length = 8) (hb2 : b2.length = 32) (hep3 : ep3.length = 8) (hrt3 : rt3.length = 32) (hep4 : ep4.length = 8) (hrt4 : rt4.length = 32) (hob3 : ob3.length = 8) (hoc3 : oc3.length = 8) (hot3 : ot3.length = 32) (hob4 : ob4.length = 8) (hoc4 : oc4.length = 8) (hot4 : ot4.length = 32) (hd0 : d0.length = 8) (hd1 : d1.length = 8) (hd2 : d2.length = 32) (hd3 : d3.length = 8) (hdr3 : dr3.length = 32) (hd4 : d4.length = 8) (hdr4 : dr4.length = 32)
    (p2 p3 pr3 p4 pr4 : BitVec 64) (hp3 : p3 ≠ 0) (hp4 : p4 ≠ 0) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 t80 t64 t112 t96 l48 l120 l128 l176 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (ht80 : t80.length = 16) (ht64 : t64.length = 16) (ht112 : t112.length = 16) (ht96 : t96.length = 16) (hl48 : l48.length = 8) (hl120 : l120.length = 8) (hl128 : l128.length = 8) (hl176 : l176.length = 8) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (hS : S < 2 ^ 60) (scratch : List UInt8) (hsc : scratch.length = S + 120)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (t80.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (t64.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (t112.At (s.regs.rsp.toBitVec - 112))
      ⋆ Eq (t96.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (l120.At (s.regs.rsp.toBitVec - 120))
      ⋆ Eq (l128.At (s.regs.rsp.toBitVec - 128))
      ⋆ Eq (l176.At (s.regs.rsp.toBitVec - 176))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 192))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 312 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
      ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
      ⋆ Eq ((Int.toBytes 8 p4.toInt).At (s.regs.rax.toBitVec + 56))
      ⋆ Eq (b2.At p2)
      ⋆ Eq (ob3.At p3)
      ⋆ Eq (ep3.At (p3 + 8))
      ⋆ Eq ((Int.toBytes 8 pr3.toInt).At (p3 + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (p3 + 24))
      ⋆ Eq (oc3.At (p3 + 32))
      ⋆ Eq (ot3.At (p3 + 40))
      ⋆ Eq (rt3.At pr3)
      ⋆ Eq (ob4.At p4)
      ⋆ Eq (ep4.At (p4 + 8))
      ⋆ Eq ((Int.toBytes 8 pr4.toInt).At (p4 + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (p4 + 24))
      ⋆ Eq (oc4.At (p4 + 32))
      ⋆ Eq (ot4.At (p4 + 40))
      ⋆ Eq (rt4.At pr4)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
      ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
      ⋆ Eq (dr3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56))
      ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
      ⋆ Eq (dr4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 96))
      ⋆ R)
    (hguard : guard.toNat + 312 < s.regs.rsp.toNat) (hcap : s.regs.rcx.toNat + 128 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec
        ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 128
        ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0
        ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8
        ∧ st.data.regs.rbp = s.regs.rbp
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 x2 x3 x4 x5 x6 x7 x8 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧ x2.length = 8 ∧ x3.length = 16 ∧ x4.length = 48 ∧ x5.length = 16 ∧ x6.length = 8 ∧ x7.length = 8 ∧ x8.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (v1.At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 176))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 178)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 192))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rsp.toBitVec - 8).toInt).At (s.regs.rsp.toBitVec - 200))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 208))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 216))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 128).toInt).At (s.regs.rsp.toBitVec - 224))
          ⋆ Eq (x5.At (s.regs.rsp.toBitVec - 240))
          ⋆ Eq (ep4.At (s.regs.rsp.toBitVec - 256))
          ⋆ Eq (x6.At (s.regs.rsp.toBitVec - 248))
          ⋆ Eq (x4.At (s.regs.rsp.toBitVec - 304))
          ⋆ Eq (x7.At (s.regs.rsp.toBitVec - 312))
          ⋆ Eq (x8.At (s.regs.rsp.toBitVec - 312 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 p4.toInt).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (b2.At p2)
          ⋆ Eq (ob3.At p3)
          ⋆ Eq (ep3.At (p3 + 8))
          ⋆ Eq ((Int.toBytes 8 pr3.toInt).At (p3 + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (p3 + 24))
          ⋆ Eq (oc3.At (p3 + 32))
          ⋆ Eq (ot3.At (p3 + 40))
          ⋆ Eq (rt3.At pr3)
          ⋆ Eq (ob4.At p4)
          ⋆ Eq (ep4.At (p4 + 8))
          ⋆ Eq ((Int.toBytes 8 pr4.toInt).At (p4 + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (p4 + 24))
          ⋆ Eq (oc4.At (p4 + 32))
          ⋆ Eq (ot4.At (p4 + 40))
          ⋆ Eq (rt4.At pr4)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (b2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
          ⋆ Eq (ep3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (rt3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56))
          ⋆ Eq (ep4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
          ⋆ Eq (rt4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 96))
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf kC hkC hfC v0 v1 b2 ep3 rt3 ep4 rt4 ob3 oc3 ot3 ob4 oc4 ot4 pre d0 d1 d2 d3 dr3 d4 dr4 hv0 hv1 hb2 hep3 hrt3 hep4 hrt4 hob3 hoc3 hot3 hob4 hoc4 hot4 hd0 hd1 hd2 hd3 hdr3 hd4 hdr4 p2 p3 pr3 p4 pr4 hp3 hp4 s ra guard hpre fp s1 s2 t80 t64 t112 t96 l48 l120 l128 l176 rslot hfp hs1 hs2 ht80 ht64 ht112 ht96 hl48 hl120 hl128 hl176 hrslot R S hS scratch hsc h_mem hguard hcap hcap63 hmm
  refine eventually_trans _ _ _ _ (Encode.generated_head k hk hf kC hkC hfC v0 v1 b2 ep3 rt3 ep4 rt4 ob3 oc3 ot3 ob4 oc4 ot4 pre d0 d1 d2 d3 dr3 d4 dr4 hv0 hv1 hb2 hep3 hrt3 hep4 hrt4 hob3 hoc3 hot3 hob4 hoc4 hot4 hd0 hd1 hd2 hd3 hdr3 hd4 hdr4 p2 p3 pr3 p4 pr4 hp3 hp4 s ra guard hpre fp s1 s2 t80 t64 t112 t96 l48 l120 l128 l176 rslot hfp hs1 hs2 ht80 ht64 ht112 ht96 hl48 hl120 hl128 hl176 hrslot R S hS scratch hsc h_mem hguard hcap hcap63 hmm) ?_
  intro st0 h0
  refine eventually_trans _ _ _ _ (Encode.generated_field_0 k hk hf kC hkC hfC v0 v1 b2 ep3 rt3 ep4 rt4 ob3 oc3 ot3 ob4 oc4 ot4 pre d0 d1 d2 d3 dr3 d4 dr4 hv0 hv1 hb2 hep3 hrt3 hep4 hrt4 hob3 hoc3 hot3 hob4 hoc4 hot4 hd0 hd1 hd2 hd3 hdr3 hd4 hdr4 p2 p3 pr3 p4 pr4 hp3 hp4 s ra guard hpre fp s1 s2 t80 t64 t112 t96 l48 l120 l128 l176 rslot hfp hs1 hs2 ht80 ht64 ht112 ht96 hl48 hl120 hl128 hl176 hrslot R S hS scratch hsc hguard hcap hcap63 hmm st0 h0) ?_
  intro st1 h1
  refine eventually_trans _ _ _ _ (Encode.generated_field_1 k hk hf kC hkC hfC v0 v1 b2 ep3 rt3 ep4 rt4 ob3 oc3 ot3 ob4 oc4 ot4 pre d0 d1 d2 d3 dr3 d4 dr4 hv0 hv1 hb2 hep3 hrt3 hep4 hrt4 hob3 hoc3 hot3 hob4 hoc4 hot4 hd0 hd1 hd2 hd3 hdr3 hd4 hdr4 p2 p3 pr3 p4 pr4 hp3 hp4 s ra guard hpre fp s1 s2 t80 t64 t112 t96 l48 l120 l128 l176 rslot hfp hs1 hs2 ht80 ht64 ht112 ht96 hl48 hl120 hl128 hl176 hrslot R S hS scratch hsc hguard hcap hcap63 hmm st1 h1) ?_
  intro st2 h2
  refine eventually_trans _ _ _ _ (Encode.generated_field_2 k hk hf kC hkC hfC v0 v1 b2 ep3 rt3 ep4 rt4 ob3 oc3 ot3 ob4 oc4 ot4 pre d0 d1 d2 d3 dr3 d4 dr4 hv0 hv1 hb2 hep3 hrt3 hep4 hrt4 hob3 hoc3 hot3 hob4 hoc4 hot4 hd0 hd1 hd2 hd3 hdr3 hd4 hdr4 p2 p3 pr3 p4 pr4 hp3 hp4 s ra guard hpre fp s1 s2 t80 t64 t112 t96 l48 l120 l128 l176 rslot hfp hs1 hs2 ht80 ht64 ht112 ht96 hl48 hl120 hl128 hl176 hrslot R S hS scratch hsc hguard hcap hcap63 hmm st2 h2) ?_
  intro st3 h3
  refine eventually_trans _ _ _ _ (Encode.generated_field_3 k hk hf kC hkC hfC v0 v1 b2 ep3 rt3 ep4 rt4 ob3 oc3 ot3 ob4 oc4 ot4 pre d0 d1 d2 d3 dr3 d4 dr4 hv0 hv1 hb2 hep3 hrt3 hep4 hrt4 hob3 hoc3 hot3 hob4 hoc4 hot4 hd0 hd1 hd2 hd3 hdr3 hd4 hdr4 p2 p3 pr3 p4 pr4 hp3 hp4 s ra guard hpre fp s1 s2 t80 t64 t112 t96 l48 l120 l128 l176 rslot hfp hs1 hs2 ht80 ht64 ht112 ht96 hl48 hl120 hl128 hl176 hrslot R S hS scratch hsc hguard hcap hcap63 hmm st3 h3) ?_
  intro st4 h4
  refine eventually_trans _ _ _ _ (Encode.generated_field_4 k hk hf kC hkC hfC v0 v1 b2 ep3 rt3 ep4 rt4 ob3 oc3 ot3 ob4 oc4 ot4 pre d0 d1 d2 d3 dr3 d4 dr4 hv0 hv1 hb2 hep3 hrt3 hep4 hrt4 hob3 hoc3 hot3 hob4 hoc4 hot4 hd0 hd1 hd2 hd3 hdr3 hd4 hdr4 p2 p3 pr3 p4 pr4 hp3 hp4 s ra guard hpre fp s1 s2 t80 t64 t112 t96 l48 l120 l128 l176 rslot hfp hs1 hs2 ht80 ht64 ht112 ht96 hl48 hl120 hl128 hl176 hrslot R S hS scratch hsc hguard hcap hcap63 hmm st4 h4) ?_
  intro st5 h5
  exact Encode.generated_epilogue k hk hf kC hkC hfC v0 v1 b2 ep3 rt3 ep4 rt4 ob3 oc3 ot3 ob4 oc4 ot4 pre d0 d1 d2 d3 dr3 d4 dr4 hv0 hv1 hb2 hep3 hrt3 hep4 hrt4 hob3 hoc3 hot3 hob4 hoc4 hot4 hd0 hd1 hd2 hd3 hdr3 hd4 hdr4 p2 p3 pr3 p4 pr4 hp3 hp4 s ra guard hpre fp s1 s2 t80 t64 t112 t96 l48 l120 l128 l176 rslot hfp hs1 hs2 ht80 ht64 ht112 ht96 hl48 hl120 hl128 hl176 hrslot R S hS scratch hsc hguard hcap hcap63 st5 h5
theorem Encode.generated_fast_kind : ∀ (h : Host), type_of% (@Encode.generated_fast h)
    = @Codec.encodeFastPathNestedKindAnyFrame h marshalSSZTo Prysm.AttestationData.Encode.generated_layout [.flat .uint64, .flat .uint64, .flat (.bytes 32), .checkpoint, .checkpoint] := by
  intro h; rfl

end Prysm.AttestationData
