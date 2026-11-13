import Prysm.BeaconBlockHeader.EncodeFastPathKindInstances
import Codec.EncodeFrameTest
import Prysm.DepositMessage.EncoderCode

/-!
# Fast path (`encoder --fast-path`): encoder fast path of `(*v1alpha1.DepositMessage).MarshalSSZTo`

Generated from the `.S` file and the IR: a symbolic dataflow walk of the fast path, one application of a
step lemma per directive (windows with the nops erased), boundary states between the fields. Every theorem
has a `_kind` line (`encodeHeadKindAnyFrame`, `encodeFieldKindAnyFrame`, `encodeEpilogueKindAnyFrame`, `encodeFastPathKindAnyFrame`).
**Fast path only**: `len(dst) + 88 ≤ cap(dst)` and every byte-vector field of its exact length. No
`runtime.growslice` directive is stepped: each capacity test is decided from the premise. Not covered: the
growslice branches, the length rejects, the morestack path. Not a complete encoder result.
FAST-PATH-JSON: {"type": "DepositMessage", "const": "marshalSSZTo", "prefix": "Encode.generated", "size": 88, "frame": 128, "guard_addend": 8, "runtime_calls": true, "fields": [["PublicKey", "b", 48], ["WithdrawalCredentials", "b", 32], ["Amount", "u", 8]], "boundaries": [9, 37, 65, 83], "layout": "Prysm.DepositMessage.Encode.generated_layout", "assembly_sha256": "e35191e9ca09807491be85e751725c784993c64668f2fee19ca337fe5b1e055c", "ir_sha256": "c1586d32018abd182c16d50f6a7a76e38814cab08cf4a7a42105fe30342a5d2a", "statement_check": "kind instance only", "assembly": "prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.MarshalSSZTo.S", "ir": "prysm/ir/ir-mainnet.json", "ir_type": "v1alpha1.DepositMessage", "kinds": [{"theorem": "Encode.generated_head", "kind": "encodeHeadKindAnyFrame"}, {"theorem": "Encode.generated_field_0", "kind": "encodeFieldKindAnyFrame"}, {"theorem": "Encode.generated_field_1", "kind": "encodeFieldKindAnyFrame"}, {"theorem": "Encode.generated_field_2", "kind": "encodeFieldKindAnyFrame"}, {"theorem": "Encode.generated_epilogue", "kind": "encodeEpilogueKindAnyFrame"}, {"theorem": "Encode.generated_fast", "kind": "encodeFastPathKindAnyFrame"}]}
-/

open Machine Runtime Codec Prysm.DepositMessage.Code
variable [Host]

namespace Prysm.DepositMessage

/-- The frame facts of `marshalSSZTo` (read from the `.S` file by the walk): frame `0x80`, stack chunks
`fp s1 s2 l16 l40 l48 l32 l64 l56 rslot`. -/
def Encode.generated_layout : EncoderFrameLayout where
  stateWord := false
  frame := 128
  guardAddend := 8
  callsMemmove := true
  stackChunkCount := 10
  stackChunkLengths := [(0, 8), (1, 8), (2, 8), (3, 8), (4, 8), (5, 8), (6, 8), (7, 8), (8, 8), (9, 8)]
  pre := [.at (.below 8) (.original 0), .at (.above 8) (.original 1), .at (.above 16) (.original 2), .at (.below 16) (.original 3), .at (.below 40) (.original 4), .at (.below 48) (.original 5), .at (.below 32) (.original 6), .at (.below 64) (.original 7), .at (.below 56) (.original 8), .at (.below 144) (.original 9), .low .scratch]
  existentials := [.low]
  post := [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 16) (.reg .rbx), .at (.below 40) (.len 48), .at (.below 48) (.reg .rdi), .at (.below 32) (.reg .rbx), .at (.below 64) (.len 80), .at (.below 56) (.reg .rdi), .at (.below 144) (.ret 65), .low (.existential 0)]


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Head: directives 0–8 (stack guard, frame, spills); entry → boundary state 0. -/
theorem Encode.generated_head : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (v2 c0 c1 b0 b1 pre d0 d1 d2 : List UInt8) (hv2 : v2.length = 8) (hc0 : c0.length = 8) (hc1 : c1.length = 8) (hb0 : b0.length = 48) (hb1 : b1.length = 32) (hd0 : d0.length = 48) (hd1 : d1.length = 32) (hd2 : d2.length = 8)
    (p0 p1 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l40 l48 l32 l64 l56 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8) (hl40 : l40.length = 8) (hl48 : l48.length = 8) (hl32 : l32.length = 8) (hl64 : l64.length = 8) (hl56 : l56.length = 8) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (l64.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (l56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 144))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 p0.toInt).At s.regs.rax.toBitVec)
      ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (c0.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (c1.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (v2.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq (b0.At p0)
      ⋆ Eq (b1.At p1)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
      ⋆ R)
    (hguard : guard.toNat + 8 < s.regs.rsp.toNat) (hsp : 144 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 88 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 9)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 136 }
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
          ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (l64.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (l56.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf v2 c0 c1 b0 b1 pre d0 d1 d2 hv2 hc0 hc1 hb0 hb1 hd0 hd1 hd2 p0 p1 s ra guard hpre fp s1 s2 l16 l40 l48 l32 l64 l56 rslot hfp hs1 hs2 hl16 hl40 hl48 hl32 hl64 hl56 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hcap hcap63 hpre ⊢
  have hcap' : rcx.toBitVec.toNat + 88 ≤ rdi.toBitVec.toNat := hcap
  apply encoder_prologue_large_frame _ _ _ (-8) 8 _ k (k + 7) (window_infix_at hk 0 7) (by rfl) (by rfl) (by rfl) guard fp hfp _ _ _ (by dsimp only; ecancel) hguard
  intro m1 H1 fl1; normalize_registers; dsimp only at H1
  apply step_add_immediate Reg64.rsp (-128) _ (k + 7) (k + 8) (window_infix_at hk 7 1) (by rfl) (by rfl)
  intro fl; normalize_registers
  apply register_value_rewrite Reg64.rsp (rsp.toBitVec - 136) _ _ _ (by show ((rsp.toBitVec - 8) + (-128) : BitVec 64) = (rsp.toBitVec - 136); bv_omega)
  normalize_registers
  apply step_store Reg64.rbx Reg64.rsp 152 _ (k + 8) (k + 9) (window_infix_at hk 8 1) (by rfl) (by rfl)
    (rsp.toBitVec - 136) (rsp.toBitVec + 16) (by encoder_address_equation) s2 hs2 _ _ _ (by rfl) (by ecancel)
  intro m2 H2; normalize_registers; simp only [Reg64s.get64] at H2
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem Encode.generated_head_kind : ∀ (h : Host), type_of% (@Encode.generated_head h)
    = @Codec.encodeHeadKindAnyFrame h marshalSSZTo Prysm.DepositMessage.Encode.generated_layout [.bytes 48, .bytes 32, .uint64]
    ⟨9, 0, [(.rax, .receiver), (.rbx, .ptr), (.rcx, .len 0), (.rdi, .cap)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.original 1), .at (.above 16) (.reg .rbx), .at (.below 16) (.original 3), .at (.below 40) (.original 4), .at (.below 48) (.original 5), .at (.below 32) (.original 6), .at (.below 64) (.original 7), .at (.below 56) (.original 8), .at (.below 144) (.original 9), .low .scratch],
      []⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 0 `PublicKey` (48 bytes): directives 9–36; boundary state 0 → 1. -/
theorem Encode.generated_field_0 : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (v2 c0 c1 b0 b1 pre d0 d1 d2 : List UInt8) (hv2 : v2.length = 8) (hc0 : c0.length = 8) (hc1 : c1.length = 8) (hb0 : b0.length = 48) (hb1 : b1.length = 32) (hd0 : d0.length = 48) (hd1 : d1.length = 32) (hd2 : d2.length = 8)
    (p0 p1 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l40 l48 l32 l64 l56 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8) (hl40 : l40.length = 8) (hl48 : l48.length = 8) (hl32 : l32.length = 8) (hl64 : l64.length = 8) (hl56 : l56.length = 8) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 144 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 88 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 9)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 136 }
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
          ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (l64.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (l56.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 37)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 136 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 : List UInt8), x0.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (l64.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (l56.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 37)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf v2 c0 c1 b0 b1 pre d0 d1 d2 hv2 hc0 hc1 hb0 hb1 hd0 hd1 hd2 p0 p1 s ra guard hpre fp s1 s2 l16 l40 l48 l32 l64 l56 rslot hfp hs1 hs2 hl16 hl40 hl48 hl32 hl64 hl56 hrslot R S scratch hsc hsp hcap hcap63 hmm
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
  have hcap' : rcx.toBitVec.toNat + 88 ≤ rdi.toBitVec.toNat := hcap
  apply step_load_value Reg64.rdx Reg64.rax 0 _ (k + 9) (k + 10) (window_infix_at hk 9 1) (by rfl) (by rfl)
    rax.toBitVec rax.toBitVec p0 (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_length_check Reg64.rax 8 48 _ _ (k + 10) (k + 12) (window_infix_at hk 10 2) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 8) (by encoder_address_equation) (Int.toBytes 8 48) (by rfl) (by decide) _ _ _ (by rfl) (by ecancel)
  intro fl; normalize_registers
  apply step_store Reg64.rax Reg64.rsp 144 _ (k + 12) (k + 13) (window_infix_at hk 12 1) (by rfl) (by rfl)
    (rsp.toBitVec - 136) (rsp.toBitVec + 8) (by encoder_address_equation) s1 hs1 _ _ _ (by rfl) (by ecancel)
  intro m3 H3; normalize_registers; simp only [Reg64s.get64] at H3
  apply step_lea Reg64.r8 Reg64.rcx 48 _ (k + 13) (k + 14) (window_infix_at hk 13 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.r8 (rcx.toBitVec + 48) _ _ _ (by show (rcx.toBitVec + 48 : BitVec 64) = (rcx.toBitVec + 48); bv_omega)
  normalize_registers
  have hl29 := Machine.label_at' hk hf (j := 29)
    (by simp only [marshalSSZTo, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply step_cmp_jae_taken Reg64.rdi Reg64.r8 _ _ (k + 14) (k + 29) (window_infix_at hk 14 2) (by rfl) hl29 _ _ (by show ((rcx.toBitVec + 48) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; normalize_registers
  apply step_label _ _ (k + 29) (k + 30) (window_infix_at hk 29 1) (by rfl) (by rfl)
  apply step_store Reg64.rbx Reg64.rsp 120 _ (k + 30) (k + 31) (window_infix_at hk 30 1) (by rfl) (by rfl)
    (rsp.toBitVec - 136) (rsp.toBitVec - 16) (by encoder_address_equation) l16 hl16 _ _ _ (by rfl) (by ecancel)
  intro m4 H4; normalize_registers; simp only [Reg64s.get64] at H4
  apply step_store Reg64.r8 Reg64.rsp 96 _ (k + 31) (k + 32) (window_infix_at hk 31 1) (by rfl) (by rfl)
    (rsp.toBitVec - 136) (rsp.toBitVec - 40) (by encoder_address_equation) l40 hl40 _ _ _ (by rfl) (by ecancel)
  intro m5 H5; normalize_registers; simp only [Reg64s.get64] at H5
  apply step_store Reg64.rdi Reg64.rsp 88 _ (k + 32) (k + 33) (window_infix_at hk 32 1) (by rfl) (by rfl)
    (rsp.toBitVec - 136) (rsp.toBitVec - 48) (by encoder_address_equation) l48 hl48 _ _ _ (by rfl) (by ecancel)
  intro m6 H6; normalize_registers; simp only [Reg64s.get64] at H6
  apply step_lea_indexed Reg64.rax Reg64.rcx Reg64.rbx _ (k + 33) (k + 34) (window_infix_at hk 33 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.rax (rbx.toBitVec + rcx.toBitVec) _ _ _ (by show (rcx.toBitVec + rbx.toBitVec : BitVec 64) = (rbx.toBitVec + rcx.toBitVec); bv_omega)
  normalize_registers
  apply step_move_register Reg64.rbx Reg64.rdx _ (k + 34) (k + 35) (window_infix_at hk 34 1) (by rfl) (by rfl)
  normalize_registers
  apply step_move_immediate Reg64.rcx 48 _ (k + 35) (k + 36) (window_infix_at hk 35 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.rcx 48 _ _ _ (by show (BitVec.zeroExtend 64 (BitVec.truncate 32 (48 : BitVec 64)) : BitVec 64) = 48; decide)
  normalize_registers
  refine eventually_trans _ _ _ _ (encode_memmove_call (k + 36) (window_infix_at hk 36 1) (rsp.toBitVec - 136) (rbx.toBitVec + rcx.toBitVec) p0
    (rsp.toBitVec - 144) (rsp.toBitVec - 144 - BitVec.ofNat 64 S) S (by bv_omega) (Codec.frame_low_address_without_calls rsp.toBitVec 136 144 S (by decide))
    b0 d0 rslot scratch (by rw [hd0, hb0]) hrslot hsc
    _ _ (by rfl) (by rfl) (by rfl) (by rw [hb0]; rfl) (by first | ecancel | (dsimp only; ecancel)) hmm) ?_
  rintro ⟨e1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, scr1, hscr1, Hc1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 Hc1
  subst hpc1
  obtain ⟨⟨raxc1, rbxc1, rcxc1, rdxc1, rsic1, rdic1, rspc1, rbpc1, r8c1, r9c1, r10c1, r11c1, r12c1, r13c1, r14c1, r15c1⟩, zmmsc1, flagsc1, memc1⟩ := e1
  simp only at hrsp1 hrbp1 hr141 Hc1
  subst rspc1 rbpc1 r14c1
  rw [show k + 36 + 1 = k + 37 from rfl] at Hc1
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, scr1, hscr1, ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem Encode.generated_field_0_kind : ∀ (h : Host), type_of% (@Encode.generated_field_0 h)
    = @Codec.encodeFieldKindAnyFrame h marshalSSZTo Prysm.DepositMessage.Encode.generated_layout [.bytes 48, .bytes 32, .uint64]
    ⟨9, 0, [(.rax, .receiver), (.rbx, .ptr), (.rcx, .len 0), (.rdi, .cap)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.original 1), .at (.above 16) (.reg .rbx), .at (.below 16) (.original 3), .at (.below 40) (.original 4), .at (.below 48) (.original 5), .at (.below 32) (.original 6), .at (.below 64) (.original 7), .at (.below 56) (.original 8), .at (.below 144) (.original 9), .low .scratch],
      []⟩
    ⟨37, 1, [],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 16) (.reg .rbx), .at (.below 40) (.len 48), .at (.below 48) (.reg .rdi), .at (.below 32) (.original 6), .at (.below 64) (.original 7), .at (.below 56) (.original 8), .at (.below 144) (.ret 37), .low (.existential 0)],
      [.low]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 1 `WithdrawalCredentials` (32 bytes): directives 37–64; boundary state 1 → 2. -/
theorem Encode.generated_field_1 : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (v2 c0 c1 b0 b1 pre d0 d1 d2 : List UInt8) (hv2 : v2.length = 8) (hc0 : c0.length = 8) (hc1 : c1.length = 8) (hb0 : b0.length = 48) (hb1 : b1.length = 32) (hd0 : d0.length = 48) (hd1 : d1.length = 32) (hd2 : d2.length = 8)
    (p0 p1 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l40 l48 l32 l64 l56 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8) (hl40 : l40.length = 8) (hl48 : l48.length = 8) (hl32 : l32.length = 8) (hl64 : l64.length = 8) (hl56 : l56.length = 8) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 144 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 88 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 37)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 136 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 : List UInt8), x0.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (l64.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (l56.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 37)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 65)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 136 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 : List UInt8), x0.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 80).toInt).At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 65)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf v2 c0 c1 b0 b1 pre d0 d1 d2 hv2 hc0 hc1 hb0 hb1 hd0 hd1 hd2 p0 p1 s ra guard hpre fp s1 s2 l16 l40 l48 l32 l64 l56 rslot hfp hs1 hs2 hl16 hl40 hl48 hl32 hl64 hl56 hrslot R S scratch hsc hsp hcap hcap63 hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hsp hcap hcap63 hpre ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, x0, hx0, Hm⟩
  dsimp only at hpc hrsp hrbp hr14  Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14  Hm
  subst rsp1 rbp1 r141
  have hcap' : rcx.toBitVec.toNat + 88 ≤ rdi.toBitVec.toNat := hcap
  apply step_load_value Reg64.rdx Reg64.rsp 144 _ (k + 37) (k + 38) (window_infix_at hk 37 1) (by rfl) (by rfl)
    (rsp.toBitVec - 136) (rsp.toBitVec + 8) rax.toBitVec (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_load_value Reg64.rbx Reg64.rdx 24 _ (k + 38) (k + 39) (window_infix_at hk 38 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 24) p1 (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_length_check Reg64.rdx 32 32 _ _ (k + 39) (k + 41) (window_infix_at hk 39 2) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 32) (by encoder_address_equation) (Int.toBytes 8 32) (by rfl) (by decide) _ _ _ (by rfl) (by ecancel)
  intro fl; normalize_registers
  apply step_load_value Reg64.r8 Reg64.rsp 96 _ (k + 41) (k + 42) (window_infix_at hk 41 1) (by rfl) (by rfl)
    (rsp.toBitVec - 136) (rsp.toBitVec - 40) (rcx.toBitVec + 48) (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_lea Reg64.r9 Reg64.r8 32 _ (k + 42) (k + 43) (window_infix_at hk 42 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.r9 (rcx.toBitVec + 80) _ _ _ (by show ((rcx.toBitVec + 48) + 32 : BitVec 64) = (rcx.toBitVec + 80); bv_omega)
  normalize_registers
  apply step_load_value Reg64.rcx Reg64.rsp 88 _ (k + 43) (k + 44) (window_infix_at hk 43 1) (by rfl) (by rfl)
    (rsp.toBitVec - 136) (rsp.toBitVec - 48) rdi.toBitVec (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_cmp_jb_not_taken Reg64.rcx Reg64.r9 _ _ (k + 44) (k + 46) (window_infix_at hk 44 2) (by rfl) (by rfl) _ _ (by show ((rcx.toBitVec + 80) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; normalize_registers
  apply step_load_value Reg64.rax Reg64.rsp 120 _ (k + 46) (k + 47) (window_infix_at hk 46 1) (by rfl) (by rfl)
    (rsp.toBitVec - 136) (rsp.toBitVec - 16) rbx.toBitVec (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  have hl58 := Machine.label_at' hk hf (j := 58)
    (by simp only [marshalSSZTo, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply step_jump _ _ (k + 47) (k + 58) (window_infix_at hk 47 1) (by rfl) hl58
  apply step_label _ _ (k + 58) (k + 59) (window_infix_at hk 58 1) (by rfl) (by rfl)
  apply step_store Reg64.rax Reg64.rsp 104 _ (k + 59) (k + 60) (window_infix_at hk 59 1) (by rfl) (by rfl)
    (rsp.toBitVec - 136) (rsp.toBitVec - 32) (by encoder_address_equation) l32 hl32 _ _ _ (by rfl) (by ecancel)
  intro m7 H7; normalize_registers; simp only [Reg64s.get64] at H7
  apply step_store Reg64.r9 Reg64.rsp 72 _ (k + 60) (k + 61) (window_infix_at hk 60 1) (by rfl) (by rfl)
    (rsp.toBitVec - 136) (rsp.toBitVec - 64) (by encoder_address_equation) l64 hl64 _ _ _ (by rfl) (by ecancel)
  intro m8 H8; normalize_registers; simp only [Reg64s.get64] at H8
  apply step_store Reg64.rcx Reg64.rsp 80 _ (k + 61) (k + 62) (window_infix_at hk 61 1) (by rfl) (by rfl)
    (rsp.toBitVec - 136) (rsp.toBitVec - 56) (by encoder_address_equation) l56 hl56 _ _ _ (by rfl) (by ecancel)
  intro m9 H9; normalize_registers; simp only [Reg64s.get64] at H9
  apply step_add_registers Reg64.rax Reg64.r8 _ (k + 62) (k + 63) (window_infix_at hk 62 1) (by rfl) (by rfl)
  intro fl; normalize_registers
  apply register_value_rewrite Reg64.rax (rbx.toBitVec + rcx.toBitVec + 48) _ _ _ (by show (rbx.toBitVec + (rcx.toBitVec + 48) : BitVec 64) = (rbx.toBitVec + rcx.toBitVec + 48); bv_omega)
  normalize_registers
  apply step_move_immediate Reg64.rcx 32 _ (k + 63) (k + 64) (window_infix_at hk 63 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.rcx 32 _ _ _ (by show (BitVec.zeroExtend 64 (BitVec.truncate 32 (32 : BitVec 64)) : BitVec 64) = 32; decide)
  normalize_registers
  refine eventually_trans _ _ _ _ (encode_memmove_call (k + 64) (window_infix_at hk 64 1) (rsp.toBitVec - 136) (rbx.toBitVec + rcx.toBitVec + 48) p1
    (rsp.toBitVec - 144) (rsp.toBitVec - 144 - BitVec.ofNat 64 S) S (by bv_omega) (Codec.frame_low_address_without_calls rsp.toBitVec 136 144 S (by decide))
    b1 d1 (Int.toBytes 8 (Host.addrOf (k + 37)).toBitVec.toInt) x0 (by rw [hd1, hb1]) (Int.toBytes_length 8 _) hx0
    _ _ (by rfl) (by rfl) (by rfl) (by rw [hb1]; rfl) (by first | ecancel | (dsimp only; ecancel)) hmm) ?_
  rintro ⟨e2, pc2⟩ ⟨hpc2, hrsp2, hrbp2, hr142, scr2, hscr2, Hc2⟩
  dsimp only at hpc2 hrsp2 hrbp2 hr142 Hc2
  subst hpc2
  obtain ⟨⟨raxc2, rbxc2, rcxc2, rdxc2, rsic2, rdic2, rspc2, rbpc2, r8c2, r9c2, r10c2, r11c2, r12c2, r13c2, r14c2, r15c2⟩, zmmsc2, flagsc2, memc2⟩ := e2
  simp only at hrsp2 hrbp2 hr142 Hc2
  subst rspc2 rbpc2 r14c2
  rw [show k + 64 + 1 = k + 65 from rfl] at Hc2
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, scr2, hscr2, ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem Encode.generated_field_1_kind : ∀ (h : Host), type_of% (@Encode.generated_field_1 h)
    = @Codec.encodeFieldKindAnyFrame h marshalSSZTo Prysm.DepositMessage.Encode.generated_layout [.bytes 48, .bytes 32, .uint64]
    ⟨37, 1, [],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 16) (.reg .rbx), .at (.below 40) (.len 48), .at (.below 48) (.reg .rdi), .at (.below 32) (.original 6), .at (.below 64) (.original 7), .at (.below 56) (.original 8), .at (.below 144) (.ret 37), .low (.existential 0)],
      [.low]⟩
    ⟨65, 2, [],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 16) (.reg .rbx), .at (.below 40) (.len 48), .at (.below 48) (.reg .rdi), .at (.below 32) (.reg .rbx), .at (.below 64) (.len 80), .at (.below 56) (.reg .rdi), .at (.below 144) (.ret 65), .low (.existential 0)],
      [.low]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 2 `Amount` (uint64): directives 65–82; boundary state 2 → 3. -/
theorem Encode.generated_field_2 : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (v2 c0 c1 b0 b1 pre d0 d1 d2 : List UInt8) (hv2 : v2.length = 8) (hc0 : c0.length = 8) (hc1 : c1.length = 8) (hb0 : b0.length = 48) (hb1 : b1.length = 32) (hd0 : d0.length = 48) (hd1 : d1.length = 32) (hd2 : d2.length = 8)
    (p0 p1 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l40 l48 l32 l64 l56 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8) (hl40 : l40.length = 8) (hl48 : l48.length = 8) (hl32 : l32.length = 8) (hl64 : l64.length = 8) (hl56 : l56.length = 8) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 144 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 88 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 65)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 136 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 : List UInt8), x0.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 80).toInt).At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 65)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 83)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 136 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.get64 Reg64.rax = s.regs.rbx.toBitVec
        ∧ st.data.regs.get64 Reg64.rbx = s.regs.rcx.toBitVec + 88
        ∧ st.data.regs.get64 Reg64.rcx = s.regs.rdi.toBitVec ∧
        ∃ (x0 : List UInt8), x0.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 80).toInt).At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 65)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf v2 c0 c1 b0 b1 pre d0 d1 d2 hv2 hc0 hc1 hb0 hb1 hd0 hd1 hd2 p0 p1 s ra guard hpre fp s1 s2 l16 l40 l48 l32 l64 l56 rslot hfp hs1 hs2 hl16 hl40 hl48 hl32 hl64 hl56 hrslot R S scratch hsc hsp hcap hcap63 hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hsp hcap hcap63 hpre ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, x0, hx0, Hm⟩
  dsimp only at hpc hrsp hrbp hr14  Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14  Hm
  subst rsp1 rbp1 r141
  have hcap' : rcx.toBitVec.toNat + 88 ≤ rdi.toBitVec.toNat := hcap
  apply step_load_value Reg64.rbx Reg64.rsp 72 _ (k + 65) (k + 66) (window_infix_at hk 65 1) (by rfl) (by rfl)
    (rsp.toBitVec - 136) (rsp.toBitVec - 64) (rcx.toBitVec + 80) (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_add_immediate Reg64.rbx 8 _ (k + 66) (k + 67) (window_infix_at hk 66 1) (by rfl) (by rfl)
  intro fl; normalize_registers
  apply register_value_rewrite Reg64.rbx (rcx.toBitVec + 88) _ _ _ (by show ((rcx.toBitVec + 80) + 8 : BitVec 64) = (rcx.toBitVec + 88); bv_omega)
  normalize_registers
  apply step_load_value Reg64.rdx Reg64.rsp 144 _ (k + 67) (k + 68) (window_infix_at hk 67 1) (by rfl) (by rfl)
    (rsp.toBitVec - 136) (rsp.toBitVec + 8) rax.toBitVec (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_load_bytes Reg64.rdx Reg64.rdx 48 _ (k + 68) (k + 69) (window_infix_at hk 68 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 48) (by encoder_address_equation) v2 hv2 _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_load_value Reg64.rcx Reg64.rsp 80 _ (k + 69) (k + 70) (window_infix_at hk 69 1) (by rfl) (by rfl)
    (rsp.toBitVec - 136) (rsp.toBitVec - 56) rdi.toBitVec (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_cmp_jb_not_taken Reg64.rcx Reg64.rbx _ _ (k + 70) (k + 72) (window_infix_at hk 70 2) (by rfl) (by rfl) _ _ (by show ((rcx.toBitVec + 88) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; normalize_registers
  apply step_load_value Reg64.rax Reg64.rsp 104 _ (k + 72) (k + 73) (window_infix_at hk 72 1) (by rfl) (by rfl)
    (rsp.toBitVec - 136) (rsp.toBitVec - 32) rbx.toBitVec (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  have hl81 := Machine.label_at' hk hf (j := 81)
    (by simp only [marshalSSZTo, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply step_jump _ _ (k + 73) (k + 81) (window_infix_at hk 73 1) (by rfl) hl81
  apply step_label _ _ (k + 81) (k + 82) (window_infix_at hk 81 1) (by rfl) (by rfl)
  apply step_store_indexed Reg64.rdx Reg64.rbx Reg64.rax (-8) _ (k + 82) (k + 83) (window_infix_at hk 82 1) (by rfl) (by rfl)
    (rcx.toBitVec + 88) rbx.toBitVec (rbx.toBitVec + rcx.toBitVec + 80) (by encoder_address_equation) d2 hd2 _ _ _ (by rfl) (by rfl) (by ecancel)
  intro m10 H10; normalize_registers; simp only [Reg64s.get64] at H10
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v2 hv2] at H10
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, x0, hx0, ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem Encode.generated_field_2_kind : ∀ (h : Host), type_of% (@Encode.generated_field_2 h)
    = @Codec.encodeFieldKindAnyFrame h marshalSSZTo Prysm.DepositMessage.Encode.generated_layout [.bytes 48, .bytes 32, .uint64]
    ⟨65, 2, [],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 16) (.reg .rbx), .at (.below 40) (.len 48), .at (.below 48) (.reg .rdi), .at (.below 32) (.reg .rbx), .at (.below 64) (.len 80), .at (.below 56) (.reg .rdi), .at (.below 144) (.ret 65), .low (.existential 0)],
      [.low]⟩
    ⟨83, 3, [(.rax, .ptr), (.rbx, .len 88), (.rcx, .cap)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 16) (.reg .rbx), .at (.below 40) (.len 48), .at (.below 48) (.reg .rdi), .at (.below 32) (.reg .rbx), .at (.below 64) (.len 80), .at (.below 56) (.reg .rdi), .at (.below 144) (.ret 65), .low (.existential 0)],
      [.low]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Epilogue: directives 83–return; boundary state 3 → the fast-path post-state. -/
theorem Encode.generated_epilogue : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (v2 c0 c1 b0 b1 pre d0 d1 d2 : List UInt8) (hv2 : v2.length = 8) (hc0 : c0.length = 8) (hc1 : c1.length = 8) (hb0 : b0.length = 48) (hb1 : b1.length = 32) (hd0 : d0.length = 48) (hd1 : d1.length = 32) (hd2 : d2.length = 8)
    (p0 p1 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l40 l48 l32 l64 l56 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8) (hl40 : l40.length = 8) (hl48 : l48.length = 8) (hl32 : l32.length = 8) (hl64 : l64.length = 8) (hl56 : l56.length = 8) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 144 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 88 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 83)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 136 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14
        ∧ st0.data.regs.get64 Reg64.rax = s.regs.rbx.toBitVec
        ∧ st0.data.regs.get64 Reg64.rbx = s.regs.rcx.toBitVec + 88
        ∧ st0.data.regs.get64 Reg64.rcx = s.regs.rdi.toBitVec ∧
        ∃ (x0 : List UInt8), x0.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 80).toInt).At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 65)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec
        ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 88
        ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0
        ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8
        ∧ st.data.regs.rbp = s.regs.rbp
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 : List UInt8), x0.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 80).toInt).At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 65)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf v2 c0 c1 b0 b1 pre d0 d1 d2 hv2 hc0 hc1 hb0 hb1 hd0 hd1 hd2 p0 p1 s ra guard hpre fp s1 s2 l16 l40 l48 l32 l64 l56 rslot hfp hs1 hs2 hl16 hl40 hl48 hl32 hl64 hl56 hrslot R S scratch hsc hsp hcap hcap63
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hsp hcap hcap63 hpre ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, hrrax, hrrbx, hrrcx, x0, hx0, Hm⟩
  dsimp only at hpc hrsp hrbp hr14 hrrax hrrbx hrrcx Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14 hrrax hrrbx hrrcx Hm
  subst rsp1 rbp1 r141
  obtain rfl : rbx = rax1 := (UInt64.toBitVec_inj.mp hrrax).symm
  obtain rfl : rbx1 = { toBitVec := rcx.toBitVec + 88 } := UInt64.toBitVec_inj.mp hrrbx
  obtain rfl : rdi = rcx1 := (UInt64.toBitVec_inj.mp hrrcx).symm
  have hcap' : rcx.toBitVec.toNat + 88 ≤ rdi.toBitVec.toNat := hcap
  apply step_xor32 Reg64.rdi _ (k + 83) (k + 84) (window_infix_at hk 83 1) (by rfl) (by rfl)
  intro fl; normalize_registers
  apply step_xor32 Reg64.rsi _ (k + 84) (k + 85) (window_infix_at hk 84 1) (by rfl) (by rfl)
  intro fl; normalize_registers
  apply step_sub_immediate Reg64.rsp (-128) _ (k + 85) (k + 86) (window_infix_at hk 85 1) (by rfl) (by rfl)
  intro fl; normalize_registers
  apply register_value_rewrite Reg64.rsp (rsp.toBitVec - 8) _ _ _ (by show ((rsp.toBitVec - 136) - (-128) : BitVec 64) = (rsp.toBitVec - 8); bv_omega)
  normalize_registers
  refine eventually_trans _ _ _ _ (decode_return_segment _ (k + 86) (window_infix_at hk 86 2) (by rfl) (rsp.toBitVec - 8) rsp.toBitVec (by bv_omega) rbp ra _ _ (by rfl) (by ecancel)) ?_
  rintro ⟨d', pc'⟩ ⟨hpc', hrsp', hrbp', hreg', hmem'⟩
  dsimp only at hpc' hrsp' hrbp' hreg' hmem'
  apply Eventually.done
  refine ⟨hpc', ?_, ?_, ?_, ?_, ?_, ?_, hrbp', ?_, x0, hx0, ?_⟩
  · exact UInt64.toBitVec_inj.mp (hreg' Reg64.rax (by decide) (by decide))
  · show d'.regs.rbx.toBitVec.toNat = rcx.toBitVec.toNat + 88
    rw [show d'.regs.rbx.toBitVec = rcx.toBitVec + 88 from hreg' Reg64.rbx (by decide) (by decide)]
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
    = @Codec.encodeEpilogueKindAnyFrame h marshalSSZTo Prysm.DepositMessage.Encode.generated_layout [.bytes 48, .bytes 32, .uint64]
    ⟨83, 3, [(.rax, .ptr), (.rbx, .len 88), (.rcx, .cap)],
      [.at (.below 8) (.reg .rbp), .at (.above 8) (.reg .rax), .at (.above 16) (.reg .rbx), .at (.below 16) (.reg .rbx), .at (.below 40) (.len 48), .at (.below 48) (.reg .rdi), .at (.below 32) (.reg .rbx), .at (.below 64) (.len 80), .at (.below 56) (.reg .rdi), .at (.below 144) (.ret 65), .low (.existential 0)],
      [.low]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Encoder fast path of `(*v1alpha1.DepositMessage).MarshalSSZTo` (Go 1.26.10), generated** (`encoder --fast-path`):
head, one theorem per field, epilogue, chained by `eventually_trans`. Premises: `len + 88 ≤ cap`,
every byte-vector field of its exact length. Statement = the kind instance (`_kind`). Fast path only. -/
theorem Encode.generated_fast : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (v2 c0 c1 b0 b1 pre d0 d1 d2 : List UInt8) (hv2 : v2.length = 8) (hc0 : c0.length = 8) (hc1 : c1.length = 8) (hb0 : b0.length = 48) (hb1 : b1.length = 32) (hd0 : d0.length = 48) (hd1 : d1.length = 32) (hd2 : d2.length = 8)
    (p0 p1 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l40 l48 l32 l64 l56 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8) (hl40 : l40.length = 8) (hl48 : l48.length = 8) (hl32 : l32.length = 8) (hl64 : l64.length = 8) (hl56 : l56.length = 8) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (l64.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (l56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 144))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 p0.toInt).At s.regs.rax.toBitVec)
      ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (c0.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (c1.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (v2.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq (b0.At p0)
      ⋆ Eq (b1.At p1)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
      ⋆ R)
    (hguard : guard.toNat + 8 < s.regs.rsp.toNat) (hsp : 144 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 88 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec
        ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 88
        ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0
        ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8
        ∧ st.data.regs.rbp = s.regs.rbp
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 : List UInt8), x0.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 80).toInt).At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 65)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf v2 c0 c1 b0 b1 pre d0 d1 d2 hv2 hc0 hc1 hb0 hb1 hd0 hd1 hd2 p0 p1 s ra guard hpre fp s1 s2 l16 l40 l48 l32 l64 l56 rslot hfp hs1 hs2 hl16 hl40 hl48 hl32 hl64 hl56 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm
  refine eventually_trans _ _ _ _ (Encode.generated_head k hk hf v2 c0 c1 b0 b1 pre d0 d1 d2 hv2 hc0 hc1 hb0 hb1 hd0 hd1 hd2 p0 p1 s ra guard hpre fp s1 s2 l16 l40 l48 l32 l64 l56 rslot hfp hs1 hs2 hl16 hl40 hl48 hl32 hl64 hl56 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm) ?_
  intro st0 h0
  refine eventually_trans _ _ _ _ (Encode.generated_field_0 k hk hf v2 c0 c1 b0 b1 pre d0 d1 d2 hv2 hc0 hc1 hb0 hb1 hd0 hd1 hd2 p0 p1 s ra guard hpre fp s1 s2 l16 l40 l48 l32 l64 l56 rslot hfp hs1 hs2 hl16 hl40 hl48 hl32 hl64 hl56 hrslot R S scratch hsc hsp hcap hcap63 hmm st0 h0) ?_
  intro st1 h1
  refine eventually_trans _ _ _ _ (Encode.generated_field_1 k hk hf v2 c0 c1 b0 b1 pre d0 d1 d2 hv2 hc0 hc1 hb0 hb1 hd0 hd1 hd2 p0 p1 s ra guard hpre fp s1 s2 l16 l40 l48 l32 l64 l56 rslot hfp hs1 hs2 hl16 hl40 hl48 hl32 hl64 hl56 hrslot R S scratch hsc hsp hcap hcap63 hmm st1 h1) ?_
  intro st2 h2
  refine eventually_trans _ _ _ _ (Encode.generated_field_2 k hk hf v2 c0 c1 b0 b1 pre d0 d1 d2 hv2 hc0 hc1 hb0 hb1 hd0 hd1 hd2 p0 p1 s ra guard hpre fp s1 s2 l16 l40 l48 l32 l64 l56 rslot hfp hs1 hs2 hl16 hl40 hl48 hl32 hl64 hl56 hrslot R S scratch hsc hsp hcap hcap63 hmm st2 h2) ?_
  intro st3 h3
  exact Encode.generated_epilogue k hk hf v2 c0 c1 b0 b1 pre d0 d1 d2 hv2 hc0 hc1 hb0 hb1 hd0 hd1 hd2 p0 p1 s ra guard hpre fp s1 s2 l16 l40 l48 l32 l64 l56 rslot hfp hs1 hs2 hl16 hl40 hl48 hl32 hl64 hl56 hrslot R S scratch hsc hsp hcap hcap63 st3 h3
theorem Encode.generated_fast_kind : ∀ (h : Host), type_of% (@Encode.generated_fast h)
    = @Codec.encodeFastPathKindAnyFrame h marshalSSZTo Prysm.DepositMessage.Encode.generated_layout [.bytes 48, .bytes 32, .uint64] := by
  intro h; rfl

end Prysm.DepositMessage
