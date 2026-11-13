import Prysm.BeaconBlockHeader.EncodeFastPathKindInstances
import Codec.EncodeFrameTest
import Prysm.Checkpoint.Code

/-!
# Fast path (`encoder --fast-path`): encoder fast path of `(*v1alpha1.Checkpoint).MarshalSSZTo`

Generated from the `.S` file and the IR: a symbolic dataflow walk of the fast path, one application of a
step lemma per directive (windows with the nops erased), boundary states between the fields. Every theorem
has a `_kind` line (`encHeadKindAnyFrame`, `encFieldKindAnyFrame`, `encEpilogueKindAnyFrame`, `encFastPathKindAnyFrame`).
**Fast path only**: `len(dst) + 40 ≤ cap(dst)` and every byte-vector field of its exact length. No
`runtime.growslice` directive is stepped: each capacity test is decided from the premise. Not covered: the
growslice branches, the length rejects, the morestack path. Not a complete encoder result.
The statement implies the committed hand statement `Prysm.Checkpoint.Encode.fast_path` through `Prysm.Checkpoint.Encode.fast_path_of_kind`.
FAST-PATH-JSON: {"type": "Checkpoint", "const": "marshalSSZTo", "prefix": "Encode.generated", "size": 40, "frame": 104, "guard_addend": 0, "runtime_calls": true, "fields": [["Epoch", "u", 8], ["Root", "b", 32]], "boundaries": [8, 36, 63], "layout": "Prysm.Checkpoint.encodeLayout", "S_sha256": "c4345527c651c0a3ff8319af3f35df1e375b8c58a6a45054762da0a0dcef1b1d", "ir_sha256": "c1586d32018abd182c16d50f6a7a76e38814cab08cf4a7a42105fe30342a5d2a", "statement_check": "same Prysm.Checkpoint.Encode.fast_path via Prysm.Checkpoint.Encode.fast_path_of_kind", "S": "prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo.S", "ir": "prysm/ir/ir-mainnet.json", "ir_type": "v1alpha1.Checkpoint", "kinds": [{"theorem": "Encode.generated_head", "kind": "encHeadKindAnyFrame"}, {"theorem": "Encode.generated_f0", "kind": "encFieldKindAnyFrame"}, {"theorem": "Encode.generated_f1", "kind": "encFieldKindAnyFrame"}, {"theorem": "Encode.generated_epi", "kind": "encEpilogueKindAnyFrame"}, {"theorem": "Encode.generated_fast", "kind": "encFastPathKindAnyFrame"}]}
-/

open Machine Runtime Codec Prysm.Checkpoint.Code
variable [Host]

namespace Prysm.Checkpoint

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Head: directives 0–7 (stack guard, frame, spills); entry → boundary state 0. -/
theorem Encode.generated_head : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v0 c1 b1 pre d0 d1 : List UInt8) (hast : ast.length = 8) (hv0 : v0.length = 8) (hc1 : c1.length = 8) (hb1 : b1.length = 32) (hd0 : d0.length = 8) (hd1 : d1.length = 32)
    (p1 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s2 l16 l24 l32 t64 t48 rslot : List UInt8) (hfp : fp.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8) (hl24 : l24.length = 8) (hl32 : l32.length = 8) (ht64 : t64.length = 16) (ht48 : t48.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (t48.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (t64.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 120))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (c1.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (b1.At p1)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
      ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 120 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 40 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 8)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 112 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.get64 Reg64.rax = s.regs.rax.toBitVec
        ∧ st.data.regs.get64 Reg64.rbx = s.regs.rbx.toBitVec
        ∧ st.data.regs.get64 Reg64.rcx = s.regs.rcx.toBitVec
        ∧ st.data.regs.get64 Reg64.rdi = s.regs.rdi.toBitVec ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (t48.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (t64.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (b1.At p1)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf ast v0 c1 b1 pre d0 d1 hast hv0 hc1 hb1 hd0 hd1 p1 s ra guard hpre fp s2 l16 l24 l32 t64 t48 rslot hfp hs2 hl16 hl24 hl32 ht64 ht48 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hcap hcap63 hpre ⊢
  have hcap' : rcx.toBitVec.toNat + 40 ≤ rdi.toBitVec.toNat := hcap
  apply encoder_prologue_small_frame _ _ _ _ k (k + 6) (window_infix_at hk 0 6) (by rfl) (by rfl) guard fp hfp _ _ _ (by dsimp only; ecancel) hguard
  intro m1 H1 fl1; normalize_registers; dsimp only at H1
  apply step_sub_immediate Reg64.rsp 104 _ (k + 6) (k + 7) (window_infix_at hk 6 1) (by rfl) (by rfl)
  intro fl; normalize_registers
  apply register_value_rewrite Reg64.rsp (rsp.toBitVec - 112) _ _ _ (by show ((rsp.toBitVec - 8) - 104 : BitVec 64) = (rsp.toBitVec - 112); bv_omega)
  normalize_registers
  apply step_store Reg64.rbx Reg64.rsp 128 _ (k + 7) (k + 8) (window_infix_at hk 7 1) (by rfl) (by rfl)
    (rsp.toBitVec - 112) (rsp.toBitVec + 16) (by encoder_address_equation) s2 hs2 _ _ _ (by rfl) (by ecancel)
  intro m2 H2; normalize_registers; simp only [Reg64s.get64] at H2
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem Encode.generated_head_kind : ∀ (h : Host), type_of% (@Encode.generated_head h)
    = @Codec.encHeadKindAnyFrame h marshalSSZTo Prysm.Checkpoint.encodeLayout [.u64, .bytes 32]
    ⟨8, 0, [(.rax, .receiver), (.rbx, .ptr), (.rcx, .len 0), (.rdi, .cap)],
      [.at (.below 8) (.reg .rbp), .at (.above 16) (.reg .rbx), .at (.below 16) (.original 2), .at (.below 24) (.original 3), .at (.below 32) (.original 4), .at (.below 48) (.original 6), .at (.below 64) (.original 5), .at (.below 120) (.original 7), .low .scratch],
      []⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 0 `Epoch` (uint64): directives 8–35; boundary state 0 → 1. -/
theorem Encode.generated_f0 : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v0 c1 b1 pre d0 d1 : List UInt8) (hast : ast.length = 8) (hv0 : v0.length = 8) (hc1 : c1.length = 8) (hb1 : b1.length = 32) (hd0 : d0.length = 8) (hd1 : d1.length = 32)
    (p1 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s2 l16 l24 l32 t64 t48 rslot : List UInt8) (hfp : fp.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8) (hl24 : l24.length = 8) (hl32 : l32.length = 8) (ht64 : t64.length = 16) (ht48 : t48.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 120 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 40 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 8)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 112 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14
        ∧ st0.data.regs.get64 Reg64.rax = s.regs.rax.toBitVec
        ∧ st0.data.regs.get64 Reg64.rbx = s.regs.rbx.toBitVec
        ∧ st0.data.regs.get64 Reg64.rcx = s.regs.rcx.toBitVec
        ∧ st0.data.regs.get64 Reg64.rdi = s.regs.rdi.toBitVec ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (t48.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (t64.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (b1.At p1)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 36)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 112 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.get64 Reg64.rax = s.regs.rax.toBitVec
        ∧ st.data.regs.get64 Reg64.rbx = s.regs.rbx.toBitVec
        ∧ st.data.regs.get64 Reg64.rdx = s.regs.rcx.toBitVec + 8
        ∧ st.data.regs.get64 Reg64.rdi = s.regs.rdi.toBitVec ∧
        ∃ (x0 x1 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (b1.At p1)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v0 c1 b1 pre d0 d1 hast hv0 hc1 hb1 hd0 hd1 p1 s ra guard hpre fp s2 l16 l24 l32 t64 t48 rslot hfp hs2 hl16 hl24 hl32 ht64 ht48 hrslot R S scratch hsc hsp hcap hcap63 hmm
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
  have hcap' : rcx.toBitVec.toNat + 40 ≤ rdi.toBitVec.toNat := hcap
  apply step_lea Reg64.rdx Reg64.rcx 8 _ (k + 8) (k + 9) (window_infix_at hk 8 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.rdx (rcx.toBitVec + 8) _ _ _ (by show (rcx.toBitVec + 8 : BitVec 64) = (rcx.toBitVec + 8); bv_omega)
  normalize_registers
  apply step_load_bytes Reg64.r8 Reg64.rax 8 _ (k + 9) (k + 10) (window_infix_at hk 9 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 8) (by encoder_address_equation) v0 hv0 _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_lea Reg64.r9 Reg64.rsp 48 _ (k + 10) (k + 14) (window_infix_at hk 10 4) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.r9 (rsp.toBitVec - 64) _ _ _ (by show ((rsp.toBitVec - 112) + 48 : BitVec 64) = (rsp.toBitVec - 64); bv_omega)
  normalize_registers
  apply step_store_xmm15 Reg64.r9 0 _ (k + 14) (k + 15) (window_infix_at hk 14 1) (by rfl) (by rfl)
    (rsp.toBitVec - 64) (rsp.toBitVec - 64) (by encoder_address_equation) t64 ht64 _ _ _ (by rfl) (by ecancel)
  intro m3 H3; normalize_registers; try dsimp only at H3
  apply step_store_xmm15 Reg64.r9 16 _ (k + 15) (k + 16) (window_infix_at hk 15 1) (by rfl) (by rfl)
    (rsp.toBitVec - 64) (rsp.toBitVec - 48) (by encoder_address_equation) t48 ht48 _ _ _ (by rfl) (by ecancel)
  intro m4 H4; normalize_registers; try dsimp only at H4
  rw [Machine.at_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 64), show (rsp.toBitVec - 64) + 8 = (rsp.toBitVec - 56) by bv_omega] at H4
  apply step_store Reg64.r8 Reg64.rsp 48 _ (k + 16) (k + 17) (window_infix_at hk 16 1) (by rfl) (by rfl)
    (rsp.toBitVec - 112) (rsp.toBitVec - 64) (by encoder_address_equation) ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).take 8) (by rw [List.length_take, Int.toBytes_length]; rfl) _ _ _ (by rfl) (by ecancel)
  intro m5 H5; normalize_registers; simp only [Reg64s.get64] at H5
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v0 hv0] at H5
  have hl33 := Machine.label_at' hk hf (j := 33)
    (by simp only [marshalSSZTo, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply step_cmp_jae_taken Reg64.rdi Reg64.rdx _ _ (k + 17) (k + 33) (window_infix_at hk 17 2) (by rfl) hl33 _ _ (by show ((rcx.toBitVec + 8) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; normalize_registers
  apply step_label _ _ (k + 33) (k + 34) (window_infix_at hk 33 1) (by rfl) (by rfl)
  apply step_load_bytes Reg64.r8 Reg64.rsp 48 _ (k + 34) (k + 35) (window_infix_at hk 34 1) (by rfl) (by rfl)
    (rsp.toBitVec - 112) (rsp.toBitVec - 64) (by encoder_address_equation) v0 hv0 _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_store_indexed Reg64.r8 Reg64.rbx Reg64.rcx 0 _ (k + 35) (k + 36) (window_infix_at hk 35 1) (by rfl) (by rfl)
    rbx.toBitVec rcx.toBitVec (rbx.toBitVec + rcx.toBitVec) (by encoder_address_equation) d0 hd0 _ _ _ (by rfl) (by rfl) (by ecancel)
  intro m6 H6; normalize_registers; simp only [Reg64s.get64] at H6
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v0 hv0] at H6
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8), (Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt), (by rw [List.length_drop, Int.toBytes_length]), (Int.toBytes_length 16 _), ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem Encode.generated_f0_kind : ∀ (h : Host), type_of% (@Encode.generated_f0 h)
    = @Codec.encFieldKindAnyFrame h marshalSSZTo Prysm.Checkpoint.encodeLayout [.u64, .bytes 32]
    ⟨8, 0, [(.rax, .receiver), (.rbx, .ptr), (.rcx, .len 0), (.rdi, .cap)],
      [.at (.below 8) (.reg .rbp), .at (.above 16) (.reg .rbx), .at (.below 16) (.original 2), .at (.below 24) (.original 3), .at (.below 32) (.original 4), .at (.below 48) (.original 6), .at (.below 64) (.original 5), .at (.below 120) (.original 7), .low .scratch],
      []⟩
    ⟨36, 1, [(.rax, .receiver), (.rbx, .ptr), (.rdx, .len 8), (.rdi, .cap)],
      [.at (.below 8) (.reg .rbp), .at (.above 16) (.reg .rbx), .at (.below 16) (.original 2), .at (.below 24) (.original 3), .at (.below 32) (.original 4), .at (.below 48) (.existential 1), .at (.below 64) (.field 0), .at (.below 56) (.existential 0), .at (.below 120) (.original 7), .low .scratch],
      [.fixed 8, .fixed 16]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 1 `Root` (32 bytes): directives 36–62; boundary state 1 → 2. -/
theorem Encode.generated_f1 : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v0 c1 b1 pre d0 d1 : List UInt8) (hast : ast.length = 8) (hv0 : v0.length = 8) (hc1 : c1.length = 8) (hb1 : b1.length = 32) (hd0 : d0.length = 8) (hd1 : d1.length = 32)
    (p1 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s2 l16 l24 l32 t64 t48 rslot : List UInt8) (hfp : fp.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8) (hl24 : l24.length = 8) (hl32 : l32.length = 8) (ht64 : t64.length = 16) (ht48 : t48.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 120 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 40 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 36)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 112 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14
        ∧ st0.data.regs.get64 Reg64.rax = s.regs.rax.toBitVec
        ∧ st0.data.regs.get64 Reg64.rbx = s.regs.rbx.toBitVec
        ∧ st0.data.regs.get64 Reg64.rdx = s.regs.rcx.toBitVec + 8
        ∧ st0.data.regs.get64 Reg64.rdi = s.regs.rdi.toBitVec ∧
        ∃ (x0 x1 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (b1.At p1)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 63)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 112 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 x2 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧ x2.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 40).toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 63)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (b1.At p1)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v0 c1 b1 pre d0 d1 hast hv0 hc1 hb1 hd0 hd1 p1 s ra guard hpre fp s2 l16 l24 l32 t64 t48 rslot hfp hs2 hl16 hl24 hl32 ht64 ht48 hrslot R S scratch hsc hsp hcap hcap63 hmm
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
  have hcap' : rcx.toBitVec.toNat + 40 ≤ rdi.toBitVec.toNat := hcap
  apply step_load_value Reg64.r8 Reg64.rax 16 _ (k + 36) (k + 37) (window_infix_at hk 36 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 16) p1 (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_length_check Reg64.rax 24 32 _ _ (k + 37) (k + 39) (window_infix_at hk 37 2) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 24) (by encoder_address_equation) (Int.toBytes 8 32) (by rfl) (by decide) _ _ _ (by rfl) (by ecancel)
  intro fl; normalize_registers
  apply step_lea Reg64.r9 Reg64.rdx 32 _ (k + 39) (k + 40) (window_infix_at hk 39 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.r9 (rcx.toBitVec + 40) _ _ _ (by show ((rcx.toBitVec + 8) + 32 : BitVec 64) = (rcx.toBitVec + 40); bv_omega)
  normalize_registers
  have hl55 := Machine.label_at' hk hf (j := 55)
    (by simp only [marshalSSZTo, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply step_cmp_jae_taken Reg64.rdi Reg64.r9 _ _ (k + 40) (k + 55) (window_infix_at hk 40 2) (by rfl) hl55 _ _ (by show ((rcx.toBitVec + 40) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; normalize_registers
  apply step_label _ _ (k + 55) (k + 56) (window_infix_at hk 55 1) (by rfl) (by rfl)
  apply step_store Reg64.rdi Reg64.rsp 88 _ (k + 56) (k + 57) (window_infix_at hk 56 1) (by rfl) (by rfl)
    (rsp.toBitVec - 112) (rsp.toBitVec - 24) (by encoder_address_equation) l24 hl24 _ _ _ (by rfl) (by ecancel)
  intro m7 H7; normalize_registers; simp only [Reg64s.get64] at H7
  apply step_store Reg64.r9 Reg64.rsp 80 _ (k + 57) (k + 58) (window_infix_at hk 57 1) (by rfl) (by rfl)
    (rsp.toBitVec - 112) (rsp.toBitVec - 32) (by encoder_address_equation) l32 hl32 _ _ _ (by rfl) (by ecancel)
  intro m8 H8; normalize_registers; simp only [Reg64s.get64] at H8
  apply step_store Reg64.rbx Reg64.rsp 96 _ (k + 58) (k + 59) (window_infix_at hk 58 1) (by rfl) (by rfl)
    (rsp.toBitVec - 112) (rsp.toBitVec - 16) (by encoder_address_equation) l16 hl16 _ _ _ (by rfl) (by ecancel)
  intro m9 H9; normalize_registers; simp only [Reg64s.get64] at H9
  apply step_lea_indexed Reg64.rax Reg64.rbx Reg64.rdx _ (k + 59) (k + 60) (window_infix_at hk 59 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.rax (rbx.toBitVec + rcx.toBitVec + 8) _ _ _ (by show (rbx.toBitVec + (rcx.toBitVec + 8) : BitVec 64) = (rbx.toBitVec + rcx.toBitVec + 8); bv_omega)
  normalize_registers
  apply step_move_register Reg64.rbx Reg64.r8 _ (k + 60) (k + 61) (window_infix_at hk 60 1) (by rfl) (by rfl)
  normalize_registers
  apply step_move_immediate Reg64.rcx 32 _ (k + 61) (k + 62) (window_infix_at hk 61 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.rcx 32 _ _ _ (by show (BitVec.zeroExtend 64 (BitVec.truncate 32 (32 : BitVec 64)) : BitVec 64) = 32; decide)
  normalize_registers
  refine eventually_trans _ _ _ _ (encode_memmove_call (k + 62) (window_infix_at hk 62 1) (rsp.toBitVec - 112) (rbx.toBitVec + rcx.toBitVec + 8) p1
    (rsp.toBitVec - 120) (rsp.toBitVec - 120 - BitVec.ofNat 64 S) S (by bv_omega) (Codec.frame_low_address_without_calls rsp.toBitVec 112 120 S (by decide))
    b1 d1 rslot scratch (by rw [hd1, hb1]) hrslot hsc
    _ _ (by rfl) (by rfl) (by rfl) (by rw [hb1]; rfl) (by first | ecancel | (dsimp only; ecancel)) hmm) ?_
  rintro ⟨e1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, scr1, hscr1, Hc1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 Hc1
  subst hpc1
  obtain ⟨⟨raxc1, rbxc1, rcxc1, rdxc1, rsic1, rdic1, rspc1, rbpc1, r8c1, r9c1, r10c1, r11c1, r12c1, r13c1, r14c1, r15c1⟩, zmmsc1, flagsc1, memc1⟩ := e1
  simp only at hrsp1 hrbp1 hr141 Hc1
  subst rspc1 rbpc1 r14c1
  rw [show k + 62 + 1 = k + 63 from rfl] at Hc1
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, x0, x1, scr1, hx0, hx1, hscr1, ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem Encode.generated_f1_kind : ∀ (h : Host), type_of% (@Encode.generated_f1 h)
    = @Codec.encFieldKindAnyFrame h marshalSSZTo Prysm.Checkpoint.encodeLayout [.u64, .bytes 32]
    ⟨36, 1, [(.rax, .receiver), (.rbx, .ptr), (.rdx, .len 8), (.rdi, .cap)],
      [.at (.below 8) (.reg .rbp), .at (.above 16) (.reg .rbx), .at (.below 16) (.original 2), .at (.below 24) (.original 3), .at (.below 32) (.original 4), .at (.below 48) (.existential 1), .at (.below 64) (.field 0), .at (.below 56) (.existential 0), .at (.below 120) (.original 7), .low .scratch],
      [.fixed 8, .fixed 16]⟩
    ⟨63, 2, [],
      [.at (.below 8) (.reg .rbp), .at (.above 16) (.reg .rbx), .at (.below 16) (.reg .rbx), .at (.below 24) (.reg .rdi), .at (.below 32) (.len 40), .at (.below 48) (.existential 1), .at (.below 64) (.field 0), .at (.below 56) (.existential 0), .at (.below 120) (.ret 63), .low (.existential 2)],
      [.fixed 8, .fixed 16, .low]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Epilogue: directives 63–return; boundary state 2 → the fast-path post-state. -/
theorem Encode.generated_epi : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v0 c1 b1 pre d0 d1 : List UInt8) (hast : ast.length = 8) (hv0 : v0.length = 8) (hc1 : c1.length = 8) (hb1 : b1.length = 32) (hd0 : d0.length = 8) (hd1 : d1.length = 32)
    (p1 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s2 l16 l24 l32 t64 t48 rslot : List UInt8) (hfp : fp.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8) (hl24 : l24.length = 8) (hl32 : l32.length = 8) (ht64 : t64.length = 16) (ht48 : t48.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 120 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 40 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 63)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 112 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 x2 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧ x2.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 40).toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 63)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (b1.At p1)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec
        ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 40
        ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0
        ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8
        ∧ st.data.regs.rbp = s.regs.rbp
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 x2 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧ x2.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 40).toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 63)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (b1.At p1)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v0 c1 b1 pre d0 d1 hast hv0 hc1 hb1 hd0 hd1 p1 s ra guard hpre fp s2 l16 l24 l32 t64 t48 rslot hfp hs2 hl16 hl24 hl32 ht64 ht48 hrslot R S scratch hsc hsp hcap hcap63
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hsp hcap hcap63 hpre ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, x0, x1, x2, hx0, hx1, hx2, Hm⟩
  dsimp only at hpc hrsp hrbp hr14  Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14  Hm
  subst rsp1 rbp1 r141
  have hcap' : rcx.toBitVec.toNat + 40 ≤ rdi.toBitVec.toNat := hcap
  apply step_load_value Reg64.rax Reg64.rsp 96 _ (k + 63) (k + 64) (window_infix_at hk 63 1) (by rfl) (by rfl)
    (rsp.toBitVec - 112) (rsp.toBitVec - 16) rbx.toBitVec (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_load_value Reg64.rbx Reg64.rsp 80 _ (k + 64) (k + 65) (window_infix_at hk 64 1) (by rfl) (by rfl)
    (rsp.toBitVec - 112) (rsp.toBitVec - 32) (rcx.toBitVec + 40) (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_load_value Reg64.rcx Reg64.rsp 88 _ (k + 65) (k + 66) (window_infix_at hk 65 1) (by rfl) (by rfl)
    (rsp.toBitVec - 112) (rsp.toBitVec - 24) rdi.toBitVec (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_xor32 Reg64.rdi _ (k + 66) (k + 67) (window_infix_at hk 66 1) (by rfl) (by rfl)
  intro fl; normalize_registers
  apply step_xor32 Reg64.rsi _ (k + 67) (k + 68) (window_infix_at hk 67 1) (by rfl) (by rfl)
  intro fl; normalize_registers
  apply step_add_immediate Reg64.rsp 104 _ (k + 68) (k + 69) (window_infix_at hk 68 1) (by rfl) (by rfl)
  intro fl; normalize_registers
  apply register_value_rewrite Reg64.rsp (rsp.toBitVec - 8) _ _ _ (by show ((rsp.toBitVec - 112) + 104 : BitVec 64) = (rsp.toBitVec - 8); bv_omega)
  normalize_registers
  refine eventually_trans _ _ _ _ (decret_seg _ (k + 69) (window_infix_at hk 69 2) (by rfl) (rsp.toBitVec - 8) rsp.toBitVec (by bv_omega) rbp ra _ _ (by rfl) (by ecancel)) ?_
  rintro ⟨d', pc'⟩ ⟨hpc', hrsp', hrbp', hreg', hmem'⟩
  dsimp only at hpc' hrsp' hrbp' hreg' hmem'
  apply Eventually.done
  refine ⟨hpc', ?_, ?_, ?_, ?_, ?_, ?_, hrbp', ?_, x0, x1, x2, hx0, hx1, hx2, ?_⟩
  · exact UInt64.toBitVec_inj.mp (hreg' Reg64.rax (by decide) (by decide))
  · show d'.regs.rbx.toBitVec.toNat = rcx.toBitVec.toNat + 40
    rw [show d'.regs.rbx.toBitVec = rcx.toBitVec + 40 from hreg' Reg64.rbx (by decide) (by decide)]
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
theorem Encode.generated_epi_kind : ∀ (h : Host), type_of% (@Encode.generated_epi h)
    = @Codec.encEpilogueKindAnyFrame h marshalSSZTo Prysm.Checkpoint.encodeLayout [.u64, .bytes 32]
    ⟨63, 2, [],
      [.at (.below 8) (.reg .rbp), .at (.above 16) (.reg .rbx), .at (.below 16) (.reg .rbx), .at (.below 24) (.reg .rdi), .at (.below 32) (.len 40), .at (.below 48) (.existential 1), .at (.below 64) (.field 0), .at (.below 56) (.existential 0), .at (.below 120) (.ret 63), .low (.existential 2)],
      [.fixed 8, .fixed 16, .low]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Encoder fast path of `(*v1alpha1.Checkpoint).MarshalSSZTo` (Go 1.26.10), generated** (`encoder --fast-path`):
head, one theorem per field, epilogue, chained by `eventually_trans`. Premises: `len + 40 ≤ cap`,
every byte-vector field of its exact length. Statement = the kind instance (`_kind`). Fast path only. -/
theorem Encode.generated_fast : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v0 c1 b1 pre d0 d1 : List UInt8) (hast : ast.length = 8) (hv0 : v0.length = 8) (hc1 : c1.length = 8) (hb1 : b1.length = 32) (hd0 : d0.length = 8) (hd1 : d1.length = 32)
    (p1 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s2 l16 l24 l32 t64 t48 rslot : List UInt8) (hfp : fp.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8) (hl24 : l24.length = 8) (hl32 : l32.length = 8) (ht64 : t64.length = 16) (ht48 : t48.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (t48.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (t64.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 120))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (c1.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (b1.At p1)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
      ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 120 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 40 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveContract S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec
        ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 40
        ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0
        ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8
        ∧ st.data.regs.rbp = s.regs.rbp
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 x2 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧ x2.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 40).toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 63)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (b1.At p1)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf ast v0 c1 b1 pre d0 d1 hast hv0 hc1 hb1 hd0 hd1 p1 s ra guard hpre fp s2 l16 l24 l32 t64 t48 rslot hfp hs2 hl16 hl24 hl32 ht64 ht48 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm
  refine eventually_trans _ _ _ _ (Encode.generated_head k hk hf ast v0 c1 b1 pre d0 d1 hast hv0 hc1 hb1 hd0 hd1 p1 s ra guard hpre fp s2 l16 l24 l32 t64 t48 rslot hfp hs2 hl16 hl24 hl32 ht64 ht48 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm) ?_
  intro st0 h0
  refine eventually_trans _ _ _ _ (Encode.generated_f0 k hk hf ast v0 c1 b1 pre d0 d1 hast hv0 hc1 hb1 hd0 hd1 p1 s ra guard hpre fp s2 l16 l24 l32 t64 t48 rslot hfp hs2 hl16 hl24 hl32 ht64 ht48 hrslot R S scratch hsc hsp hcap hcap63 hmm st0 h0) ?_
  intro st1 h1
  refine eventually_trans _ _ _ _ (Encode.generated_f1 k hk hf ast v0 c1 b1 pre d0 d1 hast hv0 hc1 hb1 hd0 hd1 p1 s ra guard hpre fp s2 l16 l24 l32 t64 t48 rslot hfp hs2 hl16 hl24 hl32 ht64 ht48 hrslot R S scratch hsc hsp hcap hcap63 hmm st1 h1) ?_
  intro st2 h2
  exact Encode.generated_epi k hk hf ast v0 c1 b1 pre d0 d1 hast hv0 hc1 hb1 hd0 hd1 p1 s ra guard hpre fp s2 l16 l24 l32 t64 t48 rslot hfp hs2 hl16 hl24 hl32 ht64 ht48 hrslot R S scratch hsc hsp hcap hcap63 st2 h2
theorem Encode.generated_fast_kind : ∀ (h : Host), type_of% (@Encode.generated_fast h)
    = @Codec.encFastPathKindAnyFrame h marshalSSZTo Prysm.Checkpoint.encodeLayout [.u64, .bytes 32] := by
  intro h; rfl

/-- Statement check: the generated theorem proves the committed hand statement (implication tie). -/
theorem Encode.generated_statement : type_of% (@Prysm.Checkpoint.Encode.fast_path ‹Host›) :=
  Prysm.Checkpoint.Encode.fast_path_of_kind Encode.generated_fast

end Prysm.Checkpoint
