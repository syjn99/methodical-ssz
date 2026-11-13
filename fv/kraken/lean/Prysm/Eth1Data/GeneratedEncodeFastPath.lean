import Prysm.BeaconBlockHeader.EncodeFastPathKindInstances
import Codec.EncodeFrameTest
import Prysm.Eth1Data.Code

/-!
# GEN6 (`p2enc --gen6`, unit E2-G): encoder fast path of `(*v1alpha1.Eth1Data).MarshalSSZTo`

Generated from the `.S` file and the IR: a symbolic dataflow walk of the fast path, one application of a
step lemma per directive (windows with the nops erased), boundary states between the fields. Every theorem
has a `_kind` line (`encHeadKindN`, `encFieldKindN`, `encEpiKindN`, `encFastKindN`).
**Fast path only**: `len(dst) + 72 ≤ cap(dst)` and every byte-vector field of its exact length. No
`runtime.growslice` directive is stepped: each capacity test is decided from the premise. Not covered: the
growslice branches, the length rejects, the morestack path. Not a complete encoder result.
The statement is the declared type of the committed hand theorem `Prysm.Eth1Data.Encode.fast_path`.
GEN6-JSON: {"type": "Eth1Data", "const": "marshalSSZTo", "prefix": "Encode.generated", "size": 72, "frame": 128, "gd": 8, "rt": true, "fields": [["DepositRoot", "b", 32], ["DepositCount", "u", 8], ["BlockHash", "b", 32]], "boundaries": [9, 37, 56, 81], "layout": "Prysm.Eth1Data.encodeLayout", "S_sha256": "911a0ea1fb983c58c9be8ea72f94afdcd9bb25d9555956f7ca02f1777136b6c1", "ir_sha256": "c1586d32018abd182c16d50f6a7a76e38814cab08cf4a7a42105fe30342a5d2a", "statement_check": "same Prysm.Eth1Data.Encode.fast_path", "S": "prysm/go1.26.10/e2e/e1/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.MarshalSSZTo.S", "ir": "prysm/ir/ir-mainnet.json", "ir_type": "v1alpha1.Eth1Data", "kinds": [{"theorem": "Encode.generated_head", "kind": "encHeadKindN"}, {"theorem": "Encode.generated_f0", "kind": "encFieldKindN"}, {"theorem": "Encode.generated_f1", "kind": "encFieldKindN"}, {"theorem": "Encode.generated_f2", "kind": "encFieldKindN"}, {"theorem": "Encode.generated_epi", "kind": "encEpiKindN"}, {"theorem": "Encode.generated_fast", "kind": "encFastKindN"}]}
-/

open Machine Runtime TestTarget Codec Prysm.Eth1Data.Code
variable [Host]

namespace Prysm.Eth1Data

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Head: directives 0–8 (stack guard, frame, spills); entry → boundary state 0. -/
theorem Encode.generated_head : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v1 c0 c2 b0 b2 pre d0 d1 d2 : List UInt8) (hast : ast.length = 8) (hv1 : v1.length = 8) (hc0 : c0.length = 8) (hc2 : c2.length = 8) (hb0 : b0.length = 32) (hb2 : b2.length = 32) (hd0 : d0.length = 32) (hd1 : d1.length = 8) (hd2 : d2.length = 32)
    (p0 p2 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l24 l32 l40 l48 l56 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8) (hl24 : l24.length = 8) (hl32 : l32.length = 8) (hl40 : l40.length = 8) (hl48 : l48.length = 8) (hl56 : l56.length = 8) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (l56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 144))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (v1.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 40))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 48))
      ⋆ Eq (c2.At (s.regs.rax.toBitVec + 56))
      ⋆ Eq (b0.At p0)
      ⋆ Eq (b2.At p2)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 32))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 40))
      ⋆ R)
    (hguard : guard.toNat + 8 < s.regs.rsp.toNat) (hsp : 144 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 72 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveC S),
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
          ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (l56.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (c2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b2.At p2)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 32))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 40))
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf ast v1 c0 c2 b0 b2 pre d0 d1 d2 hast hv1 hc0 hc2 hb0 hb2 hd0 hd1 hd2 p0 p2 s ra guard hpre fp s1 s2 l16 l24 l32 l40 l48 l56 rslot hfp hs1 hs2 hl16 hl24 hl32 hl40 hl48 hl56 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hcap hcap63 hpre ⊢
  have hcap' : rcx.toBitVec.toNat + 72 ≤ rdi.toBitVec.toNat := hcap
  apply encpro_l _ _ _ (-8) 8 _ k (k + 7) (win hk 0 7) (by rfl) (by rfl) (by rfl) guard fp hfp _ _ _ (by dsimp only; ecancel) hguard
  intro m1 H1 fl1; kn; dsimp only at H1
  apply kstep_add Reg64.rsp (-128) _ (k + 7) (k + 8) (win hk 7 1) (by rfl) (by rfl)
  intro fl; kn
  apply kreg_eq Reg64.rsp (rsp.toBitVec - 136) _ _ _ (by show ((rsp.toBitVec - 8) + (-128) : BitVec 64) = (rsp.toBitVec - 136); bv_omega)
  kn
  apply kstep_st Reg64.rbx Reg64.rsp 152 _ (k + 8) (k + 9) (win hk 8 1) (by rfl) (by rfl)
    (rsp.toBitVec - 136) (rsp.toBitVec + 16) (by eb) s2 hs2 _ _ _ (by rfl) (by ecancel)
  intro m2 H2; kn; simp only [Reg64s.get64] at H2
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem Encode.generated_head_kind : ∀ (h : Host), type_of% (@Encode.generated_head h)
    = @Codec.encHeadKindN h marshalSSZTo Prysm.Eth1Data.encodeLayout [.bytes 32, .u64, .bytes 32]
    ⟨9, 0, [(.rax, .rcv), (.rbx, .ptr), (.rcx, .len 0), (.rdi, .cap)],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.orig 1), .at (.up 16) (.reg .rbx), .at (.dn 16) (.orig 3), .at (.dn 24) (.orig 4), .at (.dn 32) (.orig 5), .at (.dn 40) (.orig 6), .at (.dn 48) (.orig 7), .at (.dn 56) (.orig 8), .at (.dn 144) (.orig 9), .lo .scr],
      []⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 0 `DepositRoot` (32 bytes): directives 9–36; boundary state 0 → 1. -/
theorem Encode.generated_f0 : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v1 c0 c2 b0 b2 pre d0 d1 d2 : List UInt8) (hast : ast.length = 8) (hv1 : v1.length = 8) (hc0 : c0.length = 8) (hc2 : c2.length = 8) (hb0 : b0.length = 32) (hb2 : b2.length = 32) (hd0 : d0.length = 32) (hd1 : d1.length = 8) (hd2 : d2.length = 32)
    (p0 p2 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l24 l32 l40 l48 l56 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8) (hl24 : l24.length = 8) (hl32 : l32.length = 8) (hl40 : l40.length = 8) (hl48 : l48.length = 8) (hl56 : l56.length = 8) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 144 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 72 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveC S) (st0 : MachineState),
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
          ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (l56.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (c2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b2.At p2)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 32))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 40))
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
          ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 32).toInt).At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 37)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (c2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b2.At p2)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 32))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 40))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v1 c0 c2 b0 b2 pre d0 d1 d2 hast hv1 hc0 hc2 hb0 hb2 hd0 hd1 hd2 p0 p2 s ra guard hpre fp s1 s2 l16 l24 l32 l40 l48 l56 rslot hfp hs1 hs2 hl16 hl24 hl32 hl40 hl48 hl56 hrslot R S scratch hsc hsp hcap hcap63 hmm
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
  have hcap' : rcx.toBitVec.toNat + 72 ≤ rdi.toBitVec.toNat := hcap
  apply kstep_ldv Reg64.rdx Reg64.rax 8 _ (k + 9) (k + 10) (win hk 9 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 8) p0 (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_lenchk Reg64.rax 16 32 _ _ (k + 10) (k + 12) (win hk 10 2) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 16) (by eb) (Int.toBytes 8 32) (by rfl) (by decide) _ _ _ (by rfl) (by ecancel)
  intro fl; kn
  apply kstep_st Reg64.rax Reg64.rsp 144 _ (k + 12) (k + 13) (win hk 12 1) (by rfl) (by rfl)
    (rsp.toBitVec - 136) (rsp.toBitVec + 8) (by eb) s1 hs1 _ _ _ (by rfl) (by ecancel)
  intro m3 H3; kn; simp only [Reg64s.get64] at H3
  apply kstep_lea Reg64.r8 Reg64.rcx 32 _ (k + 13) (k + 14) (win hk 13 1) (by rfl) (by rfl)
  kn
  apply kreg_eq Reg64.r8 (rcx.toBitVec + 32) _ _ _ (by show (rcx.toBitVec + 32 : BitVec 64) = (rcx.toBitVec + 32); bv_omega)
  kn
  have hl29 := Machine.label_at' hk hf (j := 29)
    (by simp only [marshalSSZTo, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply kstep_cmp_jae_t Reg64.rdi Reg64.r8 _ _ (k + 14) (k + 29) (win hk 14 2) (by rfl) hl29 _ _ (by show ((rcx.toBitVec + 32) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; kn
  apply kstep_label _ _ (k + 29) (k + 30) (win hk 29 1) (by rfl) (by rfl)
  apply kstep_st Reg64.rbx Reg64.rsp 112 _ (k + 30) (k + 31) (win hk 30 1) (by rfl) (by rfl)
    (rsp.toBitVec - 136) (rsp.toBitVec - 24) (by eb) l24 hl24 _ _ _ (by rfl) (by ecancel)
  intro m4 H4; kn; simp only [Reg64s.get64] at H4
  apply kstep_st Reg64.r8 Reg64.rsp 80 _ (k + 31) (k + 32) (win hk 31 1) (by rfl) (by rfl)
    (rsp.toBitVec - 136) (rsp.toBitVec - 56) (by eb) l56 hl56 _ _ _ (by rfl) (by ecancel)
  intro m5 H5; kn; simp only [Reg64s.get64] at H5
  apply kstep_st Reg64.rdi Reg64.rsp 88 _ (k + 32) (k + 33) (win hk 32 1) (by rfl) (by rfl)
    (rsp.toBitVec - 136) (rsp.toBitVec - 48) (by eb) l48 hl48 _ _ _ (by rfl) (by ecancel)
  intro m6 H6; kn; simp only [Reg64s.get64] at H6
  apply kstep_lea_idx Reg64.rax Reg64.rcx Reg64.rbx _ (k + 33) (k + 34) (win hk 33 1) (by rfl) (by rfl)
  kn
  apply kreg_eq Reg64.rax (rbx.toBitVec + rcx.toBitVec) _ _ _ (by show (rcx.toBitVec + rbx.toBitVec : BitVec 64) = (rbx.toBitVec + rcx.toBitVec); bv_omega)
  kn
  apply kstep_mov_rr Reg64.rbx Reg64.rdx _ (k + 34) (k + 35) (win hk 34 1) (by rfl) (by rfl)
  kn
  apply kstep_movi Reg64.rcx 32 _ (k + 35) (k + 36) (win hk 35 1) (by rfl) (by rfl)
  kn
  apply kreg_eq Reg64.rcx 32 _ _ _ (by show (BitVec.zeroExtend 64 (BitVec.truncate 32 (32 : BitVec 64)) : BitVec 64) = 32; decide)
  kn
  refine eventually_trans _ _ _ _ (encn_call (k + 36) (win hk 36 1) (rsp.toBitVec - 136) (rbx.toBitVec + rcx.toBitVec) p0
    (rsp.toBitVec - 144) (rsp.toBitVec - 144 - BitVec.ofNat 64 S) S (by bv_omega) (Codec.frame_lo0 rsp.toBitVec 136 144 S (by decide))
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
theorem Encode.generated_f0_kind : ∀ (h : Host), type_of% (@Encode.generated_f0 h)
    = @Codec.encFieldKindN h marshalSSZTo Prysm.Eth1Data.encodeLayout [.bytes 32, .u64, .bytes 32]
    ⟨9, 0, [(.rax, .rcv), (.rbx, .ptr), (.rcx, .len 0), (.rdi, .cap)],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.orig 1), .at (.up 16) (.reg .rbx), .at (.dn 16) (.orig 3), .at (.dn 24) (.orig 4), .at (.dn 32) (.orig 5), .at (.dn 40) (.orig 6), .at (.dn 48) (.orig 7), .at (.dn 56) (.orig 8), .at (.dn 144) (.orig 9), .lo .scr],
      []⟩
    ⟨37, 1, [],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 16) (.orig 3), .at (.dn 24) (.reg .rbx), .at (.dn 32) (.orig 5), .at (.dn 40) (.orig 6), .at (.dn 48) (.reg .rdi), .at (.dn 56) (.len 32), .at (.dn 144) (.ret 37), .lo (.ex 0)],
      [.lo]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 1 `DepositCount` (uint64): directives 37–55; boundary state 1 → 2. -/
theorem Encode.generated_f1 : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v1 c0 c2 b0 b2 pre d0 d1 d2 : List UInt8) (hast : ast.length = 8) (hv1 : v1.length = 8) (hc0 : c0.length = 8) (hc2 : c2.length = 8) (hb0 : b0.length = 32) (hb2 : b2.length = 32) (hd0 : d0.length = 32) (hd1 : d1.length = 8) (hd2 : d2.length = 32)
    (p0 p2 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l24 l32 l40 l48 l56 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8) (hl24 : l24.length = 8) (hl32 : l32.length = 8) (hl40 : l40.length = 8) (hl48 : l48.length = 8) (hl56 : l56.length = 8) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 144 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 72 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveC S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 37)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 136 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 : List UInt8), x0.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 32).toInt).At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 37)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (c2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b2.At p2)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 32))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 40))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 56)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 136 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.get64 Reg64.rax = s.regs.rbx.toBitVec
        ∧ st.data.regs.get64 Reg64.rbx = s.regs.rcx.toBitVec + 40
        ∧ st.data.regs.get64 Reg64.rcx = s.regs.rdi.toBitVec
        ∧ st.data.regs.get64 Reg64.rdx = s.regs.rax.toBitVec ∧
        ∃ (x0 : List UInt8), x0.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 32).toInt).At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 37)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (c2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b2.At p2)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 32))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 40))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v1 c0 c2 b0 b2 pre d0 d1 d2 hast hv1 hc0 hc2 hb0 hb2 hd0 hd1 hd2 p0 p2 s ra guard hpre fp s1 s2 l16 l24 l32 l40 l48 l56 rslot hfp hs1 hs2 hl16 hl24 hl32 hl40 hl48 hl56 hrslot R S scratch hsc hsp hcap hcap63 hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hsp hcap hcap63 hpre ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, x0, hx0, Hm⟩
  dsimp only at hpc hrsp hrbp hr14  Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14  Hm
  subst rsp1 rbp1 r141
  have hcap' : rcx.toBitVec.toNat + 72 ≤ rdi.toBitVec.toNat := hcap
  apply kstep_ldv Reg64.rbx Reg64.rsp 80 _ (k + 37) (k + 38) (win hk 37 1) (by rfl) (by rfl)
    (rsp.toBitVec - 136) (rsp.toBitVec - 56) (rcx.toBitVec + 32) (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_add Reg64.rbx 8 _ (k + 38) (k + 39) (win hk 38 1) (by rfl) (by rfl)
  intro fl; kn
  apply kreg_eq Reg64.rbx (rcx.toBitVec + 40) _ _ _ (by show ((rcx.toBitVec + 32) + 8 : BitVec 64) = (rcx.toBitVec + 40); bv_omega)
  kn
  apply kstep_ldv Reg64.rdx Reg64.rsp 144 _ (k + 39) (k + 40) (win hk 39 1) (by rfl) (by rfl)
    (rsp.toBitVec - 136) (rsp.toBitVec + 8) rax.toBitVec (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_ldb Reg64.rsi Reg64.rdx 32 _ (k + 40) (k + 41) (win hk 40 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 32) (by eb) v1 hv1 _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_ldv Reg64.rcx Reg64.rsp 88 _ (k + 41) (k + 42) (win hk 41 1) (by rfl) (by rfl)
    (rsp.toBitVec - 136) (rsp.toBitVec - 48) rdi.toBitVec (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_cmp_jb_f Reg64.rcx Reg64.rbx _ _ (k + 42) (k + 44) (win hk 42 2) (by rfl) (by rfl) _ _ (by show ((rcx.toBitVec + 40) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; kn
  apply kstep_ldv Reg64.rax Reg64.rsp 112 _ (k + 44) (k + 45) (win hk 44 1) (by rfl) (by rfl)
    (rsp.toBitVec - 136) (rsp.toBitVec - 24) rbx.toBitVec (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  have hl54 := Machine.label_at' hk hf (j := 54)
    (by simp only [marshalSSZTo, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply kstep_jmp _ _ (k + 45) (k + 54) (win hk 45 1) (by rfl) hl54
  apply kstep_label _ _ (k + 54) (k + 55) (win hk 54 1) (by rfl) (by rfl)
  apply kstep_st_idx Reg64.rsi Reg64.rbx Reg64.rax (-8) _ (k + 55) (k + 56) (win hk 55 1) (by rfl) (by rfl)
    (rcx.toBitVec + 40) rbx.toBitVec (rbx.toBitVec + rcx.toBitVec + 32) (by eb) d1 hd1 _ _ _ (by rfl) (by rfl) (by ecancel)
  intro m7 H7; kn; simp only [Reg64s.get64] at H7
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v1 hv1] at H7
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, x0, hx0, ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem Encode.generated_f1_kind : ∀ (h : Host), type_of% (@Encode.generated_f1 h)
    = @Codec.encFieldKindN h marshalSSZTo Prysm.Eth1Data.encodeLayout [.bytes 32, .u64, .bytes 32]
    ⟨37, 1, [],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 16) (.orig 3), .at (.dn 24) (.reg .rbx), .at (.dn 32) (.orig 5), .at (.dn 40) (.orig 6), .at (.dn 48) (.reg .rdi), .at (.dn 56) (.len 32), .at (.dn 144) (.ret 37), .lo (.ex 0)],
      [.lo]⟩
    ⟨56, 2, [(.rax, .ptr), (.rbx, .len 40), (.rcx, .cap), (.rdx, .rcv)],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 16) (.orig 3), .at (.dn 24) (.reg .rbx), .at (.dn 32) (.orig 5), .at (.dn 40) (.orig 6), .at (.dn 48) (.reg .rdi), .at (.dn 56) (.len 32), .at (.dn 144) (.ret 37), .lo (.ex 0)],
      [.lo]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 2 `BlockHash` (32 bytes): directives 56–80; boundary state 2 → 3. -/
theorem Encode.generated_f2 : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v1 c0 c2 b0 b2 pre d0 d1 d2 : List UInt8) (hast : ast.length = 8) (hv1 : v1.length = 8) (hc0 : c0.length = 8) (hc2 : c2.length = 8) (hb0 : b0.length = 32) (hb2 : b2.length = 32) (hd0 : d0.length = 32) (hd1 : d1.length = 8) (hd2 : d2.length = 32)
    (p0 p2 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l24 l32 l40 l48 l56 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8) (hl24 : l24.length = 8) (hl32 : l32.length = 8) (hl40 : l40.length = 8) (hl48 : l48.length = 8) (hl56 : l56.length = 8) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 144 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 72 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveC S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 56)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 136 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14
        ∧ st0.data.regs.get64 Reg64.rax = s.regs.rbx.toBitVec
        ∧ st0.data.regs.get64 Reg64.rbx = s.regs.rcx.toBitVec + 40
        ∧ st0.data.regs.get64 Reg64.rcx = s.regs.rdi.toBitVec
        ∧ st0.data.regs.get64 Reg64.rdx = s.regs.rax.toBitVec ∧
        ∃ (x0 : List UInt8), x0.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 32).toInt).At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 37)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (c2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b2.At p2)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 32))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 40))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 81)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 136 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 : List UInt8), x0.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 72).toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 32).toInt).At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 81)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (c2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b2.At p2)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 32))
          ⋆ Eq (b2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 40))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v1 c0 c2 b0 b2 pre d0 d1 d2 hast hv1 hc0 hc2 hb0 hb2 hd0 hd1 hd2 p0 p2 s ra guard hpre fp s1 s2 l16 l24 l32 l40 l48 l56 rslot hfp hs1 hs2 hl16 hl24 hl32 hl40 hl48 hl56 hrslot R S scratch hsc hsp hcap hcap63 hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hsp hcap hcap63 hpre ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, hrrax, hrrbx, hrrcx, hrrdx, x0, hx0, Hm⟩
  dsimp only at hpc hrsp hrbp hr14 hrrax hrrbx hrrcx hrrdx Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14 hrrax hrrbx hrrcx hrrdx Hm
  subst rsp1 rbp1 r141
  obtain rfl : rbx = rax1 := (UInt64.toBitVec_inj.mp hrrax).symm
  obtain rfl : rbx1 = { toBitVec := rcx.toBitVec + 40 } := UInt64.toBitVec_inj.mp hrrbx
  obtain rfl : rdi = rcx1 := (UInt64.toBitVec_inj.mp hrrcx).symm
  obtain rfl : rax = rdx1 := (UInt64.toBitVec_inj.mp hrrdx).symm
  have hcap' : rcx.toBitVec.toNat + 72 ≤ rdi.toBitVec.toNat := hcap
  apply kstep_ldv Reg64.r8 Reg64.rdx 40 _ (k + 56) (k + 57) (win hk 56 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 40) p2 (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_lenchk Reg64.rdx 48 32 _ _ (k + 57) (k + 59) (win hk 57 2) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 48) (by eb) (Int.toBytes 8 32) (by rfl) (by decide) _ _ _ (by rfl) (by ecancel)
  intro fl; kn
  apply kstep_lea Reg64.rdx Reg64.rbx 32 _ (k + 59) (k + 60) (win hk 59 1) (by rfl) (by rfl)
  kn
  apply kreg_eq Reg64.rdx (rcx.toBitVec + 72) _ _ _ (by show ((rcx.toBitVec + 40) + 32 : BitVec 64) = (rcx.toBitVec + 72); bv_omega)
  kn
  have hl73 := Machine.label_at' hk hf (j := 73)
    (by simp only [marshalSSZTo, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply kstep_cmp_jae_t Reg64.rcx Reg64.rdx _ _ (k + 60) (k + 73) (win hk 60 3) (by rfl) hl73 _ _ (by show ((rcx.toBitVec + 72) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; kn
  apply kstep_label _ _ (k + 73) (k + 74) (win hk 73 1) (by rfl) (by rfl)
  apply kstep_st Reg64.rax Reg64.rsp 120 _ (k + 74) (k + 75) (win hk 74 1) (by rfl) (by rfl)
    (rsp.toBitVec - 136) (rsp.toBitVec - 16) (by eb) l16 hl16 _ _ _ (by rfl) (by ecancel)
  intro m8 H8; kn; simp only [Reg64s.get64] at H8
  apply kstep_st Reg64.rdx Reg64.rsp 104 _ (k + 75) (k + 76) (win hk 75 1) (by rfl) (by rfl)
    (rsp.toBitVec - 136) (rsp.toBitVec - 32) (by eb) l32 hl32 _ _ _ (by rfl) (by ecancel)
  intro m9 H9; kn; simp only [Reg64s.get64] at H9
  apply kstep_st Reg64.rcx Reg64.rsp 96 _ (k + 76) (k + 77) (win hk 76 1) (by rfl) (by rfl)
    (rsp.toBitVec - 136) (rsp.toBitVec - 40) (by eb) l40 hl40 _ _ _ (by rfl) (by ecancel)
  intro m10 H10; kn; simp only [Reg64s.get64] at H10
  apply kstep_add_rr Reg64.rax Reg64.rbx _ (k + 77) (k + 78) (win hk 77 1) (by rfl) (by rfl)
  intro fl; kn
  apply kreg_eq Reg64.rax (rbx.toBitVec + rcx.toBitVec + 40) _ _ _ (by show (rbx.toBitVec + (rcx.toBitVec + 40) : BitVec 64) = (rbx.toBitVec + rcx.toBitVec + 40); bv_omega)
  kn
  apply kstep_mov_rr Reg64.rbx Reg64.r8 _ (k + 78) (k + 79) (win hk 78 1) (by rfl) (by rfl)
  kn
  apply kstep_movi Reg64.rcx 32 _ (k + 79) (k + 80) (win hk 79 1) (by rfl) (by rfl)
  kn
  apply kreg_eq Reg64.rcx 32 _ _ _ (by show (BitVec.zeroExtend 64 (BitVec.truncate 32 (32 : BitVec 64)) : BitVec 64) = 32; decide)
  kn
  refine eventually_trans _ _ _ _ (encn_call (k + 80) (win hk 80 1) (rsp.toBitVec - 136) (rbx.toBitVec + rcx.toBitVec + 40) p2
    (rsp.toBitVec - 144) (rsp.toBitVec - 144 - BitVec.ofNat 64 S) S (by bv_omega) (Codec.frame_lo0 rsp.toBitVec 136 144 S (by decide))
    b2 d2 (Int.toBytes 8 (Host.addrOf (k + 37)).toBitVec.toInt) x0 (by rw [hd2, hb2]) (Int.toBytes_length 8 _) hx0
    _ _ (by rfl) (by rfl) (by rfl) (by rw [hb2]; rfl) (by first | ecancel | (dsimp only; ecancel)) hmm) ?_
  rintro ⟨e2, pc2⟩ ⟨hpc2, hrsp2, hrbp2, hr142, scr2, hscr2, Hc2⟩
  dsimp only at hpc2 hrsp2 hrbp2 hr142 Hc2
  subst hpc2
  obtain ⟨⟨raxc2, rbxc2, rcxc2, rdxc2, rsic2, rdic2, rspc2, rbpc2, r8c2, r9c2, r10c2, r11c2, r12c2, r13c2, r14c2, r15c2⟩, zmmsc2, flagsc2, memc2⟩ := e2
  simp only at hrsp2 hrbp2 hr142 Hc2
  subst rspc2 rbpc2 r14c2
  rw [show k + 80 + 1 = k + 81 from rfl] at Hc2
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, scr2, hscr2, ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem Encode.generated_f2_kind : ∀ (h : Host), type_of% (@Encode.generated_f2 h)
    = @Codec.encFieldKindN h marshalSSZTo Prysm.Eth1Data.encodeLayout [.bytes 32, .u64, .bytes 32]
    ⟨56, 2, [(.rax, .ptr), (.rbx, .len 40), (.rcx, .cap), (.rdx, .rcv)],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 16) (.orig 3), .at (.dn 24) (.reg .rbx), .at (.dn 32) (.orig 5), .at (.dn 40) (.orig 6), .at (.dn 48) (.reg .rdi), .at (.dn 56) (.len 32), .at (.dn 144) (.ret 37), .lo (.ex 0)],
      [.lo]⟩
    ⟨81, 3, [],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 16) (.reg .rbx), .at (.dn 24) (.reg .rbx), .at (.dn 32) (.len 72), .at (.dn 40) (.reg .rdi), .at (.dn 48) (.reg .rdi), .at (.dn 56) (.len 32), .at (.dn 144) (.ret 81), .lo (.ex 0)],
      [.lo]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Epilogue: directives 81–return; boundary state 3 → the fast-path post-state. -/
theorem Encode.generated_epi : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v1 c0 c2 b0 b2 pre d0 d1 d2 : List UInt8) (hast : ast.length = 8) (hv1 : v1.length = 8) (hc0 : c0.length = 8) (hc2 : c2.length = 8) (hb0 : b0.length = 32) (hb2 : b2.length = 32) (hd0 : d0.length = 32) (hd1 : d1.length = 8) (hd2 : d2.length = 32)
    (p0 p2 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l24 l32 l40 l48 l56 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8) (hl24 : l24.length = 8) (hl32 : l32.length = 8) (hl40 : l40.length = 8) (hl48 : l48.length = 8) (hl56 : l56.length = 8) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 144 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 72 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 81)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 136 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 : List UInt8), x0.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 72).toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 32).toInt).At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 81)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (c2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b2.At p2)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 32))
          ⋆ Eq (b2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 40))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec
        ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 72
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
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 72).toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 32).toInt).At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 81)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (c2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b2.At p2)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 32))
          ⋆ Eq (b2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 40))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v1 c0 c2 b0 b2 pre d0 d1 d2 hast hv1 hc0 hc2 hb0 hb2 hd0 hd1 hd2 p0 p2 s ra guard hpre fp s1 s2 l16 l24 l32 l40 l48 l56 rslot hfp hs1 hs2 hl16 hl24 hl32 hl40 hl48 hl56 hrslot R S scratch hsc hsp hcap hcap63
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hsp hcap hcap63 hpre ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, x0, hx0, Hm⟩
  dsimp only at hpc hrsp hrbp hr14  Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14  Hm
  subst rsp1 rbp1 r141
  have hcap' : rcx.toBitVec.toNat + 72 ≤ rdi.toBitVec.toNat := hcap
  apply kstep_ldv Reg64.rax Reg64.rsp 120 _ (k + 81) (k + 82) (win hk 81 1) (by rfl) (by rfl)
    (rsp.toBitVec - 136) (rsp.toBitVec - 16) rbx.toBitVec (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_ldv Reg64.rbx Reg64.rsp 104 _ (k + 82) (k + 83) (win hk 82 1) (by rfl) (by rfl)
    (rsp.toBitVec - 136) (rsp.toBitVec - 32) (rcx.toBitVec + 72) (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_ldv Reg64.rcx Reg64.rsp 96 _ (k + 83) (k + 84) (win hk 83 1) (by rfl) (by rfl)
    (rsp.toBitVec - 136) (rsp.toBitVec - 40) rdi.toBitVec (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_xor32 Reg64.rdi _ (k + 84) (k + 85) (win hk 84 1) (by rfl) (by rfl)
  intro fl; kn
  apply kstep_xor32 Reg64.rsi _ (k + 85) (k + 86) (win hk 85 1) (by rfl) (by rfl)
  intro fl; kn
  apply kstep_sub_i Reg64.rsp (-128) _ (k + 86) (k + 87) (win hk 86 1) (by rfl) (by rfl)
  intro fl; kn
  apply kreg_eq Reg64.rsp (rsp.toBitVec - 8) _ _ _ (by show ((rsp.toBitVec - 136) - (-128) : BitVec 64) = (rsp.toBitVec - 8); bv_omega)
  kn
  refine eventually_trans _ _ _ _ (decret_seg _ (k + 87) (win hk 87 2) (by rfl) (rsp.toBitVec - 8) rsp.toBitVec (by bv_omega) rbp ra _ _ (by rfl) (by ecancel)) ?_
  rintro ⟨d', pc'⟩ ⟨hpc', hrsp', hrbp', hreg', hmem'⟩
  dsimp only at hpc' hrsp' hrbp' hreg' hmem'
  apply Eventually.done
  refine ⟨hpc', ?_, ?_, ?_, ?_, ?_, ?_, hrbp', ?_, x0, hx0, ?_⟩
  · exact UInt64.toBitVec_inj.mp (hreg' Reg64.rax (by decide) (by decide))
  · show d'.regs.rbx.toBitVec.toNat = rcx.toBitVec.toNat + 72
    rw [show d'.regs.rbx.toBitVec = rcx.toBitVec + 72 from hreg' Reg64.rbx (by decide) (by decide)]
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
    = @Codec.encEpiKindN h marshalSSZTo Prysm.Eth1Data.encodeLayout [.bytes 32, .u64, .bytes 32]
    ⟨81, 3, [],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 16) (.reg .rbx), .at (.dn 24) (.reg .rbx), .at (.dn 32) (.len 72), .at (.dn 40) (.reg .rdi), .at (.dn 48) (.reg .rdi), .at (.dn 56) (.len 32), .at (.dn 144) (.ret 81), .lo (.ex 0)],
      [.lo]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Encoder fast path of `(*v1alpha1.Eth1Data).MarshalSSZTo` (Go 1.26.10), generated** (`p2enc --gen6`):
head, one theorem per field, epilogue, chained by `eventually_trans`. Premises: `len + 72 ≤ cap`,
every byte-vector field of its exact length. Statement = the kind instance (`_kind`). Fast path only. -/
theorem Encode.generated_fast : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v1 c0 c2 b0 b2 pre d0 d1 d2 : List UInt8) (hast : ast.length = 8) (hv1 : v1.length = 8) (hc0 : c0.length = 8) (hc2 : c2.length = 8) (hb0 : b0.length = 32) (hb2 : b2.length = 32) (hd0 : d0.length = 32) (hd1 : d1.length = 8) (hd2 : d2.length = 32)
    (p0 p2 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l24 l32 l40 l48 l56 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8) (hl24 : l24.length = 8) (hl32 : l32.length = 8) (hl40 : l40.length = 8) (hl48 : l48.length = 8) (hl56 : l56.length = 8) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (l56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 144))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (v1.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 40))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 48))
      ⋆ Eq (c2.At (s.regs.rax.toBitVec + 56))
      ⋆ Eq (b0.At p0)
      ⋆ Eq (b2.At p2)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 32))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 40))
      ⋆ R)
    (hguard : guard.toNat + 8 < s.regs.rsp.toNat) (hsp : 144 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 72 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveC S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec
        ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 72
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
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 72).toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 32).toInt).At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 81)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (c2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b2.At p2)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 32))
          ⋆ Eq (b2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 40))
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf ast v1 c0 c2 b0 b2 pre d0 d1 d2 hast hv1 hc0 hc2 hb0 hb2 hd0 hd1 hd2 p0 p2 s ra guard hpre fp s1 s2 l16 l24 l32 l40 l48 l56 rslot hfp hs1 hs2 hl16 hl24 hl32 hl40 hl48 hl56 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm
  refine eventually_trans _ _ _ _ (Encode.generated_head k hk hf ast v1 c0 c2 b0 b2 pre d0 d1 d2 hast hv1 hc0 hc2 hb0 hb2 hd0 hd1 hd2 p0 p2 s ra guard hpre fp s1 s2 l16 l24 l32 l40 l48 l56 rslot hfp hs1 hs2 hl16 hl24 hl32 hl40 hl48 hl56 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm) ?_
  intro st0 h0
  refine eventually_trans _ _ _ _ (Encode.generated_f0 k hk hf ast v1 c0 c2 b0 b2 pre d0 d1 d2 hast hv1 hc0 hc2 hb0 hb2 hd0 hd1 hd2 p0 p2 s ra guard hpre fp s1 s2 l16 l24 l32 l40 l48 l56 rslot hfp hs1 hs2 hl16 hl24 hl32 hl40 hl48 hl56 hrslot R S scratch hsc hsp hcap hcap63 hmm st0 h0) ?_
  intro st1 h1
  refine eventually_trans _ _ _ _ (Encode.generated_f1 k hk hf ast v1 c0 c2 b0 b2 pre d0 d1 d2 hast hv1 hc0 hc2 hb0 hb2 hd0 hd1 hd2 p0 p2 s ra guard hpre fp s1 s2 l16 l24 l32 l40 l48 l56 rslot hfp hs1 hs2 hl16 hl24 hl32 hl40 hl48 hl56 hrslot R S scratch hsc hsp hcap hcap63 hmm st1 h1) ?_
  intro st2 h2
  refine eventually_trans _ _ _ _ (Encode.generated_f2 k hk hf ast v1 c0 c2 b0 b2 pre d0 d1 d2 hast hv1 hc0 hc2 hb0 hb2 hd0 hd1 hd2 p0 p2 s ra guard hpre fp s1 s2 l16 l24 l32 l40 l48 l56 rslot hfp hs1 hs2 hl16 hl24 hl32 hl40 hl48 hl56 hrslot R S scratch hsc hsp hcap hcap63 hmm st2 h2) ?_
  intro st3 h3
  exact Encode.generated_epi k hk hf ast v1 c0 c2 b0 b2 pre d0 d1 d2 hast hv1 hc0 hc2 hb0 hb2 hd0 hd1 hd2 p0 p2 s ra guard hpre fp s1 s2 l16 l24 l32 l40 l48 l56 rslot hfp hs1 hs2 hl16 hl24 hl32 hl40 hl48 hl56 hrslot R S scratch hsc hsp hcap hcap63 st3 h3
theorem Encode.generated_fast_kind : ∀ (h : Host), type_of% (@Encode.generated_fast h)
    = @Codec.encFastKindN h marshalSSZTo Prysm.Eth1Data.encodeLayout [.bytes 32, .u64, .bytes 32] := by
  intro h; rfl

/-- Statement check: the generated theorem proves the committed hand statement. -/
theorem Encode.generated_stmt : type_of% (@Prysm.Eth1Data.Encode.fast_path ‹Host›) :=
  Encode.generated_fast

end Prysm.Eth1Data
