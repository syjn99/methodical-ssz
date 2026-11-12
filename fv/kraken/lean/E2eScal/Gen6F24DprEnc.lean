import E2eScal.EncTies
import E2eScal.EncFrameTest
import E2eScal.F24Code

/-!
# GEN6 (`p2enc --gen6`, unit E2-G): encoder fast path of `(*v1alpha1.DepositRequest).MarshalSSZTo`

Generated from the `.S` file and the IR: a symbolic dataflow walk of the fast path, one application of a
step lemma per directive (windows with the nops erased), boundary states between the fields. Every theorem
has a `_kind` line (`encHeadKindN`, `encFieldKindN`, `encEpiKindN`, `encFastKindN`).
**Fast path only**: `len(dst) + 192 ≤ cap(dst)` and every byte-vector field of its exact length. No
`runtime.growslice` directive is stepped: each capacity test is decided from the premise. Not covered: the
growslice branches, the length rejects, the morestack path. Not a complete encoder result.
GEN6-JSON: {"type": "DepositRequest", "const": "DprMarshal", "prefix": "dpr_g6e", "size": 192, "frame": 168, "gd": 48, "rt": true, "fields": [["Pubkey", "b", 48], ["WithdrawalCredentials", "b", 32], ["Amount", "u", 8], ["Signature", "b", 96], ["Index", "u", 8]], "boundaries": [9, 38, 67, 87, 111, 130], "layout": "E2eScal.Gen6Enc.dpr_g6e_layout", "S_sha256": "8ec8e5eb71c2161abf46bb29a9f0e45b515aabae6cff7a14e58b090b76e27c33", "ir_sha256": "c1586d32018abd182c16d50f6a7a76e38814cab08cf4a7a42105fe30342a5d2a", "statement_check": "kind instance only", "S": "prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo.S", "ir": "prysm/ir/ir-mainnet.json", "ir_type": "v1.DepositRequest", "kinds": [{"theorem": "dpr_g6e_head", "kind": "encHeadKindN"}, {"theorem": "dpr_g6e_f0", "kind": "encFieldKindN"}, {"theorem": "dpr_g6e_f1", "kind": "encFieldKindN"}, {"theorem": "dpr_g6e_f2", "kind": "encFieldKindN"}, {"theorem": "dpr_g6e_f3", "kind": "encFieldKindN"}, {"theorem": "dpr_g6e_f4", "kind": "encFieldKindN"}, {"theorem": "dpr_g6e_epi", "kind": "encEpiKindN"}, {"theorem": "dpr_g6e_fast", "kind": "encFastKindN"}]}
-/

open Fk E2eScal E2eScal.F24Code
variable [Host]

namespace E2eScal.Gen6Enc

/-- The frame facts of `DprMarshal` (read from the `.S` file by the walk): frame `0xa8`, stack chunks
`fp s1 s2 l16 l48 l56 l32 l80 l64 l72 l88 l40 rslot`. -/
def dpr_g6e_layout : EncLayout where
  st := true
  frame := 168
  gd := 48
  rt := true
  nstk := 13
  lens := [(0, 8), (1, 8), (2, 8), (3, 8), (4, 8), (5, 8), (6, 8), (7, 8), (8, 8), (9, 8), (10, 8), (11, 8), (12, 8)]
  pre := [.at (.dn 8) (.orig 0), .at (.up 8) (.orig 1), .at (.up 16) (.orig 2), .at (.dn 16) (.orig 3), .at (.dn 48) (.orig 4), .at (.dn 56) (.orig 5), .at (.dn 32) (.orig 6), .at (.dn 80) (.orig 7), .at (.dn 64) (.orig 8), .at (.dn 72) (.orig 9), .at (.dn 88) (.orig 10), .at (.dn 40) (.orig 11), .at (.dn 184) (.orig 12), .lo .scr]
  exs := [.lo]
  post := [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 16) (.reg .rbx), .at (.dn 48) (.len 48), .at (.dn 56) (.reg .rdi), .at (.dn 32) (.reg .rbx), .at (.dn 80) (.len 80), .at (.dn 64) (.reg .rdi), .at (.dn 72) (.reg .rdi), .at (.dn 88) (.len 184), .at (.dn 40) (.reg .rbx), .at (.dn 184) (.ret 111), .lo (.ex 0)]


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Head: directives 0–8 (stack guard, frame, spills); entry → boundary state 0. -/
theorem dpr_g6e_head : ∀ (k : Nat) (hk : DprMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh DprMarshal k)
    (ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 : List UInt8) (hast : ast.length = 8) (hv2 : v2.length = 8) (hv4 : v4.length = 8) (hc0 : c0.length = 8) (hc1 : c1.length = 8) (hc3 : c3.length = 8) (hb0 : b0.length = 48) (hb1 : b1.length = 32) (hb3 : b3.length = 96) (hd0 : d0.length = 48) (hd1 : d1.length = 32) (hd2 : d2.length = 8) (hd3 : d3.length = 96) (hd4 : d4.length = 8)
    (p0 p1 p3 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l48 l56 l32 l80 l64 l72 l88 l40 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8) (hl48 : l48.length = 8) (hl56 : l56.length = 8) (hl32 : l32.length = 8) (hl80 : l80.length = 8) (hl64 : l64.length = 8) (hl72 : l72.length = 8) (hl88 : l88.length = 8) (hl40 : l40.length = 8) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (l56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (l80.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (l64.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (l72.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (l88.At (s.regs.rsp.toBitVec - 88))
      ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 184))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq (v2.At (s.regs.rax.toBitVec + 56))
      ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
      ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 72))
      ⋆ Eq (c3.At (s.regs.rax.toBitVec + 80))
      ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
      ⋆ Eq (b0.At p0)
      ⋆ Eq (b1.At p1)
      ⋆ Eq (b3.At p3)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
      ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
      ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 184))
      ⋆ R)
    (hguard : guard.toNat + 48 < s.regs.rsp.toNat) (hsp : 184 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 192 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveC S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 9)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 176 }
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
          ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (l56.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (l80.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (l64.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (l72.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (l88.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 184))
          ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
          ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 184))
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 hast hv2 hv4 hc0 hc1 hc3 hb0 hb1 hb3 hd0 hd1 hd2 hd3 hd4 p0 p1 p3 s ra guard hpre fp s1 s2 l16 l48 l56 l32 l80 l64 l72 l88 l40 rslot hfp hs1 hs2 hl16 hl48 hl56 hl32 hl80 hl64 hl72 hl88 hl40 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hcap hcap63 hpre ⊢
  have hcap' : rcx.toBitVec.toNat + 192 ≤ rdi.toBitVec.toNat := hcap
  apply encpro_l _ _ _ (-48) 48 _ k (k + 7) (win hk 0 7) (by rfl) (by rfl) (by rfl) guard fp hfp _ _ _ (by dsimp only; ecancel) hguard
  intro m1 H1 fl1; kn; dsimp only at H1
  apply kstep_sub_i Reg64.rsp 168 _ (k + 7) (k + 8) (win hk 7 1) (by rfl) (by rfl)
  intro fl; kn
  apply kreg_eq Reg64.rsp (rsp.toBitVec - 176) _ _ _ (by show ((rsp.toBitVec - 8) - 168 : BitVec 64) = (rsp.toBitVec - 176); bv_omega)
  kn
  apply kstep_st Reg64.rbx Reg64.rsp 192 _ (k + 8) (k + 9) (win hk 8 1) (by rfl) (by rfl)
    (rsp.toBitVec - 176) (rsp.toBitVec + 16) (by eb) s2 hs2 _ _ _ (by rfl) (by ecancel)
  intro m2 H2; kn; simp only [Reg64s.get64] at H2
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem dpr_g6e_head_kind : ∀ (h : Host), type_of% (@dpr_g6e_head h)
    = @E2eScal.encHeadKindN h DprMarshal E2eScal.Gen6Enc.dpr_g6e_layout [.bytes 48, .bytes 32, .u64, .bytes 96, .u64]
    ⟨9, 0, [(.rax, .rcv), (.rbx, .ptr), (.rcx, .len 0), (.rdi, .cap)],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.orig 1), .at (.up 16) (.reg .rbx), .at (.dn 16) (.orig 3), .at (.dn 48) (.orig 4), .at (.dn 56) (.orig 5), .at (.dn 32) (.orig 6), .at (.dn 80) (.orig 7), .at (.dn 64) (.orig 8), .at (.dn 72) (.orig 9), .at (.dn 88) (.orig 10), .at (.dn 40) (.orig 11), .at (.dn 184) (.orig 12), .lo .scr],
      []⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 0 `Pubkey` (48 bytes): directives 9–37; boundary state 0 → 1. -/
theorem dpr_g6e_f0 : ∀ (k : Nat) (hk : DprMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh DprMarshal k)
    (ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 : List UInt8) (hast : ast.length = 8) (hv2 : v2.length = 8) (hv4 : v4.length = 8) (hc0 : c0.length = 8) (hc1 : c1.length = 8) (hc3 : c3.length = 8) (hb0 : b0.length = 48) (hb1 : b1.length = 32) (hb3 : b3.length = 96) (hd0 : d0.length = 48) (hd1 : d1.length = 32) (hd2 : d2.length = 8) (hd3 : d3.length = 96) (hd4 : d4.length = 8)
    (p0 p1 p3 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l48 l56 l32 l80 l64 l72 l88 l40 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8) (hl48 : l48.length = 8) (hl56 : l56.length = 8) (hl32 : l32.length = 8) (hl80 : l80.length = 8) (hl64 : l64.length = 8) (hl72 : l72.length = 8) (hl88 : l88.length = 8) (hl40 : l40.length = 8) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 184 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 192 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveC S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 9)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 176 }
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
          ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (l56.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (l80.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (l64.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (l72.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (l88.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 184))
          ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
          ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 184))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 38)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 176 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 : List UInt8), x0.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (l80.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (l64.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (l72.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (l88.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 38)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 184))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
          ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 184))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 hast hv2 hv4 hc0 hc1 hc3 hb0 hb1 hb3 hd0 hd1 hd2 hd3 hd4 p0 p1 p3 s ra guard hpre fp s1 s2 l16 l48 l56 l32 l80 l64 l72 l88 l40 rslot hfp hs1 hs2 hl16 hl48 hl56 hl32 hl80 hl64 hl72 hl88 hl40 hrslot R S scratch hsc hsp hcap hcap63 hmm
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
  have hcap' : rcx.toBitVec.toNat + 192 ≤ rdi.toBitVec.toNat := hcap
  apply kstep_ldv Reg64.rdx Reg64.rax 8 _ (k + 9) (k + 10) (win hk 9 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 8) p0 (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_lenchk Reg64.rax 16 48 _ _ (k + 10) (k + 12) (win hk 10 2) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 16) (by eb) (Int.toBytes 8 48) (by rfl) (by decide) _ _ _ (by rfl) (by ecancel)
  intro fl; kn
  apply kstep_st Reg64.rax Reg64.rsp 184 _ (k + 12) (k + 13) (win hk 12 1) (by rfl) (by rfl)
    (rsp.toBitVec - 176) (rsp.toBitVec + 8) (by eb) s1 hs1 _ _ _ (by rfl) (by ecancel)
  intro m3 H3; kn; simp only [Reg64s.get64] at H3
  apply kstep_lea Reg64.r8 Reg64.rcx 48 _ (k + 13) (k + 14) (win hk 13 1) (by rfl) (by rfl)
  kn
  apply kreg_eq Reg64.r8 (rcx.toBitVec + 48) _ _ _ (by show (rcx.toBitVec + 48 : BitVec 64) = (rcx.toBitVec + 48); bv_omega)
  kn
  have hl30 := Fk.label_at' hk hf (j := 30)
    (by simp only [DprMarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [DprMarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply kstep_cmp_jae_t Reg64.rdi Reg64.r8 _ _ (k + 14) (k + 30) (win hk 14 3) (by rfl) hl30 _ _ (by show ((rcx.toBitVec + 48) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; kn
  apply kstep_label _ _ (k + 30) (k + 31) (win hk 30 1) (by rfl) (by rfl)
  apply kstep_st Reg64.rbx Reg64.rsp 160 _ (k + 31) (k + 32) (win hk 31 1) (by rfl) (by rfl)
    (rsp.toBitVec - 176) (rsp.toBitVec - 16) (by eb) l16 hl16 _ _ _ (by rfl) (by ecancel)
  intro m4 H4; kn; simp only [Reg64s.get64] at H4
  apply kstep_st Reg64.r8 Reg64.rsp 128 _ (k + 32) (k + 33) (win hk 32 1) (by rfl) (by rfl)
    (rsp.toBitVec - 176) (rsp.toBitVec - 48) (by eb) l48 hl48 _ _ _ (by rfl) (by ecancel)
  intro m5 H5; kn; simp only [Reg64s.get64] at H5
  apply kstep_st Reg64.rdi Reg64.rsp 120 _ (k + 33) (k + 34) (win hk 33 1) (by rfl) (by rfl)
    (rsp.toBitVec - 176) (rsp.toBitVec - 56) (by eb) l56 hl56 _ _ _ (by rfl) (by ecancel)
  intro m6 H6; kn; simp only [Reg64s.get64] at H6
  apply kstep_lea_idx Reg64.rax Reg64.rcx Reg64.rbx _ (k + 34) (k + 35) (win hk 34 1) (by rfl) (by rfl)
  kn
  apply kreg_eq Reg64.rax (rbx.toBitVec + rcx.toBitVec) _ _ _ (by show (rcx.toBitVec + rbx.toBitVec : BitVec 64) = (rbx.toBitVec + rcx.toBitVec); bv_omega)
  kn
  apply kstep_mov_rr Reg64.rbx Reg64.rdx _ (k + 35) (k + 36) (win hk 35 1) (by rfl) (by rfl)
  kn
  apply kstep_movi Reg64.rcx 48 _ (k + 36) (k + 37) (win hk 36 1) (by rfl) (by rfl)
  kn
  apply kreg_eq Reg64.rcx 48 _ _ _ (by show (BitVec.zeroExtend 64 (BitVec.truncate 32 (48 : BitVec 64)) : BitVec 64) = 48; decide)
  kn
  refine eventually_trans _ _ _ _ (encn_call (k + 37) (win hk 37 1) (rsp.toBitVec - 176) (rbx.toBitVec + rcx.toBitVec) p0
    (rsp.toBitVec - 184) (rsp.toBitVec - 184 - BitVec.ofNat 64 S) S (by bv_omega) (E2eScal.g5_lo0 rsp.toBitVec 176 184 S (by decide))
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
theorem dpr_g6e_f0_kind : ∀ (h : Host), type_of% (@dpr_g6e_f0 h)
    = @E2eScal.encFieldKindN h DprMarshal E2eScal.Gen6Enc.dpr_g6e_layout [.bytes 48, .bytes 32, .u64, .bytes 96, .u64]
    ⟨9, 0, [(.rax, .rcv), (.rbx, .ptr), (.rcx, .len 0), (.rdi, .cap)],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.orig 1), .at (.up 16) (.reg .rbx), .at (.dn 16) (.orig 3), .at (.dn 48) (.orig 4), .at (.dn 56) (.orig 5), .at (.dn 32) (.orig 6), .at (.dn 80) (.orig 7), .at (.dn 64) (.orig 8), .at (.dn 72) (.orig 9), .at (.dn 88) (.orig 10), .at (.dn 40) (.orig 11), .at (.dn 184) (.orig 12), .lo .scr],
      []⟩
    ⟨38, 1, [],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 16) (.reg .rbx), .at (.dn 48) (.len 48), .at (.dn 56) (.reg .rdi), .at (.dn 32) (.orig 6), .at (.dn 80) (.orig 7), .at (.dn 64) (.orig 8), .at (.dn 72) (.orig 9), .at (.dn 88) (.orig 10), .at (.dn 40) (.orig 11), .at (.dn 184) (.ret 38), .lo (.ex 0)],
      [.lo]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 1 `WithdrawalCredentials` (32 bytes): directives 38–66; boundary state 1 → 2. -/
theorem dpr_g6e_f1 : ∀ (k : Nat) (hk : DprMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh DprMarshal k)
    (ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 : List UInt8) (hast : ast.length = 8) (hv2 : v2.length = 8) (hv4 : v4.length = 8) (hc0 : c0.length = 8) (hc1 : c1.length = 8) (hc3 : c3.length = 8) (hb0 : b0.length = 48) (hb1 : b1.length = 32) (hb3 : b3.length = 96) (hd0 : d0.length = 48) (hd1 : d1.length = 32) (hd2 : d2.length = 8) (hd3 : d3.length = 96) (hd4 : d4.length = 8)
    (p0 p1 p3 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l48 l56 l32 l80 l64 l72 l88 l40 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8) (hl48 : l48.length = 8) (hl56 : l56.length = 8) (hl32 : l32.length = 8) (hl80 : l80.length = 8) (hl64 : l64.length = 8) (hl72 : l72.length = 8) (hl88 : l88.length = 8) (hl40 : l40.length = 8) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 184 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 192 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveC S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 38)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 176 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 : List UInt8), x0.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (l80.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (l64.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (l72.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (l88.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 38)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 184))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
          ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 184))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 67)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 176 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 : List UInt8), x0.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 80).toInt).At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (l72.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (l88.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 67)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 184))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
          ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 184))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 hast hv2 hv4 hc0 hc1 hc3 hb0 hb1 hb3 hd0 hd1 hd2 hd3 hd4 p0 p1 p3 s ra guard hpre fp s1 s2 l16 l48 l56 l32 l80 l64 l72 l88 l40 rslot hfp hs1 hs2 hl16 hl48 hl56 hl32 hl80 hl64 hl72 hl88 hl40 hrslot R S scratch hsc hsp hcap hcap63 hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hsp hcap hcap63 hpre ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, x0, hx0, Hm⟩
  dsimp only at hpc hrsp hrbp hr14  Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14  Hm
  subst rsp1 rbp1 r141
  have hcap' : rcx.toBitVec.toNat + 192 ≤ rdi.toBitVec.toNat := hcap
  apply kstep_ldv Reg64.rdx Reg64.rsp 184 _ (k + 38) (k + 39) (win hk 38 1) (by rfl) (by rfl)
    (rsp.toBitVec - 176) (rsp.toBitVec + 8) rax.toBitVec (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_ldv Reg64.rbx Reg64.rdx 32 _ (k + 39) (k + 40) (win hk 39 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 32) p1 (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_lenchk Reg64.rdx 40 32 _ _ (k + 40) (k + 43) (win hk 40 3) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 40) (by eb) (Int.toBytes 8 32) (by rfl) (by decide) _ _ _ (by rfl) (by ecancel)
  intro fl; kn
  apply kstep_ldv Reg64.r8 Reg64.rsp 128 _ (k + 43) (k + 44) (win hk 43 1) (by rfl) (by rfl)
    (rsp.toBitVec - 176) (rsp.toBitVec - 48) (rcx.toBitVec + 48) (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_lea Reg64.r9 Reg64.r8 32 _ (k + 44) (k + 45) (win hk 44 1) (by rfl) (by rfl)
  kn
  apply kreg_eq Reg64.r9 (rcx.toBitVec + 80) _ _ _ (by show ((rcx.toBitVec + 48) + 32 : BitVec 64) = (rcx.toBitVec + 80); bv_omega)
  kn
  apply kstep_ldv Reg64.rcx Reg64.rsp 120 _ (k + 45) (k + 46) (win hk 45 1) (by rfl) (by rfl)
    (rsp.toBitVec - 176) (rsp.toBitVec - 56) rdi.toBitVec (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_cmp_jb_f Reg64.rcx Reg64.r9 _ _ (k + 46) (k + 48) (win hk 46 2) (by rfl) (by rfl) _ _ (by show ((rcx.toBitVec + 80) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; kn
  apply kstep_ldv Reg64.rax Reg64.rsp 160 _ (k + 48) (k + 49) (win hk 48 1) (by rfl) (by rfl)
    (rsp.toBitVec - 176) (rsp.toBitVec - 16) rbx.toBitVec (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  have hl60 := Fk.label_at' hk hf (j := 60)
    (by simp only [DprMarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [DprMarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply kstep_jmp _ _ (k + 49) (k + 60) (win hk 49 1) (by rfl) hl60
  apply kstep_label _ _ (k + 60) (k + 61) (win hk 60 1) (by rfl) (by rfl)
  apply kstep_st Reg64.rax Reg64.rsp 144 _ (k + 61) (k + 62) (win hk 61 1) (by rfl) (by rfl)
    (rsp.toBitVec - 176) (rsp.toBitVec - 32) (by eb) l32 hl32 _ _ _ (by rfl) (by ecancel)
  intro m7 H7; kn; simp only [Reg64s.get64] at H7
  apply kstep_st Reg64.r9 Reg64.rsp 96 _ (k + 62) (k + 63) (win hk 62 1) (by rfl) (by rfl)
    (rsp.toBitVec - 176) (rsp.toBitVec - 80) (by eb) l80 hl80 _ _ _ (by rfl) (by ecancel)
  intro m8 H8; kn; simp only [Reg64s.get64] at H8
  apply kstep_st Reg64.rcx Reg64.rsp 112 _ (k + 63) (k + 64) (win hk 63 1) (by rfl) (by rfl)
    (rsp.toBitVec - 176) (rsp.toBitVec - 64) (by eb) l64 hl64 _ _ _ (by rfl) (by ecancel)
  intro m9 H9; kn; simp only [Reg64s.get64] at H9
  apply kstep_add_rr Reg64.rax Reg64.r8 _ (k + 64) (k + 65) (win hk 64 1) (by rfl) (by rfl)
  intro fl; kn
  apply kreg_eq Reg64.rax (rbx.toBitVec + rcx.toBitVec + 48) _ _ _ (by show (rbx.toBitVec + (rcx.toBitVec + 48) : BitVec 64) = (rbx.toBitVec + rcx.toBitVec + 48); bv_omega)
  kn
  apply kstep_movi Reg64.rcx 32 _ (k + 65) (k + 66) (win hk 65 1) (by rfl) (by rfl)
  kn
  apply kreg_eq Reg64.rcx 32 _ _ _ (by show (BitVec.zeroExtend 64 (BitVec.truncate 32 (32 : BitVec 64)) : BitVec 64) = 32; decide)
  kn
  refine eventually_trans _ _ _ _ (encn_call (k + 66) (win hk 66 1) (rsp.toBitVec - 176) (rbx.toBitVec + rcx.toBitVec + 48) p1
    (rsp.toBitVec - 184) (rsp.toBitVec - 184 - BitVec.ofNat 64 S) S (by bv_omega) (E2eScal.g5_lo0 rsp.toBitVec 176 184 S (by decide))
    b1 d1 (Int.toBytes 8 (Host.addrOf (k + 38)).toBitVec.toInt) x0 (by rw [hd1, hb1]) (Int.toBytes_length 8 _) hx0
    _ _ (by rfl) (by rfl) (by rfl) (by rw [hb1]; rfl) (by first | ecancel | (dsimp only; ecancel)) hmm) ?_
  rintro ⟨e2, pc2⟩ ⟨hpc2, hrsp2, hrbp2, hr142, scr2, hscr2, Hc2⟩
  dsimp only at hpc2 hrsp2 hrbp2 hr142 Hc2
  subst hpc2
  obtain ⟨⟨raxc2, rbxc2, rcxc2, rdxc2, rsic2, rdic2, rspc2, rbpc2, r8c2, r9c2, r10c2, r11c2, r12c2, r13c2, r14c2, r15c2⟩, zmmsc2, flagsc2, memc2⟩ := e2
  simp only at hrsp2 hrbp2 hr142 Hc2
  subst rspc2 rbpc2 r14c2
  rw [show k + 66 + 1 = k + 67 from rfl] at Hc2
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, scr2, hscr2, ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem dpr_g6e_f1_kind : ∀ (h : Host), type_of% (@dpr_g6e_f1 h)
    = @E2eScal.encFieldKindN h DprMarshal E2eScal.Gen6Enc.dpr_g6e_layout [.bytes 48, .bytes 32, .u64, .bytes 96, .u64]
    ⟨38, 1, [],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 16) (.reg .rbx), .at (.dn 48) (.len 48), .at (.dn 56) (.reg .rdi), .at (.dn 32) (.orig 6), .at (.dn 80) (.orig 7), .at (.dn 64) (.orig 8), .at (.dn 72) (.orig 9), .at (.dn 88) (.orig 10), .at (.dn 40) (.orig 11), .at (.dn 184) (.ret 38), .lo (.ex 0)],
      [.lo]⟩
    ⟨67, 2, [],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 16) (.reg .rbx), .at (.dn 48) (.len 48), .at (.dn 56) (.reg .rdi), .at (.dn 32) (.reg .rbx), .at (.dn 80) (.len 80), .at (.dn 64) (.reg .rdi), .at (.dn 72) (.orig 9), .at (.dn 88) (.orig 10), .at (.dn 40) (.orig 11), .at (.dn 184) (.ret 67), .lo (.ex 0)],
      [.lo]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 2 `Amount` (uint64): directives 67–86; boundary state 2 → 3. -/
theorem dpr_g6e_f2 : ∀ (k : Nat) (hk : DprMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh DprMarshal k)
    (ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 : List UInt8) (hast : ast.length = 8) (hv2 : v2.length = 8) (hv4 : v4.length = 8) (hc0 : c0.length = 8) (hc1 : c1.length = 8) (hc3 : c3.length = 8) (hb0 : b0.length = 48) (hb1 : b1.length = 32) (hb3 : b3.length = 96) (hd0 : d0.length = 48) (hd1 : d1.length = 32) (hd2 : d2.length = 8) (hd3 : d3.length = 96) (hd4 : d4.length = 8)
    (p0 p1 p3 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l48 l56 l32 l80 l64 l72 l88 l40 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8) (hl48 : l48.length = 8) (hl56 : l56.length = 8) (hl32 : l32.length = 8) (hl80 : l80.length = 8) (hl64 : l64.length = 8) (hl72 : l72.length = 8) (hl88 : l88.length = 8) (hl40 : l40.length = 8) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 184 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 192 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveC S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 67)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 176 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 : List UInt8), x0.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 80).toInt).At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (l72.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (l88.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 67)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 184))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
          ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 184))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 87)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 176 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.get64 Reg64.rax = s.regs.rbx.toBitVec
        ∧ st.data.regs.get64 Reg64.rbx = s.regs.rcx.toBitVec + 88
        ∧ st.data.regs.get64 Reg64.rcx = s.regs.rdi.toBitVec
        ∧ st.data.regs.get64 Reg64.rdx = s.regs.rax.toBitVec ∧
        ∃ (x0 : List UInt8), x0.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 80).toInt).At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (l72.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (l88.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 67)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 184))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
          ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 184))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 hast hv2 hv4 hc0 hc1 hc3 hb0 hb1 hb3 hd0 hd1 hd2 hd3 hd4 p0 p1 p3 s ra guard hpre fp s1 s2 l16 l48 l56 l32 l80 l64 l72 l88 l40 rslot hfp hs1 hs2 hl16 hl48 hl56 hl32 hl80 hl64 hl72 hl88 hl40 hrslot R S scratch hsc hsp hcap hcap63 hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hsp hcap hcap63 hpre ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, x0, hx0, Hm⟩
  dsimp only at hpc hrsp hrbp hr14  Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14  Hm
  subst rsp1 rbp1 r141
  have hcap' : rcx.toBitVec.toNat + 192 ≤ rdi.toBitVec.toNat := hcap
  apply kstep_ldv Reg64.rbx Reg64.rsp 96 _ (k + 67) (k + 68) (win hk 67 1) (by rfl) (by rfl)
    (rsp.toBitVec - 176) (rsp.toBitVec - 80) (rcx.toBitVec + 80) (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_add Reg64.rbx 8 _ (k + 68) (k + 69) (win hk 68 1) (by rfl) (by rfl)
  intro fl; kn
  apply kreg_eq Reg64.rbx (rcx.toBitVec + 88) _ _ _ (by show ((rcx.toBitVec + 80) + 8 : BitVec 64) = (rcx.toBitVec + 88); bv_omega)
  kn
  apply kstep_ldv Reg64.rdx Reg64.rsp 184 _ (k + 69) (k + 70) (win hk 69 1) (by rfl) (by rfl)
    (rsp.toBitVec - 176) (rsp.toBitVec + 8) rax.toBitVec (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_ldb Reg64.rsi Reg64.rdx 56 _ (k + 70) (k + 71) (win hk 70 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 56) (by eb) v2 hv2 _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_ldv Reg64.rcx Reg64.rsp 112 _ (k + 71) (k + 72) (win hk 71 1) (by rfl) (by rfl)
    (rsp.toBitVec - 176) (rsp.toBitVec - 64) rdi.toBitVec (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_cmp_jb_f Reg64.rcx Reg64.rbx _ _ (k + 72) (k + 74) (win hk 72 2) (by rfl) (by rfl) _ _ (by show ((rcx.toBitVec + 88) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; kn
  apply kstep_ldv Reg64.rax Reg64.rsp 144 _ (k + 74) (k + 75) (win hk 74 1) (by rfl) (by rfl)
    (rsp.toBitVec - 176) (rsp.toBitVec - 32) rbx.toBitVec (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  have hl85 := Fk.label_at' hk hf (j := 85)
    (by simp only [DprMarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [DprMarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply kstep_jmp _ _ (k + 75) (k + 85) (win hk 75 1) (by rfl) hl85
  apply kstep_label _ _ (k + 85) (k + 86) (win hk 85 1) (by rfl) (by rfl)
  apply kstep_st_idx Reg64.rsi Reg64.rbx Reg64.rax (-8) _ (k + 86) (k + 87) (win hk 86 1) (by rfl) (by rfl)
    (rcx.toBitVec + 88) rbx.toBitVec (rbx.toBitVec + rcx.toBitVec + 80) (by eb) d2 hd2 _ _ _ (by rfl) (by rfl) (by ecancel)
  intro m10 H10; kn; simp only [Reg64s.get64] at H10
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v2 hv2] at H10
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, x0, hx0, ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem dpr_g6e_f2_kind : ∀ (h : Host), type_of% (@dpr_g6e_f2 h)
    = @E2eScal.encFieldKindN h DprMarshal E2eScal.Gen6Enc.dpr_g6e_layout [.bytes 48, .bytes 32, .u64, .bytes 96, .u64]
    ⟨67, 2, [],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 16) (.reg .rbx), .at (.dn 48) (.len 48), .at (.dn 56) (.reg .rdi), .at (.dn 32) (.reg .rbx), .at (.dn 80) (.len 80), .at (.dn 64) (.reg .rdi), .at (.dn 72) (.orig 9), .at (.dn 88) (.orig 10), .at (.dn 40) (.orig 11), .at (.dn 184) (.ret 67), .lo (.ex 0)],
      [.lo]⟩
    ⟨87, 3, [(.rax, .ptr), (.rbx, .len 88), (.rcx, .cap), (.rdx, .rcv)],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 16) (.reg .rbx), .at (.dn 48) (.len 48), .at (.dn 56) (.reg .rdi), .at (.dn 32) (.reg .rbx), .at (.dn 80) (.len 80), .at (.dn 64) (.reg .rdi), .at (.dn 72) (.orig 9), .at (.dn 88) (.orig 10), .at (.dn 40) (.orig 11), .at (.dn 184) (.ret 67), .lo (.ex 0)],
      [.lo]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 3 `Signature` (96 bytes): directives 87–110; boundary state 3 → 4. -/
theorem dpr_g6e_f3 : ∀ (k : Nat) (hk : DprMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh DprMarshal k)
    (ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 : List UInt8) (hast : ast.length = 8) (hv2 : v2.length = 8) (hv4 : v4.length = 8) (hc0 : c0.length = 8) (hc1 : c1.length = 8) (hc3 : c3.length = 8) (hb0 : b0.length = 48) (hb1 : b1.length = 32) (hb3 : b3.length = 96) (hd0 : d0.length = 48) (hd1 : d1.length = 32) (hd2 : d2.length = 8) (hd3 : d3.length = 96) (hd4 : d4.length = 8)
    (p0 p1 p3 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l48 l56 l32 l80 l64 l72 l88 l40 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8) (hl48 : l48.length = 8) (hl56 : l56.length = 8) (hl32 : l32.length = 8) (hl80 : l80.length = 8) (hl64 : l64.length = 8) (hl72 : l72.length = 8) (hl88 : l88.length = 8) (hl40 : l40.length = 8) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 184 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 192 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveC S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 87)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 176 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14
        ∧ st0.data.regs.get64 Reg64.rax = s.regs.rbx.toBitVec
        ∧ st0.data.regs.get64 Reg64.rbx = s.regs.rcx.toBitVec + 88
        ∧ st0.data.regs.get64 Reg64.rcx = s.regs.rdi.toBitVec
        ∧ st0.data.regs.get64 Reg64.rdx = s.regs.rax.toBitVec ∧
        ∃ (x0 : List UInt8), x0.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 80).toInt).At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (l72.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (l88.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 67)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 184))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
          ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 184))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 111)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 176 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 : List UInt8), x0.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 80).toInt).At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 184).toInt).At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 111)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 184))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
          ⋆ Eq (b3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 184))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 hast hv2 hv4 hc0 hc1 hc3 hb0 hb1 hb3 hd0 hd1 hd2 hd3 hd4 p0 p1 p3 s ra guard hpre fp s1 s2 l16 l48 l56 l32 l80 l64 l72 l88 l40 rslot hfp hs1 hs2 hl16 hl48 hl56 hl32 hl80 hl64 hl72 hl88 hl40 hrslot R S scratch hsc hsp hcap hcap63 hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hsp hcap hcap63 hpre ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, hrrax, hrrbx, hrrcx, hrrdx, x0, hx0, Hm⟩
  dsimp only at hpc hrsp hrbp hr14 hrrax hrrbx hrrcx hrrdx Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14 hrrax hrrbx hrrcx hrrdx Hm
  subst rsp1 rbp1 r141
  obtain rfl : rbx = rax1 := (UInt64.toBitVec_inj.mp hrrax).symm
  obtain rfl : rbx1 = { toBitVec := rcx.toBitVec + 88 } := UInt64.toBitVec_inj.mp hrrbx
  obtain rfl : rdi = rcx1 := (UInt64.toBitVec_inj.mp hrrcx).symm
  obtain rfl : rax = rdx1 := (UInt64.toBitVec_inj.mp hrrdx).symm
  have hcap' : rcx.toBitVec.toNat + 192 ≤ rdi.toBitVec.toNat := hcap
  apply kstep_ldv Reg64.r8 Reg64.rdx 64 _ (k + 87) (k + 88) (win hk 87 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 64) p3 (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_lenchk Reg64.rdx 72 96 _ _ (k + 88) (k + 90) (win hk 88 2) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 72) (by eb) (Int.toBytes 8 96) (by rfl) (by decide) _ _ _ (by rfl) (by ecancel)
  intro fl; kn
  apply kstep_lea Reg64.r9 Reg64.rbx 96 _ (k + 90) (k + 91) (win hk 90 1) (by rfl) (by rfl)
  kn
  apply kreg_eq Reg64.r9 (rcx.toBitVec + 184) _ _ _ (by show ((rcx.toBitVec + 88) + 96 : BitVec 64) = (rcx.toBitVec + 184); bv_omega)
  kn
  have hl102 := Fk.label_at' hk hf (j := 102)
    (by simp only [DprMarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [DprMarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply kstep_cmp_jae_t Reg64.rcx Reg64.r9 _ _ (k + 91) (k + 102) (win hk 91 2) (by rfl) hl102 _ _ (by show ((rcx.toBitVec + 184) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; kn
  apply kstep_label _ _ (k + 102) (k + 103) (win hk 102 1) (by rfl) (by rfl)
  apply kstep_st Reg64.rcx Reg64.rsp 104 _ (k + 103) (k + 104) (win hk 103 1) (by rfl) (by rfl)
    (rsp.toBitVec - 176) (rsp.toBitVec - 72) (by eb) l72 hl72 _ _ _ (by rfl) (by ecancel)
  intro m11 H11; kn; simp only [Reg64s.get64] at H11
  apply kstep_st Reg64.r9 Reg64.rsp 88 _ (k + 104) (k + 105) (win hk 104 1) (by rfl) (by rfl)
    (rsp.toBitVec - 176) (rsp.toBitVec - 88) (by eb) l88 hl88 _ _ _ (by rfl) (by ecancel)
  intro m12 H12; kn; simp only [Reg64s.get64] at H12
  apply kstep_st Reg64.rax Reg64.rsp 136 _ (k + 105) (k + 106) (win hk 105 1) (by rfl) (by rfl)
    (rsp.toBitVec - 176) (rsp.toBitVec - 40) (by eb) l40 hl40 _ _ _ (by rfl) (by ecancel)
  intro m13 H13; kn; simp only [Reg64s.get64] at H13
  apply kstep_add_rr Reg64.rax Reg64.rbx _ (k + 106) (k + 107) (win hk 106 1) (by rfl) (by rfl)
  intro fl; kn
  apply kreg_eq Reg64.rax (rbx.toBitVec + rcx.toBitVec + 88) _ _ _ (by show (rbx.toBitVec + (rcx.toBitVec + 88) : BitVec 64) = (rbx.toBitVec + rcx.toBitVec + 88); bv_omega)
  kn
  apply kstep_mov_rr Reg64.rbx Reg64.r8 _ (k + 107) (k + 108) (win hk 107 1) (by rfl) (by rfl)
  kn
  apply kstep_movi Reg64.rcx 96 _ (k + 108) (k + 109) (win hk 108 1) (by rfl) (by rfl)
  kn
  apply kreg_eq Reg64.rcx 96 _ _ _ (by show (BitVec.zeroExtend 64 (BitVec.truncate 32 (96 : BitVec 64)) : BitVec 64) = 96; decide)
  kn
  apply kstep_nops _ (k + 109) (k + 110) (win hk 109 1) (by rfl) (by rfl)
  refine eventually_trans _ _ _ _ (encn_call (k + 110) (win hk 110 1) (rsp.toBitVec - 176) (rbx.toBitVec + rcx.toBitVec + 88) p3
    (rsp.toBitVec - 184) (rsp.toBitVec - 184 - BitVec.ofNat 64 S) S (by bv_omega) (E2eScal.g5_lo0 rsp.toBitVec 176 184 S (by decide))
    b3 d3 (Int.toBytes 8 (Host.addrOf (k + 67)).toBitVec.toInt) x0 (by rw [hd3, hb3]) (Int.toBytes_length 8 _) hx0
    _ _ (by rfl) (by rfl) (by rfl) (by rw [hb3]; rfl) (by first | ecancel | (dsimp only; ecancel)) hmm) ?_
  rintro ⟨e3, pc3⟩ ⟨hpc3, hrsp3, hrbp3, hr143, scr3, hscr3, Hc3⟩
  dsimp only at hpc3 hrsp3 hrbp3 hr143 Hc3
  subst hpc3
  obtain ⟨⟨raxc3, rbxc3, rcxc3, rdxc3, rsic3, rdic3, rspc3, rbpc3, r8c3, r9c3, r10c3, r11c3, r12c3, r13c3, r14c3, r15c3⟩, zmmsc3, flagsc3, memc3⟩ := e3
  simp only at hrsp3 hrbp3 hr143 Hc3
  subst rspc3 rbpc3 r14c3
  rw [show k + 110 + 1 = k + 111 from rfl] at Hc3
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, scr3, hscr3, ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem dpr_g6e_f3_kind : ∀ (h : Host), type_of% (@dpr_g6e_f3 h)
    = @E2eScal.encFieldKindN h DprMarshal E2eScal.Gen6Enc.dpr_g6e_layout [.bytes 48, .bytes 32, .u64, .bytes 96, .u64]
    ⟨87, 3, [(.rax, .ptr), (.rbx, .len 88), (.rcx, .cap), (.rdx, .rcv)],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 16) (.reg .rbx), .at (.dn 48) (.len 48), .at (.dn 56) (.reg .rdi), .at (.dn 32) (.reg .rbx), .at (.dn 80) (.len 80), .at (.dn 64) (.reg .rdi), .at (.dn 72) (.orig 9), .at (.dn 88) (.orig 10), .at (.dn 40) (.orig 11), .at (.dn 184) (.ret 67), .lo (.ex 0)],
      [.lo]⟩
    ⟨111, 4, [],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 16) (.reg .rbx), .at (.dn 48) (.len 48), .at (.dn 56) (.reg .rdi), .at (.dn 32) (.reg .rbx), .at (.dn 80) (.len 80), .at (.dn 64) (.reg .rdi), .at (.dn 72) (.reg .rdi), .at (.dn 88) (.len 184), .at (.dn 40) (.reg .rbx), .at (.dn 184) (.ret 111), .lo (.ex 0)],
      [.lo]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 4 `Index` (uint64): directives 111–129; boundary state 4 → 5. -/
theorem dpr_g6e_f4 : ∀ (k : Nat) (hk : DprMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh DprMarshal k)
    (ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 : List UInt8) (hast : ast.length = 8) (hv2 : v2.length = 8) (hv4 : v4.length = 8) (hc0 : c0.length = 8) (hc1 : c1.length = 8) (hc3 : c3.length = 8) (hb0 : b0.length = 48) (hb1 : b1.length = 32) (hb3 : b3.length = 96) (hd0 : d0.length = 48) (hd1 : d1.length = 32) (hd2 : d2.length = 8) (hd3 : d3.length = 96) (hd4 : d4.length = 8)
    (p0 p1 p3 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l48 l56 l32 l80 l64 l72 l88 l40 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8) (hl48 : l48.length = 8) (hl56 : l56.length = 8) (hl32 : l32.length = 8) (hl80 : l80.length = 8) (hl64 : l64.length = 8) (hl72 : l72.length = 8) (hl88 : l88.length = 8) (hl40 : l40.length = 8) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 184 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 192 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveC S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 111)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 176 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 : List UInt8), x0.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 80).toInt).At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 184).toInt).At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 111)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 184))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
          ⋆ Eq (b3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
          ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 184))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 130)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 176 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.get64 Reg64.rax = s.regs.rbx.toBitVec
        ∧ st.data.regs.get64 Reg64.rbx = s.regs.rcx.toBitVec + 192
        ∧ st.data.regs.get64 Reg64.rcx = s.regs.rdi.toBitVec ∧
        ∃ (x0 : List UInt8), x0.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 80).toInt).At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 184).toInt).At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 111)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 184))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
          ⋆ Eq (b3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
          ⋆ Eq (v4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 184))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 hast hv2 hv4 hc0 hc1 hc3 hb0 hb1 hb3 hd0 hd1 hd2 hd3 hd4 p0 p1 p3 s ra guard hpre fp s1 s2 l16 l48 l56 l32 l80 l64 l72 l88 l40 rslot hfp hs1 hs2 hl16 hl48 hl56 hl32 hl80 hl64 hl72 hl88 hl40 hrslot R S scratch hsc hsp hcap hcap63 hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hsp hcap hcap63 hpre ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, x0, hx0, Hm⟩
  dsimp only at hpc hrsp hrbp hr14  Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14  Hm
  subst rsp1 rbp1 r141
  have hcap' : rcx.toBitVec.toNat + 192 ≤ rdi.toBitVec.toNat := hcap
  apply kstep_ldv Reg64.rbx Reg64.rsp 88 _ (k + 111) (k + 112) (win hk 111 1) (by rfl) (by rfl)
    (rsp.toBitVec - 176) (rsp.toBitVec - 88) (rcx.toBitVec + 184) (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_add Reg64.rbx 8 _ (k + 112) (k + 113) (win hk 112 1) (by rfl) (by rfl)
  intro fl; kn
  apply kreg_eq Reg64.rbx (rcx.toBitVec + 192) _ _ _ (by show ((rcx.toBitVec + 184) + 8 : BitVec 64) = (rcx.toBitVec + 192); bv_omega)
  kn
  apply kstep_ldv Reg64.rdx Reg64.rsp 184 _ (k + 113) (k + 114) (win hk 113 1) (by rfl) (by rfl)
    (rsp.toBitVec - 176) (rsp.toBitVec + 8) rax.toBitVec (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_ldb Reg64.rdx Reg64.rdx 88 _ (k + 114) (k + 115) (win hk 114 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 88) (by eb) v4 hv4 _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_ldv Reg64.rcx Reg64.rsp 104 _ (k + 115) (k + 116) (win hk 115 1) (by rfl) (by rfl)
    (rsp.toBitVec - 176) (rsp.toBitVec - 72) rdi.toBitVec (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_cmp_jb_f Reg64.rcx Reg64.rbx _ _ (k + 116) (k + 119) (win hk 116 3) (by rfl) (by rfl) _ _ (by show ((rcx.toBitVec + 192) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; kn
  apply kstep_ldv Reg64.rax Reg64.rsp 136 _ (k + 119) (k + 120) (win hk 119 1) (by rfl) (by rfl)
    (rsp.toBitVec - 176) (rsp.toBitVec - 40) rbx.toBitVec (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  have hl128 := Fk.label_at' hk hf (j := 128)
    (by simp only [DprMarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [DprMarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply kstep_jmp _ _ (k + 120) (k + 128) (win hk 120 1) (by rfl) hl128
  apply kstep_label _ _ (k + 128) (k + 129) (win hk 128 1) (by rfl) (by rfl)
  apply kstep_st_idx Reg64.rdx Reg64.rbx Reg64.rax (-8) _ (k + 129) (k + 130) (win hk 129 1) (by rfl) (by rfl)
    (rcx.toBitVec + 192) rbx.toBitVec (rbx.toBitVec + rcx.toBitVec + 184) (by eb) d4 hd4 _ _ _ (by rfl) (by rfl) (by ecancel)
  intro m14 H14; kn; simp only [Reg64s.get64] at H14
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v4 hv4] at H14
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, x0, hx0, ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem dpr_g6e_f4_kind : ∀ (h : Host), type_of% (@dpr_g6e_f4 h)
    = @E2eScal.encFieldKindN h DprMarshal E2eScal.Gen6Enc.dpr_g6e_layout [.bytes 48, .bytes 32, .u64, .bytes 96, .u64]
    ⟨111, 4, [],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 16) (.reg .rbx), .at (.dn 48) (.len 48), .at (.dn 56) (.reg .rdi), .at (.dn 32) (.reg .rbx), .at (.dn 80) (.len 80), .at (.dn 64) (.reg .rdi), .at (.dn 72) (.reg .rdi), .at (.dn 88) (.len 184), .at (.dn 40) (.reg .rbx), .at (.dn 184) (.ret 111), .lo (.ex 0)],
      [.lo]⟩
    ⟨130, 5, [(.rax, .ptr), (.rbx, .len 192), (.rcx, .cap)],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 16) (.reg .rbx), .at (.dn 48) (.len 48), .at (.dn 56) (.reg .rdi), .at (.dn 32) (.reg .rbx), .at (.dn 80) (.len 80), .at (.dn 64) (.reg .rdi), .at (.dn 72) (.reg .rdi), .at (.dn 88) (.len 184), .at (.dn 40) (.reg .rbx), .at (.dn 184) (.ret 111), .lo (.ex 0)],
      [.lo]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Epilogue: directives 130–return; boundary state 5 → the fast-path post-state. -/
theorem dpr_g6e_epi : ∀ (k : Nat) (hk : DprMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh DprMarshal k)
    (ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 : List UInt8) (hast : ast.length = 8) (hv2 : v2.length = 8) (hv4 : v4.length = 8) (hc0 : c0.length = 8) (hc1 : c1.length = 8) (hc3 : c3.length = 8) (hb0 : b0.length = 48) (hb1 : b1.length = 32) (hb3 : b3.length = 96) (hd0 : d0.length = 48) (hd1 : d1.length = 32) (hd2 : d2.length = 8) (hd3 : d3.length = 96) (hd4 : d4.length = 8)
    (p0 p1 p3 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l48 l56 l32 l80 l64 l72 l88 l40 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8) (hl48 : l48.length = 8) (hl56 : l56.length = 8) (hl32 : l32.length = 8) (hl80 : l80.length = 8) (hl64 : l64.length = 8) (hl72 : l72.length = 8) (hl88 : l88.length = 8) (hl40 : l40.length = 8) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 184 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 192 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 130)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 176 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14
        ∧ st0.data.regs.get64 Reg64.rax = s.regs.rbx.toBitVec
        ∧ st0.data.regs.get64 Reg64.rbx = s.regs.rcx.toBitVec + 192
        ∧ st0.data.regs.get64 Reg64.rcx = s.regs.rdi.toBitVec ∧
        ∃ (x0 : List UInt8), x0.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 80).toInt).At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 184).toInt).At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 111)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 184))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
          ⋆ Eq (b3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
          ⋆ Eq (v4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 184))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec
        ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 192
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
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 80).toInt).At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 184).toInt).At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 111)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 184))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
          ⋆ Eq (b3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
          ⋆ Eq (v4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 184))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 hast hv2 hv4 hc0 hc1 hc3 hb0 hb1 hb3 hd0 hd1 hd2 hd3 hd4 p0 p1 p3 s ra guard hpre fp s1 s2 l16 l48 l56 l32 l80 l64 l72 l88 l40 rslot hfp hs1 hs2 hl16 hl48 hl56 hl32 hl80 hl64 hl72 hl88 hl40 hrslot R S scratch hsc hsp hcap hcap63
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hsp hcap hcap63 hpre ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, hrrax, hrrbx, hrrcx, x0, hx0, Hm⟩
  dsimp only at hpc hrsp hrbp hr14 hrrax hrrbx hrrcx Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14 hrrax hrrbx hrrcx Hm
  subst rsp1 rbp1 r141
  obtain rfl : rbx = rax1 := (UInt64.toBitVec_inj.mp hrrax).symm
  obtain rfl : rbx1 = { toBitVec := rcx.toBitVec + 192 } := UInt64.toBitVec_inj.mp hrrbx
  obtain rfl : rdi = rcx1 := (UInt64.toBitVec_inj.mp hrrcx).symm
  have hcap' : rcx.toBitVec.toNat + 192 ≤ rdi.toBitVec.toNat := hcap
  apply kstep_xor32 Reg64.rdi _ (k + 130) (k + 131) (win hk 130 1) (by rfl) (by rfl)
  intro fl; kn
  apply kstep_xor32 Reg64.rsi _ (k + 131) (k + 132) (win hk 131 1) (by rfl) (by rfl)
  intro fl; kn
  apply kstep_add Reg64.rsp 168 _ (k + 132) (k + 133) (win hk 132 1) (by rfl) (by rfl)
  intro fl; kn
  apply kreg_eq Reg64.rsp (rsp.toBitVec - 8) _ _ _ (by show ((rsp.toBitVec - 176) + 168 : BitVec 64) = (rsp.toBitVec - 8); bv_omega)
  kn
  refine eventually_trans _ _ _ _ (decret_seg _ (k + 133) (win hk 133 2) (by rfl) (rsp.toBitVec - 8) rsp.toBitVec (by bv_omega) rbp ra _ _ (by rfl) (by ecancel)) ?_
  rintro ⟨d', pc'⟩ ⟨hpc', hrsp', hrbp', hreg', hmem'⟩
  dsimp only at hpc' hrsp' hrbp' hreg' hmem'
  apply Eventually.done
  refine ⟨hpc', ?_, ?_, ?_, ?_, ?_, ?_, hrbp', ?_, x0, hx0, ?_⟩
  · exact UInt64.toBitVec_inj.mp (hreg' Reg64.rax (by decide) (by decide))
  · show d'.regs.rbx.toBitVec.toNat = rcx.toBitVec.toNat + 192
    rw [show d'.regs.rbx.toBitVec = rcx.toBitVec + 192 from hreg' Reg64.rbx (by decide) (by decide)]
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
theorem dpr_g6e_epi_kind : ∀ (h : Host), type_of% (@dpr_g6e_epi h)
    = @E2eScal.encEpiKindN h DprMarshal E2eScal.Gen6Enc.dpr_g6e_layout [.bytes 48, .bytes 32, .u64, .bytes 96, .u64]
    ⟨130, 5, [(.rax, .ptr), (.rbx, .len 192), (.rcx, .cap)],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 16) (.reg .rbx), .at (.dn 48) (.len 48), .at (.dn 56) (.reg .rdi), .at (.dn 32) (.reg .rbx), .at (.dn 80) (.len 80), .at (.dn 64) (.reg .rdi), .at (.dn 72) (.reg .rdi), .at (.dn 88) (.len 184), .at (.dn 40) (.reg .rbx), .at (.dn 184) (.ret 111), .lo (.ex 0)],
      [.lo]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Encoder fast path of `(*v1alpha1.DepositRequest).MarshalSSZTo` (Go 1.26.10), generated** (`p2enc --gen6`):
head, one theorem per field, epilogue, chained by `eventually_trans`. Premises: `len + 192 ≤ cap`,
every byte-vector field of its exact length. Statement = the kind instance (`_kind`). Fast path only. -/
theorem dpr_g6e_fast : ∀ (k : Nat) (hk : DprMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh DprMarshal k)
    (ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 : List UInt8) (hast : ast.length = 8) (hv2 : v2.length = 8) (hv4 : v4.length = 8) (hc0 : c0.length = 8) (hc1 : c1.length = 8) (hc3 : c3.length = 8) (hb0 : b0.length = 48) (hb1 : b1.length = 32) (hb3 : b3.length = 96) (hd0 : d0.length = 48) (hd1 : d1.length = 32) (hd2 : d2.length = 8) (hd3 : d3.length = 96) (hd4 : d4.length = 8)
    (p0 p1 p3 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l48 l56 l32 l80 l64 l72 l88 l40 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8) (hl48 : l48.length = 8) (hl56 : l56.length = 8) (hl32 : l32.length = 8) (hl80 : l80.length = 8) (hl64 : l64.length = 8) (hl72 : l72.length = 8) (hl88 : l88.length = 8) (hl40 : l40.length = 8) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (l56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (l80.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (l64.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (l72.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (l88.At (s.regs.rsp.toBitVec - 88))
      ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 184))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq (v2.At (s.regs.rax.toBitVec + 56))
      ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
      ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 72))
      ⋆ Eq (c3.At (s.regs.rax.toBitVec + 80))
      ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
      ⋆ Eq (b0.At p0)
      ⋆ Eq (b1.At p1)
      ⋆ Eq (b3.At p3)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
      ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
      ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 184))
      ⋆ R)
    (hguard : guard.toNat + 48 < s.regs.rsp.toNat) (hsp : 184 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 192 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveC S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec
        ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 192
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
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 80).toInt).At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 184).toInt).At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 111)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 184))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq (c3.At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (v4.At (s.regs.rax.toBitVec + 88))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (b3.At p3)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (v2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
          ⋆ Eq (b3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
          ⋆ Eq (v4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 184))
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 hast hv2 hv4 hc0 hc1 hc3 hb0 hb1 hb3 hd0 hd1 hd2 hd3 hd4 p0 p1 p3 s ra guard hpre fp s1 s2 l16 l48 l56 l32 l80 l64 l72 l88 l40 rslot hfp hs1 hs2 hl16 hl48 hl56 hl32 hl80 hl64 hl72 hl88 hl40 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm
  refine eventually_trans _ _ _ _ (dpr_g6e_head k hk hf ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 hast hv2 hv4 hc0 hc1 hc3 hb0 hb1 hb3 hd0 hd1 hd2 hd3 hd4 p0 p1 p3 s ra guard hpre fp s1 s2 l16 l48 l56 l32 l80 l64 l72 l88 l40 rslot hfp hs1 hs2 hl16 hl48 hl56 hl32 hl80 hl64 hl72 hl88 hl40 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm) ?_
  intro st0 h0
  refine eventually_trans _ _ _ _ (dpr_g6e_f0 k hk hf ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 hast hv2 hv4 hc0 hc1 hc3 hb0 hb1 hb3 hd0 hd1 hd2 hd3 hd4 p0 p1 p3 s ra guard hpre fp s1 s2 l16 l48 l56 l32 l80 l64 l72 l88 l40 rslot hfp hs1 hs2 hl16 hl48 hl56 hl32 hl80 hl64 hl72 hl88 hl40 hrslot R S scratch hsc hsp hcap hcap63 hmm st0 h0) ?_
  intro st1 h1
  refine eventually_trans _ _ _ _ (dpr_g6e_f1 k hk hf ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 hast hv2 hv4 hc0 hc1 hc3 hb0 hb1 hb3 hd0 hd1 hd2 hd3 hd4 p0 p1 p3 s ra guard hpre fp s1 s2 l16 l48 l56 l32 l80 l64 l72 l88 l40 rslot hfp hs1 hs2 hl16 hl48 hl56 hl32 hl80 hl64 hl72 hl88 hl40 hrslot R S scratch hsc hsp hcap hcap63 hmm st1 h1) ?_
  intro st2 h2
  refine eventually_trans _ _ _ _ (dpr_g6e_f2 k hk hf ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 hast hv2 hv4 hc0 hc1 hc3 hb0 hb1 hb3 hd0 hd1 hd2 hd3 hd4 p0 p1 p3 s ra guard hpre fp s1 s2 l16 l48 l56 l32 l80 l64 l72 l88 l40 rslot hfp hs1 hs2 hl16 hl48 hl56 hl32 hl80 hl64 hl72 hl88 hl40 hrslot R S scratch hsc hsp hcap hcap63 hmm st2 h2) ?_
  intro st3 h3
  refine eventually_trans _ _ _ _ (dpr_g6e_f3 k hk hf ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 hast hv2 hv4 hc0 hc1 hc3 hb0 hb1 hb3 hd0 hd1 hd2 hd3 hd4 p0 p1 p3 s ra guard hpre fp s1 s2 l16 l48 l56 l32 l80 l64 l72 l88 l40 rslot hfp hs1 hs2 hl16 hl48 hl56 hl32 hl80 hl64 hl72 hl88 hl40 hrslot R S scratch hsc hsp hcap hcap63 hmm st3 h3) ?_
  intro st4 h4
  refine eventually_trans _ _ _ _ (dpr_g6e_f4 k hk hf ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 hast hv2 hv4 hc0 hc1 hc3 hb0 hb1 hb3 hd0 hd1 hd2 hd3 hd4 p0 p1 p3 s ra guard hpre fp s1 s2 l16 l48 l56 l32 l80 l64 l72 l88 l40 rslot hfp hs1 hs2 hl16 hl48 hl56 hl32 hl80 hl64 hl72 hl88 hl40 hrslot R S scratch hsc hsp hcap hcap63 hmm st4 h4) ?_
  intro st5 h5
  exact dpr_g6e_epi k hk hf ast v2 v4 c0 c1 c3 b0 b1 b3 pre d0 d1 d2 d3 d4 hast hv2 hv4 hc0 hc1 hc3 hb0 hb1 hb3 hd0 hd1 hd2 hd3 hd4 p0 p1 p3 s ra guard hpre fp s1 s2 l16 l48 l56 l32 l80 l64 l72 l88 l40 rslot hfp hs1 hs2 hl16 hl48 hl56 hl32 hl80 hl64 hl72 hl88 hl40 hrslot R S scratch hsc hsp hcap hcap63 st5 h5
theorem dpr_g6e_fast_kind : ∀ (h : Host), type_of% (@dpr_g6e_fast h)
    = @E2eScal.encFastKindN h DprMarshal E2eScal.Gen6Enc.dpr_g6e_layout [.bytes 48, .bytes 32, .u64, .bytes 96, .u64] := by
  intro h; rfl

end E2eScal.Gen6Enc
