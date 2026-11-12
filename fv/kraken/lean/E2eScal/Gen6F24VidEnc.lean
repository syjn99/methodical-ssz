import E2eScal.EncTies
import Codec.EncodeFrameTest
import E2eScal.F24Code

/-!
# GEN6 (`p2enc --gen6`, unit E2-G): encoder fast path of `(*v1alpha1.ValidatorIdentity).MarshalSSZTo`

Generated from the `.S` file and the IR: a symbolic dataflow walk of the fast path, one application of a
step lemma per directive (windows with the nops erased), boundary states between the fields. Every theorem
has a `_kind` line (`encHeadKindN`, `encFieldKindN`, `encEpiKindN`, `encFastKindN`).
**Fast path only**: `len(dst) + 64 ≤ cap(dst)` and every byte-vector field of its exact length. No
`runtime.growslice` directive is stepped: each capacity test is decided from the premise. Not covered: the
growslice branches, the length rejects, the morestack path. Not a complete encoder result.
GEN6-JSON: {"type": "ValidatorIdentity", "const": "VidMarshal", "prefix": "vid_g6e", "size": 64, "frame": 144, "gd": 24, "rt": true, "fields": [["Index", "u", 8], ["Pubkey", "b", 48], ["ActivationEpoch", "u", 8]], "boundaries": [10, 36, 64, 92], "layout": "E2eScal.Gen6Enc.vid_g6e_layout", "S_sha256": "cdfd21b3d578e12dc28267992dc650230ca9c15b2e3ec1a13b66fccd337e77f7", "ir_sha256": "c1586d32018abd182c16d50f6a7a76e38814cab08cf4a7a42105fe30342a5d2a", "statement_check": "kind instance only", "S": "prysm/go1.26.10/e2e/f24/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.MarshalSSZTo.S", "ir": "prysm/ir/ir-mainnet.json", "ir_type": "v1alpha1.ValidatorIdentity", "kinds": [{"theorem": "vid_g6e_head", "kind": "encHeadKindN"}, {"theorem": "vid_g6e_f0", "kind": "encFieldKindN"}, {"theorem": "vid_g6e_f1", "kind": "encFieldKindN"}, {"theorem": "vid_g6e_f2", "kind": "encFieldKindN"}, {"theorem": "vid_g6e_epi", "kind": "encEpiKindN"}, {"theorem": "vid_g6e_fast", "kind": "encFastKindN"}]}
-/

open Machine Runtime TestTarget E2eScal Codec E2eScal.F24Code
variable [Host]

namespace E2eScal.Gen6Enc

/-- The frame facts of `VidMarshal` (read from the `.S` file by the walk): frame `0x90`, stack chunks
`fp s1 s2 t56 t40 l24 l104 l96 t88 t72 rslot`. -/
def vid_g6e_layout : EncLayout where
  st := true
  frame := 144
  gd := 24
  rt := true
  nstk := 11
  lens := [(0, 8), (1, 8), (2, 8), (3, 16), (4, 16), (5, 8), (6, 8), (7, 8), (8, 16), (9, 16), (10, 8)]
  pre := [.at (.dn 8) (.orig 0), .at (.up 8) (.orig 1), .at (.up 16) (.orig 2), .at (.dn 56) (.orig 3), .at (.dn 40) (.orig 4), .at (.dn 24) (.orig 5), .at (.dn 104) (.orig 6), .at (.dn 96) (.orig 7), .at (.dn 88) (.orig 8), .at (.dn 72) (.orig 9), .at (.dn 160) (.orig 10), .lo .scr]
  exs := [.n 8, .n 16, .lo, .n 8, .n 16]
  post := [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 56) (.fld 0), .at (.dn 48) (.ex 0), .at (.dn 40) (.ex 1), .at (.dn 24) (.reg .rbx), .at (.dn 104) (.len 56), .at (.dn 96) (.reg .rdi), .at (.dn 88) (.fld 2), .at (.dn 80) (.ex 3), .at (.dn 72) (.ex 4), .at (.dn 160) (.ret 64), .lo (.ex 2)]


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Head: directives 0–9 (stack guard, frame, spills); entry → boundary state 0. -/
theorem vid_g6e_head : ∀ (k : Nat) (hk : VidMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh VidMarshal k)
    (ast v0 v2 c1 b1 pre d0 d1 d2 : List UInt8) (hast : ast.length = 8) (hv0 : v0.length = 8) (hv2 : v2.length = 8) (hc1 : c1.length = 8) (hb1 : b1.length = 48) (hd0 : d0.length = 8) (hd1 : d1.length = 48) (hd2 : d2.length = 8)
    (p1 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 t56 t40 l24 l104 l96 t88 t72 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (ht56 : t56.length = 16) (ht40 : t40.length = 16) (hl24 : l24.length = 8) (hl104 : l104.length = 8) (hl96 : l96.length = 8) (ht88 : t88.length = 16) (ht72 : t72.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (t56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (l104.At (s.regs.rsp.toBitVec - 104))
      ⋆ Eq (l96.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (t88.At (s.regs.rsp.toBitVec - 88))
      ⋆ Eq (t72.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 160))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 160 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (c1.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (v2.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (b1.At p1)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56))
      ⋆ R)
    (hguard : guard.toNat + 24 < s.regs.rsp.toNat) (hsp : 160 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 64 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveC S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 10)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 152 }
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
          ⋆ Eq (t56.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (l104.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (l96.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (t88.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (t72.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 160 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (b1.At p1)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56))
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf ast v0 v2 c1 b1 pre d0 d1 d2 hast hv0 hv2 hc1 hb1 hd0 hd1 hd2 p1 s ra guard hpre fp s1 s2 t56 t40 l24 l104 l96 t88 t72 rslot hfp hs1 hs2 ht56 ht40 hl24 hl104 hl96 ht88 ht72 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hcap hcap63 hpre ⊢
  have hcap' : rcx.toBitVec.toNat + 64 ≤ rdi.toBitVec.toNat := hcap
  apply encpro_l _ _ _ (-24) 24 _ k (k + 7) (win hk 0 7) (by rfl) (by rfl) (by rfl) guard fp hfp _ _ _ (by dsimp only; ecancel) hguard
  intro m1 H1 fl1; kn; dsimp only at H1
  apply kstep_sub_i Reg64.rsp 144 _ (k + 7) (k + 8) (win hk 7 1) (by rfl) (by rfl)
  intro fl; kn
  apply kreg_eq Reg64.rsp (rsp.toBitVec - 152) _ _ _ (by show ((rsp.toBitVec - 8) - 144 : BitVec 64) = (rsp.toBitVec - 152); bv_omega)
  kn
  apply kstep_st Reg64.rbx Reg64.rsp 168 _ (k + 8) (k + 9) (win hk 8 1) (by rfl) (by rfl)
    (rsp.toBitVec - 152) (rsp.toBitVec + 16) (by eb) s2 hs2 _ _ _ (by rfl) (by ecancel)
  intro m2 H2; kn; simp only [Reg64s.get64] at H2
  apply kstep_st Reg64.rax Reg64.rsp 160 _ (k + 9) (k + 10) (win hk 9 1) (by rfl) (by rfl)
    (rsp.toBitVec - 152) (rsp.toBitVec + 8) (by eb) s1 hs1 _ _ _ (by rfl) (by ecancel)
  intro m3 H3; kn; simp only [Reg64s.get64] at H3
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem vid_g6e_head_kind : ∀ (h : Host), type_of% (@vid_g6e_head h)
    = @E2eScal.encHeadKindN h VidMarshal E2eScal.Gen6Enc.vid_g6e_layout [.u64, .bytes 48, .u64]
    ⟨10, 0, [(.rax, .rcv), (.rbx, .ptr), (.rcx, .len 0), (.rdi, .cap)],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 56) (.orig 3), .at (.dn 40) (.orig 4), .at (.dn 24) (.orig 5), .at (.dn 104) (.orig 6), .at (.dn 96) (.orig 7), .at (.dn 88) (.orig 8), .at (.dn 72) (.orig 9), .at (.dn 160) (.orig 10), .lo .scr],
      []⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 0 `Index` (uint64): directives 10–35; boundary state 0 → 1. -/
theorem vid_g6e_f0 : ∀ (k : Nat) (hk : VidMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh VidMarshal k)
    (ast v0 v2 c1 b1 pre d0 d1 d2 : List UInt8) (hast : ast.length = 8) (hv0 : v0.length = 8) (hv2 : v2.length = 8) (hc1 : c1.length = 8) (hb1 : b1.length = 48) (hd0 : d0.length = 8) (hd1 : d1.length = 48) (hd2 : d2.length = 8)
    (p1 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 t56 t40 l24 l104 l96 t88 t72 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (ht56 : t56.length = 16) (ht40 : t40.length = 16) (hl24 : l24.length = 8) (hl104 : l104.length = 8) (hl96 : l96.length = 8) (ht88 : t88.length = 16) (ht72 : t72.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 160 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 64 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveC S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 10)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 152 }
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
          ⋆ Eq (t56.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (l104.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (l96.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (t88.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (t72.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 160 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (b1.At p1)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 36)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 152 }
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
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (l104.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (l96.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (t88.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (t72.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 160 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (b1.At p1)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v0 v2 c1 b1 pre d0 d1 d2 hast hv0 hv2 hc1 hb1 hd0 hd1 hd2 p1 s ra guard hpre fp s1 s2 t56 t40 l24 l104 l96 t88 t72 rslot hfp hs1 hs2 ht56 ht40 hl24 hl104 hl96 ht88 ht72 hrslot R S scratch hsc hsp hcap hcap63 hmm
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
  have hcap' : rcx.toBitVec.toNat + 64 ≤ rdi.toBitVec.toNat := hcap
  apply kstep_lea Reg64.rdx Reg64.rcx 8 _ (k + 10) (k + 11) (win hk 10 1) (by rfl) (by rfl)
  kn
  apply kreg_eq Reg64.rdx (rcx.toBitVec + 8) _ _ _ (by show (rcx.toBitVec + 8 : BitVec 64) = (rcx.toBitVec + 8); bv_omega)
  kn
  apply kstep_ldb Reg64.r8 Reg64.rax 8 _ (k + 11) (k + 12) (win hk 11 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 8) (by eb) v0 hv0 _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_lea Reg64.r9 Reg64.rsp 96 _ (k + 12) (k + 16) (win hk 12 4) (by rfl) (by rfl)
  kn
  apply kreg_eq Reg64.r9 (rsp.toBitVec - 56) _ _ _ (by show ((rsp.toBitVec - 152) + 96 : BitVec 64) = (rsp.toBitVec - 56); bv_omega)
  kn
  apply kstep_movups15 Reg64.r9 0 _ (k + 16) (k + 17) (win hk 16 1) (by rfl) (by rfl)
    (rsp.toBitVec - 56) (rsp.toBitVec - 56) (by eb) t56 ht56 _ _ _ (by rfl) (by ecancel)
  intro m4 H4; kn; try dsimp only at H4
  apply kstep_movups15 Reg64.r9 16 _ (k + 17) (k + 18) (win hk 17 1) (by rfl) (by rfl)
    (rsp.toBitVec - 56) (rsp.toBitVec - 40) (by eb) t40 ht40 _ _ _ (by rfl) (by ecancel)
  intro m5 H5; kn; try dsimp only at H5
  rw [lr_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 56), show (rsp.toBitVec - 56) + 8 = (rsp.toBitVec - 48) by bv_omega] at H5
  apply kstep_st Reg64.r8 Reg64.rsp 96 _ (k + 18) (k + 19) (win hk 18 1) (by rfl) (by rfl)
    (rsp.toBitVec - 152) (rsp.toBitVec - 56) (by eb) ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).take 8) (by rw [List.length_take, Int.toBytes_length]; rfl) _ _ _ (by rfl) (by ecancel)
  intro m6 H6; kn; simp only [Reg64s.get64] at H6
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v0 hv0] at H6
  have hl33 := Machine.label_at' hk hf (j := 33)
    (by simp only [VidMarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [VidMarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply kstep_cmp_jae_t Reg64.rdi Reg64.rdx _ _ (k + 19) (k + 33) (win hk 19 2) (by rfl) hl33 _ _ (by show ((rcx.toBitVec + 8) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; kn
  apply kstep_label _ _ (k + 33) (k + 34) (win hk 33 1) (by rfl) (by rfl)
  apply kstep_ldb Reg64.r8 Reg64.rsp 96 _ (k + 34) (k + 35) (win hk 34 1) (by rfl) (by rfl)
    (rsp.toBitVec - 152) (rsp.toBitVec - 56) (by eb) v0 hv0 _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_st_idx Reg64.r8 Reg64.rbx Reg64.rcx 0 _ (k + 35) (k + 36) (win hk 35 1) (by rfl) (by rfl)
    rbx.toBitVec rcx.toBitVec (rbx.toBitVec + rcx.toBitVec) (by eb) d0 hd0 _ _ _ (by rfl) (by rfl) (by ecancel)
  intro m7 H7; kn; simp only [Reg64s.get64] at H7
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v0 hv0] at H7
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8), (Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt), (by rw [List.length_drop, Int.toBytes_length]), (Int.toBytes_length 16 _), ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem vid_g6e_f0_kind : ∀ (h : Host), type_of% (@vid_g6e_f0 h)
    = @E2eScal.encFieldKindN h VidMarshal E2eScal.Gen6Enc.vid_g6e_layout [.u64, .bytes 48, .u64]
    ⟨10, 0, [(.rax, .rcv), (.rbx, .ptr), (.rcx, .len 0), (.rdi, .cap)],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 56) (.orig 3), .at (.dn 40) (.orig 4), .at (.dn 24) (.orig 5), .at (.dn 104) (.orig 6), .at (.dn 96) (.orig 7), .at (.dn 88) (.orig 8), .at (.dn 72) (.orig 9), .at (.dn 160) (.orig 10), .lo .scr],
      []⟩
    ⟨36, 1, [(.rax, .rcv), (.rbx, .ptr), (.rdx, .len 8), (.rdi, .cap)],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 56) (.fld 0), .at (.dn 48) (.ex 0), .at (.dn 40) (.ex 1), .at (.dn 24) (.orig 5), .at (.dn 104) (.orig 6), .at (.dn 96) (.orig 7), .at (.dn 88) (.orig 8), .at (.dn 72) (.orig 9), .at (.dn 160) (.orig 10), .lo .scr],
      [.n 8, .n 16]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 1 `Pubkey` (48 bytes): directives 36–63; boundary state 1 → 2. -/
theorem vid_g6e_f1 : ∀ (k : Nat) (hk : VidMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh VidMarshal k)
    (ast v0 v2 c1 b1 pre d0 d1 d2 : List UInt8) (hast : ast.length = 8) (hv0 : v0.length = 8) (hv2 : v2.length = 8) (hc1 : c1.length = 8) (hb1 : b1.length = 48) (hd0 : d0.length = 8) (hd1 : d1.length = 48) (hd2 : d2.length = 8)
    (p1 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 t56 t40 l24 l104 l96 t88 t72 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (ht56 : t56.length = 16) (ht40 : t40.length = 16) (hl24 : l24.length = 8) (hl104 : l104.length = 8) (hl96 : l96.length = 8) (ht88 : t88.length = 16) (ht72 : t72.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 160 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 64 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveC S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 36)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 152 }
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
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (l104.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (l96.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (t88.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (t72.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 160 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (b1.At p1)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 64)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 152 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 x2 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧ x2.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 56).toInt).At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (t88.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (t72.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 64)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 160 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (b1.At p1)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v0 v2 c1 b1 pre d0 d1 d2 hast hv0 hv2 hc1 hb1 hd0 hd1 hd2 p1 s ra guard hpre fp s1 s2 t56 t40 l24 l104 l96 t88 t72 rslot hfp hs1 hs2 ht56 ht40 hl24 hl104 hl96 ht88 ht72 hrslot R S scratch hsc hsp hcap hcap63 hmm
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
  have hcap' : rcx.toBitVec.toNat + 64 ≤ rdi.toBitVec.toNat := hcap
  apply kstep_ldv Reg64.r8 Reg64.rax 16 _ (k + 36) (k + 37) (win hk 36 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 16) p1 (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_lenchk Reg64.rax 24 48 _ _ (k + 37) (k + 40) (win hk 37 3) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 24) (by eb) (Int.toBytes 8 48) (by rfl) (by decide) _ _ _ (by rfl) (by ecancel)
  intro fl; kn
  apply kstep_lea Reg64.r9 Reg64.rdx 48 _ (k + 40) (k + 41) (win hk 40 1) (by rfl) (by rfl)
  kn
  apply kreg_eq Reg64.r9 (rcx.toBitVec + 56) _ _ _ (by show ((rcx.toBitVec + 8) + 48 : BitVec 64) = (rcx.toBitVec + 56); bv_omega)
  kn
  have hl56 := Machine.label_at' hk hf (j := 56)
    (by simp only [VidMarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [VidMarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply kstep_cmp_jae_t Reg64.rdi Reg64.r9 _ _ (k + 41) (k + 56) (win hk 41 2) (by rfl) hl56 _ _ (by show ((rcx.toBitVec + 56) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; kn
  apply kstep_label _ _ (k + 56) (k + 57) (win hk 56 1) (by rfl) (by rfl)
  apply kstep_st Reg64.rbx Reg64.rsp 128 _ (k + 57) (k + 58) (win hk 57 1) (by rfl) (by rfl)
    (rsp.toBitVec - 152) (rsp.toBitVec - 24) (by eb) l24 hl24 _ _ _ (by rfl) (by ecancel)
  intro m8 H8; kn; simp only [Reg64s.get64] at H8
  apply kstep_st Reg64.r9 Reg64.rsp 48 _ (k + 58) (k + 59) (win hk 58 1) (by rfl) (by rfl)
    (rsp.toBitVec - 152) (rsp.toBitVec - 104) (by eb) l104 hl104 _ _ _ (by rfl) (by ecancel)
  intro m9 H9; kn; simp only [Reg64s.get64] at H9
  apply kstep_st Reg64.rdi Reg64.rsp 56 _ (k + 59) (k + 60) (win hk 59 1) (by rfl) (by rfl)
    (rsp.toBitVec - 152) (rsp.toBitVec - 96) (by eb) l96 hl96 _ _ _ (by rfl) (by ecancel)
  intro m10 H10; kn; simp only [Reg64s.get64] at H10
  apply kstep_lea_idx Reg64.rax Reg64.rbx Reg64.rdx _ (k + 60) (k + 61) (win hk 60 1) (by rfl) (by rfl)
  kn
  apply kreg_eq Reg64.rax (rbx.toBitVec + rcx.toBitVec + 8) _ _ _ (by show (rbx.toBitVec + (rcx.toBitVec + 8) : BitVec 64) = (rbx.toBitVec + rcx.toBitVec + 8); bv_omega)
  kn
  apply kstep_mov_rr Reg64.rbx Reg64.r8 _ (k + 61) (k + 62) (win hk 61 1) (by rfl) (by rfl)
  kn
  apply kstep_movi Reg64.rcx 48 _ (k + 62) (k + 63) (win hk 62 1) (by rfl) (by rfl)
  kn
  apply kreg_eq Reg64.rcx 48 _ _ _ (by show (BitVec.zeroExtend 64 (BitVec.truncate 32 (48 : BitVec 64)) : BitVec 64) = 48; decide)
  kn
  refine eventually_trans _ _ _ _ (encn_call (k + 63) (win hk 63 1) (rsp.toBitVec - 152) (rbx.toBitVec + rcx.toBitVec + 8) p1
    (rsp.toBitVec - 160) (rsp.toBitVec - 160 - BitVec.ofNat 64 S) S (by bv_omega) (Codec.frame_lo0 rsp.toBitVec 152 160 S (by decide))
    b1 d1 rslot scratch (by rw [hd1, hb1]) hrslot hsc
    _ _ (by rfl) (by rfl) (by rfl) (by rw [hb1]; rfl) (by first | ecancel | (dsimp only; ecancel)) hmm) ?_
  rintro ⟨e1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, scr1, hscr1, Hc1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 Hc1
  subst hpc1
  obtain ⟨⟨raxc1, rbxc1, rcxc1, rdxc1, rsic1, rdic1, rspc1, rbpc1, r8c1, r9c1, r10c1, r11c1, r12c1, r13c1, r14c1, r15c1⟩, zmmsc1, flagsc1, memc1⟩ := e1
  simp only at hrsp1 hrbp1 hr141 Hc1
  subst rspc1 rbpc1 r14c1
  rw [show k + 63 + 1 = k + 64 from rfl] at Hc1
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, x0, x1, scr1, hx0, hx1, hscr1, ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem vid_g6e_f1_kind : ∀ (h : Host), type_of% (@vid_g6e_f1 h)
    = @E2eScal.encFieldKindN h VidMarshal E2eScal.Gen6Enc.vid_g6e_layout [.u64, .bytes 48, .u64]
    ⟨36, 1, [(.rax, .rcv), (.rbx, .ptr), (.rdx, .len 8), (.rdi, .cap)],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 56) (.fld 0), .at (.dn 48) (.ex 0), .at (.dn 40) (.ex 1), .at (.dn 24) (.orig 5), .at (.dn 104) (.orig 6), .at (.dn 96) (.orig 7), .at (.dn 88) (.orig 8), .at (.dn 72) (.orig 9), .at (.dn 160) (.orig 10), .lo .scr],
      [.n 8, .n 16]⟩
    ⟨64, 2, [],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 56) (.fld 0), .at (.dn 48) (.ex 0), .at (.dn 40) (.ex 1), .at (.dn 24) (.reg .rbx), .at (.dn 104) (.len 56), .at (.dn 96) (.reg .rdi), .at (.dn 88) (.orig 8), .at (.dn 72) (.orig 9), .at (.dn 160) (.ret 64), .lo (.ex 2)],
      [.n 8, .n 16, .lo]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 2 `ActivationEpoch` (uint64): directives 64–91; boundary state 2 → 3. -/
theorem vid_g6e_f2 : ∀ (k : Nat) (hk : VidMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh VidMarshal k)
    (ast v0 v2 c1 b1 pre d0 d1 d2 : List UInt8) (hast : ast.length = 8) (hv0 : v0.length = 8) (hv2 : v2.length = 8) (hc1 : c1.length = 8) (hb1 : b1.length = 48) (hd0 : d0.length = 8) (hd1 : d1.length = 48) (hd2 : d2.length = 8)
    (p1 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 t56 t40 l24 l104 l96 t88 t72 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (ht56 : t56.length = 16) (ht40 : t40.length = 16) (hl24 : l24.length = 8) (hl104 : l104.length = 8) (hl96 : l96.length = 8) (ht88 : t88.length = 16) (ht72 : t72.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 160 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 64 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveC S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 64)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 152 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 x2 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧ x2.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 56).toInt).At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (t88.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (t72.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 64)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 160 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (b1.At p1)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 92)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 152 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.get64 Reg64.rax = s.regs.rbx.toBitVec
        ∧ st.data.regs.get64 Reg64.rcx = s.regs.rdi.toBitVec
        ∧ st.data.regs.get64 Reg64.rdx = s.regs.rcx.toBitVec + 64 ∧
        ∃ (x0 x1 x2 x3 x4 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧ x2.length = S ∧ x3.length = 8 ∧ x4.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 56).toInt).At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (v2.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x4.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 64)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 160 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (b1.At p1)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (v2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v0 v2 c1 b1 pre d0 d1 d2 hast hv0 hv2 hc1 hb1 hd0 hd1 hd2 p1 s ra guard hpre fp s1 s2 t56 t40 l24 l104 l96 t88 t72 rslot hfp hs1 hs2 ht56 ht40 hl24 hl104 hl96 ht88 ht72 hrslot R S scratch hsc hsp hcap hcap63 hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hsp hcap hcap63 hpre ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, x0, x1, x2, hx0, hx1, hx2, Hm⟩
  dsimp only at hpc hrsp hrbp hr14  Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14  Hm
  subst rsp1 rbp1 r141
  have hcap' : rcx.toBitVec.toNat + 64 ≤ rdi.toBitVec.toNat := hcap
  apply kstep_ldv Reg64.rbx Reg64.rsp 48 _ (k + 64) (k + 65) (win hk 64 1) (by rfl) (by rfl)
    (rsp.toBitVec - 152) (rsp.toBitVec - 104) (rcx.toBitVec + 56) (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_lea Reg64.rdx Reg64.rbx 8 _ (k + 65) (k + 66) (win hk 65 1) (by rfl) (by rfl)
  kn
  apply kreg_eq Reg64.rdx (rcx.toBitVec + 64) _ _ _ (by show ((rcx.toBitVec + 56) + 8 : BitVec 64) = (rcx.toBitVec + 64); bv_omega)
  kn
  apply kstep_ldv Reg64.rsi Reg64.rsp 160 _ (k + 66) (k + 67) (win hk 66 1) (by rfl) (by rfl)
    (rsp.toBitVec - 152) (rsp.toBitVec + 8) rax.toBitVec (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_ldb Reg64.rsi Reg64.rsi 40 _ (k + 67) (k + 68) (win hk 67 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 40) (by eb) v2 hv2 _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_lea Reg64.rdi Reg64.rsp 64 _ (k + 68) (k + 72) (win hk 68 4) (by rfl) (by rfl)
  kn
  apply kreg_eq Reg64.rdi (rsp.toBitVec - 88) _ _ _ (by show ((rsp.toBitVec - 152) + 64 : BitVec 64) = (rsp.toBitVec - 88); bv_omega)
  kn
  apply kstep_movups15 Reg64.rdi 0 _ (k + 72) (k + 73) (win hk 72 1) (by rfl) (by rfl)
    (rsp.toBitVec - 88) (rsp.toBitVec - 88) (by eb) t88 ht88 _ _ _ (by rfl) (by ecancel)
  intro m11 H11; kn; try dsimp only at H11
  apply kstep_movups15 Reg64.rdi 16 _ (k + 73) (k + 74) (win hk 73 1) (by rfl) (by rfl)
    (rsp.toBitVec - 88) (rsp.toBitVec - 72) (by eb) t72 ht72 _ _ _ (by rfl) (by ecancel)
  intro m12 H12; kn; try dsimp only at H12
  rw [lr_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 88), show (rsp.toBitVec - 88) + 8 = (rsp.toBitVec - 80) by bv_omega] at H12
  apply kstep_st Reg64.rsi Reg64.rsp 64 _ (k + 74) (k + 75) (win hk 74 1) (by rfl) (by rfl)
    (rsp.toBitVec - 152) (rsp.toBitVec - 88) (by eb) ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).take 8) (by rw [List.length_take, Int.toBytes_length]; rfl) _ _ _ (by rfl) (by ecancel)
  intro m13 H13; kn; simp only [Reg64s.get64] at H13
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v2 hv2] at H13
  apply kstep_ldv Reg64.rcx Reg64.rsp 56 _ (k + 75) (k + 76) (win hk 75 1) (by rfl) (by rfl)
    (rsp.toBitVec - 152) (rsp.toBitVec - 96) rdi.toBitVec (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_cmp_jb_f Reg64.rcx Reg64.rdx _ _ (k + 76) (k + 79) (win hk 76 3) (by rfl) (by rfl) _ _ (by show ((rcx.toBitVec + 64) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; kn
  apply kstep_ldv Reg64.rax Reg64.rsp 128 _ (k + 79) (k + 80) (win hk 79 1) (by rfl) (by rfl)
    (rsp.toBitVec - 152) (rsp.toBitVec - 24) rbx.toBitVec (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  have hl89 := Machine.label_at' hk hf (j := 89)
    (by simp only [VidMarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [VidMarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply kstep_jmp _ _ (k + 80) (k + 89) (win hk 80 1) (by rfl) hl89
  apply kstep_label _ _ (k + 89) (k + 90) (win hk 89 1) (by rfl) (by rfl)
  apply kstep_ldb Reg64.r8 Reg64.rsp 64 _ (k + 90) (k + 91) (win hk 90 1) (by rfl) (by rfl)
    (rsp.toBitVec - 152) (rsp.toBitVec - 88) (by eb) v2 hv2 _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_st_idx Reg64.r8 Reg64.rax Reg64.rbx 0 _ (k + 91) (k + 92) (win hk 91 1) (by rfl) (by rfl)
    rbx.toBitVec (rcx.toBitVec + 56) (rbx.toBitVec + rcx.toBitVec + 56) (by eb) d2 hd2 _ _ _ (by rfl) (by rfl) (by ecancel)
  intro m14 H14; kn; simp only [Reg64s.get64] at H14
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v2 hv2] at H14
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, x0, x1, x2, ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8), (Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt), hx0, hx1, hx2, (by rw [List.length_drop, Int.toBytes_length]), (Int.toBytes_length 16 _), ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem vid_g6e_f2_kind : ∀ (h : Host), type_of% (@vid_g6e_f2 h)
    = @E2eScal.encFieldKindN h VidMarshal E2eScal.Gen6Enc.vid_g6e_layout [.u64, .bytes 48, .u64]
    ⟨64, 2, [],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 56) (.fld 0), .at (.dn 48) (.ex 0), .at (.dn 40) (.ex 1), .at (.dn 24) (.reg .rbx), .at (.dn 104) (.len 56), .at (.dn 96) (.reg .rdi), .at (.dn 88) (.orig 8), .at (.dn 72) (.orig 9), .at (.dn 160) (.ret 64), .lo (.ex 2)],
      [.n 8, .n 16, .lo]⟩
    ⟨92, 3, [(.rax, .ptr), (.rcx, .cap), (.rdx, .len 64)],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 56) (.fld 0), .at (.dn 48) (.ex 0), .at (.dn 40) (.ex 1), .at (.dn 24) (.reg .rbx), .at (.dn 104) (.len 56), .at (.dn 96) (.reg .rdi), .at (.dn 88) (.fld 2), .at (.dn 80) (.ex 3), .at (.dn 72) (.ex 4), .at (.dn 160) (.ret 64), .lo (.ex 2)],
      [.n 8, .n 16, .lo, .n 8, .n 16]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Epilogue: directives 92–return; boundary state 3 → the fast-path post-state. -/
theorem vid_g6e_epi : ∀ (k : Nat) (hk : VidMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh VidMarshal k)
    (ast v0 v2 c1 b1 pre d0 d1 d2 : List UInt8) (hast : ast.length = 8) (hv0 : v0.length = 8) (hv2 : v2.length = 8) (hc1 : c1.length = 8) (hb1 : b1.length = 48) (hd0 : d0.length = 8) (hd1 : d1.length = 48) (hd2 : d2.length = 8)
    (p1 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 t56 t40 l24 l104 l96 t88 t72 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (ht56 : t56.length = 16) (ht40 : t40.length = 16) (hl24 : l24.length = 8) (hl104 : l104.length = 8) (hl96 : l96.length = 8) (ht88 : t88.length = 16) (ht72 : t72.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 160 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 64 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 92)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 152 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14
        ∧ st0.data.regs.get64 Reg64.rax = s.regs.rbx.toBitVec
        ∧ st0.data.regs.get64 Reg64.rcx = s.regs.rdi.toBitVec
        ∧ st0.data.regs.get64 Reg64.rdx = s.regs.rcx.toBitVec + 64 ∧
        ∃ (x0 x1 x2 x3 x4 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧ x2.length = S ∧ x3.length = 8 ∧ x4.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 56).toInt).At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (v2.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x4.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 64)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 160 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (b1.At p1)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (v2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec
        ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 64
        ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0
        ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8
        ∧ st.data.regs.rbp = s.regs.rbp
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 x2 x3 x4 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧ x2.length = S ∧ x3.length = 8 ∧ x4.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 56).toInt).At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (v2.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x4.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 64)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 160 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (b1.At p1)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (v2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v0 v2 c1 b1 pre d0 d1 d2 hast hv0 hv2 hc1 hb1 hd0 hd1 hd2 p1 s ra guard hpre fp s1 s2 t56 t40 l24 l104 l96 t88 t72 rslot hfp hs1 hs2 ht56 ht40 hl24 hl104 hl96 ht88 ht72 hrslot R S scratch hsc hsp hcap hcap63
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
  obtain rfl : rdx1 = { toBitVec := rcx.toBitVec + 64 } := UInt64.toBitVec_inj.mp hrrdx
  have hcap' : rcx.toBitVec.toNat + 64 ≤ rdi.toBitVec.toNat := hcap
  apply kstep_mov_rr Reg64.rbx Reg64.rdx _ (k + 92) (k + 93) (win hk 92 1) (by rfl) (by rfl)
  kn
  apply kstep_xor32 Reg64.rdi _ (k + 93) (k + 94) (win hk 93 1) (by rfl) (by rfl)
  intro fl; kn
  apply kstep_xor32 Reg64.rsi _ (k + 94) (k + 95) (win hk 94 1) (by rfl) (by rfl)
  intro fl; kn
  apply kstep_add Reg64.rsp 144 _ (k + 95) (k + 96) (win hk 95 1) (by rfl) (by rfl)
  intro fl; kn
  apply kreg_eq Reg64.rsp (rsp.toBitVec - 8) _ _ _ (by show ((rsp.toBitVec - 152) + 144 : BitVec 64) = (rsp.toBitVec - 8); bv_omega)
  kn
  refine eventually_trans _ _ _ _ (decret_seg _ (k + 96) (win hk 96 2) (by rfl) (rsp.toBitVec - 8) rsp.toBitVec (by bv_omega) rbp ra _ _ (by rfl) (by ecancel)) ?_
  rintro ⟨d', pc'⟩ ⟨hpc', hrsp', hrbp', hreg', hmem'⟩
  dsimp only at hpc' hrsp' hrbp' hreg' hmem'
  apply Eventually.done
  refine ⟨hpc', ?_, ?_, ?_, ?_, ?_, ?_, hrbp', ?_, x0, x1, x2, x3, x4, hx0, hx1, hx2, hx3, hx4, ?_⟩
  · exact UInt64.toBitVec_inj.mp (hreg' Reg64.rax (by decide) (by decide))
  · show d'.regs.rbx.toBitVec.toNat = rcx.toBitVec.toNat + 64
    rw [show d'.regs.rbx.toBitVec = rcx.toBitVec + 64 from hreg' Reg64.rbx (by decide) (by decide)]
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
theorem vid_g6e_epi_kind : ∀ (h : Host), type_of% (@vid_g6e_epi h)
    = @E2eScal.encEpiKindN h VidMarshal E2eScal.Gen6Enc.vid_g6e_layout [.u64, .bytes 48, .u64]
    ⟨92, 3, [(.rax, .ptr), (.rcx, .cap), (.rdx, .len 64)],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 56) (.fld 0), .at (.dn 48) (.ex 0), .at (.dn 40) (.ex 1), .at (.dn 24) (.reg .rbx), .at (.dn 104) (.len 56), .at (.dn 96) (.reg .rdi), .at (.dn 88) (.fld 2), .at (.dn 80) (.ex 3), .at (.dn 72) (.ex 4), .at (.dn 160) (.ret 64), .lo (.ex 2)],
      [.n 8, .n 16, .lo, .n 8, .n 16]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Encoder fast path of `(*v1alpha1.ValidatorIdentity).MarshalSSZTo` (Go 1.26.10), generated** (`p2enc --gen6`):
head, one theorem per field, epilogue, chained by `eventually_trans`. Premises: `len + 64 ≤ cap`,
every byte-vector field of its exact length. Statement = the kind instance (`_kind`). Fast path only. -/
theorem vid_g6e_fast : ∀ (k : Nat) (hk : VidMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh VidMarshal k)
    (ast v0 v2 c1 b1 pre d0 d1 d2 : List UInt8) (hast : ast.length = 8) (hv0 : v0.length = 8) (hv2 : v2.length = 8) (hc1 : c1.length = 8) (hb1 : b1.length = 48) (hd0 : d0.length = 8) (hd1 : d1.length = 48) (hd2 : d2.length = 8)
    (p1 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 t56 t40 l24 l104 l96 t88 t72 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (ht56 : t56.length = 16) (ht40 : t40.length = 16) (hl24 : l24.length = 8) (hl104 : l104.length = 8) (hl96 : l96.length = 8) (ht88 : t88.length = 16) (ht72 : t72.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (t56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (l104.At (s.regs.rsp.toBitVec - 104))
      ⋆ Eq (l96.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (t88.At (s.regs.rsp.toBitVec - 88))
      ⋆ Eq (t72.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 160))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 160 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (c1.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (v2.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (b1.At p1)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56))
      ⋆ R)
    (hguard : guard.toNat + 24 < s.regs.rsp.toNat) (hsp : 160 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 64 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveC S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec
        ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 64
        ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0
        ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8
        ∧ st.data.regs.rbp = s.regs.rbp
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 x2 x3 x4 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧ x2.length = S ∧ x3.length = 8 ∧ x4.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 56).toInt).At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (v2.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (x4.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 64)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 160))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 160 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (v2.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (b1.At p1)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (v2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56))
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf ast v0 v2 c1 b1 pre d0 d1 d2 hast hv0 hv2 hc1 hb1 hd0 hd1 hd2 p1 s ra guard hpre fp s1 s2 t56 t40 l24 l104 l96 t88 t72 rslot hfp hs1 hs2 ht56 ht40 hl24 hl104 hl96 ht88 ht72 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm
  refine eventually_trans _ _ _ _ (vid_g6e_head k hk hf ast v0 v2 c1 b1 pre d0 d1 d2 hast hv0 hv2 hc1 hb1 hd0 hd1 hd2 p1 s ra guard hpre fp s1 s2 t56 t40 l24 l104 l96 t88 t72 rslot hfp hs1 hs2 ht56 ht40 hl24 hl104 hl96 ht88 ht72 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm) ?_
  intro st0 h0
  refine eventually_trans _ _ _ _ (vid_g6e_f0 k hk hf ast v0 v2 c1 b1 pre d0 d1 d2 hast hv0 hv2 hc1 hb1 hd0 hd1 hd2 p1 s ra guard hpre fp s1 s2 t56 t40 l24 l104 l96 t88 t72 rslot hfp hs1 hs2 ht56 ht40 hl24 hl104 hl96 ht88 ht72 hrslot R S scratch hsc hsp hcap hcap63 hmm st0 h0) ?_
  intro st1 h1
  refine eventually_trans _ _ _ _ (vid_g6e_f1 k hk hf ast v0 v2 c1 b1 pre d0 d1 d2 hast hv0 hv2 hc1 hb1 hd0 hd1 hd2 p1 s ra guard hpre fp s1 s2 t56 t40 l24 l104 l96 t88 t72 rslot hfp hs1 hs2 ht56 ht40 hl24 hl104 hl96 ht88 ht72 hrslot R S scratch hsc hsp hcap hcap63 hmm st1 h1) ?_
  intro st2 h2
  refine eventually_trans _ _ _ _ (vid_g6e_f2 k hk hf ast v0 v2 c1 b1 pre d0 d1 d2 hast hv0 hv2 hc1 hb1 hd0 hd1 hd2 p1 s ra guard hpre fp s1 s2 t56 t40 l24 l104 l96 t88 t72 rslot hfp hs1 hs2 ht56 ht40 hl24 hl104 hl96 ht88 ht72 hrslot R S scratch hsc hsp hcap hcap63 hmm st2 h2) ?_
  intro st3 h3
  exact vid_g6e_epi k hk hf ast v0 v2 c1 b1 pre d0 d1 d2 hast hv0 hv2 hc1 hb1 hd0 hd1 hd2 p1 s ra guard hpre fp s1 s2 t56 t40 l24 l104 l96 t88 t72 rslot hfp hs1 hs2 ht56 ht40 hl24 hl104 hl96 ht88 ht72 hrslot R S scratch hsc hsp hcap hcap63 st3 h3
theorem vid_g6e_fast_kind : ∀ (h : Host), type_of% (@vid_g6e_fast h)
    = @E2eScal.encFastKindN h VidMarshal E2eScal.Gen6Enc.vid_g6e_layout [.u64, .bytes 48, .u64] := by
  intro h; rfl

end E2eScal.Gen6Enc
