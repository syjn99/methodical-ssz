import E2eScal.EncTies
import E2eScal.EncFrameTest
import E2eScal.BhCode

/-!
# ENC2 worked example: `(*v1alpha1.BeaconBlockHeader).MarshalSSZTo`, fast-path theorem in generated style

Text produced from the `.S` file and the IR by the recipe of the E2-L hand-over (a scratch emitter of the
unit, not the generator): a symbolic walk of the fast path, one application of a step lemma per directive
(`StepK.lean`, `EncSteps.lean`; windows with the nops erased), boundary states between the fields. Every
theorem has a `_kind` line (`encHeadKindN`, `encFieldKindN`, `encEpiKindN`, `encFastKindN`).
**Fast path only**: `len(dst) + 112 ≤ cap(dst)` and every byte-vector field of its exact length. No
`runtime.growslice` directive is stepped: each capacity test is decided from the premise. Not covered: the
growslice branches, the length rejects, the morestack path.
The statement is the declared type of the committed hand theorem `Bh.bh_e2e_marshal_main` (`bh_e2e_marshal_g6_stmt`).
-/

open Fk E2eScal E2eScal.BhCode
variable [Host]

namespace E2eScal.Gen6

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Head: directives 0–9 (stack guard, frame, spills); entry → boundary state 0. -/
theorem bh_g6_head : ∀ (k : Nat) (hk : BhMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh BhMarshal k)
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
    (hcap : s.regs.rcx.toNat + 112 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveC S),
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
  apply encpro_l _ _ _ (-32) 32 _ k (k + 7) (win hk 0 7) (by rfl) (by rfl) (by rfl) guard fp hfp _ _ _ (by dsimp only; ecancel) hguard
  intro m1 H1 fl1; kn; dsimp only at H1
  apply kstep_sub_i Reg64.rsp 152 _ (k + 7) (k + 8) (win hk 7 1) (by rfl) (by rfl)
  intro fl; kn
  apply kreg_eq Reg64.rsp (rsp.toBitVec - 160) _ _ _ (by show ((rsp.toBitVec - 8) - 152 : BitVec 64) = (rsp.toBitVec - 160); bv_omega)
  kn
  apply kstep_st Reg64.rbx Reg64.rsp 176 _ (k + 8) (k + 9) (win hk 8 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec + 16) (by eb) s2 hs2 _ _ _ (by rfl) (by ecancel)
  intro m2 H2; kn; simp only [Reg64s.get64] at H2
  apply kstep_st Reg64.rax Reg64.rsp 168 _ (k + 9) (k + 10) (win hk 9 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec + 8) (by eb) s1 hs1 _ _ _ (by rfl) (by ecancel)
  intro m3 H3; kn; simp only [Reg64s.get64] at H3
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem bh_g6_head_kind : ∀ (h : Host), type_of% (@bh_g6_head h)
    = @E2eScal.encHeadKindN h BhMarshal E2eScal.layEncBh [.u64, .u64, .bytes 32, .bytes 32, .bytes 32]
    ⟨10, 0, [(.rax, .rcv), (.rbx, .ptr), (.rcx, .len 0), (.rdi, .cap)],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 16) (.orig 3), .at (.dn 96) (.orig 4), .at (.dn 104) (.orig 5), .at (.dn 56) (.orig 6), .at (.dn 40) (.orig 7), .at (.dn 88) (.orig 8), .at (.dn 72) (.orig 9), .at (.dn 168) (.orig 10), .lo .scr],
      []⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 0 `Slot` (uint64): directives 10–35; boundary state 0 → 1. -/
theorem bh_g6_f0 : ∀ (k : Nat) (hk : BhMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh BhMarshal k)
    (ast v0 v1 c2 c3 c4 b2 b3 b4 pre d0 d1 d2 d3 d4 : List UInt8) (hast : ast.length = 8) (hv0 : v0.length = 8) (hv1 : v1.length = 8) (hc2 : c2.length = 8) (hc3 : c3.length = 8) (hc4 : c4.length = 8) (hb2 : b2.length = 32) (hb3 : b3.length = 32) (hb4 : b4.length = 32) (hd0 : d0.length = 8) (hd1 : d1.length = 8) (hd2 : d2.length = 32) (hd3 : d3.length = 32) (hd4 : d4.length = 32)
    (p2 p3 p4 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l96 l104 t56 t40 t88 t72 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8) (hl96 : l96.length = 8) (hl104 : l104.length = 8) (ht56 : t56.length = 16) (ht40 : t40.length = 16) (ht88 : t88.length = 16) (ht72 : t72.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 168 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 112 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveC S) (st0 : MachineState),
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
  apply kstep_lea Reg64.rdx Reg64.rcx 8 _ (k + 10) (k + 11) (win hk 10 1) (by rfl) (by rfl)
  kn
  apply kreg_eq Reg64.rdx (rcx.toBitVec + 8) _ _ _ (by show (rcx.toBitVec + 8 : BitVec 64) = (rcx.toBitVec + 8); bv_omega)
  kn
  apply kstep_ldb Reg64.r8 Reg64.rax 8 _ (k + 11) (k + 12) (win hk 11 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 8) (by eb) v0 hv0 _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_lea Reg64.r9 Reg64.rsp 104 _ (k + 12) (k + 16) (win hk 12 4) (by rfl) (by rfl)
  kn
  apply kreg_eq Reg64.r9 (rsp.toBitVec - 56) _ _ _ (by show ((rsp.toBitVec - 160) + 104 : BitVec 64) = (rsp.toBitVec - 56); bv_omega)
  kn
  apply kstep_movups15 Reg64.r9 0 _ (k + 16) (k + 17) (win hk 16 1) (by rfl) (by rfl)
    (rsp.toBitVec - 56) (rsp.toBitVec - 56) (by eb) t56 ht56 _ _ _ (by rfl) (by ecancel)
  intro m4 H4; kn; try dsimp only at H4
  apply kstep_movups15 Reg64.r9 16 _ (k + 17) (k + 18) (win hk 17 1) (by rfl) (by rfl)
    (rsp.toBitVec - 56) (rsp.toBitVec - 40) (by eb) t40 ht40 _ _ _ (by rfl) (by ecancel)
  intro m5 H5; kn; try dsimp only at H5
  rw [lr_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 56), show (rsp.toBitVec - 56) + 8 = (rsp.toBitVec - 48) by bv_omega] at H5
  apply kstep_st Reg64.r8 Reg64.rsp 104 _ (k + 18) (k + 19) (win hk 18 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 56) (by eb) ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).take 8) (by rw [List.length_take, Int.toBytes_length]; rfl) _ _ _ (by rfl) (by ecancel)
  intro m6 H6; kn; simp only [Reg64s.get64] at H6
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v0 hv0] at H6
  have hl33 := Fk.label_at' hk hf (j := 33)
    (by simp only [BhMarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [BhMarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply kstep_cmp_jae_t Reg64.rdi Reg64.rdx _ _ (k + 19) (k + 33) (win hk 19 2) (by rfl) hl33 _ _ (by show ((rcx.toBitVec + 8) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; kn
  apply kstep_label _ _ (k + 33) (k + 34) (win hk 33 1) (by rfl) (by rfl)
  apply kstep_ldb Reg64.r8 Reg64.rsp 104 _ (k + 34) (k + 35) (win hk 34 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 56) (by eb) v0 hv0 _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_st_idx Reg64.r8 Reg64.rbx Reg64.rcx 0 _ (k + 35) (k + 36) (win hk 35 1) (by rfl) (by rfl)
    rbx.toBitVec rcx.toBitVec (rbx.toBitVec + rcx.toBitVec) (by eb) d0 hd0 _ _ _ (by rfl) (by rfl) (by ecancel)
  intro m7 H7; kn; simp only [Reg64s.get64] at H7
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v0 hv0] at H7
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8), (Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt), (by rw [List.length_drop, Int.toBytes_length]), (Int.toBytes_length 16 _), ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem bh_g6_f0_kind : ∀ (h : Host), type_of% (@bh_g6_f0 h)
    = @E2eScal.encFieldKindN h BhMarshal E2eScal.layEncBh [.u64, .u64, .bytes 32, .bytes 32, .bytes 32]
    ⟨10, 0, [(.rax, .rcv), (.rbx, .ptr), (.rcx, .len 0), (.rdi, .cap)],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 16) (.orig 3), .at (.dn 96) (.orig 4), .at (.dn 104) (.orig 5), .at (.dn 56) (.orig 6), .at (.dn 40) (.orig 7), .at (.dn 88) (.orig 8), .at (.dn 72) (.orig 9), .at (.dn 168) (.orig 10), .lo .scr],
      []⟩
    ⟨36, 1, [(.rax, .rcv), (.rbx, .ptr), (.rdx, .len 8), (.rdi, .cap)],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 16) (.orig 3), .at (.dn 96) (.orig 4), .at (.dn 104) (.orig 5), .at (.dn 56) (.fld 0), .at (.dn 48) (.ex 0), .at (.dn 40) (.ex 1), .at (.dn 88) (.orig 8), .at (.dn 72) (.orig 9), .at (.dn 168) (.orig 10), .lo .scr],
      [.n 8, .n 16]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 1 `ProposerIndex` (uint64): directives 36–61; boundary state 1 → 2. -/
theorem bh_g6_f1 : ∀ (k : Nat) (hk : BhMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh BhMarshal k)
    (ast v0 v1 c2 c3 c4 b2 b3 b4 pre d0 d1 d2 d3 d4 : List UInt8) (hast : ast.length = 8) (hv0 : v0.length = 8) (hv1 : v1.length = 8) (hc2 : c2.length = 8) (hc3 : c3.length = 8) (hc4 : c4.length = 8) (hb2 : b2.length = 32) (hb3 : b3.length = 32) (hb4 : b4.length = 32) (hd0 : d0.length = 8) (hd1 : d1.length = 8) (hd2 : d2.length = 32) (hd3 : d3.length = 32) (hd4 : d4.length = 32)
    (p2 p3 p4 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l96 l104 t56 t40 t88 t72 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8) (hl96 : l96.length = 8) (hl104 : l104.length = 8) (ht56 : t56.length = 16) (ht40 : t40.length = 16) (ht88 : t88.length = 16) (ht72 : t72.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 168 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 112 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveC S) (st0 : MachineState),
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
  apply kstep_lea Reg64.r8 Reg64.rdx 8 _ (k + 36) (k + 37) (win hk 36 1) (by rfl) (by rfl)
  kn
  apply kreg_eq Reg64.r8 (rcx.toBitVec + 16) _ _ _ (by show ((rcx.toBitVec + 8) + 8 : BitVec 64) = (rcx.toBitVec + 16); bv_omega)
  kn
  apply kstep_ldb Reg64.r9 Reg64.rax 16 _ (k + 37) (k + 38) (win hk 37 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 16) (by eb) v1 hv1 _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_lea Reg64.r10 Reg64.rsp 72 _ (k + 38) (k + 42) (win hk 38 4) (by rfl) (by rfl)
  kn
  apply kreg_eq Reg64.r10 (rsp.toBitVec - 88) _ _ _ (by show ((rsp.toBitVec - 160) + 72 : BitVec 64) = (rsp.toBitVec - 88); bv_omega)
  kn
  apply kstep_movups15 Reg64.r10 0 _ (k + 42) (k + 43) (win hk 42 1) (by rfl) (by rfl)
    (rsp.toBitVec - 88) (rsp.toBitVec - 88) (by eb) t88 ht88 _ _ _ (by rfl) (by ecancel)
  intro m8 H8; kn; try dsimp only at H8
  apply kstep_movups15 Reg64.r10 16 _ (k + 43) (k + 44) (win hk 43 1) (by rfl) (by rfl)
    (rsp.toBitVec - 88) (rsp.toBitVec - 72) (by eb) t72 ht72 _ _ _ (by rfl) (by ecancel)
  intro m9 H9; kn; try dsimp only at H9
  rw [lr_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 88), show (rsp.toBitVec - 88) + 8 = (rsp.toBitVec - 80) by bv_omega] at H9
  apply kstep_st Reg64.r9 Reg64.rsp 72 _ (k + 44) (k + 45) (win hk 44 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 88) (by eb) ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).take 8) (by rw [List.length_take, Int.toBytes_length]; rfl) _ _ _ (by rfl) (by ecancel)
  intro m10 H10; kn; simp only [Reg64s.get64] at H10
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v1 hv1] at H10
  have hl59 := Fk.label_at' hk hf (j := 59)
    (by simp only [BhMarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [BhMarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply kstep_cmp_jae_t Reg64.rdi Reg64.r8 _ _ (k + 45) (k + 59) (win hk 45 2) (by rfl) hl59 _ _ (by show ((rcx.toBitVec + 16) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; kn
  apply kstep_label _ _ (k + 59) (k + 60) (win hk 59 1) (by rfl) (by rfl)
  apply kstep_ldb Reg64.r9 Reg64.rsp 72 _ (k + 60) (k + 61) (win hk 60 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 88) (by eb) v1 hv1 _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_st_idx Reg64.r9 Reg64.rbx Reg64.rdx 0 _ (k + 61) (k + 62) (win hk 61 1) (by rfl) (by rfl)
    rbx.toBitVec (rcx.toBitVec + 8) (rbx.toBitVec + rcx.toBitVec + 8) (by eb) d1 hd1 _ _ _ (by rfl) (by rfl) (by ecancel)
  intro m11 H11; kn; simp only [Reg64s.get64] at H11
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v1 hv1] at H11
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, x0, x1, ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8), (Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt), hx0, hx1, (by rw [List.length_drop, Int.toBytes_length]), (Int.toBytes_length 16 _), ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem bh_g6_f1_kind : ∀ (h : Host), type_of% (@bh_g6_f1 h)
    = @E2eScal.encFieldKindN h BhMarshal E2eScal.layEncBh [.u64, .u64, .bytes 32, .bytes 32, .bytes 32]
    ⟨36, 1, [(.rax, .rcv), (.rbx, .ptr), (.rdx, .len 8), (.rdi, .cap)],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 16) (.orig 3), .at (.dn 96) (.orig 4), .at (.dn 104) (.orig 5), .at (.dn 56) (.fld 0), .at (.dn 48) (.ex 0), .at (.dn 40) (.ex 1), .at (.dn 88) (.orig 8), .at (.dn 72) (.orig 9), .at (.dn 168) (.orig 10), .lo .scr],
      [.n 8, .n 16]⟩
    ⟨62, 2, [(.rax, .rcv), (.rbx, .ptr), (.rdi, .cap), (.r8, .len 16)],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 16) (.orig 3), .at (.dn 96) (.orig 4), .at (.dn 104) (.orig 5), .at (.dn 56) (.fld 0), .at (.dn 48) (.ex 0), .at (.dn 40) (.ex 1), .at (.dn 88) (.fld 1), .at (.dn 80) (.ex 2), .at (.dn 72) (.ex 3), .at (.dn 168) (.orig 10), .lo .scr],
      [.n 8, .n 16, .n 8, .n 16]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 2 `ParentRoot` (32 bytes): directives 62–89; boundary state 2 → 3. -/
theorem bh_g6_f2 : ∀ (k : Nat) (hk : BhMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh BhMarshal k)
    (ast v0 v1 c2 c3 c4 b2 b3 b4 pre d0 d1 d2 d3 d4 : List UInt8) (hast : ast.length = 8) (hv0 : v0.length = 8) (hv1 : v1.length = 8) (hc2 : c2.length = 8) (hc3 : c3.length = 8) (hc4 : c4.length = 8) (hb2 : b2.length = 32) (hb3 : b3.length = 32) (hb4 : b4.length = 32) (hd0 : d0.length = 8) (hd1 : d1.length = 8) (hd2 : d2.length = 32) (hd3 : d3.length = 32) (hd4 : d4.length = 32)
    (p2 p3 p4 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l96 l104 t56 t40 t88 t72 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8) (hl96 : l96.length = 8) (hl104 : l104.length = 8) (ht56 : t56.length = 16) (ht40 : t40.length = 16) (ht88 : t88.length = 16) (ht72 : t72.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 168 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 112 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveC S) (st0 : MachineState),
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
  apply kstep_ldv Reg64.rdx Reg64.rax 24 _ (k + 62) (k + 63) (win hk 62 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 24) p2 (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_lenchk Reg64.rax 32 32 _ _ (k + 63) (k + 66) (win hk 63 3) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 32) (by eb) (Int.toBytes 8 32) (by rfl) (by decide) _ _ _ (by rfl) (by ecancel)
  intro fl; kn
  apply kstep_lea Reg64.r9 Reg64.r8 32 _ (k + 66) (k + 67) (win hk 66 1) (by rfl) (by rfl)
  kn
  apply kreg_eq Reg64.r9 (rcx.toBitVec + 48) _ _ _ (by show ((rcx.toBitVec + 16) + 32 : BitVec 64) = (rcx.toBitVec + 48); bv_omega)
  kn
  have hl82 := Fk.label_at' hk hf (j := 82)
    (by simp only [BhMarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [BhMarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply kstep_cmp_jae_t Reg64.rdi Reg64.r9 _ _ (k + 67) (k + 82) (win hk 67 2) (by rfl) hl82 _ _ (by show ((rcx.toBitVec + 48) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; kn
  apply kstep_label _ _ (k + 82) (k + 83) (win hk 82 1) (by rfl) (by rfl)
  apply kstep_st Reg64.rbx Reg64.rsp 144 _ (k + 83) (k + 84) (win hk 83 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 16) (by eb) l16 hl16 _ _ _ (by rfl) (by ecancel)
  intro m12 H12; kn; simp only [Reg64s.get64] at H12
  apply kstep_st Reg64.r9 Reg64.rsp 64 _ (k + 84) (k + 85) (win hk 84 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 96) (by eb) l96 hl96 _ _ _ (by rfl) (by ecancel)
  intro m13 H13; kn; simp only [Reg64s.get64] at H13
  apply kstep_st Reg64.rdi Reg64.rsp 56 _ (k + 85) (k + 86) (win hk 85 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 104) (by eb) l104 hl104 _ _ _ (by rfl) (by ecancel)
  intro m14 H14; kn; simp only [Reg64s.get64] at H14
  apply kstep_lea_idx Reg64.rax Reg64.rbx Reg64.r8 _ (k + 86) (k + 87) (win hk 86 1) (by rfl) (by rfl)
  kn
  apply kreg_eq Reg64.rax (rbx.toBitVec + rcx.toBitVec + 16) _ _ _ (by show (rbx.toBitVec + (rcx.toBitVec + 16) : BitVec 64) = (rbx.toBitVec + rcx.toBitVec + 16); bv_omega)
  kn
  apply kstep_mov_rr Reg64.rbx Reg64.rdx _ (k + 87) (k + 88) (win hk 87 1) (by rfl) (by rfl)
  kn
  apply kstep_movi Reg64.rcx 32 _ (k + 88) (k + 89) (win hk 88 1) (by rfl) (by rfl)
  kn
  apply kreg_eq Reg64.rcx 32 _ _ _ (by show (BitVec.zeroExtend 64 (BitVec.truncate 32 (32 : BitVec 64)) : BitVec 64) = 32; decide)
  kn
  refine eventually_trans _ _ _ _ (encn_call (k + 89) (win hk 89 1) (rsp.toBitVec - 160) (rbx.toBitVec + rcx.toBitVec + 16) p2
    (rsp.toBitVec - 168) (rsp.toBitVec - 168 - BitVec.ofNat 64 S) S (by bv_omega) (E2eScal.g5_lo0 rsp.toBitVec 160 168 S (by decide))
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
theorem bh_g6_f2_kind : ∀ (h : Host), type_of% (@bh_g6_f2 h)
    = @E2eScal.encFieldKindN h BhMarshal E2eScal.layEncBh [.u64, .u64, .bytes 32, .bytes 32, .bytes 32]
    ⟨62, 2, [(.rax, .rcv), (.rbx, .ptr), (.rdi, .cap), (.r8, .len 16)],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 16) (.orig 3), .at (.dn 96) (.orig 4), .at (.dn 104) (.orig 5), .at (.dn 56) (.fld 0), .at (.dn 48) (.ex 0), .at (.dn 40) (.ex 1), .at (.dn 88) (.fld 1), .at (.dn 80) (.ex 2), .at (.dn 72) (.ex 3), .at (.dn 168) (.orig 10), .lo .scr],
      [.n 8, .n 16, .n 8, .n 16]⟩
    ⟨90, 3, [],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 16) (.reg .rbx), .at (.dn 96) (.len 48), .at (.dn 104) (.reg .rdi), .at (.dn 56) (.fld 0), .at (.dn 48) (.ex 0), .at (.dn 40) (.ex 1), .at (.dn 88) (.fld 1), .at (.dn 80) (.ex 2), .at (.dn 72) (.ex 3), .at (.dn 168) (.ret 90), .lo (.ex 4)],
      [.n 8, .n 16, .n 8, .n 16, .lo]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 3 `StateRoot` (32 bytes): directives 90–117; boundary state 3 → 4. -/
theorem bh_g6_f3 : ∀ (k : Nat) (hk : BhMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh BhMarshal k)
    (ast v0 v1 c2 c3 c4 b2 b3 b4 pre d0 d1 d2 d3 d4 : List UInt8) (hast : ast.length = 8) (hv0 : v0.length = 8) (hv1 : v1.length = 8) (hc2 : c2.length = 8) (hc3 : c3.length = 8) (hc4 : c4.length = 8) (hb2 : b2.length = 32) (hb3 : b3.length = 32) (hb4 : b4.length = 32) (hd0 : d0.length = 8) (hd1 : d1.length = 8) (hd2 : d2.length = 32) (hd3 : d3.length = 32) (hd4 : d4.length = 32)
    (p2 p3 p4 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l96 l104 t56 t40 t88 t72 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8) (hl96 : l96.length = 8) (hl104 : l104.length = 8) (ht56 : t56.length = 16) (ht40 : t40.length = 16) (ht88 : t88.length = 16) (ht72 : t72.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 168 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 112 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveC S) (st0 : MachineState),
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
  apply kstep_ldv Reg64.rdx Reg64.rsp 168 _ (k + 90) (k + 91) (win hk 90 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec + 8) rax.toBitVec (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_ldv Reg64.rbx Reg64.rdx 48 _ (k + 91) (k + 92) (win hk 91 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 48) p3 (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_lenchk Reg64.rdx 56 32 _ _ (k + 92) (k + 94) (win hk 92 2) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 56) (by eb) (Int.toBytes 8 32) (by rfl) (by decide) _ _ _ (by rfl) (by ecancel)
  intro fl; kn
  apply kstep_ldv Reg64.r8 Reg64.rsp 64 _ (k + 94) (k + 95) (win hk 94 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 96) (rcx.toBitVec + 48) (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_lea Reg64.r9 Reg64.r8 32 _ (k + 95) (k + 96) (win hk 95 1) (by rfl) (by rfl)
  kn
  apply kreg_eq Reg64.r9 (rcx.toBitVec + 80) _ _ _ (by show ((rcx.toBitVec + 48) + 32 : BitVec 64) = (rcx.toBitVec + 80); bv_omega)
  kn
  apply kstep_ldv Reg64.rcx Reg64.rsp 56 _ (k + 96) (k + 97) (win hk 96 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 104) rdi.toBitVec (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_cmp_jb_f Reg64.rcx Reg64.r9 _ _ (k + 97) (k + 99) (win hk 97 2) (by rfl) (by rfl) _ _ (by show ((rcx.toBitVec + 80) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; kn
  apply kstep_ldv Reg64.rax Reg64.rsp 144 _ (k + 99) (k + 100) (win hk 99 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 16) rbx.toBitVec (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  have hl111 := Fk.label_at' hk hf (j := 111)
    (by simp only [BhMarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [BhMarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply kstep_jmp _ _ (k + 100) (k + 111) (win hk 100 1) (by rfl) hl111
  apply kstep_label _ _ (k + 111) (k + 112) (win hk 111 1) (by rfl) (by rfl)
  apply kstep_st Reg64.rcx Reg64.rsp 64 _ (k + 112) (k + 113) (win hk 112 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 96) (by eb) (Int.toBytes 8 (rcx.toBitVec + 48).toInt) (Int.toBytes_length 8 _) _ _ _ (by rfl) (by ecancel)
  intro m15 H15; kn; simp only [Reg64s.get64] at H15
  apply kstep_st Reg64.r9 Reg64.rsp 56 _ (k + 113) (k + 114) (win hk 113 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 104) (by eb) (Int.toBytes 8 rdi.toBitVec.toInt) (Int.toBytes_length 8 _) _ _ _ (by rfl) (by ecancel)
  intro m16 H16; kn; simp only [Reg64s.get64] at H16
  apply kstep_st Reg64.rax Reg64.rsp 144 _ (k + 114) (k + 115) (win hk 114 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 16) (by eb) (Int.toBytes 8 rbx.toBitVec.toInt) (Int.toBytes_length 8 _) _ _ _ (by rfl) (by ecancel)
  intro m17 H17; kn; simp only [Reg64s.get64] at H17
  apply kstep_add_rr Reg64.rax Reg64.r8 _ (k + 115) (k + 116) (win hk 115 1) (by rfl) (by rfl)
  intro fl; kn
  apply kreg_eq Reg64.rax (rbx.toBitVec + rcx.toBitVec + 48) _ _ _ (by show (rbx.toBitVec + (rcx.toBitVec + 48) : BitVec 64) = (rbx.toBitVec + rcx.toBitVec + 48); bv_omega)
  kn
  apply kstep_movi Reg64.rcx 32 _ (k + 116) (k + 117) (win hk 116 1) (by rfl) (by rfl)
  kn
  apply kreg_eq Reg64.rcx 32 _ _ _ (by show (BitVec.zeroExtend 64 (BitVec.truncate 32 (32 : BitVec 64)) : BitVec 64) = 32; decide)
  kn
  refine eventually_trans _ _ _ _ (encn_call (k + 117) (win hk 117 1) (rsp.toBitVec - 160) (rbx.toBitVec + rcx.toBitVec + 48) p3
    (rsp.toBitVec - 168) (rsp.toBitVec - 168 - BitVec.ofNat 64 S) S (by bv_omega) (E2eScal.g5_lo0 rsp.toBitVec 160 168 S (by decide))
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
theorem bh_g6_f3_kind : ∀ (h : Host), type_of% (@bh_g6_f3 h)
    = @E2eScal.encFieldKindN h BhMarshal E2eScal.layEncBh [.u64, .u64, .bytes 32, .bytes 32, .bytes 32]
    ⟨90, 3, [],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 16) (.reg .rbx), .at (.dn 96) (.len 48), .at (.dn 104) (.reg .rdi), .at (.dn 56) (.fld 0), .at (.dn 48) (.ex 0), .at (.dn 40) (.ex 1), .at (.dn 88) (.fld 1), .at (.dn 80) (.ex 2), .at (.dn 72) (.ex 3), .at (.dn 168) (.ret 90), .lo (.ex 4)],
      [.n 8, .n 16, .n 8, .n 16, .lo]⟩
    ⟨118, 4, [],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 16) (.reg .rbx), .at (.dn 96) (.reg .rdi), .at (.dn 104) (.len 80), .at (.dn 56) (.fld 0), .at (.dn 48) (.ex 0), .at (.dn 40) (.ex 1), .at (.dn 88) (.fld 1), .at (.dn 80) (.ex 2), .at (.dn 72) (.ex 3), .at (.dn 168) (.ret 118), .lo (.ex 4)],
      [.n 8, .n 16, .n 8, .n 16, .lo]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 4 `BodyRoot` (32 bytes): directives 118–147; boundary state 4 → 5. -/
theorem bh_g6_f4 : ∀ (k : Nat) (hk : BhMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh BhMarshal k)
    (ast v0 v1 c2 c3 c4 b2 b3 b4 pre d0 d1 d2 d3 d4 : List UInt8) (hast : ast.length = 8) (hv0 : v0.length = 8) (hv1 : v1.length = 8) (hc2 : c2.length = 8) (hc3 : c3.length = 8) (hc4 : c4.length = 8) (hb2 : b2.length = 32) (hb3 : b3.length = 32) (hb4 : b4.length = 32) (hd0 : d0.length = 8) (hd1 : d1.length = 8) (hd2 : d2.length = 32) (hd3 : d3.length = 32) (hd4 : d4.length = 32)
    (p2 p3 p4 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l96 l104 t56 t40 t88 t72 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8) (hl96 : l96.length = 8) (hl104 : l104.length = 8) (ht56 : t56.length = 16) (ht40 : t40.length = 16) (ht88 : t88.length = 16) (ht72 : t72.length = 16) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 168 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 112 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveC S) (st0 : MachineState),
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
  apply kstep_ldv Reg64.rdx Reg64.rsp 168 _ (k + 118) (k + 119) (win hk 118 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec + 8) rax.toBitVec (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_ldv Reg64.rbx Reg64.rdx 72 _ (k + 119) (k + 120) (win hk 119 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 72) p4 (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_lenchk Reg64.rdx 80 32 _ _ (k + 120) (k + 122) (win hk 120 2) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 80) (by eb) (Int.toBytes 8 32) (by rfl) (by decide) _ _ _ (by rfl) (by ecancel)
  intro fl; kn
  apply kstep_ldv Reg64.rdx Reg64.rsp 56 _ (k + 122) (k + 123) (win hk 122 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 104) (rcx.toBitVec + 80) (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_lea Reg64.r8 Reg64.rdx 32 _ (k + 123) (k + 124) (win hk 123 1) (by rfl) (by rfl)
  kn
  apply kreg_eq Reg64.r8 (rcx.toBitVec + 112) _ _ _ (by show ((rcx.toBitVec + 80) + 32 : BitVec 64) = (rcx.toBitVec + 112); bv_omega)
  kn
  apply kstep_ldv Reg64.rcx Reg64.rsp 64 _ (k + 124) (k + 125) (win hk 124 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 96) rdi.toBitVec (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_cmp_jb_f Reg64.rcx Reg64.r8 _ _ (k + 125) (k + 128) (win hk 125 3) (by rfl) (by rfl) _ _ (by show ((rcx.toBitVec + 112) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; kn
  apply kstep_ldv Reg64.rax Reg64.rsp 144 _ (k + 128) (k + 129) (win hk 128 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 16) rbx.toBitVec (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  have hl140 := Fk.label_at' hk hf (j := 140)
    (by simp only [BhMarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [BhMarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply kstep_jmp _ _ (k + 129) (k + 140) (win hk 129 1) (by rfl) hl140
  apply kstep_label _ _ (k + 140) (k + 141) (win hk 140 1) (by rfl) (by rfl)
  apply kstep_st Reg64.rcx Reg64.rsp 64 _ (k + 141) (k + 142) (win hk 141 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 96) (by eb) (Int.toBytes 8 rdi.toBitVec.toInt) (Int.toBytes_length 8 _) _ _ _ (by rfl) (by ecancel)
  intro m18 H18; kn; simp only [Reg64s.get64] at H18
  apply kstep_st Reg64.r8 Reg64.rsp 56 _ (k + 142) (k + 143) (win hk 142 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 104) (by eb) (Int.toBytes 8 (rcx.toBitVec + 80).toInt) (Int.toBytes_length 8 _) _ _ _ (by rfl) (by ecancel)
  intro m19 H19; kn; simp only [Reg64s.get64] at H19
  apply kstep_st Reg64.rax Reg64.rsp 144 _ (k + 143) (k + 144) (win hk 143 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 16) (by eb) (Int.toBytes 8 rbx.toBitVec.toInt) (Int.toBytes_length 8 _) _ _ _ (by rfl) (by ecancel)
  intro m20 H20; kn; simp only [Reg64s.get64] at H20
  apply kstep_add_rr Reg64.rax Reg64.rdx _ (k + 144) (k + 145) (win hk 144 1) (by rfl) (by rfl)
  intro fl; kn
  apply kreg_eq Reg64.rax (rbx.toBitVec + rcx.toBitVec + 80) _ _ _ (by show (rbx.toBitVec + (rcx.toBitVec + 80) : BitVec 64) = (rbx.toBitVec + rcx.toBitVec + 80); bv_omega)
  kn
  apply kstep_movi Reg64.rcx 32 _ (k + 145) (k + 146) (win hk 145 1) (by rfl) (by rfl)
  kn
  apply kreg_eq Reg64.rcx 32 _ _ _ (by show (BitVec.zeroExtend 64 (BitVec.truncate 32 (32 : BitVec 64)) : BitVec 64) = 32; decide)
  kn
  apply kstep_nops _ (k + 146) (k + 147) (win hk 146 1) (by rfl) (by rfl)
  refine eventually_trans _ _ _ _ (encn_call (k + 147) (win hk 147 1) (rsp.toBitVec - 160) (rbx.toBitVec + rcx.toBitVec + 80) p4
    (rsp.toBitVec - 168) (rsp.toBitVec - 168 - BitVec.ofNat 64 S) S (by bv_omega) (E2eScal.g5_lo0 rsp.toBitVec 160 168 S (by decide))
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
theorem bh_g6_f4_kind : ∀ (h : Host), type_of% (@bh_g6_f4 h)
    = @E2eScal.encFieldKindN h BhMarshal E2eScal.layEncBh [.u64, .u64, .bytes 32, .bytes 32, .bytes 32]
    ⟨118, 4, [],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 16) (.reg .rbx), .at (.dn 96) (.reg .rdi), .at (.dn 104) (.len 80), .at (.dn 56) (.fld 0), .at (.dn 48) (.ex 0), .at (.dn 40) (.ex 1), .at (.dn 88) (.fld 1), .at (.dn 80) (.ex 2), .at (.dn 72) (.ex 3), .at (.dn 168) (.ret 118), .lo (.ex 4)],
      [.n 8, .n 16, .n 8, .n 16, .lo]⟩
    ⟨148, 5, [],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 16) (.reg .rbx), .at (.dn 96) (.reg .rdi), .at (.dn 104) (.len 112), .at (.dn 56) (.fld 0), .at (.dn 48) (.ex 0), .at (.dn 40) (.ex 1), .at (.dn 88) (.fld 1), .at (.dn 80) (.ex 2), .at (.dn 72) (.ex 3), .at (.dn 168) (.ret 148), .lo (.ex 4)],
      [.n 8, .n 16, .n 8, .n 16, .lo]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Epilogue: directives 148–return; boundary state 5 → the fast-path post-state. -/
theorem bh_g6_epi : ∀ (k : Nat) (hk : BhMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh BhMarshal k)
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
  apply kstep_ldv Reg64.rax Reg64.rsp 144 _ (k + 148) (k + 149) (win hk 148 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 16) rbx.toBitVec (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_ldv Reg64.rbx Reg64.rsp 56 _ (k + 149) (k + 150) (win hk 149 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 104) (rcx.toBitVec + 112) (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_ldv Reg64.rcx Reg64.rsp 64 _ (k + 150) (k + 151) (win hk 150 1) (by rfl) (by rfl)
    (rsp.toBitVec - 160) (rsp.toBitVec - 96) rdi.toBitVec (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_xor32 Reg64.rdi _ (k + 151) (k + 152) (win hk 151 1) (by rfl) (by rfl)
  intro fl; kn
  apply kstep_xor32 Reg64.rsi _ (k + 152) (k + 153) (win hk 152 1) (by rfl) (by rfl)
  intro fl; kn
  apply kstep_add Reg64.rsp 152 _ (k + 153) (k + 154) (win hk 153 1) (by rfl) (by rfl)
  intro fl; kn
  apply kreg_eq Reg64.rsp (rsp.toBitVec - 8) _ _ _ (by show ((rsp.toBitVec - 160) + 152 : BitVec 64) = (rsp.toBitVec - 8); bv_omega)
  kn
  refine eventually_trans _ _ _ _ (decret_seg _ (k + 154) (win hk 154 2) (by rfl) (rsp.toBitVec - 8) rsp.toBitVec (by bv_omega) rbp ra _ _ (by rfl) (by ecancel)) ?_
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
theorem bh_g6_epi_kind : ∀ (h : Host), type_of% (@bh_g6_epi h)
    = @E2eScal.encEpiKindN h BhMarshal E2eScal.layEncBh [.u64, .u64, .bytes 32, .bytes 32, .bytes 32]
    ⟨148, 5, [],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 16) (.reg .rbx), .at (.dn 96) (.reg .rdi), .at (.dn 104) (.len 112), .at (.dn 56) (.fld 0), .at (.dn 48) (.ex 0), .at (.dn 40) (.ex 1), .at (.dn 88) (.fld 1), .at (.dn 80) (.ex 2), .at (.dn 72) (.ex 3), .at (.dn 168) (.ret 148), .lo (.ex 4)],
      [.n 8, .n 16, .n 8, .n 16, .lo]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Fast path of `(*v1alpha1.BeaconBlockHeader).MarshalSSZTo` (Go 1.26.10), generated-style proof**: head, one theorem per
field, epilogue, chained by `eventually_trans`. Premises: `len + 112 ≤ cap`, every byte-vector field of its exact
length. Statement = the kind instance (`_kind`). Fast path only. -/
theorem bh_e2e_marshal_g6 : ∀ (k : Nat) (hk : BhMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh BhMarshal k)
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
    (hcap : s.regs.rcx.toNat + 112 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveC S),
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
  refine eventually_trans _ _ _ _ (bh_g6_head k hk hf ast v0 v1 c2 c3 c4 b2 b3 b4 pre d0 d1 d2 d3 d4 hast hv0 hv1 hc2 hc3 hc4 hb2 hb3 hb4 hd0 hd1 hd2 hd3 hd4 p2 p3 p4 s ra guard hpre fp s1 s2 l16 l96 l104 t56 t40 t88 t72 rslot hfp hs1 hs2 hl16 hl96 hl104 ht56 ht40 ht88 ht72 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm) ?_
  intro st0 h0
  refine eventually_trans _ _ _ _ (bh_g6_f0 k hk hf ast v0 v1 c2 c3 c4 b2 b3 b4 pre d0 d1 d2 d3 d4 hast hv0 hv1 hc2 hc3 hc4 hb2 hb3 hb4 hd0 hd1 hd2 hd3 hd4 p2 p3 p4 s ra guard hpre fp s1 s2 l16 l96 l104 t56 t40 t88 t72 rslot hfp hs1 hs2 hl16 hl96 hl104 ht56 ht40 ht88 ht72 hrslot R S scratch hsc hsp hcap hcap63 hmm st0 h0) ?_
  intro st1 h1
  refine eventually_trans _ _ _ _ (bh_g6_f1 k hk hf ast v0 v1 c2 c3 c4 b2 b3 b4 pre d0 d1 d2 d3 d4 hast hv0 hv1 hc2 hc3 hc4 hb2 hb3 hb4 hd0 hd1 hd2 hd3 hd4 p2 p3 p4 s ra guard hpre fp s1 s2 l16 l96 l104 t56 t40 t88 t72 rslot hfp hs1 hs2 hl16 hl96 hl104 ht56 ht40 ht88 ht72 hrslot R S scratch hsc hsp hcap hcap63 hmm st1 h1) ?_
  intro st2 h2
  refine eventually_trans _ _ _ _ (bh_g6_f2 k hk hf ast v0 v1 c2 c3 c4 b2 b3 b4 pre d0 d1 d2 d3 d4 hast hv0 hv1 hc2 hc3 hc4 hb2 hb3 hb4 hd0 hd1 hd2 hd3 hd4 p2 p3 p4 s ra guard hpre fp s1 s2 l16 l96 l104 t56 t40 t88 t72 rslot hfp hs1 hs2 hl16 hl96 hl104 ht56 ht40 ht88 ht72 hrslot R S scratch hsc hsp hcap hcap63 hmm st2 h2) ?_
  intro st3 h3
  refine eventually_trans _ _ _ _ (bh_g6_f3 k hk hf ast v0 v1 c2 c3 c4 b2 b3 b4 pre d0 d1 d2 d3 d4 hast hv0 hv1 hc2 hc3 hc4 hb2 hb3 hb4 hd0 hd1 hd2 hd3 hd4 p2 p3 p4 s ra guard hpre fp s1 s2 l16 l96 l104 t56 t40 t88 t72 rslot hfp hs1 hs2 hl16 hl96 hl104 ht56 ht40 ht88 ht72 hrslot R S scratch hsc hsp hcap hcap63 hmm st3 h3) ?_
  intro st4 h4
  refine eventually_trans _ _ _ _ (bh_g6_f4 k hk hf ast v0 v1 c2 c3 c4 b2 b3 b4 pre d0 d1 d2 d3 d4 hast hv0 hv1 hc2 hc3 hc4 hb2 hb3 hb4 hd0 hd1 hd2 hd3 hd4 p2 p3 p4 s ra guard hpre fp s1 s2 l16 l96 l104 t56 t40 t88 t72 rslot hfp hs1 hs2 hl16 hl96 hl104 ht56 ht40 ht88 ht72 hrslot R S scratch hsc hsp hcap hcap63 hmm st4 h4) ?_
  intro st5 h5
  exact bh_g6_epi k hk hf ast v0 v1 c2 c3 c4 b2 b3 b4 pre d0 d1 d2 d3 d4 hast hv0 hv1 hc2 hc3 hc4 hb2 hb3 hb4 hd0 hd1 hd2 hd3 hd4 p2 p3 p4 s ra guard hpre fp s1 s2 l16 l96 l104 t56 t40 t88 t72 rslot hfp hs1 hs2 hl16 hl96 hl104 ht56 ht40 ht88 ht72 hrslot R S scratch hsc hsp hcap hcap63 st5 h5
theorem bh_e2e_marshal_g6_kind : ∀ (h : Host), type_of% (@bh_e2e_marshal_g6 h)
    = @E2eScal.encFastKindN h BhMarshal E2eScal.layEncBh [.u64, .u64, .bytes 32, .bytes 32, .bytes 32] := by
  intro h; rfl

/-- The generated-style theorem proves the committed hand statement. -/
theorem bh_e2e_marshal_g6_stmt : type_of% (@E2eScal.Bh.bh_e2e_marshal_main ‹Host›) := bh_e2e_marshal_g6

end E2eScal.Gen6
