import E2eScal.EncTies
import E2eScal.EncFrameTest
import E2eScal.Enc2Code

/-!
# GEN6 (`p2enc --gen6`, unit E2-G): encoder fast path of `(*v1alpha1.PendingConsolidation).MarshalSSZTo`

Generated from the `.S` file and the IR: a symbolic dataflow walk of the fast path, one application of a
step lemma per directive (windows with the nops erased), boundary states between the fields. Every theorem
has a `_kind` line (`encHeadKindN`, `encFieldKindN`, `encEpiKindN`, `encFastKindN`).
**Fast path only**: `len(dst) + 16 ≤ cap(dst)` and every byte-vector field of its exact length. No
`runtime.growslice` directive is stepped: each capacity test is decided from the premise. Not covered: the
growslice branches, the length rejects, the morestack path. Not a complete encoder result.
GEN6-JSON: {"type": "PendingConsolidation", "const": "PcMarshal", "prefix": "pc_g6e", "size": 16, "frame": 112, "gd": 0, "rt": false, "fields": [["SourceIndex", "u", 8], ["TargetIndex", "u", 8]], "boundaries": [8, 35, 60], "layout": "E2eScal.Gen6Enc.pc_g6e_layout", "S_sha256": "06564f29c3d2813bf0ee98d06c9ddcf6fd0a78b15d1b7091bc399ef628bcd0cb", "ir_sha256": "c1586d32018abd182c16d50f6a7a76e38814cab08cf4a7a42105fe30342a5d2a", "statement_check": "kind instance only", "S": "prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.MarshalSSZTo.S", "ir": "prysm/ir/ir-mainnet.json", "ir_type": "v1alpha1.PendingConsolidation", "kinds": [{"theorem": "pc_g6e_head", "kind": "encHeadKindN"}, {"theorem": "pc_g6e_f0", "kind": "encFieldKindN"}, {"theorem": "pc_g6e_f1", "kind": "encFieldKindN"}, {"theorem": "pc_g6e_epi", "kind": "encEpiKindN"}, {"theorem": "pc_g6e_fast", "kind": "encFastKindN"}]}
-/

open Fk E2eScal E2eScal.Enc2Code
variable [Host]

namespace E2eScal.Gen6Enc

/-- The frame facts of `PcMarshal` (read from the `.S` file by the walk): frame `0x70`, stack chunks
`fp s2 t40 t24 t72 t56`. -/
def pc_g6e_layout : EncLayout where
  st := true
  frame := 112
  gd := 0
  rt := false
  nstk := 6
  lens := [(0, 8), (1, 8), (2, 16), (3, 16), (4, 16), (5, 16)]
  pre := [.at (.dn 8) (.orig 0), .at (.up 16) (.orig 1), .at (.dn 40) (.orig 2), .at (.dn 24) (.orig 3), .at (.dn 72) (.orig 4), .at (.dn 56) (.orig 5)]
  exs := [.n 8, .n 16, .n 8, .n 16]
  post := [.at (.dn 8) (.reg .rbp), .at (.up 16) (.reg .rbx), .at (.dn 40) (.fld 0), .at (.dn 32) (.ex 0), .at (.dn 24) (.ex 1), .at (.dn 72) (.fld 1), .at (.dn 64) (.ex 2), .at (.dn 56) (.ex 3)]


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Head: directives 0–7 (stack guard, frame, spills); entry → boundary state 0. -/
theorem pc_g6e_head : ∀ (k : Nat) (hk : PcMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PcMarshal k)
    (ast v0 v1 pre d0 d1 : List UInt8) (hast : ast.length = 8) (hv0 : v0.length = 8) (hv1 : v1.length = 8) (hd0 : d0.length = 8) (hd1 : d1.length = 8)
    (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s2 t40 t24 t72 t56 : List UInt8) (hfp : fp.length = 8) (hs2 : s2.length = 8) (ht40 : t40.length = 16) (ht24 : t24.length = 16) (ht72 : t72.length = 16) (ht56 : t56.length = 16)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (t24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (t72.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (t56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
      ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 128 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 16 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 8)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 120 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.get64 Reg64.rax = s.regs.rax.toBitVec
        ∧ st.data.regs.get64 Reg64.rbx = s.regs.rbx.toBitVec
        ∧ st.data.regs.get64 Reg64.rcx = s.regs.rcx.toBitVec
        ∧ st.data.regs.get64 Reg64.rdi = s.regs.rdi.toBitVec ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (t24.At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (t72.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (t56.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf ast v0 v1 pre d0 d1 hast hv0 hv1 hd0 hd1 s ra guard hpre fp s2 t40 t24 t72 t56 hfp hs2 ht40 ht24 ht72 ht56 R h_mem hguard hsp hcap hcap63
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hcap hcap63 hpre ⊢
  have hcap' : rcx.toBitVec.toNat + 16 ≤ rdi.toBitVec.toNat := hcap
  apply encpro_s _ _ _ _ k (k + 6) (win hk 0 6) (by rfl) (by rfl) guard fp hfp _ _ _ (by dsimp only; ecancel) hguard
  intro m1 H1 fl1; kn; dsimp only at H1
  apply kstep_sub_i Reg64.rsp 112 _ (k + 6) (k + 7) (win hk 6 1) (by rfl) (by rfl)
  intro fl; kn
  apply kreg_eq Reg64.rsp (rsp.toBitVec - 120) _ _ _ (by show ((rsp.toBitVec - 8) - 112 : BitVec 64) = (rsp.toBitVec - 120); bv_omega)
  kn
  apply kstep_st Reg64.rbx Reg64.rsp 136 _ (k + 7) (k + 8) (win hk 7 1) (by rfl) (by rfl)
    (rsp.toBitVec - 120) (rsp.toBitVec + 16) (by eb) s2 hs2 _ _ _ (by rfl) (by ecancel)
  intro m2 H2; kn; simp only [Reg64s.get64] at H2
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem pc_g6e_head_kind : ∀ (h : Host), type_of% (@pc_g6e_head h)
    = @E2eScal.encHeadKindN h PcMarshal E2eScal.Gen6Enc.pc_g6e_layout [.u64, .u64]
    ⟨8, 0, [(.rax, .rcv), (.rbx, .ptr), (.rcx, .len 0), (.rdi, .cap)],
      [.at (.dn 8) (.reg .rbp), .at (.up 16) (.reg .rbx), .at (.dn 40) (.orig 2), .at (.dn 24) (.orig 3), .at (.dn 72) (.orig 4), .at (.dn 56) (.orig 5)],
      []⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 0 `SourceIndex` (uint64): directives 8–34; boundary state 0 → 1. -/
theorem pc_g6e_f0 : ∀ (k : Nat) (hk : PcMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PcMarshal k)
    (ast v0 v1 pre d0 d1 : List UInt8) (hast : ast.length = 8) (hv0 : v0.length = 8) (hv1 : v1.length = 8) (hd0 : d0.length = 8) (hd1 : d1.length = 8)
    (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s2 t40 t24 t72 t56 : List UInt8) (hfp : fp.length = 8) (hs2 : s2.length = 8) (ht40 : t40.length = 16) (ht24 : t24.length = 16) (ht72 : t72.length = 16) (ht56 : t56.length = 16)
    (R : DataMem → Prop)
    (hsp : 128 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 16 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 8)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 120 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14
        ∧ st0.data.regs.get64 Reg64.rax = s.regs.rax.toBitVec
        ∧ st0.data.regs.get64 Reg64.rbx = s.regs.rbx.toBitVec
        ∧ st0.data.regs.get64 Reg64.rcx = s.regs.rcx.toBitVec
        ∧ st0.data.regs.get64 Reg64.rdi = s.regs.rdi.toBitVec ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (t24.At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (t72.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (t56.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 35)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 120 }
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
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (t72.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (t56.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v0 v1 pre d0 d1 hast hv0 hv1 hd0 hd1 s ra guard hpre fp s2 t40 t24 t72 t56 hfp hs2 ht40 ht24 ht72 ht56 R hsp hcap hcap63
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
  have hcap' : rcx.toBitVec.toNat + 16 ≤ rdi.toBitVec.toNat := hcap
  apply kstep_lea Reg64.rdx Reg64.rcx 8 _ (k + 8) (k + 9) (win hk 8 1) (by rfl) (by rfl)
  kn
  apply kreg_eq Reg64.rdx (rcx.toBitVec + 8) _ _ _ (by show (rcx.toBitVec + 8 : BitVec 64) = (rcx.toBitVec + 8); bv_omega)
  kn
  apply kstep_ldb Reg64.r8 Reg64.rax 8 _ (k + 9) (k + 10) (win hk 9 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 8) (by eb) v0 hv0 _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_lea Reg64.r9 Reg64.rsp 80 _ (k + 10) (k + 14) (win hk 10 4) (by rfl) (by rfl)
  kn
  apply kreg_eq Reg64.r9 (rsp.toBitVec - 40) _ _ _ (by show ((rsp.toBitVec - 120) + 80 : BitVec 64) = (rsp.toBitVec - 40); bv_omega)
  kn
  apply kstep_movups15 Reg64.r9 0 _ (k + 14) (k + 15) (win hk 14 1) (by rfl) (by rfl)
    (rsp.toBitVec - 40) (rsp.toBitVec - 40) (by eb) t40 ht40 _ _ _ (by rfl) (by ecancel)
  intro m3 H3; kn; try dsimp only at H3
  apply kstep_movups15 Reg64.r9 16 _ (k + 15) (k + 16) (win hk 15 1) (by rfl) (by rfl)
    (rsp.toBitVec - 40) (rsp.toBitVec - 24) (by eb) t24 ht24 _ _ _ (by rfl) (by ecancel)
  intro m4 H4; kn; try dsimp only at H4
  rw [lr_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 40), show (rsp.toBitVec - 40) + 8 = (rsp.toBitVec - 32) by bv_omega] at H4
  apply kstep_st Reg64.r8 Reg64.rsp 80 _ (k + 16) (k + 17) (win hk 16 1) (by rfl) (by rfl)
    (rsp.toBitVec - 120) (rsp.toBitVec - 40) (by eb) ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).take 8) (by rw [List.length_take, Int.toBytes_length]; rfl) _ _ _ (by rfl) (by ecancel)
  intro m5 H5; kn; simp only [Reg64s.get64] at H5
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v0 hv0] at H5
  have hl32 := Fk.label_at' hk hf (j := 32)
    (by simp only [PcMarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [PcMarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply kstep_cmp_jae_t Reg64.rdi Reg64.rdx _ _ (k + 17) (k + 32) (win hk 17 2) (by rfl) hl32 _ _ (by show ((rcx.toBitVec + 8) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; kn
  apply kstep_label _ _ (k + 32) (k + 33) (win hk 32 1) (by rfl) (by rfl)
  apply kstep_ldb Reg64.r8 Reg64.rsp 80 _ (k + 33) (k + 34) (win hk 33 1) (by rfl) (by rfl)
    (rsp.toBitVec - 120) (rsp.toBitVec - 40) (by eb) v0 hv0 _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_st_idx Reg64.r8 Reg64.rbx Reg64.rcx 0 _ (k + 34) (k + 35) (win hk 34 1) (by rfl) (by rfl)
    rbx.toBitVec rcx.toBitVec (rbx.toBitVec + rcx.toBitVec) (by eb) d0 hd0 _ _ _ (by rfl) (by rfl) (by ecancel)
  intro m6 H6; kn; simp only [Reg64s.get64] at H6
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v0 hv0] at H6
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8), (Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt), (by rw [List.length_drop, Int.toBytes_length]), (Int.toBytes_length 16 _), ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem pc_g6e_f0_kind : ∀ (h : Host), type_of% (@pc_g6e_f0 h)
    = @E2eScal.encFieldKindN h PcMarshal E2eScal.Gen6Enc.pc_g6e_layout [.u64, .u64]
    ⟨8, 0, [(.rax, .rcv), (.rbx, .ptr), (.rcx, .len 0), (.rdi, .cap)],
      [.at (.dn 8) (.reg .rbp), .at (.up 16) (.reg .rbx), .at (.dn 40) (.orig 2), .at (.dn 24) (.orig 3), .at (.dn 72) (.orig 4), .at (.dn 56) (.orig 5)],
      []⟩
    ⟨35, 1, [(.rax, .rcv), (.rbx, .ptr), (.rdx, .len 8), (.rdi, .cap)],
      [.at (.dn 8) (.reg .rbp), .at (.up 16) (.reg .rbx), .at (.dn 40) (.fld 0), .at (.dn 32) (.ex 0), .at (.dn 24) (.ex 1), .at (.dn 72) (.orig 4), .at (.dn 56) (.orig 5)],
      [.n 8, .n 16]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 1 `TargetIndex` (uint64): directives 35–59; boundary state 1 → 2. -/
theorem pc_g6e_f1 : ∀ (k : Nat) (hk : PcMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PcMarshal k)
    (ast v0 v1 pre d0 d1 : List UInt8) (hast : ast.length = 8) (hv0 : v0.length = 8) (hv1 : v1.length = 8) (hd0 : d0.length = 8) (hd1 : d1.length = 8)
    (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s2 t40 t24 t72 t56 : List UInt8) (hfp : fp.length = 8) (hs2 : s2.length = 8) (ht40 : t40.length = 16) (ht24 : t24.length = 16) (ht72 : t72.length = 16) (ht56 : t56.length = 16)
    (R : DataMem → Prop)
    (hsp : 128 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 16 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 35)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 120 }
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
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (t72.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (t56.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 60)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 120 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.get64 Reg64.rbx = s.regs.rbx.toBitVec
        ∧ st.data.regs.get64 Reg64.rdi = s.regs.rdi.toBitVec
        ∧ st.data.regs.get64 Reg64.r8 = s.regs.rcx.toBitVec + 16 ∧
        ∃ (x0 x1 x2 x3 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧ x2.length = 8 ∧ x3.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (v1.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v0 v1 pre d0 d1 hast hv0 hv1 hd0 hd1 s ra guard hpre fp s2 t40 t24 t72 t56 hfp hs2 ht40 ht24 ht72 ht56 R hsp hcap hcap63
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
  have hcap' : rcx.toBitVec.toNat + 16 ≤ rdi.toBitVec.toNat := hcap
  apply kstep_lea Reg64.r8 Reg64.rdx 8 _ (k + 35) (k + 36) (win hk 35 1) (by rfl) (by rfl)
  kn
  apply kreg_eq Reg64.r8 (rcx.toBitVec + 16) _ _ _ (by show ((rcx.toBitVec + 8) + 8 : BitVec 64) = (rcx.toBitVec + 16); bv_omega)
  kn
  apply kstep_ldb Reg64.r9 Reg64.rax 16 _ (k + 36) (k + 37) (win hk 36 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 16) (by eb) v1 hv1 _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_lea Reg64.r10 Reg64.rsp 48 _ (k + 37) (k + 41) (win hk 37 4) (by rfl) (by rfl)
  kn
  apply kreg_eq Reg64.r10 (rsp.toBitVec - 72) _ _ _ (by show ((rsp.toBitVec - 120) + 48 : BitVec 64) = (rsp.toBitVec - 72); bv_omega)
  kn
  apply kstep_movups15 Reg64.r10 0 _ (k + 41) (k + 42) (win hk 41 1) (by rfl) (by rfl)
    (rsp.toBitVec - 72) (rsp.toBitVec - 72) (by eb) t72 ht72 _ _ _ (by rfl) (by ecancel)
  intro m7 H7; kn; try dsimp only at H7
  apply kstep_movups15 Reg64.r10 16 _ (k + 42) (k + 43) (win hk 42 1) (by rfl) (by rfl)
    (rsp.toBitVec - 72) (rsp.toBitVec - 56) (by eb) t56 ht56 _ _ _ (by rfl) (by ecancel)
  intro m8 H8; kn; try dsimp only at H8
  rw [lr_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 72), show (rsp.toBitVec - 72) + 8 = (rsp.toBitVec - 64) by bv_omega] at H8
  apply kstep_st Reg64.r9 Reg64.rsp 48 _ (k + 43) (k + 44) (win hk 43 1) (by rfl) (by rfl)
    (rsp.toBitVec - 120) (rsp.toBitVec - 72) (by eb) ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).take 8) (by rw [List.length_take, Int.toBytes_length]; rfl) _ _ _ (by rfl) (by ecancel)
  intro m9 H9; kn; simp only [Reg64s.get64] at H9
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v1 hv1] at H9
  have hl57 := Fk.label_at' hk hf (j := 57)
    (by simp only [PcMarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [PcMarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply kstep_cmp_jae_t Reg64.rdi Reg64.r8 _ _ (k + 44) (k + 57) (win hk 44 2) (by rfl) hl57 _ _ (by show ((rcx.toBitVec + 16) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; kn
  apply kstep_label _ _ (k + 57) (k + 58) (win hk 57 1) (by rfl) (by rfl)
  apply kstep_ldb Reg64.r9 Reg64.rsp 48 _ (k + 58) (k + 59) (win hk 58 1) (by rfl) (by rfl)
    (rsp.toBitVec - 120) (rsp.toBitVec - 72) (by eb) v1 hv1 _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_st_idx Reg64.r9 Reg64.rbx Reg64.rdx 0 _ (k + 59) (k + 60) (win hk 59 1) (by rfl) (by rfl)
    rbx.toBitVec (rcx.toBitVec + 8) (rbx.toBitVec + rcx.toBitVec + 8) (by eb) d1 hd1 _ _ _ (by rfl) (by rfl) (by ecancel)
  intro m10 H10; kn; simp only [Reg64s.get64] at H10
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v1 hv1] at H10
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, x0, x1, ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8), (Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt), hx0, hx1, (by rw [List.length_drop, Int.toBytes_length]), (Int.toBytes_length 16 _), ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem pc_g6e_f1_kind : ∀ (h : Host), type_of% (@pc_g6e_f1 h)
    = @E2eScal.encFieldKindN h PcMarshal E2eScal.Gen6Enc.pc_g6e_layout [.u64, .u64]
    ⟨35, 1, [(.rax, .rcv), (.rbx, .ptr), (.rdx, .len 8), (.rdi, .cap)],
      [.at (.dn 8) (.reg .rbp), .at (.up 16) (.reg .rbx), .at (.dn 40) (.fld 0), .at (.dn 32) (.ex 0), .at (.dn 24) (.ex 1), .at (.dn 72) (.orig 4), .at (.dn 56) (.orig 5)],
      [.n 8, .n 16]⟩
    ⟨60, 2, [(.rbx, .ptr), (.rdi, .cap), (.r8, .len 16)],
      [.at (.dn 8) (.reg .rbp), .at (.up 16) (.reg .rbx), .at (.dn 40) (.fld 0), .at (.dn 32) (.ex 0), .at (.dn 24) (.ex 1), .at (.dn 72) (.fld 1), .at (.dn 64) (.ex 2), .at (.dn 56) (.ex 3)],
      [.n 8, .n 16, .n 8, .n 16]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Epilogue: directives 60–return; boundary state 2 → the fast-path post-state. -/
theorem pc_g6e_epi : ∀ (k : Nat) (hk : PcMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PcMarshal k)
    (ast v0 v1 pre d0 d1 : List UInt8) (hast : ast.length = 8) (hv0 : v0.length = 8) (hv1 : v1.length = 8) (hd0 : d0.length = 8) (hd1 : d1.length = 8)
    (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s2 t40 t24 t72 t56 : List UInt8) (hfp : fp.length = 8) (hs2 : s2.length = 8) (ht40 : t40.length = 16) (ht24 : t24.length = 16) (ht72 : t72.length = 16) (ht56 : t56.length = 16)
    (R : DataMem → Prop)
    (hsp : 128 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 16 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 60)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 120 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14
        ∧ st0.data.regs.get64 Reg64.rbx = s.regs.rbx.toBitVec
        ∧ st0.data.regs.get64 Reg64.rdi = s.regs.rdi.toBitVec
        ∧ st0.data.regs.get64 Reg64.r8 = s.regs.rcx.toBitVec + 16 ∧
        ∃ (x0 x1 x2 x3 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧ x2.length = 8 ∧ x3.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (v1.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec
        ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 16
        ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0
        ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8
        ∧ st.data.regs.rbp = s.regs.rbp
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 x2 x3 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧ x2.length = 8 ∧ x3.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (v1.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v0 v1 pre d0 d1 hast hv0 hv1 hd0 hd1 s ra guard hpre fp s2 t40 t24 t72 t56 hfp hs2 ht40 ht24 ht72 ht56 R hsp hcap hcap63
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hsp hcap hcap63 hpre ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, hrrbx, hrrdi, hrr8, x0, x1, x2, x3, hx0, hx1, hx2, hx3, Hm⟩
  dsimp only at hpc hrsp hrbp hr14 hrrbx hrrdi hrr8 Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14 hrrbx hrrdi hrr8 Hm
  subst rsp1 rbp1 r141
  obtain rfl : rbx = rbx1 := (UInt64.toBitVec_inj.mp hrrbx).symm
  obtain rfl : rdi = rdi1 := (UInt64.toBitVec_inj.mp hrrdi).symm
  obtain rfl : r81 = { toBitVec := rcx.toBitVec + 16 } := UInt64.toBitVec_inj.mp hrr8
  have hcap' : rcx.toBitVec.toNat + 16 ≤ rdi.toBitVec.toNat := hcap
  apply kstep_mov_rr Reg64.rax Reg64.rbx _ (k + 60) (k + 61) (win hk 60 1) (by rfl) (by rfl)
  kn
  apply kstep_mov_rr Reg64.rbx Reg64.r8 _ (k + 61) (k + 62) (win hk 61 1) (by rfl) (by rfl)
  kn
  apply kstep_mov_rr Reg64.rcx Reg64.rdi _ (k + 62) (k + 63) (win hk 62 1) (by rfl) (by rfl)
  kn
  apply kstep_xor32 Reg64.rdi _ (k + 63) (k + 64) (win hk 63 1) (by rfl) (by rfl)
  intro fl; kn
  apply kstep_xor32 Reg64.rsi _ (k + 64) (k + 65) (win hk 64 1) (by rfl) (by rfl)
  intro fl; kn
  apply kstep_add Reg64.rsp 112 _ (k + 65) (k + 66) (win hk 65 1) (by rfl) (by rfl)
  intro fl; kn
  apply kreg_eq Reg64.rsp (rsp.toBitVec - 8) _ _ _ (by show ((rsp.toBitVec - 120) + 112 : BitVec 64) = (rsp.toBitVec - 8); bv_omega)
  kn
  refine eventually_trans _ _ _ _ (decret_seg _ (k + 66) (win hk 66 2) (by rfl) (rsp.toBitVec - 8) rsp.toBitVec (by bv_omega) rbp ra _ _ (by rfl) (by ecancel)) ?_
  rintro ⟨d', pc'⟩ ⟨hpc', hrsp', hrbp', hreg', hmem'⟩
  dsimp only at hpc' hrsp' hrbp' hreg' hmem'
  apply Eventually.done
  refine ⟨hpc', ?_, ?_, ?_, ?_, ?_, ?_, hrbp', ?_, x0, x1, x2, x3, hx0, hx1, hx2, hx3, ?_⟩
  · exact UInt64.toBitVec_inj.mp (hreg' Reg64.rax (by decide) (by decide))
  · show d'.regs.rbx.toBitVec.toNat = rcx.toBitVec.toNat + 16
    rw [show d'.regs.rbx.toBitVec = rcx.toBitVec + 16 from hreg' Reg64.rbx (by decide) (by decide)]
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
theorem pc_g6e_epi_kind : ∀ (h : Host), type_of% (@pc_g6e_epi h)
    = @E2eScal.encEpiKindN h PcMarshal E2eScal.Gen6Enc.pc_g6e_layout [.u64, .u64]
    ⟨60, 2, [(.rbx, .ptr), (.rdi, .cap), (.r8, .len 16)],
      [.at (.dn 8) (.reg .rbp), .at (.up 16) (.reg .rbx), .at (.dn 40) (.fld 0), .at (.dn 32) (.ex 0), .at (.dn 24) (.ex 1), .at (.dn 72) (.fld 1), .at (.dn 64) (.ex 2), .at (.dn 56) (.ex 3)],
      [.n 8, .n 16, .n 8, .n 16]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Encoder fast path of `(*v1alpha1.PendingConsolidation).MarshalSSZTo` (Go 1.26.10), generated** (`p2enc --gen6`):
head, one theorem per field, epilogue, chained by `eventually_trans`. Premises: `len + 16 ≤ cap`,
every byte-vector field of its exact length. Statement = the kind instance (`_kind`). Fast path only. -/
theorem pc_g6e_fast : ∀ (k : Nat) (hk : PcMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PcMarshal k)
    (ast v0 v1 pre d0 d1 : List UInt8) (hast : ast.length = 8) (hv0 : v0.length = 8) (hv1 : v1.length = 8) (hd0 : d0.length = 8) (hd1 : d1.length = 8)
    (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s2 t40 t24 t72 t56 : List UInt8) (hfp : fp.length = 8) (hs2 : s2.length = 8) (ht40 : t40.length = 16) (ht24 : t24.length = 16) (ht72 : t72.length = 16) (ht56 : t56.length = 16)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (t24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (t72.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (t56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
      ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 128 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 16 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec
        ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 16
        ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0
        ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8
        ∧ st.data.regs.rbp = s.regs.rbp
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 x2 x3 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧ x2.length = 8 ∧ x3.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (v1.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (x2.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (x3.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (v1.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (v1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf ast v0 v1 pre d0 d1 hast hv0 hv1 hd0 hd1 s ra guard hpre fp s2 t40 t24 t72 t56 hfp hs2 ht40 ht24 ht72 ht56 R h_mem hguard hsp hcap hcap63
  refine eventually_trans _ _ _ _ (pc_g6e_head k hk hf ast v0 v1 pre d0 d1 hast hv0 hv1 hd0 hd1 s ra guard hpre fp s2 t40 t24 t72 t56 hfp hs2 ht40 ht24 ht72 ht56 R h_mem hguard hsp hcap hcap63) ?_
  intro st0 h0
  refine eventually_trans _ _ _ _ (pc_g6e_f0 k hk hf ast v0 v1 pre d0 d1 hast hv0 hv1 hd0 hd1 s ra guard hpre fp s2 t40 t24 t72 t56 hfp hs2 ht40 ht24 ht72 ht56 R hsp hcap hcap63 st0 h0) ?_
  intro st1 h1
  refine eventually_trans _ _ _ _ (pc_g6e_f1 k hk hf ast v0 v1 pre d0 d1 hast hv0 hv1 hd0 hd1 s ra guard hpre fp s2 t40 t24 t72 t56 hfp hs2 ht40 ht24 ht72 ht56 R hsp hcap hcap63 st1 h1) ?_
  intro st2 h2
  exact pc_g6e_epi k hk hf ast v0 v1 pre d0 d1 hast hv0 hv1 hd0 hd1 s ra guard hpre fp s2 t40 t24 t72 t56 hfp hs2 ht40 ht24 ht72 ht56 R hsp hcap hcap63 st2 h2
theorem pc_g6e_fast_kind : ∀ (h : Host), type_of% (@pc_g6e_fast h)
    = @E2eScal.encFastKindN h PcMarshal E2eScal.Gen6Enc.pc_g6e_layout [.u64, .u64] := by
  intro h; rfl

end E2eScal.Gen6Enc
