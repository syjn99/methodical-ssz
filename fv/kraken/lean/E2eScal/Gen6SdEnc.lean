import E2eScal.EncTies
import Codec.EncodeFrameTest
import E2eScal.Enc2Code

/-!
# GEN6 (`p2enc --gen6`, unit E2-G): encoder fast path of `(*v1alpha1.SigningData).MarshalSSZTo`

Generated from the `.S` file and the IR: a symbolic dataflow walk of the fast path, one application of a
step lemma per directive (windows with the nops erased), boundary states between the fields. Every theorem
has a `_kind` line (`encHeadKindN`, `encFieldKindN`, `encEpiKindN`, `encFastKindN`).
**Fast path only**: `len(dst) + 64 ≤ cap(dst)` and every byte-vector field of its exact length. No
`runtime.growslice` directive is stepped: each capacity test is decided from the premise. Not covered: the
growslice branches, the length rejects, the morestack path. Not a complete encoder result.
GEN6-JSON: {"type": "SigningData", "const": "SdMarshal", "prefix": "sd_g6e", "size": 64, "frame": 80, "gd": 0, "rt": true, "fields": [["ObjectRoot", "b", 32], ["Domain", "b", 32]], "boundaries": [8, 37, 66], "layout": "E2eScal.Gen6Enc.sd_g6e_layout", "S_sha256": "65be2f0e02190d370e5762b30610233d9412a259bbd0b6770a6219192955955a", "ir_sha256": "c1586d32018abd182c16d50f6a7a76e38814cab08cf4a7a42105fe30342a5d2a", "statement_check": "kind instance only", "S": "prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.MarshalSSZTo.S", "ir": "prysm/ir/ir-mainnet.json", "ir_type": "v1alpha1.SigningData", "kinds": [{"theorem": "sd_g6e_head", "kind": "encHeadKindN"}, {"theorem": "sd_g6e_f0", "kind": "encFieldKindN"}, {"theorem": "sd_g6e_f1", "kind": "encFieldKindN"}, {"theorem": "sd_g6e_epi", "kind": "encEpiKindN"}, {"theorem": "sd_g6e_fast", "kind": "encFastKindN"}]}
-/

open Machine Runtime TestTarget E2eScal Codec E2eScal.Enc2Code
variable [Host]

namespace E2eScal.Gen6Enc

/-- The frame facts of `SdMarshal` (read from the `.S` file by the walk): frame `0x50`, stack chunks
`fp s1 s2 l32 l40 l16 rslot`. -/
def sd_g6e_layout : EncLayout where
  st := false
  frame := 80
  gd := 0
  rt := true
  nstk := 7
  lens := [(0, 8), (1, 8), (2, 8), (3, 8), (4, 8), (5, 8), (6, 8)]
  pre := [.at (.dn 8) (.orig 0), .at (.up 8) (.orig 1), .at (.up 16) (.orig 2), .at (.dn 32) (.orig 3), .at (.dn 40) (.orig 4), .at (.dn 16) (.orig 5), .at (.dn 96) (.orig 6), .lo .scr]
  exs := [.lo]
  post := [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 32) (.reg .rdi), .at (.dn 40) (.len 64), .at (.dn 16) (.reg .rbx), .at (.dn 96) (.ret 66), .lo (.ex 0)]


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Head: directives 0–7 (stack guard, frame, spills); entry → boundary state 0. -/
theorem sd_g6e_head : ∀ (k : Nat) (hk : SdMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh SdMarshal k)
    (c0 c1 b0 b1 pre d0 d1 : List UInt8) (hc0 : c0.length = 8) (hc1 : c1.length = 8) (hb0 : b0.length = 32) (hb1 : b1.length = 32) (hd0 : d0.length = 32) (hd1 : d1.length = 32)
    (p0 p1 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l32 l40 l16 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl32 : l32.length = 8) (hl40 : l40.length = 8) (hl16 : l16.length = 8) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 96 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 p0.toInt).At s.regs.rax.toBitVec)
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (c0.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (c1.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (b0.At p0)
      ⋆ Eq (b1.At p1)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 32))
      ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 96 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 64 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveC S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 8)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 88 }
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
          ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 96 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 32))
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf c0 c1 b0 b1 pre d0 d1 hc0 hc1 hb0 hb1 hd0 hd1 p0 p1 s ra guard hpre fp s1 s2 l32 l40 l16 rslot hfp hs1 hs2 hl32 hl40 hl16 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hcap hcap63 hpre ⊢
  have hcap' : rcx.toBitVec.toNat + 64 ≤ rdi.toBitVec.toNat := hcap
  apply encpro_s _ _ _ _ k (k + 6) (win hk 0 6) (by rfl) (by rfl) guard fp hfp _ _ _ (by dsimp only; ecancel) hguard
  intro m1 H1 fl1; kn; dsimp only at H1
  apply kstep_sub_i Reg64.rsp 80 _ (k + 6) (k + 7) (win hk 6 1) (by rfl) (by rfl)
  intro fl; kn
  apply kreg_eq Reg64.rsp (rsp.toBitVec - 88) _ _ _ (by show ((rsp.toBitVec - 8) - 80 : BitVec 64) = (rsp.toBitVec - 88); bv_omega)
  kn
  apply kstep_st Reg64.rbx Reg64.rsp 104 _ (k + 7) (k + 8) (win hk 7 1) (by rfl) (by rfl)
    (rsp.toBitVec - 88) (rsp.toBitVec + 16) (by eb) s2 hs2 _ _ _ (by rfl) (by ecancel)
  intro m2 H2; kn; simp only [Reg64s.get64] at H2
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem sd_g6e_head_kind : ∀ (h : Host), type_of% (@sd_g6e_head h)
    = @E2eScal.encHeadKindN h SdMarshal E2eScal.Gen6Enc.sd_g6e_layout [.bytes 32, .bytes 32]
    ⟨8, 0, [(.rax, .rcv), (.rbx, .ptr), (.rcx, .len 0), (.rdi, .cap)],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.orig 1), .at (.up 16) (.reg .rbx), .at (.dn 32) (.orig 3), .at (.dn 40) (.orig 4), .at (.dn 16) (.orig 5), .at (.dn 96) (.orig 6), .lo .scr],
      []⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 0 `ObjectRoot` (32 bytes): directives 8–36; boundary state 0 → 1. -/
theorem sd_g6e_f0 : ∀ (k : Nat) (hk : SdMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh SdMarshal k)
    (c0 c1 b0 b1 pre d0 d1 : List UInt8) (hc0 : c0.length = 8) (hc1 : c1.length = 8) (hb0 : b0.length = 32) (hb1 : b1.length = 32) (hd0 : d0.length = 32) (hd1 : d1.length = 32)
    (p0 p1 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l32 l40 l16 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl32 : l32.length = 8) (hl40 : l40.length = 8) (hl16 : l16.length = 8) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 96 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 64 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveC S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 8)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 88 }
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
          ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 96 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 32))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 37)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 88 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 : List UInt8), x0.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 32).toInt).At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 37)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 96 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 32))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf c0 c1 b0 b1 pre d0 d1 hc0 hc1 hb0 hb1 hd0 hd1 p0 p1 s ra guard hpre fp s1 s2 l32 l40 l16 rslot hfp hs1 hs2 hl32 hl40 hl16 hrslot R S scratch hsc hsp hcap hcap63 hmm
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
  apply kstep_ldv Reg64.rdx Reg64.rax 0 _ (k + 8) (k + 9) (win hk 8 1) (by rfl) (by rfl)
    rax.toBitVec rax.toBitVec p0 (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_lenchk Reg64.rax 8 32 _ _ (k + 9) (k + 12) (win hk 9 3) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 8) (by eb) (Int.toBytes 8 32) (by rfl) (by decide) _ _ _ (by rfl) (by ecancel)
  intro fl; kn
  apply kstep_st Reg64.rax Reg64.rsp 96 _ (k + 12) (k + 13) (win hk 12 1) (by rfl) (by rfl)
    (rsp.toBitVec - 88) (rsp.toBitVec + 8) (by eb) s1 hs1 _ _ _ (by rfl) (by ecancel)
  intro m3 H3; kn; simp only [Reg64s.get64] at H3
  apply kstep_lea Reg64.r8 Reg64.rcx 32 _ (k + 13) (k + 14) (win hk 13 1) (by rfl) (by rfl)
  kn
  apply kreg_eq Reg64.r8 (rcx.toBitVec + 32) _ _ _ (by show (rcx.toBitVec + 32 : BitVec 64) = (rcx.toBitVec + 32); bv_omega)
  kn
  have hl29 := Machine.label_at' hk hf (j := 29)
    (by simp only [SdMarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [SdMarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply kstep_cmp_jae_t Reg64.rdi Reg64.r8 _ _ (k + 14) (k + 29) (win hk 14 2) (by rfl) hl29 _ _ (by show ((rcx.toBitVec + 32) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; kn
  apply kstep_label _ _ (k + 29) (k + 30) (win hk 29 1) (by rfl) (by rfl)
  apply kstep_st Reg64.rdi Reg64.rsp 56 _ (k + 30) (k + 31) (win hk 30 1) (by rfl) (by rfl)
    (rsp.toBitVec - 88) (rsp.toBitVec - 32) (by eb) l32 hl32 _ _ _ (by rfl) (by ecancel)
  intro m4 H4; kn; simp only [Reg64s.get64] at H4
  apply kstep_st Reg64.r8 Reg64.rsp 48 _ (k + 31) (k + 32) (win hk 31 1) (by rfl) (by rfl)
    (rsp.toBitVec - 88) (rsp.toBitVec - 40) (by eb) l40 hl40 _ _ _ (by rfl) (by ecancel)
  intro m5 H5; kn; simp only [Reg64s.get64] at H5
  apply kstep_st Reg64.rbx Reg64.rsp 72 _ (k + 32) (k + 33) (win hk 32 1) (by rfl) (by rfl)
    (rsp.toBitVec - 88) (rsp.toBitVec - 16) (by eb) l16 hl16 _ _ _ (by rfl) (by ecancel)
  intro m6 H6; kn; simp only [Reg64s.get64] at H6
  apply kstep_lea_idx Reg64.rax Reg64.rbx Reg64.rcx _ (k + 33) (k + 34) (win hk 33 1) (by rfl) (by rfl)
  kn
  apply kreg_eq Reg64.rax (rbx.toBitVec + rcx.toBitVec) _ _ _ (by show (rbx.toBitVec + rcx.toBitVec : BitVec 64) = (rbx.toBitVec + rcx.toBitVec); bv_omega)
  kn
  apply kstep_mov_rr Reg64.rbx Reg64.rdx _ (k + 34) (k + 35) (win hk 34 1) (by rfl) (by rfl)
  kn
  apply kstep_movi Reg64.rcx 32 _ (k + 35) (k + 36) (win hk 35 1) (by rfl) (by rfl)
  kn
  apply kreg_eq Reg64.rcx 32 _ _ _ (by show (BitVec.zeroExtend 64 (BitVec.truncate 32 (32 : BitVec 64)) : BitVec 64) = 32; decide)
  kn
  refine eventually_trans _ _ _ _ (encn_call (k + 36) (win hk 36 1) (rsp.toBitVec - 88) (rbx.toBitVec + rcx.toBitVec) p0
    (rsp.toBitVec - 96) (rsp.toBitVec - 96 - BitVec.ofNat 64 S) S (by bv_omega) (Codec.frame_lo0 rsp.toBitVec 88 96 S (by decide))
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
theorem sd_g6e_f0_kind : ∀ (h : Host), type_of% (@sd_g6e_f0 h)
    = @E2eScal.encFieldKindN h SdMarshal E2eScal.Gen6Enc.sd_g6e_layout [.bytes 32, .bytes 32]
    ⟨8, 0, [(.rax, .rcv), (.rbx, .ptr), (.rcx, .len 0), (.rdi, .cap)],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.orig 1), .at (.up 16) (.reg .rbx), .at (.dn 32) (.orig 3), .at (.dn 40) (.orig 4), .at (.dn 16) (.orig 5), .at (.dn 96) (.orig 6), .lo .scr],
      []⟩
    ⟨37, 1, [],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 32) (.reg .rdi), .at (.dn 40) (.len 32), .at (.dn 16) (.reg .rbx), .at (.dn 96) (.ret 37), .lo (.ex 0)],
      [.lo]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 1 `Domain` (32 bytes): directives 37–65; boundary state 1 → 2. -/
theorem sd_g6e_f1 : ∀ (k : Nat) (hk : SdMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh SdMarshal k)
    (c0 c1 b0 b1 pre d0 d1 : List UInt8) (hc0 : c0.length = 8) (hc1 : c1.length = 8) (hb0 : b0.length = 32) (hb1 : b1.length = 32) (hd0 : d0.length = 32) (hd1 : d1.length = 32)
    (p0 p1 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l32 l40 l16 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl32 : l32.length = 8) (hl40 : l40.length = 8) (hl16 : l16.length = 8) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 96 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 64 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveC S) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 37)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 88 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 : List UInt8), x0.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 32).toInt).At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 37)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 96 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 32))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 66)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 88 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 : List UInt8), x0.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 64).toInt).At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 66)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 96 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 32))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf c0 c1 b0 b1 pre d0 d1 hc0 hc1 hb0 hb1 hd0 hd1 p0 p1 s ra guard hpre fp s1 s2 l32 l40 l16 rslot hfp hs1 hs2 hl32 hl40 hl16 hrslot R S scratch hsc hsp hcap hcap63 hmm
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hsp hcap hcap63 hpre ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, x0, hx0, Hm⟩
  dsimp only at hpc hrsp hrbp hr14  Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14  Hm
  subst rsp1 rbp1 r141
  have hcap' : rcx.toBitVec.toNat + 64 ≤ rdi.toBitVec.toNat := hcap
  apply kstep_ldv Reg64.rdx Reg64.rsp 96 _ (k + 37) (k + 38) (win hk 37 1) (by rfl) (by rfl)
    (rsp.toBitVec - 88) (rsp.toBitVec + 8) rax.toBitVec (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_ldv Reg64.rbx Reg64.rdx 24 _ (k + 38) (k + 39) (win hk 38 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 24) p1 (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_lenchk Reg64.rdx 32 32 _ _ (k + 39) (k + 41) (win hk 39 2) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 32) (by eb) (Int.toBytes 8 32) (by rfl) (by decide) _ _ _ (by rfl) (by ecancel)
  intro fl; kn
  apply kstep_ldv Reg64.rdx Reg64.rsp 48 _ (k + 41) (k + 42) (win hk 41 1) (by rfl) (by rfl)
    (rsp.toBitVec - 88) (rsp.toBitVec - 40) (rcx.toBitVec + 32) (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_lea Reg64.r8 Reg64.rdx 32 _ (k + 42) (k + 43) (win hk 42 1) (by rfl) (by rfl)
  kn
  apply kreg_eq Reg64.r8 (rcx.toBitVec + 64) _ _ _ (by show ((rcx.toBitVec + 32) + 32 : BitVec 64) = (rcx.toBitVec + 64); bv_omega)
  kn
  apply kstep_ldv Reg64.rcx Reg64.rsp 56 _ (k + 43) (k + 44) (win hk 43 1) (by rfl) (by rfl)
    (rsp.toBitVec - 88) (rsp.toBitVec - 32) rdi.toBitVec (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_cmp_jb_f Reg64.rcx Reg64.r8 _ _ (k + 44) (k + 46) (win hk 44 2) (by rfl) (by rfl) _ _ (by show ((rcx.toBitVec + 64) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; kn
  apply kstep_ldv Reg64.rax Reg64.rsp 72 _ (k + 46) (k + 47) (win hk 46 1) (by rfl) (by rfl)
    (rsp.toBitVec - 88) (rsp.toBitVec - 16) rbx.toBitVec (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  have hl58 := Machine.label_at' hk hf (j := 58)
    (by simp only [SdMarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [SdMarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply kstep_jmp _ _ (k + 47) (k + 58) (win hk 47 1) (by rfl) hl58
  apply kstep_label _ _ (k + 58) (k + 59) (win hk 58 1) (by rfl) (by rfl)
  apply kstep_st Reg64.rax Reg64.rsp 72 _ (k + 59) (k + 60) (win hk 59 1) (by rfl) (by rfl)
    (rsp.toBitVec - 88) (rsp.toBitVec - 16) (by eb) (Int.toBytes 8 rbx.toBitVec.toInt) (Int.toBytes_length 8 _) _ _ _ (by rfl) (by ecancel)
  intro m7 H7; kn; simp only [Reg64s.get64] at H7
  apply kstep_st Reg64.rcx Reg64.rsp 56 _ (k + 60) (k + 61) (win hk 60 1) (by rfl) (by rfl)
    (rsp.toBitVec - 88) (rsp.toBitVec - 32) (by eb) (Int.toBytes 8 rdi.toBitVec.toInt) (Int.toBytes_length 8 _) _ _ _ (by rfl) (by ecancel)
  intro m8 H8; kn; simp only [Reg64s.get64] at H8
  apply kstep_st Reg64.r8 Reg64.rsp 48 _ (k + 61) (k + 62) (win hk 61 1) (by rfl) (by rfl)
    (rsp.toBitVec - 88) (rsp.toBitVec - 40) (by eb) (Int.toBytes 8 (rcx.toBitVec + 32).toInt) (Int.toBytes_length 8 _) _ _ _ (by rfl) (by ecancel)
  intro m9 H9; kn; simp only [Reg64s.get64] at H9
  apply kstep_add_rr Reg64.rax Reg64.rdx _ (k + 62) (k + 63) (win hk 62 1) (by rfl) (by rfl)
  intro fl; kn
  apply kreg_eq Reg64.rax (rbx.toBitVec + rcx.toBitVec + 32) _ _ _ (by show (rbx.toBitVec + (rcx.toBitVec + 32) : BitVec 64) = (rbx.toBitVec + rcx.toBitVec + 32); bv_omega)
  kn
  apply kstep_movi Reg64.rcx 32 _ (k + 63) (k + 64) (win hk 63 1) (by rfl) (by rfl)
  kn
  apply kreg_eq Reg64.rcx 32 _ _ _ (by show (BitVec.zeroExtend 64 (BitVec.truncate 32 (32 : BitVec 64)) : BitVec 64) = 32; decide)
  kn
  apply kstep_nops _ (k + 64) (k + 65) (win hk 64 1) (by rfl) (by rfl)
  refine eventually_trans _ _ _ _ (encn_call (k + 65) (win hk 65 1) (rsp.toBitVec - 88) (rbx.toBitVec + rcx.toBitVec + 32) p1
    (rsp.toBitVec - 96) (rsp.toBitVec - 96 - BitVec.ofNat 64 S) S (by bv_omega) (Codec.frame_lo0 rsp.toBitVec 88 96 S (by decide))
    b1 d1 (Int.toBytes 8 (Host.addrOf (k + 37)).toBitVec.toInt) x0 (by rw [hd1, hb1]) (Int.toBytes_length 8 _) hx0
    _ _ (by rfl) (by rfl) (by rfl) (by rw [hb1]; rfl) (by first | ecancel | (dsimp only; ecancel)) hmm) ?_
  rintro ⟨e2, pc2⟩ ⟨hpc2, hrsp2, hrbp2, hr142, scr2, hscr2, Hc2⟩
  dsimp only at hpc2 hrsp2 hrbp2 hr142 Hc2
  subst hpc2
  obtain ⟨⟨raxc2, rbxc2, rcxc2, rdxc2, rsic2, rdic2, rspc2, rbpc2, r8c2, r9c2, r10c2, r11c2, r12c2, r13c2, r14c2, r15c2⟩, zmmsc2, flagsc2, memc2⟩ := e2
  simp only at hrsp2 hrbp2 hr142 Hc2
  subst rspc2 rbpc2 r14c2
  rw [show k + 65 + 1 = k + 66 from rfl] at Hc2
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, scr2, hscr2, ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem sd_g6e_f1_kind : ∀ (h : Host), type_of% (@sd_g6e_f1 h)
    = @E2eScal.encFieldKindN h SdMarshal E2eScal.Gen6Enc.sd_g6e_layout [.bytes 32, .bytes 32]
    ⟨37, 1, [],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 32) (.reg .rdi), .at (.dn 40) (.len 32), .at (.dn 16) (.reg .rbx), .at (.dn 96) (.ret 37), .lo (.ex 0)],
      [.lo]⟩
    ⟨66, 2, [],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 32) (.reg .rdi), .at (.dn 40) (.len 64), .at (.dn 16) (.reg .rbx), .at (.dn 96) (.ret 66), .lo (.ex 0)],
      [.lo]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Epilogue: directives 66–return; boundary state 2 → the fast-path post-state. -/
theorem sd_g6e_epi : ∀ (k : Nat) (hk : SdMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh SdMarshal k)
    (c0 c1 b0 b1 pre d0 d1 : List UInt8) (hc0 : c0.length = 8) (hc1 : c1.length = 8) (hb0 : b0.length = 32) (hb1 : b1.length = 32) (hd0 : d0.length = 32) (hd1 : d1.length = 32)
    (p0 p1 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l32 l40 l16 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl32 : l32.length = 8) (hl40 : l40.length = 8) (hl16 : l16.length = 8) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (hsp : 96 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 64 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 66)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 88 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 : List UInt8), x0.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 64).toInt).At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 66)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 96 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 32))
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
        ∃ (x0 : List UInt8), x0.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 64).toInt).At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 66)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 96 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 32))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf c0 c1 b0 b1 pre d0 d1 hc0 hc1 hb0 hb1 hd0 hd1 p0 p1 s ra guard hpre fp s1 s2 l32 l40 l16 rslot hfp hs1 hs2 hl32 hl40 hl16 hrslot R S scratch hsc hsp hcap hcap63
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hsp hcap hcap63 hpre ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, x0, hx0, Hm⟩
  dsimp only at hpc hrsp hrbp hr14  Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14  Hm
  subst rsp1 rbp1 r141
  have hcap' : rcx.toBitVec.toNat + 64 ≤ rdi.toBitVec.toNat := hcap
  apply kstep_ldv Reg64.rbx Reg64.rsp 72 _ (k + 66) (k + 67) (win hk 66 1) (by rfl) (by rfl)
    (rsp.toBitVec - 88) (rsp.toBitVec - 16) rbx.toBitVec (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_mov_rr Reg64.rdx Reg64.rbx _ (k + 67) (k + 68) (win hk 67 1) (by rfl) (by rfl)
  kn
  apply kstep_sub_rr Reg64.rdx Reg64.rsp _ (k + 68) (k + 69) (win hk 68 1) (by rfl) (by rfl)
  intro fl; kn
  apply kreg_eq Reg64.rdx (rbx.toBitVec - (rsp.toBitVec - 88)) _ _ _ (by show (rbx.toBitVec - (rsp.toBitVec - 88) : BitVec 64) = (rbx.toBitVec - (rsp.toBitVec - 88)); bv_omega)
  kn
  apply kstep_lea Reg64.rsi Reg64.rsp 96 _ (k + 69) (k + 70) (win hk 69 1) (by rfl) (by rfl)
  kn
  apply kreg_eq Reg64.rsi (rsp.toBitVec + 8) _ _ _ (by show ((rsp.toBitVec - 88) + 96 : BitVec 64) = (rsp.toBitVec + 8); bv_omega)
  kn
  apply kstep_sub_rr Reg64.rsi Reg64.rsp _ (k + 70) (k + 71) (win hk 70 1) (by rfl) (by rfl)
  intro fl; kn
  apply kreg_eq Reg64.rsi 96 _ _ _ (by show ((rsp.toBitVec + 8) - (rsp.toBitVec - 88) : BitVec 64) = 96; bv_omega)
  kn
  have hrdi := rdi.toBitVec.isLt
  have hcapn : pre.length + 64 ≤ rdi.toBitVec.toNat := by rw [hpre]; exact hcap
  have hO : Eq ((pre ++ (b0 ++ b1)).At rbx.toBitVec) = Eq (pre.At rbx.toBitVec) ⋆ (Eq (b0.At (rbx.toBitVec + rcx.toBitVec)) ⋆ Eq (b1.At (rbx.toBitVec + rcx.toBitVec + 32))) := by
    rw [at_app pre (b0 ++ (b1)) (b := rbx.toBitVec + rcx.toBitVec)
      (by rw [hpre]; show _ = _ + BitVec.ofNat 64 rcx.toBitVec.toNat; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
      (by simp only [List.length_append, hb0, hb1]; omega),
    at_app b0 b1 (b := rbx.toBitVec + rcx.toBitVec + 32)
      (by rw [hb0] <;> bv_omega) (by simp only [List.length_append, hb0, hb1]; omega)]
  have hfar : 96 ≤ (rbx.toBitVec - (rsp.toBitVec - 88)).toNat :=
    frame50_ptr_far (pre ++ (b0 ++ b1)) (Int.toBytes 8 (rcx.toBitVec + 64).toInt) (Int.toBytes 8 rdi.toBitVec.toInt) (Int.toBytes 8 rbx.toBitVec.toInt) (Int.toBytes 8 rbp.toBitVec.toInt) (Int.toBytes 8 ra.toBitVec.toInt) rbx.toBitVec rsp.toBitVec _ mem1
      (by rw [hO]; ecancel) (by simp only [List.length_append, hb0, hb1]; omega) (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) (Int.toBytes_length 8 _)
  apply kstep_cmp_jb_f Reg64.rdx Reg64.rsi _ _ (k + 71) (k + 73) (win hk 71 2) (by rfl) (by rfl) _ _ (by show (96 : BitVec 64).toNat ≤ (rbx.toBitVec - (rsp.toBitVec - 88)).toNat; exact hfar)
  intro fl; kn
  apply kstep_ldv Reg64.rbx Reg64.rsp 48 _ (k + 73) (k + 74) (win hk 73 1) (by rfl) (by rfl)
    (rsp.toBitVec - 88) (rsp.toBitVec - 40) (rcx.toBitVec + 64) (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_ldv Reg64.rcx Reg64.rsp 56 _ (k + 74) (k + 75) (win hk 74 1) (by rfl) (by rfl)
    (rsp.toBitVec - 88) (rsp.toBitVec - 32) rdi.toBitVec (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  apply kstep_ldv Reg64.rax Reg64.rsp 72 _ (k + 75) (k + 76) (win hk 75 1) (by rfl) (by rfl)
    (rsp.toBitVec - 88) (rsp.toBitVec - 16) rbx.toBitVec (by eb) _ _ _ (by rfl) (by ecancel)
  kn
  have hl81 := Machine.label_at' hk hf (j := 81)
    (by simp only [SdMarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [SdMarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply kstep_jmp _ _ (k + 76) (k + 81) (win hk 76 1) (by rfl) hl81
  apply kstep_label _ _ (k + 81) (k + 82) (win hk 81 1) (by rfl) (by rfl)
  apply kstep_xor32 Reg64.rdi _ (k + 82) (k + 83) (win hk 82 1) (by rfl) (by rfl)
  intro fl; kn
  apply kstep_xor32 Reg64.rsi _ (k + 83) (k + 84) (win hk 83 1) (by rfl) (by rfl)
  intro fl; kn
  apply kstep_add Reg64.rsp 80 _ (k + 84) (k + 85) (win hk 84 1) (by rfl) (by rfl)
  intro fl; kn
  apply kreg_eq Reg64.rsp (rsp.toBitVec - 8) _ _ _ (by show ((rsp.toBitVec - 88) + 80 : BitVec 64) = (rsp.toBitVec - 8); bv_omega)
  kn
  refine eventually_trans _ _ _ _ (decret_seg _ (k + 85) (win hk 85 2) (by rfl) (rsp.toBitVec - 8) rsp.toBitVec (by bv_omega) rbp ra _ _ (by rfl) (by ecancel)) ?_
  rintro ⟨d', pc'⟩ ⟨hpc', hrsp', hrbp', hreg', hmem'⟩
  dsimp only at hpc' hrsp' hrbp' hreg' hmem'
  apply Eventually.done
  refine ⟨hpc', ?_, ?_, ?_, ?_, ?_, ?_, hrbp', ?_, x0, hx0, ?_⟩
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
theorem sd_g6e_epi_kind : ∀ (h : Host), type_of% (@sd_g6e_epi h)
    = @E2eScal.encEpiKindN h SdMarshal E2eScal.Gen6Enc.sd_g6e_layout [.bytes 32, .bytes 32]
    ⟨66, 2, [],
      [.at (.dn 8) (.reg .rbp), .at (.up 8) (.reg .rax), .at (.up 16) (.reg .rbx), .at (.dn 32) (.reg .rdi), .at (.dn 40) (.len 64), .at (.dn 16) (.reg .rbx), .at (.dn 96) (.ret 66), .lo (.ex 0)],
      [.lo]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Encoder fast path of `(*v1alpha1.SigningData).MarshalSSZTo` (Go 1.26.10), generated** (`p2enc --gen6`):
head, one theorem per field, epilogue, chained by `eventually_trans`. Premises: `len + 64 ≤ cap`,
every byte-vector field of its exact length. Statement = the kind instance (`_kind`). Fast path only. -/
theorem sd_g6e_fast : ∀ (k : Nat) (hk : SdMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh SdMarshal k)
    (c0 c1 b0 b1 pre d0 d1 : List UInt8) (hc0 : c0.length = 8) (hc1 : c1.length = 8) (hb0 : b0.length = 32) (hb1 : b1.length = 32) (hd0 : d0.length = 32) (hd1 : d1.length = 32)
    (p0 p1 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l32 l40 l16 rslot : List UInt8) (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hl32 : l32.length = 8) (hl40 : l40.length = 8) (hl16 : l16.length = 8) (hrslot : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 96 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 p0.toInt).At s.regs.rax.toBitVec)
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (c0.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (c1.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (b0.At p0)
      ⋆ Eq (b1.At p1)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 32))
      ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 96 ≤ s.regs.rsp.toNat)
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
        ∃ (x0 : List UInt8), x0.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 64).toInt).At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 66)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 96 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p0.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (c0.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (c1.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (b0.At p0)
          ⋆ Eq (b1.At p1)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (b0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (b1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 32))
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf c0 c1 b0 b1 pre d0 d1 hc0 hc1 hb0 hb1 hd0 hd1 p0 p1 s ra guard hpre fp s1 s2 l32 l40 l16 rslot hfp hs1 hs2 hl32 hl40 hl16 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm
  refine eventually_trans _ _ _ _ (sd_g6e_head k hk hf c0 c1 b0 b1 pre d0 d1 hc0 hc1 hb0 hb1 hd0 hd1 p0 p1 s ra guard hpre fp s1 s2 l32 l40 l16 rslot hfp hs1 hs2 hl32 hl40 hl16 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm) ?_
  intro st0 h0
  refine eventually_trans _ _ _ _ (sd_g6e_f0 k hk hf c0 c1 b0 b1 pre d0 d1 hc0 hc1 hb0 hb1 hd0 hd1 p0 p1 s ra guard hpre fp s1 s2 l32 l40 l16 rslot hfp hs1 hs2 hl32 hl40 hl16 hrslot R S scratch hsc hsp hcap hcap63 hmm st0 h0) ?_
  intro st1 h1
  refine eventually_trans _ _ _ _ (sd_g6e_f1 k hk hf c0 c1 b0 b1 pre d0 d1 hc0 hc1 hb0 hb1 hd0 hd1 p0 p1 s ra guard hpre fp s1 s2 l32 l40 l16 rslot hfp hs1 hs2 hl32 hl40 hl16 hrslot R S scratch hsc hsp hcap hcap63 hmm st1 h1) ?_
  intro st2 h2
  exact sd_g6e_epi k hk hf c0 c1 b0 b1 pre d0 d1 hc0 hc1 hb0 hb1 hd0 hd1 p0 p1 s ra guard hpre fp s1 s2 l32 l40 l16 rslot hfp hs1 hs2 hl32 hl40 hl16 hrslot R S scratch hsc hsp hcap hcap63 st2 h2
theorem sd_g6e_fast_kind : ∀ (h : Host), type_of% (@sd_g6e_fast h)
    = @E2eScal.encFastKindN h SdMarshal E2eScal.Gen6Enc.sd_g6e_layout [.bytes 32, .bytes 32] := by
  intro h; rfl

end E2eScal.Gen6Enc
