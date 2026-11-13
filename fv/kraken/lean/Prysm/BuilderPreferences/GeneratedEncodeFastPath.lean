import Prysm.BeaconBlockHeader.EncodeFastPathKindInstances
import Codec.EncodeFrameTest
import Prysm.BuilderPreferences.Code

/-!
# Fast path (`encoder --fast-path`): encoder fast path of `(*v1alpha1.BuilderPreferences).MarshalSSZTo`

Generated from the `.S` file and the IR: a symbolic dataflow walk of the fast path, one application of a
step lemma per directive (windows with the nops erased), boundary states between the fields. Every theorem
has a `_kind` line (`encHeadKindAnyFrame`, `encFieldKindAnyFrame`, `encEpilogueKindAnyFrame`, `encFastPathKindAnyFrame`).
**Fast path only**: `len(dst) + 8 ≤ cap(dst)` and every byte-vector field of its exact length. No
`runtime.growslice` directive is stepped: each capacity test is decided from the premise. Not covered: the
growslice branches, the length rejects, the morestack path. Not a complete encoder result.
FAST-PATH-JSON: {"type": "BuilderPreferences", "const": "marshalSSZTo", "prefix": "Encode.generated", "size": 8, "frame": 72, "guard_addend": 0, "runtime_calls": false, "fields": [["MaxExecutionPayment", "u", 8]], "boundaries": [8, 33], "layout": "Prysm.BuilderPreferences.Encode.generated_layout", "S_sha256": "e21892cbe54a798fd0e798ad727b5201c979e46c184d63cc012fb826f2375377", "ir_sha256": "c1586d32018abd182c16d50f6a7a76e38814cab08cf4a7a42105fe30342a5d2a", "statement_check": "kind instance only", "S": "prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPreferences.MarshalSSZTo.S", "ir": "prysm/ir/ir-mainnet.json", "ir_type": "v1alpha1.BuilderPreferences", "kinds": [{"theorem": "Encode.generated_head", "kind": "encHeadKindAnyFrame"}, {"theorem": "Encode.generated_field_0", "kind": "encFieldKindAnyFrame"}, {"theorem": "Encode.generated_epilogue", "kind": "encEpilogueKindAnyFrame"}, {"theorem": "Encode.generated_fast", "kind": "encFastPathKindAnyFrame"}]}
-/

open Machine Runtime Codec Prysm.BuilderPreferences.Code
variable [Host]

namespace Prysm.BuilderPreferences

/-- The frame facts of `marshalSSZTo` (read from the `.S` file by the walk): frame `0x48`, stack chunks
`fp s2 t40 t24`. -/
def Encode.generated_layout : EncoderFrameLayout where
  stateWord := true
  frame := 72
  guardAddend := 0
  callsMemmove := false
  stackChunkCount := 4
  stackChunkLengths := [(0, 8), (1, 8), (2, 16), (3, 16)]
  pre := [.at (.below 8) (.original 0), .at (.above 16) (.original 1), .at (.below 40) (.original 2), .at (.below 24) (.original 3)]
  existentials := [.fixed 8, .fixed 16]
  post := [.at (.below 8) (.reg .rbp), .at (.above 16) (.reg .rbx), .at (.below 40) (.field 0), .at (.below 32) (.existential 0), .at (.below 24) (.existential 1)]


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Head: directives 0–7 (stack guard, frame, spills); entry → boundary state 0. -/
theorem Encode.generated_head : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v0 pre d0 : List UInt8) (hast : ast.length = 8) (hv0 : v0.length = 8) (hd0 : d0.length = 8)
    (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s2 t40 t24 : List UInt8) (hfp : fp.length = 8) (hs2 : s2.length = 8) (ht40 : t40.length = 16) (ht24 : t24.length = 16)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (t24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 88 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 8 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 8)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 80 }
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
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf ast v0 pre d0 hast hv0 hd0 s ra guard hpre fp s2 t40 t24 hfp hs2 ht40 ht24 R h_mem hguard hsp hcap hcap63
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hcap hcap63 hpre ⊢
  have hcap' : rcx.toBitVec.toNat + 8 ≤ rdi.toBitVec.toNat := hcap
  apply encoder_prologue_small_frame _ _ _ _ k (k + 6) (window_infix_at hk 0 6) (by rfl) (by rfl) guard fp hfp _ _ _ (by dsimp only; ecancel) hguard
  intro m1 H1 fl1; normalize_registers; dsimp only at H1
  apply step_sub_immediate Reg64.rsp 72 _ (k + 6) (k + 7) (window_infix_at hk 6 1) (by rfl) (by rfl)
  intro fl; normalize_registers
  apply register_value_rewrite Reg64.rsp (rsp.toBitVec - 80) _ _ _ (by show ((rsp.toBitVec - 8) - 72 : BitVec 64) = (rsp.toBitVec - 80); bv_omega)
  normalize_registers
  apply step_store Reg64.rbx Reg64.rsp 96 _ (k + 7) (k + 8) (window_infix_at hk 7 1) (by rfl) (by rfl)
    (rsp.toBitVec - 80) (rsp.toBitVec + 16) (by encoder_address_equation) s2 hs2 _ _ _ (by rfl) (by ecancel)
  intro m2 H2; normalize_registers; simp only [Reg64s.get64] at H2
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem Encode.generated_head_kind : ∀ (h : Host), type_of% (@Encode.generated_head h)
    = @Codec.encHeadKindAnyFrame h marshalSSZTo Prysm.BuilderPreferences.Encode.generated_layout [.u64]
    ⟨8, 0, [(.rax, .receiver), (.rbx, .ptr), (.rcx, .len 0), (.rdi, .cap)],
      [.at (.below 8) (.reg .rbp), .at (.above 16) (.reg .rbx), .at (.below 40) (.original 2), .at (.below 24) (.original 3)],
      []⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Field 0 `MaxExecutionPayment` (uint64): directives 8–32; boundary state 0 → 1. -/
theorem Encode.generated_field_0 : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v0 pre d0 : List UInt8) (hast : ast.length = 8) (hv0 : v0.length = 8) (hd0 : d0.length = 8)
    (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s2 t40 t24 : List UInt8) (hfp : fp.length = 8) (hs2 : s2.length = 8) (ht40 : t40.length = 16) (ht24 : t24.length = 16)
    (R : DataMem → Prop)
    (hsp : 88 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 8 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 8)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 80 }
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
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 33)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 80 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st.data.regs.r14 = s.regs.r14
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
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v0 pre d0 hast hv0 hd0 s ra guard hpre fp s2 t40 t24 hfp hs2 ht40 ht24 R hsp hcap hcap63
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
  have hcap' : rcx.toBitVec.toNat + 8 ≤ rdi.toBitVec.toNat := hcap
  apply step_lea Reg64.rdx Reg64.rcx 8 _ (k + 8) (k + 9) (window_infix_at hk 8 1) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.rdx (rcx.toBitVec + 8) _ _ _ (by show (rcx.toBitVec + 8 : BitVec 64) = (rcx.toBitVec + 8); bv_omega)
  normalize_registers
  apply step_load_bytes Reg64.r8 Reg64.rax 8 _ (k + 9) (k + 10) (window_infix_at hk 9 1) (by rfl) (by rfl)
    rax.toBitVec (rax.toBitVec + 8) (by encoder_address_equation) v0 hv0 _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_lea Reg64.r9 Reg64.rsp 40 _ (k + 10) (k + 14) (window_infix_at hk 10 4) (by rfl) (by rfl)
  normalize_registers
  apply register_value_rewrite Reg64.r9 (rsp.toBitVec - 40) _ _ _ (by show ((rsp.toBitVec - 80) + 40 : BitVec 64) = (rsp.toBitVec - 40); bv_omega)
  normalize_registers
  apply step_store_xmm15 Reg64.r9 0 _ (k + 14) (k + 15) (window_infix_at hk 14 1) (by rfl) (by rfl)
    (rsp.toBitVec - 40) (rsp.toBitVec - 40) (by encoder_address_equation) t40 ht40 _ _ _ (by rfl) (by ecancel)
  intro m3 H3; normalize_registers; try dsimp only at H3
  apply step_store_xmm15 Reg64.r9 16 _ (k + 15) (k + 16) (window_infix_at hk 15 1) (by rfl) (by rfl)
    (rsp.toBitVec - 40) (rsp.toBitVec - 24) (by encoder_address_equation) t24 ht24 _ _ _ (by rfl) (by ecancel)
  intro m4 H4; normalize_registers; try dsimp only at H4
  rw [Machine.at_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 40), show (rsp.toBitVec - 40) + 8 = (rsp.toBitVec - 32) by bv_omega] at H4
  apply step_store Reg64.r8 Reg64.rsp 40 _ (k + 16) (k + 17) (window_infix_at hk 16 1) (by rfl) (by rfl)
    (rsp.toBitVec - 80) (rsp.toBitVec - 40) (by encoder_address_equation) ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).take 8) (by rw [List.length_take, Int.toBytes_length]; rfl) _ _ _ (by rfl) (by ecancel)
  intro m5 H5; normalize_registers; simp only [Reg64s.get64] at H5
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v0 hv0] at H5
  have hl30 := Machine.label_at' hk hf (j := 30)
    (by simp only [marshalSSZTo, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  apply step_cmp_jae_taken Reg64.rdi Reg64.rdx _ _ (k + 17) (k + 30) (window_infix_at hk 17 2) (by rfl) hl30 _ _ (by show ((rcx.toBitVec + 8) : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)
  intro fl; normalize_registers
  apply step_label _ _ (k + 30) (k + 31) (window_infix_at hk 30 1) (by rfl) (by rfl)
  apply step_load_bytes Reg64.r8 Reg64.rsp 40 _ (k + 31) (k + 32) (window_infix_at hk 31 1) (by rfl) (by rfl)
    (rsp.toBitVec - 80) (rsp.toBitVec - 40) (by encoder_address_equation) v0 hv0 _ _ _ (by rfl) (by ecancel)
  normalize_registers
  apply step_store_indexed Reg64.r8 Reg64.rbx Reg64.rcx 0 _ (k + 32) (k + 33) (window_infix_at hk 32 1) (by rfl) (by rfl)
    rbx.toBitVec rcx.toBitVec (rbx.toBitVec + rcx.toBitVec) (by encoder_address_equation) d0 hd0 _ _ _ (by rfl) (by rfl) (by ecancel)
  intro m6 H6; normalize_registers; simp only [Reg64s.get64] at H6
  simp only [toBytes_ofInt_ofBytes 64 8 rfl v0 hv0] at H6
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ((Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8), (Int.toBytes 16 (zmms1.get (AvxReg.xmm RegMm.mm15)).toInt), (by rw [List.length_drop, Int.toBytes_length]), (Int.toBytes_length 16 _), ?_⟩
  first | ecancel | (dsimp only; ecancel)
theorem Encode.generated_field_0_kind : ∀ (h : Host), type_of% (@Encode.generated_field_0 h)
    = @Codec.encFieldKindAnyFrame h marshalSSZTo Prysm.BuilderPreferences.Encode.generated_layout [.u64]
    ⟨8, 0, [(.rax, .receiver), (.rbx, .ptr), (.rcx, .len 0), (.rdi, .cap)],
      [.at (.below 8) (.reg .rbp), .at (.above 16) (.reg .rbx), .at (.below 40) (.original 2), .at (.below 24) (.original 3)],
      []⟩
    ⟨33, 1, [(.rbx, .ptr), (.rdx, .len 8), (.rdi, .cap)],
      [.at (.below 8) (.reg .rbp), .at (.above 16) (.reg .rbx), .at (.below 40) (.field 0), .at (.below 32) (.existential 0), .at (.below 24) (.existential 1)],
      [.fixed 8, .fixed 16]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Epilogue: directives 33–return; boundary state 1 → the fast-path post-state. -/
theorem Encode.generated_epilogue : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v0 pre d0 : List UInt8) (hast : ast.length = 8) (hv0 : v0.length = 8) (hd0 : d0.length = 8)
    (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s2 t40 t24 : List UInt8) (hfp : fp.length = 8) (hs2 : s2.length = 8) (ht40 : t40.length = 16) (ht24 : t24.length = 16)
    (R : DataMem → Prop)
    (hsp : 88 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 8 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (st0 : MachineState),
    (st0.pc = Host.addrOf (k + 33)
        ∧ st0.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 80 }
        ∧ st0.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 }
        ∧ st0.data.regs.r14 = s.regs.r14
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
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ R) st0.data.dmem) →
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec
        ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 8
        ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0
        ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8
        ∧ st.data.regs.rbp = s.regs.rbp
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ R) st.data.dmem)
      st0 := by
  intro k hk hf ast v0 pre d0 hast hv0 hd0 s ra guard hpre fp s2 t40 t24 hfp hs2 ht40 ht24 R hsp hcap hcap63
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hsp hcap hcap63 hpre ⊢
  rintro ⟨d, pc⟩ ⟨hpc, hrsp, hrbp, hr14, hrrbx, hrrdx, hrrdi, x0, x1, hx0, hx1, Hm⟩
  dsimp only at hpc hrsp hrbp hr14 hrrbx hrrdx hrrdi Hm
  subst hpc
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩, zmms1, flags1, mem1⟩ := d
  simp only [Reg64s.get64] at hrsp hrbp hr14 hrrbx hrrdx hrrdi Hm
  subst rsp1 rbp1 r141
  obtain rfl : rbx = rbx1 := (UInt64.toBitVec_inj.mp hrrbx).symm
  obtain rfl : rdx1 = { toBitVec := rcx.toBitVec + 8 } := UInt64.toBitVec_inj.mp hrrdx
  obtain rfl : rdi = rdi1 := (UInt64.toBitVec_inj.mp hrrdi).symm
  have hcap' : rcx.toBitVec.toNat + 8 ≤ rdi.toBitVec.toNat := hcap
  apply step_move_register Reg64.rax Reg64.rbx _ (k + 33) (k + 34) (window_infix_at hk 33 1) (by rfl) (by rfl)
  normalize_registers
  apply step_move_register Reg64.rbx Reg64.rdx _ (k + 34) (k + 35) (window_infix_at hk 34 1) (by rfl) (by rfl)
  normalize_registers
  apply step_move_register Reg64.rcx Reg64.rdi _ (k + 35) (k + 36) (window_infix_at hk 35 1) (by rfl) (by rfl)
  normalize_registers
  apply step_xor32 Reg64.rdi _ (k + 36) (k + 37) (window_infix_at hk 36 1) (by rfl) (by rfl)
  intro fl; normalize_registers
  apply step_xor32 Reg64.rsi _ (k + 37) (k + 38) (window_infix_at hk 37 1) (by rfl) (by rfl)
  intro fl; normalize_registers
  apply step_add_immediate Reg64.rsp 72 _ (k + 38) (k + 39) (window_infix_at hk 38 1) (by rfl) (by rfl)
  intro fl; normalize_registers
  apply register_value_rewrite Reg64.rsp (rsp.toBitVec - 8) _ _ _ (by show ((rsp.toBitVec - 80) + 72 : BitVec 64) = (rsp.toBitVec - 8); bv_omega)
  normalize_registers
  refine eventually_trans _ _ _ _ (dec_return_seg _ (k + 39) (window_infix_at hk 39 2) (by rfl) (rsp.toBitVec - 8) rsp.toBitVec (by bv_omega) rbp ra _ _ (by rfl) (by ecancel)) ?_
  rintro ⟨d', pc'⟩ ⟨hpc', hrsp', hrbp', hreg', hmem'⟩
  dsimp only at hpc' hrsp' hrbp' hreg' hmem'
  apply Eventually.done
  refine ⟨hpc', ?_, ?_, ?_, ?_, ?_, ?_, hrbp', ?_, x0, x1, hx0, hx1, ?_⟩
  · exact UInt64.toBitVec_inj.mp (hreg' Reg64.rax (by decide) (by decide))
  · show d'.regs.rbx.toBitVec.toNat = rcx.toBitVec.toNat + 8
    rw [show d'.regs.rbx.toBitVec = rcx.toBitVec + 8 from hreg' Reg64.rbx (by decide) (by decide)]
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
    = @Codec.encEpilogueKindAnyFrame h marshalSSZTo Prysm.BuilderPreferences.Encode.generated_layout [.u64]
    ⟨33, 1, [(.rbx, .ptr), (.rdx, .len 8), (.rdi, .cap)],
      [.at (.below 8) (.reg .rbp), .at (.above 16) (.reg .rbx), .at (.below 40) (.field 0), .at (.below 32) (.existential 0), .at (.below 24) (.existential 1)],
      [.fixed 8, .fixed 16]⟩ := by
  intro h; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Encoder fast path of `(*v1alpha1.BuilderPreferences).MarshalSSZTo` (Go 1.26.10), generated** (`encoder --fast-path`):
head, one theorem per field, epilogue, chained by `eventually_trans`. Premises: `len + 8 ≤ cap`,
every byte-vector field of its exact length. Statement = the kind instance (`_kind`). Fast path only. -/
theorem Encode.generated_fast : ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (ast v0 pre d0 : List UInt8) (hast : ast.length = 8) (hv0 : v0.length = 8) (hd0 : d0.length = 8)
    (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s2 t40 t24 : List UInt8) (hfp : fp.length = 8) (hs2 : s2.length = 8) (ht40 : t40.length = 16) (ht24 : t24.length = 16)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (t24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 88 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 8 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec
        ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 8
        ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0
        ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8
        ∧ st.data.regs.rbp = s.regs.rbp
        ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 : List UInt8), x0.length = 8 ∧ x1.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (v0.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq (v0.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (v0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf ast v0 pre d0 hast hv0 hd0 s ra guard hpre fp s2 t40 t24 hfp hs2 ht40 ht24 R h_mem hguard hsp hcap hcap63
  refine eventually_trans _ _ _ _ (Encode.generated_head k hk hf ast v0 pre d0 hast hv0 hd0 s ra guard hpre fp s2 t40 t24 hfp hs2 ht40 ht24 R h_mem hguard hsp hcap hcap63) ?_
  intro st0 h0
  refine eventually_trans _ _ _ _ (Encode.generated_field_0 k hk hf ast v0 pre d0 hast hv0 hd0 s ra guard hpre fp s2 t40 t24 hfp hs2 ht40 ht24 R hsp hcap hcap63 st0 h0) ?_
  intro st1 h1
  exact Encode.generated_epilogue k hk hf ast v0 pre d0 hast hv0 hd0 s ra guard hpre fp s2 t40 t24 hfp hs2 ht40 ht24 R hsp hcap hcap63 st1 h1
theorem Encode.generated_fast_kind : ∀ (h : Host), type_of% (@Encode.generated_fast h)
    = @Codec.encFastPathKindAnyFrame h marshalSSZTo Prysm.BuilderPreferences.Encode.generated_layout [.u64] := by
  intro h; rfl

end Prysm.BuilderPreferences
