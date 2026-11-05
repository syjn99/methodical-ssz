import Fk.CpMarshal
import Fk.LcReject
import Fk.AdSpec

/-!
# Prysm AttestationData.MarshalSSZTo, fast path, on Kraken main

With Source and Target non-nil, `len(BeaconBlockRoot) = len(Source.Root) =
len(Target.Root) = 32`, and `cap(dst) ≥ len(dst) + 128`, the code appends
Slot, CommitteeIndex, BeaconBlockRoot (`memmove`), then the inlined
`Checkpoint.MarshalSSZTo` for Source and Target (Epoch, Root by `memmove`), and
returns `(dst[:len+128], nil)`; `dst[:len]` (`pre`) is kept.
Premises the Go caller provides: receiver, objects, roots, `dst` and stack
chunks separated; non-nil Source and Target (a nil one takes the
`new(Checkpoint)` path, not proved); the stack guard below rsp − 104;
`cap < 2^63`; the memmove contract.
-/

open Fk Fk.Code
variable [Host]

theorem adm_slot (x : BitVec 64) : x - 8#64 - 224 - 8#64 = x - 240 := by bv_omega
theorem adm_slot' (x : BitVec 64) : ({ toBitVec := x - 240 } + 8 : UInt64).toBitVec - 8#64 = x - 240 := by
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
theorem adm_g (x o : BitVec 64) : ({ toBitVec := x - 240 } + 8 : UInt64).toBitVec + o = x - 232 + o := by
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
theorem adm_pop (x : BitVec 64) : 224 + ({ toBitVec := x - 240 } + 8 : UInt64).toBitVec = x - 8 := by
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
theorem adm_a1 (x y : BitVec 64) : 8 + (y + 8) + x * 1#64 + -8 = x + y + 8 := by
  rw [add8_neg8, BitVec.add_assoc]

theorem toNat_add_neg104 (x : BitVec 64) (h : 104 ≤ x.toNat) : (x + -104).toNat = x.toNat - 104 := by
  rw [← BitVec.sub_eq_add_neg, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simpa using h)]; rfl

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
theorem ad_marshal_main (k : Nat) (hk : PrysmAttestationDataMarshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh PrysmAttestationDataMarshalSSZTo k)
    (e0 e1 root se sroot te troot pre d0 d1 d2 d3 d4 d5 d6 : List UInt8)
    (h0 : e0.length = 8) (h1 : e1.length = 8) (hroot : root.length = 32) (hse : se.length = 8)
    (hsroot : sroot.length = 32) (hte : te.length = 8) (htroot : troot.length = 32)
    (hd0 : d0.length = 8) (hd1 : d1.length = 8) (hd2 : d2.length = 32) (hd3 : d3.length = 8) (hd4 : d4.length = 32)
    (hd5 : d5.length = 8) (hd6 : d6.length = 32)
    (p ps pt p1 p2 : BitVec 64)
    (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s8 s16 l72 l80 l120 l128 l136 l144 rslot : List UInt8)
    (hfp : fp.length = 8) (hs8 : s8.length = 8) (hs16 : s16.length = 8) (hl72 : l72.length = 8)
    (hl80 : l80.length = 8) (hl120 : l120.length = 8) (hl128 : l128.length = 8) (hl136 : l136.length = 8)
    (hl144 : l144.length = 8) (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s8.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s16.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l72.At (s.regs.rsp.toBitVec - 72)) ⋆ Eq (l80.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (l120.At (s.regs.rsp.toBitVec - 120)) ⋆ Eq (l128.At (s.regs.rsp.toBitVec - 128))
      ⋆ Eq (l136.At (s.regs.rsp.toBitVec - 136)) ⋆ Eq (l144.At (s.regs.rsp.toBitVec - 144))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 240)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 240 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (e0.At s.regs.rax.toBitVec) ⋆ Eq (e1.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ((Int.toBytes 8 ps.toInt).At (s.regs.rax.toBitVec + 40))
      ⋆ Eq ((Int.toBytes 8 pt.toInt).At (s.regs.rax.toBitVec + 48)) ⋆ Eq (root.At p)
      ⋆ Eq (se.At ps) ⋆ Eq ((Int.toBytes 8 p1.toInt).At (ps + 8)) ⋆ Eq ((Int.toBytes 8 32).At (ps + 16))
      ⋆ Eq (sroot.At p1)
      ⋆ Eq (te.At pt) ⋆ Eq ((Int.toBytes 8 p2.toInt).At (pt + 8)) ⋆ Eq ((Int.toBytes 8 32).At (pt + 16))
      ⋆ Eq (troot.At p2)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
      ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
      ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56))
      ⋆ Eq (d5.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
      ⋆ Eq (d6.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 96)) ⋆ R)
    (hps : ps ≠ 0) (hpt : pt ≠ 0)
    (hguard : guard.toNat + 104 < s.regs.rsp.toNat) (hsp : 240 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 128 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hmm : MemmoveC S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 128 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (e0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (e1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (root.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
          ⋆ Eq (se.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq (sroot.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56))
          ⋆ Eq (te.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
          ⋆ Eq (troot.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 96)) ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hcap hcap63 hpre ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *
  kat hk PrysmAttestationDataMarshalSSZTo 0
  kat hk PrysmAttestationDataMarshalSSZTo 1
  kat hk PrysmAttestationDataMarshalSSZTo 2
  kat hk PrysmAttestationDataMarshalSSZTo 3
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 4
  split
  case isTrue h =>
    exfalso
    rw [cmp_be_false _ _ _ _ (by rw [toNat_add_neg104 _ (by simp; omega)]; simp; omega)] at h
    exact absurd h (by simp)
  simp only [Effects.All]
  kat hk PrysmAttestationDataMarshalSSZTo 5
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 6
  kat hk PrysmAttestationDataMarshalSSZTo 7
  kat hk PrysmAttestationDataMarshalSSZTo 8
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s16 _ _ (by bv_omega) (by ecancel) (by exact hs16)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 9
  apply store_step_at _ _ (rsp.toBitVec + 8) _ _ _ s8 _ _ (by bv_omega) (by ecancel) (by exact hs8)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 10
  kat hk PrysmAttestationDataMarshalSSZTo 11
  apply load_step _ _ _ _ e0 _ _ (by ecancel) (by exact h0)
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 12
  kat hk PrysmAttestationDataMarshalSSZTo 13
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf PrysmAttestationDataMarshalSSZTo 26
  kat hk PrysmAttestationDataMarshalSSZTo 26
  kat hk PrysmAttestationDataMarshalSSZTo 27
  rw [cpm_addr]
  apply store_step _ _ _ _ _ d0 _ _ (by ecancel) (by exact hd0)
  intro m4 H4
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl e0 h0] at H4
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 28
  kat hk PrysmAttestationDataMarshalSSZTo 29
  apply load_step_at _ _ (rax.toBitVec + 8) _ _ e1 _ _ (by kaddr) (by ecancel) (by exact h1)
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 30
  kat hk PrysmAttestationDataMarshalSSZTo 31
  kat hk PrysmAttestationDataMarshalSSZTo 32
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf PrysmAttestationDataMarshalSSZTo 45
  kat hk PrysmAttestationDataMarshalSSZTo 45
  kat hk PrysmAttestationDataMarshalSSZTo 46
  rw [adm_a1]
  apply store_step _ _ _ _ _ d1 _ _ (by ecancel) (by exact hd1)
  intro m5 H5
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl e1 h1] at H5
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 47
  apply load_step_at _ _ (rax.toBitVec + 16) _ _ (Int.toBytes 8 p.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 48
  apply load_step_at _ _ (rax.toBitVec + 24) _ _ (Int.toBytes 8 32) _ _ (by kaddr) (by ecancel) (by rfl)
  simp only [show Int.ofBytes (Int.toBytes 8 32) = 32 by decide]
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 49
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk PrysmAttestationDataMarshalSSZTo 50
  kat hk PrysmAttestationDataMarshalSSZTo 51
  kat hk PrysmAttestationDataMarshalSSZTo 52
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf PrysmAttestationDataMarshalSSZTo 67
  kat hk PrysmAttestationDataMarshalSSZTo 67
  kat hk PrysmAttestationDataMarshalSSZTo 68
  apply store_step_at _ _ (rsp.toBitVec - 72) _ _ _ l72 _ _ (by bv_omega) (by ecancel) (by exact hl72)
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 69
  apply store_step_at _ _ (rsp.toBitVec - 136) _ _ _ l136 _ _ (by bv_omega) (by ecancel) (by exact hl136)
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 70
  apply store_step_at _ _ (rsp.toBitVec - 120) _ _ _ l120 _ _ (by bv_omega) (by ecancel) (by exact hl120)
  intro m8 H8
  simp only [Width.bytes, Width.bits] at H8
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 71
  kat hk PrysmAttestationDataMarshalSSZTo 72
  kat hk PrysmAttestationDataMarshalSSZTo 73
  kat hk PrysmAttestationDataMarshalSSZTo 74
  apply store_step_at _ _ (rsp.toBitVec - 240) _ _ _ rslot _ _ (adm_slot _) (by ecancel) (by exact hrs)
  intro m9 H9
  simp only [Width.bytes, Width.bits] at H9
  kunfold
  rw [adm_slot] at *
  rw [show rbx.toBitVec + (8 + (rcx.toBitVec + 8)) * 1#64 = rbx.toBitVec + rcx.toBitVec + 16 by
    rw [BitVec.mul_one]; bv_omega] at *
  refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (k + 74 + 1)) root d2 scratch _
    (by rw [hroot]; rfl) (by rw [hroot, hd2]) hsc (by dsimp only; ecancel)) ?_
  rintro ⟨e1', pc1⟩ ⟨hpc1, hrsp1, stk1, hstk1, Hm1⟩
  dsimp only at hpc1 hrsp1 Hm1
  subst hpc1
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩,
    zmms1, flags1, mem1⟩ := e1'
  simp only at hrsp1 Hm1
  subst hrsp1
  kat hk PrysmAttestationDataMarshalSSZTo 75
  rw [adm_g, show rsp.toBitVec - 232 + 240 = rsp.toBitVec + 8 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 76
  apply load_step_at _ _ (rax.toBitVec + 40) _ _ (Int.toBytes 8 ps.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 77
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h; exact hps h
  simp only [Effects.All]
  klabel hk hf PrysmAttestationDataMarshalSSZTo 92
  kat hk PrysmAttestationDataMarshalSSZTo 92
  kat hk PrysmAttestationDataMarshalSSZTo 93
  apply load_step_at _ _ (rax.toBitVec + 40) _ _ (Int.toBytes 8 ps.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 94
  rw [adm_g, show rsp.toBitVec - 232 + 96 = rsp.toBitVec - 136 by bv_omega]
  generalize hv9 : (8 + (rcx.toBitVec + 8) + 32) = v9 at *
  apply load_step _ _ _ _ (Int.toBytes 8 v9.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 95
  kat hk PrysmAttestationDataMarshalSSZTo 96
  apply load_step _ _ _ _ se _ _ (by ecancel) (by exact hse)
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 97
  rw [adm_g, show rsp.toBitVec - 232 + 112 = rsp.toBitVec - 120 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rdi.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 98
  kat hk PrysmAttestationDataMarshalSSZTo 99
  kat hk PrysmAttestationDataMarshalSSZTo 100
  have hv9n : v9.toNat = rcx.toNat + 48 := by rw [← hv9]; simp [BitVec.toNat_add]; omega
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  kat hk PrysmAttestationDataMarshalSSZTo 101
  rw [adm_g, show rsp.toBitVec - 232 + 160 = rsp.toBitVec - 72 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 102
  klabel hk hf PrysmAttestationDataMarshalSSZTo 113
  kat hk PrysmAttestationDataMarshalSSZTo 113
  kat hk PrysmAttestationDataMarshalSSZTo 114
  rw [add8_neg8, show rbx.toBitVec + v9 = rbx.toBitVec + rcx.toBitVec + 48 by rw [← hv9]; bv_omega]
  apply store_step _ _ _ _ _ d3 _ _ (by ecancel) (by exact hd3)
  intro m10 H10
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl se hse] at H10
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 115
  apply load_step_at _ _ (ps + 8) _ _ (Int.toBytes 8 p1.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 116
  apply load_step_at _ _ (ps + 16) _ _ (Int.toBytes 8 32) _ _ (by kaddr) (by ecancel) (by rfl)
  simp only [show Int.ofBytes (Int.toBytes 8 32) = 32 by decide]
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 117
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf PrysmAttestationDataMarshalSSZTo 124
  kat hk PrysmAttestationDataMarshalSSZTo 124
  kat hk PrysmAttestationDataMarshalSSZTo 125
  kat hk PrysmAttestationDataMarshalSSZTo 126
  kat hk PrysmAttestationDataMarshalSSZTo 127
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf PrysmAttestationDataMarshalSSZTo 137
  kat hk PrysmAttestationDataMarshalSSZTo 137
  kat hk PrysmAttestationDataMarshalSSZTo 138
  rw [adm_g, show rsp.toBitVec - 232 + 96 = rsp.toBitVec - 136 by bv_omega]
  apply store_step _ _ _ _ _ (Int.toBytes 8 v9.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m11 H11
  simp only [Width.bytes, Width.bits] at H11
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 139
  rw [adm_g, show rsp.toBitVec - 232 + 112 = rsp.toBitVec - 120 by bv_omega]
  apply store_step _ _ _ _ _ (Int.toBytes 8 rdi.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m12 H12
  simp only [Width.bytes, Width.bits] at H12
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 140
  rw [adm_g, show rsp.toBitVec - 232 + 160 = rsp.toBitVec - 72 by bv_omega]
  apply store_step _ _ _ _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m13 H13
  simp only [Width.bytes, Width.bits] at H13
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 141
  kat hk PrysmAttestationDataMarshalSSZTo 142
  kat hk PrysmAttestationDataMarshalSSZTo 143
  kat hk PrysmAttestationDataMarshalSSZTo 144
  apply store_step_at _ _ (rsp.toBitVec - 240) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 74 + 1)).toBitVec.toInt) _ _
    (adm_slot' _) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m14 H14
  simp only [Width.bytes, Width.bits] at H14
  kunfold
  rw [adm_slot'] at *
  rw [show 8 + v9 + rbx.toBitVec = rbx.toBitVec + rcx.toBitVec + 56 by rw [← hv9]; bv_omega] at *
  refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (k + 144 + 1)) sroot d4 stk1 _
    (by rw [hsroot]; rfl) (by rw [hsroot, hd4]) hstk1 (by dsimp only; ecancel)) ?_
  rintro ⟨e2', pc2⟩ ⟨hpc2, hrsp2, stk2, hstk2, Hm2⟩
  dsimp only at hpc2 hrsp2 Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := e2'
  simp only at hrsp2 Hm2
  subst hrsp2
  kat hk PrysmAttestationDataMarshalSSZTo 145
  rw [adm_g, show rsp.toBitVec - 232 + 240 = rsp.toBitVec + 8 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 146
  intro _
  kat hk PrysmAttestationDataMarshalSSZTo 147
  rw [adm_g, show rsp.toBitVec - 232 + 112 = rsp.toBitVec - 120 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rdi.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 148
  rw [adm_g, show rsp.toBitVec - 232 + 160 = rsp.toBitVec - 72 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 149
  rw [adm_g, show rsp.toBitVec - 232 + 96 = rsp.toBitVec - 136 by bv_omega]
  generalize hv10 : (8 + v9 + 32) = v10 at *
  have hv10n : v10.toNat = rcx.toNat + 88 := by rw [← hv10]; simp [BitVec.toNat_add]; omega
  apply load_step _ _ _ _ (Int.toBytes 8 v10.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 150
  intro _
  kat hk PrysmAttestationDataMarshalSSZTo 151
  kat hk PrysmAttestationDataMarshalSSZTo 152
  intro _
  kat hk PrysmAttestationDataMarshalSSZTo 153
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf PrysmAttestationDataMarshalSSZTo 186
  kat hk PrysmAttestationDataMarshalSSZTo 186
  kat hk PrysmAttestationDataMarshalSSZTo 187
  apply load_step_at _ _ (rax.toBitVec + 48) _ _ (Int.toBytes 8 pt.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 188
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h; exact hpt h
  simp only [Effects.All]
  klabel hk hf PrysmAttestationDataMarshalSSZTo 210
  kat hk PrysmAttestationDataMarshalSSZTo 210
  kat hk PrysmAttestationDataMarshalSSZTo 211
  apply load_step_at _ _ (rax.toBitVec + 48) _ _ (Int.toBytes 8 pt.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 212
  kat hk PrysmAttestationDataMarshalSSZTo 213
  apply load_step _ _ _ _ te _ _ (by ecancel) (by exact hte)
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 214
  kat hk PrysmAttestationDataMarshalSSZTo 215
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf PrysmAttestationDataMarshalSSZTo 229
  kat hk PrysmAttestationDataMarshalSSZTo 229
  kat hk PrysmAttestationDataMarshalSSZTo 230
  rw [add8_neg8, show rbx.toBitVec + v10 = rbx.toBitVec + rcx.toBitVec + 88 by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega]
  apply store_step _ _ _ _ _ d5 _ _ (by ecancel) (by exact hd5)
  intro m15 H15
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl te hte] at H15
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 231
  apply load_step_at _ _ (pt + 8) _ _ (Int.toBytes 8 p2.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 232
  apply load_step_at _ _ (pt + 16) _ _ (Int.toBytes 8 32) _ _ (by kaddr) (by ecancel) (by rfl)
  simp only [show Int.ofBytes (Int.toBytes 8 32) = 32 by decide]
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 233
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf PrysmAttestationDataMarshalSSZTo 240
  kat hk PrysmAttestationDataMarshalSSZTo 240
  kat hk PrysmAttestationDataMarshalSSZTo 241
  kat hk PrysmAttestationDataMarshalSSZTo 242
  kat hk PrysmAttestationDataMarshalSSZTo 243
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf PrysmAttestationDataMarshalSSZTo 259
  kat hk PrysmAttestationDataMarshalSSZTo 259
  kat hk PrysmAttestationDataMarshalSSZTo 260
  rw [adm_g, show rsp.toBitVec - 232 + 152 = rsp.toBitVec - 80 by bv_omega]
  apply store_step _ _ _ _ _ l80 _ _ (by ecancel) (by exact hl80)
  intro m16 H16
  simp only [Width.bytes, Width.bits] at H16
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 261
  rw [adm_g, show rsp.toBitVec - 232 + 88 = rsp.toBitVec - 144 by bv_omega]
  apply store_step _ _ _ _ _ l144 _ _ (by ecancel) (by exact hl144)
  intro m17 H17
  simp only [Width.bytes, Width.bits] at H17
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 262
  rw [adm_g, show rsp.toBitVec - 232 + 104 = rsp.toBitVec - 128 by bv_omega]
  apply store_step _ _ _ _ _ l128 _ _ (by ecancel) (by exact hl128)
  intro m18 H18
  simp only [Width.bytes, Width.bits] at H18
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 263
  kat hk PrysmAttestationDataMarshalSSZTo 264
  kat hk PrysmAttestationDataMarshalSSZTo 265
  kat hk PrysmAttestationDataMarshalSSZTo 266
  apply store_step_at _ _ (rsp.toBitVec - 240) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 144 + 1)).toBitVec.toInt) _ _
    (adm_slot' _) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m19 H19
  simp only [Width.bytes, Width.bits] at H19
  kunfold
  rw [adm_slot'] at *
  rw [show rbx.toBitVec + (8 + v10) * 1#64 = rbx.toBitVec + rcx.toBitVec + 96 by
    rw [BitVec.mul_one]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega] at *
  refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (k + 266 + 1)) troot d6 stk2 _
    (by rw [htroot]; rfl) (by rw [htroot, hd6]) hstk2 (by dsimp only; ecancel)) ?_
  rintro ⟨e3', pc3⟩ ⟨hpc3, hrsp3, stk3, hstk3, Hm3⟩
  dsimp only at hpc3 hrsp3 Hm3
  subst hpc3
  obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,
    zmms3, flags3, mem3⟩ := e3'
  simp only at hrsp3 Hm3
  subst hrsp3
  kat hk PrysmAttestationDataMarshalSSZTo 267
  intro _
  kat hk PrysmAttestationDataMarshalSSZTo 268
  intro _
  kat hk PrysmAttestationDataMarshalSSZTo 269
  rw [adm_g, show rsp.toBitVec - 232 + 88 = rsp.toBitVec - 144 by bv_omega]
  generalize hv11 : (8 + v10 + 32) = v11 at *
  have hv11n : v11.toNat = rcx.toNat + 128 := by rw [← hv11]; simp [BitVec.toNat_add]; omega
  apply load_step _ _ _ _ (Int.toBytes 8 v11.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 270
  rw [adm_g, show rsp.toBitVec - 232 + 104 = rsp.toBitVec - 128 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rdi.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 271
  rw [adm_g, show rsp.toBitVec - 232 + 152 = rsp.toBitVec - 80 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 272
  kat hk PrysmAttestationDataMarshalSSZTo 273
  intro _
  kat hk PrysmAttestationDataMarshalSSZTo 274
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf PrysmAttestationDataMarshalSSZTo 306
  kat hk PrysmAttestationDataMarshalSSZTo 306
  kat hk PrysmAttestationDataMarshalSSZTo 307
  kat hk PrysmAttestationDataMarshalSSZTo 308
  kat hk PrysmAttestationDataMarshalSSZTo 309
  kat hk PrysmAttestationDataMarshalSSZTo 310
  kat hk PrysmAttestationDataMarshalSSZTo 311
  kat hk PrysmAttestationDataMarshalSSZTo 312
  kat hk PrysmAttestationDataMarshalSSZTo 313
  rw [adm_pop]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmAttestationDataMarshalSSZTo 314
  rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left 7
  · exact sep_true (P := Eq (pre.At rbx.toBitVec) ⋆ Eq (e0.At (rbx.toBitVec + rcx.toBitVec))
      ⋆ Eq (e1.At (rbx.toBitVec + rcx.toBitVec + 8)) ⋆ Eq (root.At (rbx.toBitVec + rcx.toBitVec + 16))
      ⋆ Eq (se.At (rbx.toBitVec + rcx.toBitVec + 48)) ⋆ Eq (sroot.At (rbx.toBitVec + rcx.toBitVec + 56))
      ⋆ Eq (te.At (rbx.toBitVec + rcx.toBitVec + 88)) ⋆ Eq (troot.At (rbx.toBitVec + rcx.toBitVec + 96))) (by ecancel)
  all_goals first
    | exact True.intro
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (show v11.toNat = _; omega)


open Fv1 EthLib.Serialization.Ssz in
/-- The bytes the fast path writes are `adEncode g`, the EthLib serialization. -/
theorem ad_marshal_bytes (g : AttestationDataG) :
    serialize adDesc g.toValue = .ok (adEncode g) ∧
    (adEncode g).toList = (uintBytes 8 g.slot.toNat).toList ++ (uintBytes 8 g.index.toNat).toList ++ g.root.toList
      ++ (uintBytes 8 g.source.epoch.toNat).toList ++ g.source.root.toList
      ++ (uintBytes 8 g.target.epoch.toNat).toList ++ g.target.root.toList :=
  ⟨ad_serialize g, by simp [adEncode, cpEncode]; rfl⟩
