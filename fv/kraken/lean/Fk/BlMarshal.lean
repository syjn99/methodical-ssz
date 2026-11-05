import Fk.CpMarshal
import Fk.Vbl
import Fk.LuRejectCall
import Fv1.SpecBitList

/-!
# BitL.MarshalSSZTo, on Kraken main (regenerated code, generator fix F2)

    type BitL struct { B bitfield.Bitlist `ssz-max:"2048"` }

The fixed generator replaces the byte-count check `len(c.B) > 2048` with
`ssz.ValidateBitlist(c.B, 2048)` (contract `ValidateBitlistC`, behind `bsr`).
The code first appends the offset 4 to dst, then validates, then appends the
bytes of `c.B`.

`bl_marshal_main`: if `c.B` is a valid bitlist (`blValid`, EthLib's rule) and
dst has room, the function writes `4 ‖ c.B` after `dst[:len]` and returns
`(dst[:len+4+n], nil)`. Every stack chunk comes back (existentially).

`bl_marshal_reject_main`: if `c.B` is not valid, the function wraps the
ValidateBitlist error with `fmt.errorf("B: %w")` and returns a non-nil error
with a nil slice. `bl_marshal_rejects_overlong` instantiates it with the
finding-F2 input (258 bytes) and with 2049 bits (257 bytes ending in 0x02);
`bl_marshal_accepts_2048` checks that 2048 bits (257 bytes ending in 0x01)
are valid.
-/

open Fk Fk.Code
variable [Host]

theorem blk_a (x c : BitVec 64) : x - 8#64 - 144 + c = x - 152 + c := by bv_omega
theorem blk_b (x : BitVec 64) : ({ toBitVec := x - 160 } + 8 : UInt64).toBitVec = x - 152 := by
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
theorem blk_168 (x : BitVec 64) : x - 152 + 168 = x + 16 := by bv_omega
theorem blk_160 (x : BitVec 64) : x - 152 + 160 = x + 8 := by bv_omega
theorem blk_104 (x : BitVec 64) : x - 152 + 104 = x - 48 := by bv_omega
theorem blk_64 (x : BitVec 64) : x - 152 + 64 = x - 88 := by bv_omega
theorem blk_72 (x : BitVec 64) : x - 152 + 72 = x - 80 := by bv_omega
theorem blk_112 (x : BitVec 64) : x - 152 + 112 = x - 40 := by bv_omega
theorem blk_80 (x : BitVec 64) : x - 152 + 80 = x - 72 := by bv_omega
theorem blk_120 (x : BitVec 64) : x - 152 + 120 = x - 32 := by bv_omega
theorem blk_96 (x : BitVec 64) : x - 152 + 96 = x - 56 := by bv_omega
theorem blk_88 (x : BitVec 64) : x - 152 + 88 = x - 64 := by bv_omega
theorem blk_128 (x : BitVec 64) : x - 152 + 128 = x - 24 := by bv_omega
theorem blk_136 (x : BitVec 64) : x - 152 + 136 = x - 16 := by bv_omega
theorem blk_call (x : BitVec 64) : x - 8#64 - 144 - 8#64 = x - 160 := by bv_omega
theorem blk_call' (x : BitVec 64) : x - 152 - 8#64 = x - 160 := by bv_omega
theorem blk_sp (x : BitVec 64) : x - 160 + 8 = x - 152 := by bv_omega
theorem blk_pop (x : BitVec 64) : (144 : BitVec 64) + (x - 152) = x - 8 := by bv_omega
theorem blk_d0 (x y : BitVec 64) : y + 4 + x * 1#64 + -4 = x + y := by rw [BitVec.mul_one]; bv_omega
theorem blk_dst (x y : BitVec 64) : x + (y + 4) * 1#64 = x + y + 4 := by rw [BitVec.mul_one]; bv_omega
theorem blk_g (x : UInt64) (h : 24 ≤ x.toNat) : (x.toBitVec + -24).toNat = x.toNat - 24 := by
  rw [← BitVec.sub_eq_add_neg, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bl_marshal_main (k : Nat) (hk : BitLMarshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh BitLMarshalSSZTo k)
    (bl pre d0 d1 : List UInt8) (hv : blValid bl)
    (hd0 : d0.length = 4) (hd1 : d1.length = bl.length) (q c : BitVec 64)
    (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l32 l40 l48 l56 l64 l72 l80 l88 spl rslot : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (hl32 : l32.length = 8) (hl40 : l40.length = 8)
    (hl48 : l48.length = 8) (hl56 : l56.length = 8) (hl64 : l64.length = 8) (hl72 : l72.length = 8)
    (hl80 : l80.length = 8) (hl88 : l88.length = 8) (hspl : spl.length = 32) (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32)) ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (l56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (l64.At (s.regs.rsp.toBitVec - 64)) ⋆ Eq (l72.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (l80.At (s.regs.rsp.toBitVec - 80)) ⋆ Eq (l88.At (s.regs.rsp.toBitVec - 88))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 152))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 160)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 160 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 q.toInt).At s.regs.rax.toBitVec)
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 bl.length).toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 c.toInt).At (s.regs.rax.toBitVec + 16)) ⋆ Eq (bl.At q)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 4)) ⋆ R)
    (hguard : guard.toNat + 24 < s.regs.rsp.toNat) (hsp : 160 + S ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 4 + bl.length ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hvbl : ValidateBitlistC S) (hmm : MemmoveC S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 4 + bl.length ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧
        ∃ fp' s1' s2' l32' l40' l48' l56' l64' l72' l80' l88' spl' rs' sc' : List UInt8,
          fp'.length = 8 ∧ s1'.length = 8 ∧ s2'.length = 8 ∧ l32'.length = 8 ∧ l40'.length = 8 ∧ l48'.length = 8
          ∧ l56'.length = 8 ∧ l64'.length = 8 ∧ l72'.length = 8 ∧ l80'.length = 8 ∧ l88'.length = 8
          ∧ spl'.length = 32 ∧ rs'.length = 8 ∧ sc'.length = S ∧
        (Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq ([4, 0, 0, 0].At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (bl.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 4)) ⋆ Eq (bl.At q)
          ⋆ Eq ((Int.toBytes 8 q.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 bl.length).toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 c.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq (fp'.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1'.At (s.regs.rsp.toBitVec + 8)) ⋆ Eq (s2'.At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (l32'.At (s.regs.rsp.toBitVec - 32)) ⋆ Eq (l40'.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (l48'.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (l56'.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (l64'.At (s.regs.rsp.toBitVec - 64)) ⋆ Eq (l72'.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (l80'.At (s.regs.rsp.toBitVec - 80)) ⋆ Eq (l88'.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 152))
          ⋆ Eq (rs'.At (s.regs.rsp.toBitVec - 160)) ⋆ Eq (sc'.At (s.regs.rsp.toBitVec - 160 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hcap hcap63 hpre ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *
  kat hk BitLMarshalSSZTo 0
  kat hk BitLMarshalSSZTo 1
  kat hk BitLMarshalSSZTo 2
  kat hk BitLMarshalSSZTo 3
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLMarshalSSZTo 4
  split
  case isTrue h =>
    exfalso
    rw [cmp_be_false _ _ _ _ (by rw [blk_g _ (by omega)]; simp; omega)] at h
    exact absurd h (by simp)
  simp only [Effects.All]
  kat hk BitLMarshalSSZTo 5
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk BitLMarshalSSZTo 6
  kat hk BitLMarshalSSZTo 7
  kat hk BitLMarshalSSZTo 8
  rw [blk_a, blk_168]
  apply store_step _ _ _ _ _ s2 _ _ (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk BitLMarshalSSZTo 9
  rw [blk_a, blk_160]
  apply store_step _ _ _ _ _ s1 _ _ (by ecancel) (by exact h1)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk BitLMarshalSSZTo 10
  kat hk BitLMarshalSSZTo 11
  kat hk BitLMarshalSSZTo 12
  kat hk BitLMarshalSSZTo 13
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf BitLMarshalSSZTo 24
  kat hk BitLMarshalSSZTo 24
  kat hk BitLMarshalSSZTo 25
  rw [blk_a, blk_104]
  apply store_step _ _ _ _ _ l48 _ _ (by ecancel) (by exact hl48)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  kat hk BitLMarshalSSZTo 26
  rw [blk_a, blk_64]
  apply store_step _ _ _ _ _ l88 _ _ (by ecancel) (by exact hl88)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  kat hk BitLMarshalSSZTo 27
  rw [blk_a, blk_72]
  apply store_step _ _ _ _ _ l80 _ _ (by ecancel) (by exact hl80)
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  kat hk BitLMarshalSSZTo 28
  rw [blk_d0]
  apply store_step _ _ _ _ _ d0 _ _ (by ecancel) (by exact hd0)
  intro m7 H7
  simp only [Width.bytes, Width.bits, show Int.toBytes 4 (BitVec.truncate 32 (4 : BitVec 64)).toInt = [4, 0, 0, 0] by decide] at H7
  kunfold
  kat hk BitLMarshalSSZTo 29
  apply load_step_at _ _ (rax.toBitVec + 8) _ _ (Int.toBytes 8 (BitVec.ofNat 64 bl.length).toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLMarshalSSZTo 30
  apply load_step_at _ _ (rax.toBitVec + 16) _ _ (Int.toBytes 8 c.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLMarshalSSZTo 31
  apply load_step _ _ _ _ (Int.toBytes 8 q.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLMarshalSSZTo 32
  kat hk BitLMarshalSSZTo 33
  rw [blk_call]
  apply store_step _ _ _ _ _ rslot _ _ (by ecancel) (by exact hrs)
  intro m8 H8
  simp only [Width.bytes, Width.bits] at H8
  kunfold
  try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Fk.ofInt_ofBytes_toBytes64] at *  -- ponytail: values already normalized
  refine eventually_trans _ _ _ _ (hvbl _ (Host.addrOf (k + 33 + 1)) bl scratch spl _ ?_ ?_ hsc hspl
    (by dsimp only; rw [blk_sp]; ecancel)) ?_
  · dsimp only; simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
    first | (rw [UInt64.toNat_ofNat]; omega) | (simp [UInt64.toNat_ofNat]; omega) | (show (UInt64.ofNat bl.length).toNat = bl.length; simp; omega)
  · dsimp only; rfl
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrsp2, hr142, hrbp2, hiff, -, stk2, spl2, hstk2, hspl2, Hm2⟩
  dsimp only at hpc2 hrsp2 hr142 hrbp2 hiff Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := d2
  simp only at hrsp2 hr142 hrbp2 hiff Hm2
  subst hrsp2 hr142 hrbp2
  have hz := hiff.mpr hv
  subst hz
  rw [blk_sp] at Hm2
  kat hk BitLMarshalSSZTo 34
  intro _
  kat hk BitLMarshalSSZTo 35
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf BitLMarshalSSZTo 67
  kat hk BitLMarshalSSZTo 67
  kat hk BitLMarshalSSZTo 68
  rw [blk_b, blk_112]
  apply store_step _ _ _ _ _ l40 _ _ (by ecancel) (by exact hl40)
  intro m9 H9
  simp only [Width.bytes, Width.bits] at H9
  kunfold
  kat hk BitLMarshalSSZTo 69
  rw [blk_b, blk_80]
  apply store_step _ _ _ _ _ l72 _ _ (by ecancel) (by exact hl72)
  intro m10 H10
  simp only [Width.bytes, Width.bits] at H10
  kunfold
  kat hk BitLMarshalSSZTo 70
  rw [blk_b, blk_160]
  apply load_step _ _ _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLMarshalSSZTo 71
  apply load_step_at _ _ (rax.toBitVec + 8) _ _ (Int.toBytes 8 (BitVec.ofNat 64 bl.length).toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLMarshalSSZTo 72
  rw [blk_b, blk_64]
  apply load_step _ _ _ _ (Int.toBytes 8 (rcx.toBitVec + 4).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLMarshalSSZTo 73
  kat hk BitLMarshalSSZTo 74
  apply load_step _ _ _ _ (Int.toBytes 8 q.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLMarshalSSZTo 75
  rw [blk_b, blk_72]
  apply load_step _ _ _ _ (Int.toBytes 8 rdi.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLMarshalSSZTo 76
  kat hk BitLMarshalSSZTo 77
  kat hk BitLMarshalSSZTo 78
  split
  case isTrue h =>
    exfalso
    have hl : bl.length < 2 ^ 63 := by omega
    simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add, BitVec.toNat_sub] at h
    omega
  simp only [Effects.All]
  kat hk BitLMarshalSSZTo 79
  rw [blk_b, blk_104]
  apply load_step _ _ _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLMarshalSSZTo 80
  klabel hk hf BitLMarshalSSZTo 93
  kat hk BitLMarshalSSZTo 93
  kat hk BitLMarshalSSZTo 94
  rw [blk_b, blk_120]
  apply store_step _ _ _ _ _ l32 _ _ (by ecancel) (by exact hl32)
  intro m11 H11
  simp only [Width.bytes, Width.bits] at H11
  kunfold
  kat hk BitLMarshalSSZTo 95
  rw [blk_b, blk_96]
  apply store_step _ _ _ _ _ l56 _ _ (by ecancel) (by exact hl56)
  intro m12 H12
  simp only [Width.bytes, Width.bits] at H12
  kunfold
  kat hk BitLMarshalSSZTo 96
  rw [blk_b, blk_88]
  apply store_step _ _ _ _ _ l64 _ _ (by ecancel) (by exact hl64)
  intro m13 H13
  simp only [Width.bytes, Width.bits] at H13
  kunfold
  kat hk BitLMarshalSSZTo 97
  kat hk BitLMarshalSSZTo 98
  kat hk BitLMarshalSSZTo 99
  kat hk BitLMarshalSSZTo 100
  rw [blk_b, blk_call']
  apply store_step _ _ _ _ _ (Int.toBytes 8 (Host.addrOf (k + 33 + 1)).toBitVec.toInt) _ _ (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m14 H14
  simp only [Width.bytes, Width.bits] at H14
  kunfold
  rw [blk_dst] at *
  refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (k + 100 + 1)) bl d1 stk2 _
    (by show (BitVec.ofNat 64 bl.length).toNat = _; simp; omega) hd1 hstk2 (by dsimp only; ecancel)) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrsp3, -, -, stk3, hstk3, Hm3⟩
  dsimp only at hpc3 hrsp3 Hm3
  subst hpc3
  obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,
    zmms3, flags3, mem3⟩ := d3
  simp only at hrsp3 Hm3
  subst hrsp3
  kat hk BitLMarshalSSZTo 101
  rw [blk_b, blk_120]
  apply load_step _ _ _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLMarshalSSZTo 102
  rw [blk_b, blk_96]
  apply load_step _ _ _ _ (Int.toBytes 8 (rcx.toBitVec + 4 + BitVec.ofNat 64 bl.length * 1#64).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLMarshalSSZTo 103
  rw [blk_b, blk_88]
  apply load_step _ _ _ _ (Int.toBytes 8 rdi.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLMarshalSSZTo 104
  rw [blk_b, blk_80]
  apply load_step _ _ _ _ (Int.toBytes 8 (0#64).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLMarshalSSZTo 105
  rw [blk_b, blk_112]
  apply load_step _ _ _ _ (Int.toBytes 8 rbx2.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLMarshalSSZTo 106
  kat hk BitLMarshalSSZTo 107
  rw [blk_b, blk_pop]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLMarshalSSZTo 108
  rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, Int.toBytes 8 rbp.toBitVec.toInt, Int.toBytes 8 rax.toBitVec.toInt,
    Int.toBytes 8 rbx.toBitVec.toInt, Int.toBytes 8 rbx.toBitVec.toInt, Int.toBytes 8 rbx2.toBitVec.toInt,
    Int.toBytes 8 rbx.toBitVec.toInt, Int.toBytes 8 (rcx.toBitVec + 4 + BitVec.ofNat 64 bl.length * 1#64).toInt,
    Int.toBytes 8 rdi.toBitVec.toInt, Int.toBytes 8 (0#64).toInt, Int.toBytes 8 rdi.toBitVec.toInt,
    Int.toBytes 8 (rcx.toBitVec + 4).toInt, spl2, Int.toBytes 8 (Host.addrOf (k + 100 + 1)).toBitVec.toInt, stk3,
    Int.toBytes_length 8 _, Int.toBytes_length 8 _, Int.toBytes_length 8 _, Int.toBytes_length 8 _,
    Int.toBytes_length 8 _, Int.toBytes_length 8 _, Int.toBytes_length 8 _, Int.toBytes_length 8 _,
    Int.toBytes_length 8 _, Int.toBytes_length 8 _, Int.toBytes_length 8 _, hspl2, Int.toBytes_length 8 _, hstk3, ?mem⟩
  case mem => dsimp only; ecancel
  all_goals dsimp only
  all_goals first
    | (simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Fk.ofInt_ofBytes_toBytes64]; done)
    | (apply UInt64.toBitVec_inj.mp; simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Fk.ofInt_ofBytes_toBytes64]; done)
    | (apply UInt64.toBitVec_inj.mp; simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]; done)
    | (simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Fk.ofInt_ofBytes_toBytes64, UInt64.toNat]
       rw [BitVec.mul_one]; simp [BitVec.toNat_add]; omega)

-- "B: %w" (types1b.ssz.go, the wrap of the ValidateBitlist error)
def blFmtB : List UInt8 := [66, 58, 32, 37, 119]
theorem blFmtB_len : blFmtB.length = 5 := by rfl

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- **F2, fixed: the encoder rejects an invalid bitlist.** If `c.B` is not a
valid Bitlist[2048] encoding (`¬ blValid`, EthLib's rule), MarshalSSZTo
returns a nil slice and a non-nil error (rdi ≠ 0): `ValidateBitlistC` gives
the errorString itab, the code reads its type word and wraps the error with
`fmt.errorf("B: %w")` (`FmtErrorfC`). The offset 4 was already written after
`dst[:len]`; the caller sees a nil slice (G2: `MarshalSSZTo` leaves `dst[:len]`
as it was). -/
theorem bl_marshal_reject_main (k : Nat) (hk : BitLMarshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh BitLMarshalSSZTo k)
    (bl pre d0 : List UInt8) (hv : ¬ blValid bl)
    (hd0 : d0.length = 4) (q c : BitVec 64)
    (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l48 l80 l88 a16 spl sp8 rslot ity : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8)
    (hl48 : l48.length = 8) (hl80 : l80.length = 8) (hl88 : l88.length = 8) (ha16 : a16.length = 16)
    (hspl : spl.length = 32) (hsp8 : sp8.length = 8) (hrs : rslot.length = 8) (hity : ity.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (l80.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (l88.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (a16.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 152)) ⋆ Eq (sp8.At (s.regs.rsp.toBitVec - 120))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 160)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 160 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 q.toInt).At s.regs.rax.toBitVec)
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 bl.length).toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 c.toInt).At (s.regs.rax.toBitVec + 16)) ⋆ Eq (bl.At q)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8))
      ⋆ Eq (blFmtB.At (label "go_string._" + 526).toBitVec) ⋆ Heap avail ⋆ R)
    (hguard : guard.toNat + 24 < s.regs.rsp.toNat) (hsp : 160 + S ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 4 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hbl : bl.length < 2 ^ 63) (hit : (label "go_itab._errors.errorString_error").toBitVec ≠ 0)
    (hvbl : ValidateBitlistC S) (hfe : FmtErrorfC Heap S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rdi ≠ 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (bl.At q) ⋆ R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hcap hcap63 hpre ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *
  kat hk BitLMarshalSSZTo 0
  kat hk BitLMarshalSSZTo 1
  kat hk BitLMarshalSSZTo 2
  kat hk BitLMarshalSSZTo 3
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLMarshalSSZTo 4
  split
  case isTrue h =>
    exfalso
    rw [cmp_be_false _ _ _ _ (by rw [blk_g _ (by omega)]; simp; omega)] at h
    exact absurd h (by simp)
  simp only [Effects.All]
  kat hk BitLMarshalSSZTo 5
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk BitLMarshalSSZTo 6
  kat hk BitLMarshalSSZTo 7
  kat hk BitLMarshalSSZTo 8
  rw [blk_a, blk_168]
  apply store_step _ _ _ _ _ s2 _ _ (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk BitLMarshalSSZTo 9
  rw [blk_a, blk_160]
  apply store_step _ _ _ _ _ s1 _ _ (by ecancel) (by exact h1)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk BitLMarshalSSZTo 10
  kat hk BitLMarshalSSZTo 11
  kat hk BitLMarshalSSZTo 12
  kat hk BitLMarshalSSZTo 13
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf BitLMarshalSSZTo 24
  kat hk BitLMarshalSSZTo 24
  kat hk BitLMarshalSSZTo 25
  rw [blk_a, blk_104]
  apply store_step _ _ _ _ _ l48 _ _ (by ecancel) (by exact hl48)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  kat hk BitLMarshalSSZTo 26
  rw [blk_a, blk_64]
  apply store_step _ _ _ _ _ l88 _ _ (by ecancel) (by exact hl88)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  kat hk BitLMarshalSSZTo 27
  rw [blk_a, blk_72]
  apply store_step _ _ _ _ _ l80 _ _ (by ecancel) (by exact hl80)
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  kat hk BitLMarshalSSZTo 28
  rw [blk_d0]
  apply store_step _ _ _ _ _ d0 _ _ (by ecancel) (by exact hd0)
  intro m7 H7
  simp only [Width.bytes, Width.bits, show Int.toBytes 4 (BitVec.truncate 32 (4 : BitVec 64)).toInt = [4, 0, 0, 0] by decide] at H7
  kunfold
  kat hk BitLMarshalSSZTo 29
  apply load_step_at _ _ (rax.toBitVec + 8) _ _ (Int.toBytes 8 (BitVec.ofNat 64 bl.length).toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLMarshalSSZTo 30
  apply load_step_at _ _ (rax.toBitVec + 16) _ _ (Int.toBytes 8 c.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLMarshalSSZTo 31
  apply load_step _ _ _ _ (Int.toBytes 8 q.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLMarshalSSZTo 32
  kat hk BitLMarshalSSZTo 33
  rw [blk_call]
  apply store_step _ _ _ _ _ rslot _ _ (by ecancel) (by exact hrs)
  intro m8 H8
  simp only [Width.bytes, Width.bits] at H8
  kunfold
  try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Fk.ofInt_ofBytes_toBytes64] at *  -- ponytail: values already normalized
  refine eventually_trans _ _ _ _ (hvbl _ (Host.addrOf (k + 33 + 1)) bl scratch spl _ ?_ ?_ hsc hspl
    (by dsimp only; rw [blk_sp]; ecancel)) ?_
  · dsimp only; simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
    first | (rw [UInt64.toNat_ofNat]; omega) | (simp [UInt64.toNat_ofNat]; omega) | (show (UInt64.ofNat bl.length).toNat = bl.length; simp; omega)
  · dsimp only; rfl
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrsp2, hr142, hrbp2, -, hinv, stk2, spl2, hstk2, hspl2, Hm2⟩
  dsimp only at hpc2 hrsp2 hr142 hrbp2 hinv Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := d2
  simp only at hrsp2 hr142 hrbp2 hinv Hm2
  subst hrsp2 hr142 hrbp2
  have hrax2 := hinv hv
  rw [blk_sp] at Hm2
  kat hk BitLMarshalSSZTo 34
  intro _
  kat hk BitLMarshalSSZTo 35
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h; exact hit (by rw [← hrax2, h]; rfl)
  simp only [Effects.All]
  kat hk BitLMarshalSSZTo 36
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  kunfold
  rw [blk_b, blk_128]
  apply store_avx_step _ _ _ _ a16 _ _ (by ecancel) (by exact ha16) (by decide)
  intro m9 H9
  kunfold
  rw [lr_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 24)] at H9
  kat hk BitLMarshalSSZTo 37
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h; exact hit (by rw [← hrax2, h]; rfl)
  simp only [Effects.All]
  kat hk BitLMarshalSSZTo 38
  apply load_step_at _ _ ((label "go_itab._errors.errorString_error").toBitVec + 8) _ _ ity _ _ (by rw [hrax2])
    (by ecancel) (by exact hity)
  kunfold
  kat hk BitLMarshalSSZTo 39
  kat hk BitLMarshalSSZTo 40
  rw [blk_b, blk_128]
  apply store_step _ _ _ _ _ ((Int.toBytes 16 (zmms2.get (AvxReg.xmm RegMm.mm15)).toInt).take 8) _ _ (by ecancel)
    (by simp [Int.toBytes_length])
  intro m10 H10
  simp only [Width.bytes, Width.bits] at H10
  kunfold
  kat hk BitLMarshalSSZTo 41
  rw [blk_b, blk_136, show rsp.toBitVec - 24 + 8 = rsp.toBitVec - 16 by bv_omega] at *
  apply store_step _ _ _ _ _ ((Int.toBytes 16 (zmms2.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8) _ _ (by ecancel)
    (by simp [Int.toBytes_length])
  intro m11 H11
  simp only [Width.bytes, Width.bits] at H11
  kunfold
  kat hk BitLMarshalSSZTo 42
  kat hk BitLMarshalSSZTo 43
  kat hk BitLMarshalSSZTo 44
  rw [blk_b, blk_128]
  kat hk BitLMarshalSSZTo 45
  kat hk BitLMarshalSSZTo 46
  kat hk BitLMarshalSSZTo 47
  rw [blk_b, blk_call']
  apply store_step _ _ _ _ _ (Int.toBytes 8 (Host.addrOf (k + 33 + 1)).toBitVec.toInt) _ _ (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m12 H12
  simp only [Width.bytes, Width.bits] at H12
  kunfold
  have hA : Eq ((Int.toBytes 8 (BitVec.ofInt 64 (Int.ofBytes ity)).toInt ++ Int.toBytes 8 rbx2.toBitVec.toInt).At
      (rsp.toBitVec - 24)) = Eq ((Int.toBytes 8 (BitVec.ofInt 64 (Int.ofBytes ity)).toInt).At (rsp.toBitVec - 24))
      ⋆ Eq ((Int.toBytes 8 rbx2.toBitVec.toInt).At (rsp.toBitVec - 16)) :=
    at_app _ _ (by rw [Int.toBytes_length]; bv_omega) (by simp [Int.toBytes_length])
  have hC : Eq ((spl2 ++ sp8).At (rsp.toBitVec - 160 + 8))
      = Eq (spl2.At (rsp.toBitVec - 152)) ⋆ Eq (sp8.At (rsp.toBitVec - 120)) := by
    rw [blk_sp]; exact at_app _ _ (by rw [hspl2]; bv_omega) (by simp [hspl2, hsp8])
  refine eventually_trans _ _ _ _ (hfe _ (Host.addrOf (k + 47 + 1)) avail blFmtB
    (Int.toBytes 8 (BitVec.ofInt 64 (Int.ofBytes ity)).toInt ++ Int.toBytes 8 rbx2.toBitVec.toInt)
    stk2 (spl2 ++ sp8) _ ?f1 ?f2 ?f3 ?f4 hstk2 (by simp [hspl2, hsp8])
    (by dsimp only; rw [hA, hC]; ecancel)) ?_
  case f1 => dsimp only; rfl
  case f2 => dsimp only; decide
  case f3 => dsimp only
  case f4 => dsimp only; simp [Int.toBytes_length]; decide
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrsp3, -, hrax3, stk3, sp3, av3, hstk3, hsp3, hav3, Hm3⟩
  dsimp only at hpc3 hrsp3 hrax3 Hm3
  subst hpc3
  obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,
    zmms3, flags3, mem3⟩ := d3
  simp only at hrsp3 hrax3 Hm3
  subst hrsp3
  kat hk BitLMarshalSSZTo 48
  intro _
  kat hk BitLMarshalSSZTo 49
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h; exact hrax3 (UInt64.toBitVec_inj.mp (by simpa using h))
  simp only [Effects.All]
  klabel hk hf BitLMarshalSSZTo 58
  kat hk BitLMarshalSSZTo 58
  kat hk BitLMarshalSSZTo 59
  intro _
  kat hk BitLMarshalSSZTo 60
  kat hk BitLMarshalSSZTo 61
  kat hk BitLMarshalSSZTo 62
  intro _
  kat hk BitLMarshalSSZTo 63
  kat hk BitLMarshalSSZTo 64
  kat hk BitLMarshalSSZTo 65
  rw [blk_b, blk_pop]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLMarshalSSZTo 66
  rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, sep_true (by ecancel)⟩
  all_goals dsimp only
  all_goals first
    | (simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Fk.ofInt_ofBytes_toBytes64]; done)
    | exact hrax3
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (apply UInt64.toBitVec_inj.mp; simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]; done)

/-- 2049 bits: 257 bytes, the last one 0x02 (delimiter at bit 2049). -/
def bl2049 : List UInt8 := List.replicate 256 0 ++ [2]
/-- 2048 bits: 257 bytes, the last one 0x01 (delimiter at bit 2048). -/
def bl2048 : List UInt8 := List.replicate 256 0 ++ [1]

theorem bl2049_len : bl2049.length = 257 := by
  simp only [bl2049, List.length_append, List.length_replicate, List.length_singleton]

theorem bl2048_len : bl2048.length = 257 := by
  simp only [bl2048, List.length_append, List.length_replicate, List.length_singleton]

/-- **F2 boundary, EthLib side.** 258 bytes (`blOverlong`) and 2049 bits are
not valid Bitlist[2048] encodings; 2048 bits is. With `bl_marshal_reject_main`
and `bl_marshal_main` the encoder rejects the first two and accepts the third
(the old code accepted all three: it counted bytes). -/
theorem bl_marshal_rejects_overlong :
    ¬ blValid Fv1.blOverlong.toList ∧ ¬ blValid bl2049 ∧ blValid bl2048 := by
  have hl : ∀ (l : List UInt8) (x : UInt8), (l ++ [x]).getLastD 0 = x := by intro l x; simp
  have hn : ∀ (x : UInt8), (List.replicate 256 (0 : UInt8) ++ [x]).length = 257 := by
    intro x; simp only [List.length_append, List.length_replicate, List.length_singleton]
  have ho : Fv1.blOverlong.toList.length = 258 := by
    rw [Array.length_toList]; simp only [Fv1.blOverlong, Array.size_append, Array.size_replicate]; rfl
  simp only [blValid, blValid_iff, blArith, bl2049, bl2048, hl, hn, ho]
  refine ⟨?_, ?_, ?_⟩
  · intro ⟨_, h, _⟩; omega
  · intro ⟨_, _, _, h⟩; exact absurd (h trivial) (by decide)
  · exact ⟨List.append_ne_nil_of_right_ne_nil _ (by simp), by omega, by decide, fun _ => trivial⟩

set_option maxHeartbeats 4000000 in
/-- **Finding F2, fixed (machine).** On `c.B = blOverlong` (258 bytes, 2056
bits) the marshal returns a nil slice and a non-nil error. EthLib rejects
`offset 4 ‖ blOverlong` too (`bl_spec_rejects_overlong`). -/
theorem bl_marshal_overlong_rejected (k : Nat) (hk : BitLMarshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh BitLMarshalSSZTo k)
    (pre d0 : List UInt8) (hd0 : d0.length = 4) (q c : BitVec 64)
    (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l48 l80 l88 a16 spl sp8 rslot ity : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8)
    (hl48 : l48.length = 8) (hl80 : l80.length = 8) (hl88 : l88.length = 8) (ha16 : a16.length = 16)
    (hspl : spl.length = 32) (hsp8 : sp8.length = 8) (hrs : rslot.length = 8) (hity : ity.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (l80.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (l88.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (a16.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 152)) ⋆ Eq (sp8.At (s.regs.rsp.toBitVec - 120))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 160)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 160 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 q.toInt).At s.regs.rax.toBitVec)
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 Fv1.blOverlong.toList.length).toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 c.toInt).At (s.regs.rax.toBitVec + 16)) ⋆ Eq (Fv1.blOverlong.toList.At q)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8))
      ⋆ Eq (blFmtB.At (label "go_string._" + 526).toBitVec) ⋆ Heap avail ⋆ R)
    (hguard : guard.toNat + 24 < s.regs.rsp.toNat) (hsp : 160 + S ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 4 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hit : (label "go_itab._errors.errorString_error").toBitVec ≠ 0)
    (hvbl : ValidateBitlistC S) (hfe : FmtErrorfC Heap S) :
    (∃ e, EthLib.Serialization.Ssz.deserialize Fv1.blDesc (#[4, 0, 0, 0] ++ Fv1.blOverlong) = .error e) ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rdi ≠ 0 ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (Fv1.blOverlong.toList.At q) ⋆ R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ :=
  ⟨Fv1.bl_spec_rejects_overlong,
   bl_marshal_reject_main k hk hf Fv1.blOverlong.toList pre d0 bl_marshal_rejects_overlong.1 hd0 q c s ra guard hpre
    fp s1 s2 l48 l80 l88 a16 spl sp8 rslot ity hfp h1 h2 hl48 hl80 hl88 ha16 hspl hsp8 hrs hity R S scratch hsc
    Heap avail h_mem hguard hsp hcap hcap63
    (by rw [Array.length_toList]; simp only [Fv1.blOverlong, Array.size_append, Array.size_replicate]; decide)
    hit hvbl hfe⟩
