import Fk.CpMarshal
import Fv1.SpecBitList

/-!
# BitL.MarshalSSZTo, fast path, on Kraken main

    type BitL struct { B bitfield.Bitlist `ssz-max:"2048"` }

With `len(c.B) = n ≤ 2048` and `cap(dst) ≥ len(dst) + 4 + n`, MarshalSSZTo
writes the offset 4 (`ssz.WriteOffset`, inlined: a 4-byte store) at
`dst[len:]`, copies the n bytes of `c.B` with `runtime.memmove` (contract
`MemmoveC`) at `dst[len+4:]`, and returns `(dst[:len+4+n], nil)`.
The only check is `len(c.B) > 2048`: it counts **bytes**, while the SSZ limit
is 2048 **bits** (at most 257 bytes with the delimiter). Finding F2
(`bl_marshal_overlong`): the code encodes a 258-byte bitlist that EthLib (and
the same type's decoder, through `ssz.ValidateBitlist`) rejects.
Premises the Go caller provides: receiver, `c.B` bytes, `dst` and stack
chunks separated; the stack guard; `cap < 2^63` (Go slice bound).
-/

open Fk Fk.Code
variable [Host]

theorem blm_addr (x y : BitVec 64) : y + 4 + x * 1#64 + -4 = x + y := by
  rw [BitVec.mul_one, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm 4, BitVec.add_assoc]
  rw [show (-4 : BitVec 64) + 4 = 0 by decide, Fk.add_lit_zero, BitVec.add_comm]

/-- `cmp $0x800, a; jg` is not taken when `a ≤ 2048`. -/
theorem jg2048_false (a : BitVec 64) (af : Bool) (h : a.toNat ≤ 2048) :
    CondCode.g.interp (StatusFlags.from_result (a - 2048)
      { cf := BitVec.unsigned (a - 2048) != a.unsigned - BitVec.unsigned (2048 : BitVec 64), af := af,
        of := BitVec.toInt (a - 2048) != a.toInt - BitVec.toInt (2048 : BitVec 64) }) = false := by
  have ta : a.toInt = a.toNat := BitVec.toInt_eq_toNat_of_lt (by omega)
  have t2 : BitVec.toInt (2048 : BitVec 64) = 2048 := by decide
  by_cases h0 : a.toNat = 2048
  · have : a = 2048 := BitVec.eq_of_toNat_eq h0
    subst this; cases af <;> decide
  · have hs : (a - 2048).toInt = (a.toNat : Int) - 2048 := by
      rw [BitVec.toInt_sub, ta, t2]; apply Int.bmod_eq_of_le <;> omega
    have hm : (a - 2048).msb = true := by
      rw [BitVec.msb_eq_toInt, hs]; simp; omega
    simp [CondCode.interp, StatusFlags.from_result, ta, hs]
    intro _
    rw [show (a - 2048#64) = a - 2048 from rfl, hm, Int.bmod_eq_of_le (by omega) (by omega)]; simp

theorem blm_dst (x y : BitVec 64) : x + (y + 4) * 1#64 = x + y + 4 := by
  rw [BitVec.mul_one, BitVec.add_assoc]

theorem blm_slot (x : BitVec 64) : x - 8#64 - 96 - 8#64 = x - 112 := by bv_omega
theorem blm_g (x o : BitVec 64) : ({ toBitVec := x - 112 } + 8 : UInt64).toBitVec + o = x - 104 + o := by
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
theorem blm_pop (x : BitVec 64) : 96 + ({ toBitVec := x - 112 } + 8 : UInt64).toBitVec = x - 8 := by
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem bl_marshal_main (k : Nat) (hk : BitLMarshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh BitLMarshalSSZTo k)
    (bl pre d0 d1 : List UInt8) (hn : bl.length ≤ 2048)
    (hd0 : d0.length = 4) (hd1 : d1.length = bl.length) (q : BitVec 64)
    (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s2 l16 l24 l32 rslot : List UInt8)
    (hfp : fp.length = 8) (h2 : s2.length = 8) (hl16 : l16.length = 8) (hl24 : l24.length = 8)
    (hl32 : l32.length = 8) (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16)) ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 112)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 112 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 q.toInt).At s.regs.rax.toBitVec)
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 bl.length).toInt).At (s.regs.rax.toBitVec + 8)) ⋆ Eq (bl.At q)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 4)) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 112 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 4 + bl.length ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hmm : MemmoveC S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 4 + bl.length ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq ([4, 0, 0, 0].At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (bl.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 4)) ⋆ Eq (bl.At q) ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hcap hcap63 hpre ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *
  kat hk BitLMarshalSSZTo 0
  kat hk BitLMarshalSSZTo 1
  kat hk BitLMarshalSSZTo 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLMarshalSSZTo 3
  split
  · rename_i h; exfalso
    simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk BitLMarshalSSZTo 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk BitLMarshalSSZTo 5
  kat hk BitLMarshalSSZTo 6
  kat hk BitLMarshalSSZTo 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by bv_omega) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk BitLMarshalSSZTo 8
  kat hk BitLMarshalSSZTo 9
  kat hk BitLMarshalSSZTo 10
  kat hk BitLMarshalSSZTo 11
  kat hk BitLMarshalSSZTo 12
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf BitLMarshalSSZTo 25
  kat hk BitLMarshalSSZTo 25
  kat hk BitLMarshalSSZTo 26
  rw [blm_addr]
  apply store_step _ _ _ _ _ d0 _ _ (by ecancel) (by exact hd0)
  intro m3 H3
  simp only [Width.bytes, Width.bits, show Int.toBytes 4 (BitVec.truncate 32 (4 : BitVec 64)).toInt = [4, 0, 0, 0] by decide] at H3
  kunfold
  kat hk BitLMarshalSSZTo 27
  apply load_step_at _ _ (rax.toBitVec + 8) _ _ (Int.toBytes 8 (BitVec.ofNat 64 bl.length).toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk BitLMarshalSSZTo 28
  apply load_step _ _ _ _ (Int.toBytes 8 q.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLMarshalSSZTo 29
  kat hk BitLMarshalSSZTo 30
  rw [jg2048_false _ _ (by simp; omega)]
  simp only [Bool.false_eq_true, ↓reduceIte, Effects.All]
  kat hk BitLMarshalSSZTo 31
  kat hk BitLMarshalSSZTo 32
  kat hk BitLMarshalSSZTo 33
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf BitLMarshalSSZTo 50
  kat hk BitLMarshalSSZTo 50
  kat hk BitLMarshalSSZTo 51
  apply store_step_at _ _ (rsp.toBitVec - 16) _ _ _ l16 _ _ (by bv_omega) (by ecancel) (by exact hl16)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  kat hk BitLMarshalSSZTo 52
  apply store_step_at _ _ (rsp.toBitVec - 24) _ _ _ l24 _ _ (by bv_omega) (by ecancel) (by exact hl24)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  kat hk BitLMarshalSSZTo 53
  apply store_step_at _ _ (rsp.toBitVec - 32) _ _ _ l32 _ _ (by bv_omega) (by ecancel) (by exact hl32)
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  kat hk BitLMarshalSSZTo 54
  kat hk BitLMarshalSSZTo 55
  kat hk BitLMarshalSSZTo 56
  apply store_step_at _ _ (rsp.toBitVec - 112) _ _ _ rslot _ _ (blm_slot _) (by ecancel) (by exact hrs)
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  rw [blm_slot] at *
  rw [blm_dst] at *
  refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (k + 56 + 1)) bl d1 scratch _
    (by show (BitVec.ofNat 64 bl.length).toNat = _; simp; omega) hd1 hsc (by dsimp only; ecancel)) ?_
  rintro ⟨e1, pc1⟩ ⟨hpc1, hrsp1, stk1, hstk1, Hm1⟩
  dsimp only at hpc1 hrsp1 Hm1
  subst hpc1
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩,
    zmms1, flags1, mem1⟩ := e1
  simp only at hrsp1 Hm1
  subst hrsp1
  kat hk BitLMarshalSSZTo 57
  rw [blm_g, show rsp.toBitVec - 104 + 88 = rsp.toBitVec - 16 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLMarshalSSZTo 58
  rw [blm_g, show rsp.toBitVec - 104 + 80 = rsp.toBitVec - 24 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 (rcx.toBitVec + 4 + BitVec.ofNat 64 bl.length * 1#64).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLMarshalSSZTo 59
  rw [blm_g, show rsp.toBitVec - 104 + 72 = rsp.toBitVec - 32 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rdi.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLMarshalSSZTo 60
  intro _
  kat hk BitLMarshalSSZTo 61
  intro _
  kat hk BitLMarshalSSZTo 62
  kat hk BitLMarshalSSZTo 63
  rw [blm_pop]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLMarshalSSZTo 64
  rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left 7
  · exact sep_true (P := Eq (pre.At rbx.toBitVec) ⋆ Eq ([4, 0, 0, 0].At (rbx.toBitVec + rcx.toBitVec))
      ⋆ Eq (bl.At (rbx.toBitVec + rcx.toBitVec + 4)) ⋆ Eq (bl.At q)) (by ecancel)
  all_goals first
    | trivial | rfl
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (show (rcx.toBitVec + 4 + BitVec.ofNat 64 bl.length * 1#64).toNat = _
       simp [BitVec.toNat_add]; omega)


open Fv1 EthLib.Serialization.Ssz in
/-- **Finding F2.** For `c.B = blOverlong` (258 bytes, 2056 bits), the marshal
fast path returns success (nil error, `rdi = rsi = 0`) and writes
`offset 4 ‖ c.B`, which EthLib rejects: the `len(c.B) > 2048` check counts
bytes, the SSZ limit 2048 counts bits. (The same type's decoder rejects the
bytes too, through `ssz.ValidateBitlist`: `maxBytes = 2048 / 8 + 1 = 257`.) -/
theorem bl_marshal_overlong (k : Nat) (hk : BitLMarshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh BitLMarshalSSZTo k)
    (pre d0 d1 : List UInt8) (hd0 : d0.length = 4) (hd1 : d1.length = 258) (q : BitVec 64)
    (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s2 l16 l24 l32 rslot : List UInt8)
    (hfp : fp.length = 8) (h2 : s2.length = 8) (hl16 : l16.length = 8) (hl24 : l24.length = 8)
    (hl32 : l32.length = 8) (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16)) ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 112)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 112 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 q.toInt).At s.regs.rax.toBitVec)
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 258).toInt).At (s.regs.rax.toBitVec + 8)) ⋆ Eq (blOverlong.toList.At q)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 4)) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 112 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 4 + 258 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hmm : MemmoveC S) :
    (∃ e, deserialize blDesc (#[4, 0, 0, 0] ++ blOverlong) = .error e) ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 4 + 258 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq ([4, 0, 0, 0].At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (blOverlong.toList.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 4)) ⋆ Eq (blOverlong.toList.At q)
          ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  have hlen : blOverlong.toList.length = 258 := by
    rw [Array.length_toList]; simp only [blOverlong, Array.size_append, Array.size_replicate]; rfl
  refine ⟨bl_spec_rejects_overlong, ?_⟩
  have := bl_marshal_main k hk hf blOverlong.toList pre d0 d1 (by omega) hd0 (by omega) q s ra guard hpre
    fp s2 l16 l24 l32 rslot hfp h2 hl16 hl24 hl32 hrs R S scratch hsc (by rw [hlen]; exact h_mem) hguard hsp
    (by omega) hcap63 hmm
  rw [hlen] at this
  exact this
