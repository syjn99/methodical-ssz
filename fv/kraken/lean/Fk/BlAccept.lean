import Fk.BlMarshal
import Fk.LcReject
import Fk.Witness

/-!
# BitL.UnmarshalSSZ, accept path, on Kraken main

The key check is behind a contract. `ssz.ValidateBitlist` uses `bsr`
(`bits.Len8`), which Kraken does not parse (REPORT-1b, Kraken request list).
`ValidateBitlistC`: the call returns rax = 0 exactly when EthLib's
`unpackDelimited (some 2048)` accepts the bytes (non-empty, last byte
non-zero, at most 2048 bits before the delimiter). This contract is the
whole bitlist rule. The machine proof covers only what the decoder does
around it: length and offset checks, the call, `append([]byte{}, buf[4:]...)`
(`runtime.growslice` + `runtime.memmove` contracts), the receiver header.

`bl_accept_main`: with `len(buf) = 4 + n` (n ≥ 1), offset 4, and
`unpackDelimited (some 2048) tl` = ok (tl the n bytes after the offset), the
function returns a nil error (rax = 0) with `c.B = (p, n, c)`, the n bytes
at p.
Premises the Go caller provides: separated receiver, input and stack chunks,
the stack guard below rsp − 120, the write barrier off, the three contracts.
-/

open Fk Fk.Code Fv1 EthLib.Serialization.Ssz
variable [Host]

/-- The bitlist rule (EthLib): `unpackDelimited` with the limit 2048 accepts. -/
def blValid (tl : List UInt8) : Prop := ∃ bits, unpackDelimited (some 2048) tl.toArray = .ok bits

/-- `ssz.ValidateBitlist(buf []byte, bitLimit uint64) error` (rax = ptr,
rbx = len, rcx = cap, rdi = limit): returns to the return address with
rsp + 8, the frame `F` and the bytes unchanged, and rax = 0 (nil error) exactly
when `blValid` holds. The error's second word (rbx) is not specified. -/
def ValidateBitlistC (S : Nat) : Prop :=
  ∀ (st : MachineData) (ret : Int64) (buf stk : List UInt8) (F : DataMem → Prop),
    st.regs.rbx.toNat = buf.length → st.regs.rdi = 2048 → stk.length = S →
    (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
      ⋆ Eq (stk.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (buf.At st.regs.rax.toBitVec) ⋆ F) st.dmem →
    Eventually (step1 Host.exe)
      (fun st' => st'.pc = ret ∧ st'.data.regs.rsp = st.regs.rsp + 8 ∧ (st'.data.regs.rax = 0 ↔ blValid buf) ∧
        ∃ stk' : List UInt8, stk'.length = S ∧
        (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
          ⋆ Eq (stk'.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (buf.At st.regs.rax.toBitVec) ⋆ F) st'.data.dmem)
      ⟨st, label "ssz.ValidateBitlist"⟩

theorem bla_rbx4 (x : BitVec 64) : x + 4 * 1#64 = x + 4 := by rw [BitVec.mul_one]

theorem bla_slot (x : BitVec 64) : x - 8#64 - 112 - 8#64 = x - 128 := by bv_omega
theorem bla_slot' (x : BitVec 64) : ({ toBitVec := x - 128 } + 8 : UInt64).toBitVec - 8#64 = x - 128 := by
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
theorem bla_g (x o : BitVec 64) : ({ toBitVec := x - 128 } + 8 : UInt64).toBitVec + o = x - 120 + o := by
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
theorem bla_pop (x : BitVec 64) : 112 + ({ toBitVec := x - 128 } + 8 : UInt64).toBitVec = x - 8 := by
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem bl_accept_main (k : Nat) (hk : BitLUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh BitLUnmarshalSSZ k)
    (tl : List UInt8) (hn1 : 1 ≤ tl.length) (hval : blValid tl)
    (s : MachineData) (ra guard : UInt64)
    (fp s8 s16 s24 l32 l40 l48 l56 l64 l72 l80 rslot cP cL cC : List UInt8)
    (hfp : fp.length = 8) (h8 : s8.length = 8) (h16 : s16.length = 8) (h24 : s24.length = 8)
    (hl32 : l32.length = 8) (hl40 : l40.length = 8) (hl48 : l48.length = 8) (hl56 : l56.length = 8)
    (hl64 : l64.length = 8) (hl72 : l72.length = 8) (hl80 : l80.length = 8) (hrs : rslot.length = 8)
    (hcP : cP.length = 8) (hcL : cL.length = 8) (hcC : cC.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s8.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s16.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s24.At (s.regs.rsp.toBitVec + 24))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32)) ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (l56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (l64.At (s.regs.rsp.toBitVec - 64)) ⋆ Eq (l72.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (l80.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 128)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 128 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16)) ⋆ Heap avail
      ⋆ Eq ([4, 0, 0, 0].At s.regs.rbx.toBitVec) ⋆ Eq (tl.At (s.regs.rbx.toBitVec + 4))
      ⋆ Eq (cP.At s.regs.rax.toBitVec) ⋆ Eq (cL.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 128 ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rcx.toNat = 4 + tl.length) (hcap : s.regs.rcx.toNat ≤ s.regs.rdi.toNat)
    (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hvb : ValidateBitlistC S) (hgs : GrowsliceC Heap (label "type__" + 48736).toBitVec 1 S) (hmm : MemmoveC S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧
        ∃ (p : BitVec 64) (c : Nat) (rest : List UInt8), tl.length + rest.length = c ∧
          (Eq ((Int.toBytes 8 p.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 tl.length).toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 c).toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (tl.At p) ⋆ Eq (rest.At (p + BitVec.ofNat 64 tl.length))
          ⋆ Eq (tl.At (s.regs.rbx.toBitVec + 4)) ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hlen hcap hcap63 ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *
  kat hk BitLUnmarshalSSZ 0
  kat hk BitLUnmarshalSSZ 1
  kat hk BitLUnmarshalSSZ 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLUnmarshalSSZ 3
  split
  · rename_i h; exfalso
    simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk BitLUnmarshalSSZ 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk BitLUnmarshalSSZ 5
  kat hk BitLUnmarshalSSZ 6
  kat hk BitLUnmarshalSSZ 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s16 _ _ (by bv_omega) (by ecancel) (by exact h16)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk BitLUnmarshalSSZ 8
  kat hk BitLUnmarshalSSZ 9
  kat hk BitLUnmarshalSSZ 10
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
  simp only [Effects.All]
  kat hk BitLUnmarshalSSZ 11
  apply load_step_at _ _ rbx.toBitVec _ _ [4, 0, 0, 0] _ _ (by bv_omega) (by ecancel) (by simp)
  simp only [show Int.ofBytes [4, 0, 0, 0] = 4 by simp [Int.ofBytes]]
  kunfold
  kat hk BitLUnmarshalSSZ 12
  kat hk BitLUnmarshalSSZ 13
  kat hk BitLUnmarshalSSZ 14
  kat hk BitLUnmarshalSSZ 15
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk BitLUnmarshalSSZ 16
  apply store_step_at _ _ (rsp.toBitVec + 8) _ _ _ s8 _ _ (by kaddr) (by ecancel) (by exact h8)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk BitLUnmarshalSSZ 17
  apply store_step_at _ _ (rsp.toBitVec + 24) _ _ _ s24 _ _ (by kaddr) (by ecancel) (by exact h24)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  kat hk BitLUnmarshalSSZ 18
  kat hk BitLUnmarshalSSZ 19
  kat hk BitLUnmarshalSSZ 20
  kat hk BitLUnmarshalSSZ 21
  kshl64 63
  kat hk BitLUnmarshalSSZ 22
  intro _
  rw [lc_rdx4 _ (by simp; omega) (by simp; omega)]
  kat hk BitLUnmarshalSSZ 23
  rw [bla_rbx4]
  kat hk BitLUnmarshalSSZ 24
  apply store_step_at _ _ (rsp.toBitVec - 48) _ _ _ l48 _ _ (by kaddr) (by ecancel) (by exact hl48)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  kat hk BitLUnmarshalSSZ 25
  kat hk BitLUnmarshalSSZ 26
  apply store_step_at _ _ (rsp.toBitVec - 80) _ _ _ l80 _ _ (by kaddr) (by ecancel) (by exact hl80)
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  kat hk BitLUnmarshalSSZ 27
  kat hk BitLUnmarshalSSZ 28
  kat hk BitLUnmarshalSSZ 29
  kat hk BitLUnmarshalSSZ 30
  apply store_step_at _ _ (rsp.toBitVec - 128) _ _ _ rslot _ _ (bla_slot _) (by ecancel) (by exact hrs)
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  rw [bla_slot] at *
  have hn4 : (-4 + rcx.toBitVec).toNat = tl.length := by
    rw [BitVec.add_comm, ← BitVec.sub_eq_add_neg, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]
    simp; omega
  refine eventually_trans _ _ _ _ (hvb _ (Host.addrOf (k + 30 + 1)) tl scratch _ hn4
    (by apply UInt64.toBitVec_inj.mp; apply BitVec.eq_of_toNat_eq; simp) hsc (by dsimp only; ecancel)) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hrax1, stk1, hstk1, Hm1⟩
  dsimp only at hpc1 hrsp1 hrax1 Hm1
  subst hpc1
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩,
    zmms1, flags1, mem1⟩ := d1
  simp only at hrsp1 hrax1 Hm1
  subst hrsp1
  have hr0 : rax1 = 0 := hrax1.mpr hval
  subst hr0
  kat hk BitLUnmarshalSSZ 31
  kat hk BitLUnmarshalSSZ 32
  intro _
  kat hk BitLUnmarshalSSZ 33
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf BitLUnmarshalSSZ 62
  kat hk BitLUnmarshalSSZ 62
  kat hk BitLUnmarshalSSZ 63
  rw [bla_g, show rsp.toBitVec - 120 + 80 = rsp.toBitVec - 40 by bv_omega]
  apply store_step _ _ _ _ _ l40 _ _ (by ecancel) (by exact hl40)
  intro m8 H8
  simp only [Width.bytes, Width.bits] at H8
  kunfold
  kat hk BitLUnmarshalSSZ 64
  rw [bla_g, show rsp.toBitVec - 120 + 48 = rsp.toBitVec - 72 by bv_omega]
  apply store_step _ _ _ _ _ l72 _ _ (by ecancel) (by exact hl72)
  intro m9 H9
  simp only [Width.bytes, Width.bits] at H9
  kunfold
  kat hk BitLUnmarshalSSZ 65
  rw [bla_g, show rsp.toBitVec - 120 + 144 = rsp.toBitVec + 24 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rcx.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLUnmarshalSSZ 66
  kat hk BitLUnmarshalSSZ 67
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at h
    have := congrArg BitVec.toNat h; simp [BitVec.toNat_add] at this; omega
  simp only [Effects.All]
  klabel hk hf BitLUnmarshalSSZ 72
  kat hk BitLUnmarshalSSZ 72
  kat hk BitLUnmarshalSSZ 73
  kat hk BitLUnmarshalSSZ 74
  rw [bla_g, show rsp.toBitVec - 120 + 40 = rsp.toBitVec - 80 by bv_omega]
  generalize hnv : (-4 + rcx.toBitVec) = nV at *
  apply load_step _ _ _ _ (Int.toBytes 8 nV.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk BitLUnmarshalSSZ 75
  intro _
  kat hk BitLUnmarshalSSZ 76
  kat hk BitLUnmarshalSSZ 77
  kat hk BitLUnmarshalSSZ 78
  apply store_step_at _ _ (rsp.toBitVec - 128) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 30 + 1)).toBitVec.toInt) _ _
    (bla_slot' _) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m10 H10
  simp only [Width.bytes, Width.bits] at H10
  kunfold
  rw [bla_slot'] at *
  refine eventually_trans _ _ _ _ (hgs _ (Host.addrOf (k + 78 + 1)) [] stk1 avail _ rfl (Nat.le_refl _)
    (by simp) hstk1 (by dsimp only; rw [Fk.Witness.nil_At_emp]; simp only [Std.ExtHashMap.sep_emp]; ecancel)) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrsp2, hrbp2, hrbx2, hcap2, hcap63', stk2, tail, av2, hstk2, htl, Hm2⟩
  dsimp only at hpc2 hrsp2 hrbp2 hrbx2 hcap2 hcap63' htl Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := d2
  simp only at hrsp2 hrbp2 hrbx2 hcap2 hcap63' Hm2
  subst hrsp2 hrbp2 hrbx2
  rw [Fk.Witness.nil_At_emp, List.nil_append] at Hm2
  simp only [Std.ExtHashMap.sep_emp, List.length_nil, Nat.zero_add, Nat.one_mul] at Hm2 htl
  have hnv : nV.toNat = tl.length := hn4
  have hc2 : tl.length ≤ rcx2.toNat := by
    have := hcap2; simp only [UInt64.toNat, ← UInt64.toNat_toBitVec] at this ⊢; omega
  have htk : (tail.take tl.length).length = tl.length := by simp; omega
  have hsplit : Eq (tail.At rax2.toBitVec) = Eq ((tail.take tl.length).At rax2.toBitVec)
      ⋆ Eq ((tail.drop tl.length).At (rax2.toBitVec + BitVec.ofNat 64 tl.length)) := by
    conv => lhs; rw [← List.take_append_drop tl.length tail]
    rw [Mem.At_append_sep _ _ _ (by simp; omega), htk]
  rw [hsplit] at Hm2
  kat hk BitLUnmarshalSSZ 79
  kat hk BitLUnmarshalSSZ 80
  kat hk BitLUnmarshalSSZ 81
  kat hk BitLUnmarshalSSZ 82
  kat hk BitLUnmarshalSSZ 83
  rw [bla_g, show rsp.toBitVec - 120 + 88 = rsp.toBitVec - 32 by bv_omega]
  apply store_step _ _ _ _ _ l32 _ _ (by ecancel) (by exact hl32)
  intro m11 H11
  simp only [Width.bytes, Width.bits] at H11
  kunfold
  kat hk BitLUnmarshalSSZ 84
  rw [bla_g, show rsp.toBitVec - 120 + 64 = rsp.toBitVec - 56 by bv_omega]
  apply store_step _ _ _ _ _ l56 _ _ (by ecancel) (by exact hl56)
  intro m12 H12
  simp only [Width.bytes, Width.bits] at H12
  kunfold
  kat hk BitLUnmarshalSSZ 85
  rw [bla_g, show rsp.toBitVec - 120 + 56 = rsp.toBitVec - 64 by bv_omega]
  apply store_step _ _ _ _ _ l64 _ _ (by ecancel) (by exact hl64)
  intro m13 H13
  simp only [Width.bytes, Width.bits] at H13
  kunfold
  kat hk BitLUnmarshalSSZ 86
  kat hk BitLUnmarshalSSZ 87
  rw [bla_g, show rsp.toBitVec - 120 + 72 = rsp.toBitVec - 48 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 (rbx.toBitVec + 4).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk BitLUnmarshalSSZ 88
  rw [bla_g, show rsp.toBitVec - 120 + 40 = rsp.toBitVec - 80 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 nV.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk BitLUnmarshalSSZ 89
  kat hk BitLUnmarshalSSZ 90
  apply store_step_at _ _ (rsp.toBitVec - 128) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 78 + 1)).toBitVec.toInt) _ _
    (bla_slot' _) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m14 H14
  simp only [Width.bytes, Width.bits] at H14
  kunfold
  rw [bla_slot'] at *
  refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (k + 90 + 1)) tl (tail.take tl.length) stk2 _
    (by simpa using hnv) htk hstk2 (by dsimp only; ecancel)) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrsp3, stk3, hstk3, Hm3⟩
  dsimp only at hpc3 hrsp3 Hm3
  subst hpc3
  obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,
    zmms3, flags3, mem3⟩ := d3
  simp only at hrsp3 Hm3
  subst hrsp3
  kat hk BitLUnmarshalSSZ 91
  rw [bla_g, show rsp.toBitVec - 120 + 64 = rsp.toBitVec - 56 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 nV.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk BitLUnmarshalSSZ 92
  rw [bla_g, show rsp.toBitVec - 120 + 128 = rsp.toBitVec + 8 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk BitLUnmarshalSSZ 93
  apply store_step_at _ _ (rax.toBitVec + 8) _ _ _ cL _ _ (by kaddr) (by ecancel) (by exact hcL)
  intro m15 H15
  simp only [Width.bytes, Width.bits] at H15
  kunfold
  kat hk BitLUnmarshalSSZ 94
  rw [bla_g, show rsp.toBitVec - 120 + 56 = rsp.toBitVec - 64 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rcx2.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk BitLUnmarshalSSZ 95
  apply store_step_at _ _ (rax.toBitVec + 16) _ _ _ cC _ _ (by kaddr) (by ecancel) (by exact hcC)
  intro m16 H16
  simp only [Width.bytes, Width.bits] at H16
  kunfold
  kat hk BitLUnmarshalSSZ 96
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk BitLUnmarshalSSZ 97
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk BitLUnmarshalSSZ 98
  rw [bla_g, show rsp.toBitVec - 120 + 88 = rsp.toBitVec - 32 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rax2.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk BitLUnmarshalSSZ 99
  klabel hk hf BitLUnmarshalSSZ 106
  kat hk BitLUnmarshalSSZ 106
  kat hk BitLUnmarshalSSZ 107
  apply store_step_at _ _ rax.toBitVec _ _ _ cP _ _ (by kaddr) (by ecancel) (by exact hcP)
  intro m17 H17
  simp only [Width.bytes, Width.bits] at H17
  kunfold
  kat hk BitLUnmarshalSSZ 108
  rw [bla_g, show rsp.toBitVec - 120 + 48 = rsp.toBitVec - 72 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 (0#64).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk BitLUnmarshalSSZ 109
  rw [bla_g, show rsp.toBitVec - 120 + 80 = rsp.toBitVec - 40 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rbx1.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLUnmarshalSSZ 110
  kat hk BitLUnmarshalSSZ 111
  rw [bla_pop]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLUnmarshalSSZ 112
  rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  have hnvE : nV = BitVec.ofNat 64 tl.length := BitVec.eq_of_toNat_eq (by simp; omega)
  have hcE : rcx2.toBitVec = BitVec.ofNat 64 rcx2.toNat := by simp
  rw [hnvE] at H17
  rw [hcE] at H17
  refine ⟨trivial, rfl, ?_, trivial, rax2.toBitVec, rcx2.toNat, tail.drop tl.length, by simp; omega, ?_⟩
  · apply UInt64.toBitVec_inj.mp; simp
  · exact sep_true (P := Eq ((Int.toBytes 8 rax2.toBitVec.toInt).At rax.toBitVec)
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 tl.length).toInt).At (rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 rcx2.toNat).toInt).At (rax.toBitVec + 16))
      ⋆ Eq (tl.At rax2.toBitVec) ⋆ Eq ((tail.drop tl.length).At (rax2.toBitVec + BitVec.ofNat 64 tl.length))
      ⋆ Eq (tl.At (rbx.toBitVec + 4))) (by ecancel)
