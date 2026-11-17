import Codec.SegmentAddress
import Prysm.CommitteeIndex.EncodeFastPath
import Prysm.ElfData.PrysmTarget

/-!
# Prysm `(*primitives.CommitteeIndex).MarshalSSZTo`, growslice path, Go 1.26.10 machine code

`Encode.grow_first_site` covers the case `cap(dst) < len(dst) + 8`.
Then the only capacity test (directives 16–17) fails.
The inlined `append(dst, value bytes...)` then calls `runtime.growslice` (directives 18–24).
The arguments are `old = dst.ptr`, `newLen = len + 8`, `oldCap = cap`, `num = 8`, `et = uint8`.
The contract is `GrowsliceContract Heap typeUint8_addr 1 S`, the form that the Checkpoint encoder uses.
The type word is `type__+387072`, as in the Checkpoint encoder.
The code continues at `L_61` (directive 29) on the new block.
It stores the 8 value bytes at `new[len..len+8]` and returns `(new, len + 8, newCap, nil)`.
The new block holds the copied prefix, and the old block is unchanged.
The rest of the new block (`newCap − len − 8` bytes) is named.
Only this path writes the rcx spill slot at rsp + 24 (directive 18).
The call pushes its return address at rsp − 88.
The 40-byte growslice spill area is at rsp − 80.
Label freshness is not a premise, because this path has no jump to a label.
-/

open Machine Runtime Prysm.CommitteeIndex.Code

namespace Prysm.CommitteeIndex

theorem Encode.grow_first_site_split (np len : BitVec 64) (pre tail : List UInt8) (hpre : pre.length = len.toNat)
    (ht : 8 ≤ tail.length) (hb : pre.length + tail.length < 2 ^ 64) :
    Eq ((pre ++ tail).At np) = Eq (pre.At np) ⋆ Eq ((tail.take 8).At (np + len))
      ⋆ Eq ((tail.drop 8).At (np + len + 8)) := by
  rw [at_app pre tail (b := np + len) (by rw [hpre, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega)]
  have e1 : Eq (tail.At (np + len)) = Eq ((tail.take 8).At (np + len)) ⋆ Eq ((tail.drop 8).At (np + len + 8)) := by
    conv => lhs; rw [← List.take_append_drop 8 tail]
    exact at_app _ _ (by rw [List.length_take, Nat.min_eq_left (by omega)]; rfl) (by simp; omega)
  rw [e1]
  simp only [Std.ExtHashMap.sep_assoc]

theorem Encode.grow_first_site_add8_toNat (x : UInt64) (h : x.toNat + 8 < 2 ^ 64) :
    ({ toBitVec := x.toBitVec + 8 } : UInt64).toNat = x.toNat + 8 := by
  show (x.toBitVec + 8).toNat = x.toNat + 8
  simp [BitVec.toNat_add]; omega

theorem Encode.grow_first_site_word_toNat (x : UInt64) : ({ toBitVec := x.toBitVec } : UInt64).toNat = x.toNat := rfl

theorem Encode.grow_first_site_zero_extend8 :
    ({ toBitVec := BitVec.zeroExtend 64 (BitVec.truncate 32 (8 : BitVec 64)) } : UInt64).toNat = 8 := by
  decide

theorem Encode.grow_first_site_slot (x : BitVec 64) : x - 8#64 - 72 - 8#64 = x - 88 := by bv_omega

theorem Encode.grow_first_site_ret (x : BitVec 64) :
    ({ toBitVec := x - 88 } + 8 : UInt64) = { toBitVec := x - 80 } := by
  apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega

variable [Host]

theorem Encode.grow_first_site (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k)
    (e8 pre : List UInt8) (he8 : e8.length = 8)
    (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s2 s3 t28 t18 rslot spl : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8) (h3 : s3.length = 8)
    (ht28 : t28.length = 16) (ht18 : t18.length = 16) (hrs : rslot.length = 8) (hspl : spl.length = 40)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (s3.At (s.regs.rsp.toBitVec + 24))
      ⋆ Eq (t28.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (t18.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (e8.At s.regs.rax.toBitVec)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Heap avail ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat)
    (hlc : s.regs.rcx.toNat ≤ s.regs.rdi.toNat) (hgrow : s.regs.rdi.toNat < s.regs.rcx.toNat + 8)
    (hbud : 2 * nextSliceCap (s.regs.rcx.toNat + 8) s.regs.rdi.toNat + 8192 ≤ avail) (hmax : avail ≤ maxAlloc)
    (hgs : GrowsliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 8
        ∧ nextSliceCap (s.regs.rcx.toNat + 8) s.regs.rdi.toNat ≤ st.data.regs.rcx.toNat
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (t u scr spl' rest : List UInt8) (av' : Nat), t.length = 8 ∧ u.length = 16 ∧ scr.length = S
          ∧ spl'.length = 40 ∧ s.regs.rcx.toNat + 8 + rest.length = st.data.regs.rcx.toNat
          ∧ av' + st.data.regs.rcx.toNat ≤ avail ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rcx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 24))
          ⋆ Eq (e8.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (t.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (u.At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 25)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (e8.At s.regs.rax.toBitVec)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (pre.At st.data.regs.rax.toBitVec) ⋆ Eq (e8.At (st.data.regs.rax.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (rest.At (st.data.regs.rax.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Heap av' ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlc hgrow hbud hpre ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *
  have hnsc := nextSliceCap_ge (rcx.toNat + 8) rdi.toNat
  have hrcx48 : rcx.toNat + 8 ≤ 2 ^ 48 := by unfold maxAlloc at hmax; omega
  have hn8 := Encode.grow_first_site_add8_toNat rcx (by omega)
  step_directive hk marshalSSZTo 0
  step_directive hk marshalSSZTo 1
  step_directive hk marshalSSZTo 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk marshalSSZTo 3
  split
  · rename_i h; exfalso
    simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  step_directive hk marshalSSZTo 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  unfold_step
  step_directive hk marshalSSZTo 5
  step_directive hk marshalSSZTo 6
  step_directive hk marshalSSZTo 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by bv_omega) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  unfold_step
  step_directive hk marshalSSZTo 8
  step_directive hk marshalSSZTo 9
  apply load_step _ _ _ _ e8 _ _ (by ecancel) (by exact he8)
  unfold_step
  step_directive hk marshalSSZTo 10
  step_directive hk marshalSSZTo 11
  step_directive hk marshalSSZTo 12
  step_directive hk marshalSSZTo 13
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  unfold_step
  rw [show rsp.toBitVec - 8#64 - 72 + 40 = rsp.toBitVec - 40 by bv_omega]
  apply Machine.store_avx_step _ _ _ _ t28 _ _ (by ecancel) (by exact ht28) (by decide)
  intro m3 H3
  unfold_step
  step_directive hk marshalSSZTo 14
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  unfold_step
  rw [show rsp.toBitVec - 40 + 16 = rsp.toBitVec - 24 by bv_omega]
  apply Machine.store_avx_step _ _ _ _ t18 _ _ (by ecancel) (by exact ht18) (by decide)
  intro m4 H4
  unfold_step
  rw [Machine.at_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 40),
    show rsp.toBitVec - 40 + 8 = rsp.toBitVec - 32 by bv_omega] at H4
  step_directive hk marshalSSZTo 15
  apply store_step_at _ _ (rsp.toBitVec - 40) _ _ _ ((Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).take 8)
    _ _ (by segment_addr) (by ecancel) (by rw [List.length_take, Int.toBytes_length]; rfl)
  intro m5 H5
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl e8 he8] at H5
  unfold_step
  step_directive hk marshalSSZTo 16
  step_directive hk marshalSSZTo 17
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  -- growslice call (directives 18–24)
  step_directive hk marshalSSZTo 18
  apply store_step_at _ _ (rsp.toBitVec + 24) _ _ _ s3 _ _ (by segment_addr) (by ecancel) (by exact h3)
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  unfold_step
  step_directive hk marshalSSZTo 19
  step_directive hk marshalSSZTo 20
  step_directive hk marshalSSZTo 21
  step_directive hk marshalSSZTo 22
  step_directive hk marshalSSZTo 23
  step_directive hk marshalSSZTo 24
  apply store_step_at _ _ (rsp.toBitVec - 88) _ _ _ rslot _ _ (Encode.grow_first_site_slot _) (by ecancel) (by exact hrs)
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  unfold_step
  rw [Encode.grow_first_site_slot] at *
  refine eventually_trans _ _ _ _ (hgs _ (Host.addrOf (k + 24 + 1)) pre scratch spl avail _ (by decide) rfl
    ?gnum ?gold ?gcap ?gbud hmax ?glen hsc hspl
    (by dsimp only; rw [show rsp.toBitVec - 88 + 8 = rsp.toBitVec - 80 by bv_omega]; ecancel)) ?_
  case gnum => dsimp only; rw [Encode.grow_first_site_zero_extend8, hn8]; omega
  case gold => dsimp only; (try simp) <;> omega
  case gcap => dsimp only; rw [Encode.grow_first_site_word_toNat rdi, hn8]; omega
  case gbud => dsimp only; rw [Encode.grow_first_site_word_toNat rdi, hn8]; omega
  case glen => dsimp only; rw [Encode.grow_first_site_zero_extend8, hn8]; omega
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, hrbx1, hnc1, hub1, stk1, spl1, tail, av1, hstk1, hspl1, htail, hav1,
    Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 hrbx1 hnc1 hub1 htail hav1 Hm1
  subst hpc1
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩,
    zmms1, flags1, mem1⟩ := d1
  simp only at hrsp1 hrbp1 hr141 hrbx1 hnc1 hub1 htail hav1 Hm1
  simp only [Encode.grow_first_site_word_toNat rdi, hn8] at hnc1 hub1
  obtain ⟨hc1, hc2⟩ := growslice_cap_bounds (by decide) (Nat.le_trans (by simpa using hbud) hmax) hnc1 hub1
  have htl : 8 ≤ tail.length := by omega
  have ht8 : (tail.take 8).length = 8 := by simp only [List.length_take]; omega
  rw [Encode.grow_first_site_ret] at hrsp1
  subst rsp1 r141 rbp1 rbx1
  rw [Encode.grow_first_site_split rax1.toBitVec rcx.toBitVec pre tail hpre htl (by omega),
    show rsp.toBitVec - 88 + 8 = rsp.toBitVec - 80 by bv_omega] at Hm1
  step_directive hk marshalSSZTo 25
  step_directive hk marshalSSZTo 26
  step_directive hk marshalSSZTo 27
  apply load_step_at _ _ (rsp.toBitVec + 24) _ _ (Int.toBytes 8 rcx.toBitVec.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  try simp only [ofInt_ofBytes_toBytes64]
  step_directive hk marshalSSZTo 28
  step_directive hk marshalSSZTo 29
  step_directive hk marshalSSZTo 30
  apply load_step_at _ _ (rsp.toBitVec - 40) _ _ e8 _ _ (by segment_addr) (by ecancel) (by exact he8)
  unfold_step
  step_directive hk marshalSSZTo 31
  rw [Codec.add_mul_one]
  apply store_step _ _ _ _ _ (tail.take 8) _ _ (by ecancel) (by exact ht8)
  intro m8 H8
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl e8 he8] at H8
  unfold_step
  step_directive hk marshalSSZTo 32
  step_directive hk marshalSSZTo 33
  step_directive hk marshalSSZTo 34
  step_directive hk marshalSSZTo 35
  intro _
  step_directive hk marshalSSZTo 36
  intro _
  step_directive hk marshalSSZTo 37
  step_directive hk marshalSSZTo 38
  apply load_step_at _ _ (rsp.toBitVec - 8) _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk marshalSSZTo 39
  apply load_step_at _ _ rsp.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  apply Eventually.done
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, (Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8,
    Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt, stk1, spl1, tail.drop 8, av1, ?htt, ?huu, hstk1, hspl1,
    ?hrest, ?hav, ?hmem⟩
  case hmem =>
    rw [show k + 24 + 1 = k + 25 from rfl] at H8
    simp only [show AvxWidth.W128.bytes = 16 from rfl, Std.ExtHashMap.sep_emp] at H8
    dsimp only
    ecancel
  case htt => simp [Int.toBytes_length]
  case huu => simp [Int.toBytes_length]
  case hrest => show rcx.toNat + 8 + (tail.drop 8).length = rcx1.toNat; simp only [List.length_drop]; omega
  case hav => show av1 + rcx1.toNat ≤ avail; omega
  all_goals first
    | exact trivial
    | with_reducible rfl
    | (exact hn8)
    | (exact hnc1)
    | (dsimp only; omega)
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (apply UInt64.toBitVec_inj.mp; segment_addr)

end Prysm.CommitteeIndex
