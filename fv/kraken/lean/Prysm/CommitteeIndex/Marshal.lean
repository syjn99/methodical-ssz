module

public import Codec.SegmentAddress
public import Prysm.CommitteeIndex.Code
public import Prysm.CommitteeIndex.EncodeGrowFirstSite
public import Prysm.CommitteeIndex.SpecDescription
public import Prysm.Epoch.Size
public import Machine.WitnessHost

@[expose] public section

/-!
# Prysm `(*primitives.CommitteeIndex).MarshalSSZ`, Go 1.26.10 machine code

`Marshal.result` covers the path where the stack check passes.
The morestack path (directives 23–27) is not covered.
The code loads the 8-byte value and spills it at rsp − 16 (directives 7–8).
It calls `runtime.growslice` with `old = runtime.zerobase`, `newLen = 8`, `oldCap = 0`, `num = 8`, `et = uint8`.
The old slice is empty, so the code reads no byte at `runtime.zerobase`.
So the theorem has no premise on the bytes at that address.
`link/check.py` (b) confirms that `runtime.zerobase` is a symbol of the ELF.
The contract is `GrowsliceContract Heap typeUint8_addr 1 S`, the form of `Encode.grow_first_site`.
The code stores the value at `new[0..8]` and returns `(new, 8, newCap, nil)`.
The rest of the new block (`newCap − 8` bytes) is named.
The call pushes its return address at rsp − 88.
The 40-byte growslice spill area is at rsp − 80.
Label freshness is not a premise, because this path has no jump to a label.
`Marshal.result_spec` states the same result for a receiver that holds `uintBytes 8 x`.
Then the first 8 bytes of the new block are the bytes of `serialize desc (.uint x)`.
-/

open Machine Runtime Prysm.CommitteeIndex.Code EthLib.Serialization.Ssz

namespace Prysm.CommitteeIndex

theorem Marshal.result_split (np : BitVec 64) (tail : List UInt8) (ht : 8 ≤ tail.length) (hb : tail.length < 2 ^ 64) :
    Eq (([] ++ tail).At np) = Eq ((tail.take 8).At np) ⋆ Eq ((tail.drop 8).At (np + 8)) := by
  rw [List.nil_append]
  conv => lhs; rw [← List.take_append_drop 8 tail]
  exact at_app _ _ (by rw [List.length_take, Nat.min_eq_left (by omega)]; rfl) (by simp; omega)

theorem Marshal.result_slot (x : BitVec 64) : x - 8#64 - 72 - 8#64 = x - 88 := by bv_omega

theorem Marshal.result_ret (x : BitVec 64) :
    ({ toBitVec := x - 88 } + 8 : UInt64) = { toBitVec := x - 80 } := by
  apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega

theorem Marshal.result_next_slice_cap : nextSliceCap 8 0 = 8 := by decide

theorem Marshal.result_eight :
    ({ toBitVec := BitVec.zeroExtend 64 (BitVec.truncate 32 (8 : BitVec 64)) } : UInt64).toNat = 8 := by
  decide

theorem Marshal.result_zero (x : BitVec 64) :
    ({ toBitVec := BitVec.zeroExtend 64 (BitVec.extractLsb' 0 32 x ^^^ BitVec.extractLsb' 0 32 x) } : UInt64).toNat
      = 0 := by
  simp

variable [Host]

theorem Marshal.result (k : Nat) (hk : marshalSSZ.IsInfixAt Host.prog k)
    (e8 : List UInt8) (he8 : e8.length = 8)
    (s : MachineData) (ra guard : UInt64)
    (fp vs rslot spl : List UInt8) (hfp : fp.length = 8) (hv : vs.length = 8) (hrs : rslot.length = 8)
    (hspl : spl.length = 40)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (vs.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (e8.At s.regs.rax.toBitVec) ⋆ Heap avail ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat)
    (hbud : 2 * nextSliceCap 8 0 + 8192 ≤ avail) (hmax : avail ≤ maxAlloc)
    (hgs : GrowsliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec
        ∧ st.data.regs.rbx = 8
        ∧ nextSliceCap 8 0 ≤ st.data.regs.rcx.toNat ∧ st.data.regs.rcx.toNat ≤ 2 * nextSliceCap 8 0 + 8192
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (scr spl' rest : List UInt8) (av' : Nat), scr.length = S ∧ spl'.length = 40
          ∧ 8 + rest.length = st.data.regs.rcx.toNat ∧ av' + st.data.regs.rcx.toNat ≤ avail ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq (e8.At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 15)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (e8.At s.regs.rax.toBitVec)
          ⋆ Eq (e8.At st.data.regs.rax.toBitVec)
          ⋆ Eq (rest.At (st.data.regs.rax.toBitVec + 8))
          ⋆ Heap av' ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size
  simp only [UInt64.size] at *
  rw [Marshal.result_next_slice_cap] at hbud ⊢
  step_directive hk marshalSSZ 0
  step_directive hk marshalSSZ 1
  step_directive hk marshalSSZ 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk marshalSSZ 3
  split
  · rename_i h; exfalso
    simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  step_directive hk marshalSSZ 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  unfold_step
  step_directive hk marshalSSZ 5
  step_directive hk marshalSSZ 6
  step_directive hk marshalSSZ 7
  apply load_step _ _ _ _ e8 _ _ (by ecancel) (by exact he8)
  unfold_step
  step_directive hk marshalSSZ 8
  apply store_step_at _ _ (rsp.toBitVec - 16) _ _ _ vs _ _ (by segment_addr) (by ecancel) (by exact hv)
  intro m2 H2
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl e8 he8] at H2
  unfold_step
  step_directive hk marshalSSZ 9
  step_directive hk marshalSSZ 10
  step_directive hk marshalSSZ 11
  intro _
  step_directive hk marshalSSZ 12
  step_directive hk marshalSSZ 13
  step_directive hk marshalSSZ 14
  apply store_step_at _ _ (rsp.toBitVec - 88) _ _ _ rslot _ _ (Marshal.result_slot _) (by ecancel) (by exact hrs)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  unfold_step
  rw [Marshal.result_slot] at *
  rw [← Std.ExtHashMap.emp_sep (Eq _), ← Machine.Witness.nil_At_emp (label "runtime.zerobase").toBitVec] at H3
  refine eventually_trans _ _ _ _ (hgs _ (Host.addrOf (k + 14 + 1)) [] scratch spl avail _ (by decide) rfl
    ?gnum ?gold ?gcap ?gbud hmax ?glen hsc hspl
    (by dsimp only; rw [show rsp.toBitVec - 88 + 8 = rsp.toBitVec - 80 by bv_omega]; ecancel)) ?_
  all_goals try (dsimp only; simp only [Marshal.result_eight, Marshal.result_zero, Marshal.result_next_slice_cap,
    List.length_nil] <;> omega)
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, hrbx1, hnc1, hub1, stk1, spl1, tail, av1, hstk1, hspl1, htail, hav1,
    Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 hrbx1 hnc1 hub1 htail hav1 Hm1
  subst hpc1
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩,
    zmms1, flags1, mem1⟩ := d1
  simp only at hrsp1 hrbp1 hr141 hrbx1 hnc1 hub1 htail hav1 Hm1
  simp only [Marshal.result_eight, Marshal.result_zero, Marshal.result_next_slice_cap, Nat.one_mul,
    List.length_nil, Nat.zero_add] at hnc1 hub1 htail hav1
  have hrcx1 := rcx1.toNat_lt_size
  simp only [UInt64.size] at hrcx1
  have htl : 8 ≤ tail.length := by omega
  have ht8 : (tail.take 8).length = 8 := by simp only [List.length_take]; omega
  rw [Marshal.result_ret] at hrsp1
  subst rsp1 r141 rbp1 rbx1
  rw [Marshal.result_split rax1.toBitVec tail htl (by omega), Machine.Witness.nil_At_emp, Std.ExtHashMap.emp_sep,
    show rsp.toBitVec - 88 + 8 = rsp.toBitVec - 80 by bv_omega] at Hm1
  step_directive hk marshalSSZ 15
  apply load_step_at _ _ (rsp.toBitVec - 16) _ _ e8 _ _ (by segment_addr) (by ecancel) (by exact he8)
  unfold_step
  step_directive hk marshalSSZ 16
  apply store_step _ _ _ _ _ (tail.take 8) _ _ (by ecancel) (by exact ht8)
  intro m4 H4
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl e8 he8] at H4
  unfold_step
  step_directive hk marshalSSZ 17
  step_directive hk marshalSSZ 18
  intro _
  step_directive hk marshalSSZ 19
  intro _
  step_directive hk marshalSSZ 20
  step_directive hk marshalSSZ 21
  apply load_step_at _ _ (rsp.toBitVec - 8) _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk marshalSSZ 22
  apply load_step_at _ _ rsp.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  apply Eventually.done
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, stk1, spl1, tail.drop 8, av1, hstk1, hspl1, ?hrest, ?hav, ?hmem⟩
  case hmem =>
    rw [show k + 14 + 1 = k + 15 from rfl] at H4
    dsimp only
    ecancel
  case hrest => show 8 + (tail.drop 8).length = rcx1.toNat; simp only [List.length_drop]; omega
  case hav => show av1 + rcx1.toNat ≤ avail; omega
  all_goals first
    | exact trivial
    | with_reducible rfl
    | (dsimp only; omega)
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (apply UInt64.toBitVec_inj.mp; segment_addr)

theorem Marshal.result_spec (k : Nat) (hk : marshalSSZ.IsInfixAt Host.prog k)
    (x : UInt64)
    (s : MachineData) (ra guard : UInt64)
    (fp vs rslot spl : List UInt8) (hfp : fp.length = 8) (hv : vs.length = 8) (hrs : rslot.length = 8)
    (hspl : spl.length = 40)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (vs.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((uintBytes 8 x.toNat).toList.At s.regs.rax.toBitVec) ⋆ Heap avail ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat)
    (hbud : 2 * nextSliceCap 8 0 + 8192 ≤ avail) (hmax : avail ≤ maxAlloc)
    (hgs : GrowsliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 S) :
    ∃ bs, serialize desc (.uint x.toNat) = .ok bs ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec
        ∧ st.data.regs.rbx = 8
        ∧ nextSliceCap 8 0 ≤ st.data.regs.rcx.toNat ∧ st.data.regs.rcx.toNat ≤ 2 * nextSliceCap 8 0 + 8192
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (scr spl' rest : List UInt8) (av' : Nat), scr.length = S ∧ spl'.length = 40
          ∧ 8 + rest.length = st.data.regs.rcx.toNat ∧ av' + st.data.regs.rcx.toNat ≤ avail ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq (bs.toList.At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 15)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (bs.toList.At s.regs.rax.toBitVec)
          ⋆ Eq (bs.toList.At st.data.regs.rax.toBitVec)
          ⋆ Eq (rest.At (st.data.regs.rax.toBitVec + 8))
          ⋆ Heap av' ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ :=
  ⟨uintBytes 8 x.toNat, Prysm.Epoch.uint64_serialize_eq x,
    Marshal.result k hk _ (by simp [Spec.uintBytes_size]) s ra guard fp vs rslot spl hfp hv hrs hspl R S scratch hsc
      Heap avail h_mem hguard hbud hmax hgs⟩

end Prysm.CommitteeIndex
