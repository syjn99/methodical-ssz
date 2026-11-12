import Prysm.Checkpoint.CapacityReservedEncodeTail
import Codec.StackGuard

/-!
# OPT-R1 reserve encoder: the two prefixes up to `L_e5` (directive 48)

- `head_fast` (`len + 40 ≤ cap`, `cap < 2^63`): directives 0–15: large-frame stack guard
  (`lea -0x18(%rsp),%r12`, premise `guard + 24 < rsp`, lemma `Codec.lea_cmp_be_false`), prologue
  (`sub $0x90`, spills of rbx, rax, rcx to rsp + 16, + 8, + 24), `rdx := cap`, `rdi := cap − len`,
  `cmp $0x28,%rdi; jge L_e5` taken (signed; `Encode.reserve_ge`). Nothing else is written.
- `head_grow` (`len ≤ cap < len + 40`): directives 0–47: the reserve. `z` (40 bytes at rsp0 − 112) is
  zeroed with three `movups %xmm15` (X15 is not assumed zero: `z`'s bytes are existential), the
  `jae` at 22 is not taken, one `runtime.growslice(old = dst.ptr, newLen = len + 40, oldCap = cap,
  num = 40, et = uint8)` (`GrowsliceC Heap e2eU8Type_addr 1 S`, the existing form), `memmove(new +
  len, &z, 40)` (`MemmoveC S`), the `[:len(dst)]` bounds check `cmp %rdx,%rbx; ja panicBounds` not
  taken (`Encode.reserve_ja_false`, from `newLen ≤ newCap` of the contract), reload of rax, rcx, rbx. The caller's
  block keeps `pre` (it is the growslice source) and is not written. The new block is
  `pre ++ z ++ tail`.
-/

open Machine Runtime TestTarget Prysm.Checkpoint.CapacityReserved.Code
variable [Host]

namespace Prysm.Checkpoint.CapacityReserved

omit [Host] in
/-- `cmp y, x; jge` is taken when `y ≤ x < 2^63` (signed compare without overflow). -/
theorem Encode.reserve_ge (x y : BitVec 64) (cf af : Bool) (hle : y.toNat ≤ x.toNat) (hlt : x.toNat < 2 ^ 63) :
    CondCode.ge.interp (StatusFlags.from_result (x - y)
      { cf := cf, af := af, of := BitVec.toInt (x - y) != BitVec.toInt x - BitVec.toInt y }) = true := by
  have hs : (x - y).toNat = x.toNat - y.toNat := BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
  have tx : x.toInt = (x.toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  have ty : y.toInt = (y.toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  have td : (x - y).toInt = ((x - y).toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  have hm : (x - y).msb = false := by
    rw [BitVec.msb_eq_decide, hs]; simp only [decide_eq_false_iff_not, Nat.not_le]; omega
  have hof : (((x - y).toNat : Int) != (x.toNat : Int) - (y.toNat : Int)) = false := by
    rw [hs]; simp only [bne_eq_false_iff_eq]; omega
  simp only [CondCode.interp, StatusFlags.from_result, hm, td, tx, ty, hof]
  rfl

omit [Host] in
/-- `cmp b, a; ja` is not taken when `a ≤ b`. -/
theorem Encode.reserve_ja_false (a b : BitVec 64) (af of' : Bool) (h : a.toNat ≤ b.toNat) :
    CondCode.a.interp (StatusFlags.from_result (a - b)
      { cf := BitVec.unsigned (a - b) != a.unsigned - b.unsigned, af := af, of := of' }) = false := by
  rcases Nat.lt_or_eq_of_le h with h | h
  · have hs : (a - b).toNat = 2 ^ 64 - b.toNat + a.toNat := by
      rw [BitVec.toNat_sub]; have := b.isLt; omega
    have hc : (((a - b).toNat : Int) != (a.toNat : Int) - (b.toNat : Int)) = true := by
      rw [hs]; simp only [bne_iff_ne, ne_eq]; omega
    simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, hc]
    rfl
  · have : a = b := BitVec.eq_of_toNat_eq h
    subst this
    simp [CondCode.interp, StatusFlags.from_result]

omit [Host] in
theorem Encode.reserve_sub40a (rcx rdi : UInt64) (h : rcx.toNat + 40 ≤ rdi.toNat) :
    (40 : BitVec 64).toNat ≤ (rdi.toBitVec - rcx.toBitVec).toNat := by
  have h' : rcx.toBitVec.toNat + 40 ≤ rdi.toBitVec.toNat := h
  bv_omega

omit [Host] in
theorem Encode.reserve_sub40b (rcx rdi : UInt64) (h : rcx.toNat + 40 ≤ rdi.toNat) (h2 : rdi.toNat < 2 ^ 63) :
    (rdi.toBitVec - rcx.toBitVec).toNat < 2 ^ 63 := by
  have h' : rcx.toBitVec.toNat + 40 ≤ rdi.toBitVec.toNat := h
  have h2' : rdi.toBitVec.toNat < 2 ^ 63 := h2
  bv_omega

omit [Host] in
theorem Encode.reserve_sub40c (rcx rdi : UInt64) (h1 : rcx.toNat ≤ rdi.toNat) (h : rdi.toNat < rcx.toNat + 40) :
    (rdi.toBitVec - rcx.toBitVec).toNat < (40 : BitVec 64).toNat := by
  have h1' : rcx.toBitVec.toNat ≤ rdi.toBitVec.toNat := h1
  have h' : rdi.toBitVec.toNat < rcx.toBitVec.toNat + 40 := h
  bv_omega

omit [Host] in
/-- `cmp y, x; jge` is not taken when `x < y < 2^63`. -/
theorem Encode.reserve_lt (x y : BitVec 64) (cf af : Bool) (hlt : x.toNat < y.toNat) (hy : y.toNat < 2 ^ 63) :
    CondCode.ge.interp (StatusFlags.from_result (x - y)
      { cf := cf, af := af, of := BitVec.toInt (x - y) != BitVec.toInt x - BitVec.toInt y }) = false := by
  have hs : (x - y).toNat = 2 ^ 64 - y.toNat + x.toNat := by
    rw [BitVec.toNat_sub]; have := y.isLt; omega
  have tx : x.toInt = (x.toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  have ty : y.toInt = (y.toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  have hm : (x - y).msb = true := by
    rw [BitVec.msb_eq_decide, hs]; simp only [decide_eq_true_eq]; omega
  have td : (x - y).toInt = (x.toNat : Int) - (y.toNat : Int) := by
    rw [BitVec.toInt_eq_msb_cond, hm]; simp only [if_true, hs]; omega
  have hof : (((x.toNat : Int) - (y.toNat : Int)) != (x.toNat : Int) - (y.toNat : Int)) = false := by
    simp
  simp only [CondCode.interp, StatusFlags.from_result, hm, td, tx, ty, hof]
  rfl

omit [Host] in
theorem Encode.reserve_e40 : ({ toBitVec := BitVec.zeroExtend 64 (BitVec.truncate 32 (40 : BitVec 64)) } : UInt64).toNat = 40 := by
  decide

omit [Host] in
theorem Encode.reserve_n40 (x : UInt64) (h : x.toNat + 40 < 2 ^ 64) :
    ({ toBitVec := x.toBitVec + 40 } : UInt64).toNat = x.toNat + 40 := by
  have h' : x.toBitVec.toNat + 40 < 2 ^ 64 := h
  show (x.toBitVec + 40).toNat = x.toBitVec.toNat + 40
  bv_omega

omit [Host] in
theorem Encode.reserve_slot (x : BitVec 64) : x - 8#64 - 144 - 8#64 = x - 160 := by bv_omega

omit [Host] in
/-- The new block `pre ++ tail` (`40 ≤ tail.length`) around the reserved 40 bytes at `np + L`. -/
theorem Encode.reserve_split40 (np : BitVec 64) (L : UInt64) (pre tail : List UInt8) (hpre : pre.length = L.toNat)
    (ht : 40 ≤ tail.length) (hb : pre.length + tail.length < 2 ^ 64) :
    Eq ((pre ++ tail).At np) = Eq (pre.At np) ⋆ Eq ((tail.take 40).At (np + L.toBitVec))
      ⋆ Eq ((tail.drop 40).At (np + L.toBitVec + 40)) := by
  have e : pre ++ tail = pre ++ (tail.take 40 ++ tail.drop 40) := by simp only [List.take_append_drop]
  rw [e, at_app pre _ (b := np + L.toBitVec) (by rw [hpre]; apply BitVec.eq_of_toNat_eq; simp)
      (by simp only [List.length_append, List.length_take, List.length_drop]; omega),
    at_app (tail.take 40) _ (b := np + L.toBitVec + 40) (by rw [List.length_take, Nat.min_eq_left ht]; rfl)
      (by simp only [List.length_take, List.length_drop]; omega)]
  simp only [Std.ExtHashMap.sep_assoc]

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem Encode.head_fast (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (s : MachineData) (ra guard : UInt64) (fp s1 s2 s3 : List UInt8) (hfp : fp.length = 8)
    (h1 : s1.length = 8) (h2 : s2.length = 8) (h3 : s3.length = 8) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s3.At (s.regs.rsp.toBitVec + 24))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16)) ⋆ R)
    (hguard : guard.toNat + 24 < s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 40 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 48) ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 152 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8#64 } ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.rax = s.regs.rax ∧ st.data.regs.rbx = s.regs.rbx ∧ st.data.regs.rcx = s.regs.rcx
        ∧ st.data.regs.rdx = s.regs.rdi ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rcx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hcap hcap63 ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *
  kat hk marshalSSZTo 0
  kat hk marshalSSZTo 1
  kat hk marshalSSZTo 2
  kat hk marshalSSZTo 3
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 4
  split
  case isTrue h =>
    exfalso
    rw [Codec.lea_cmp_be_false rsp.toBitVec _ guard.toBitVec _ _ 24 (by rfl) hguard] at h
    exact Bool.noConfusion h
  simp only [Effects.All]
  kat hk marshalSSZTo 5
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk marshalSSZTo 6
  kat hk marshalSSZTo 7
  kat hk marshalSSZTo 8
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by bv_omega) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk marshalSSZTo 9
  apply store_step_at _ _ (rsp.toBitVec + 8) _ _ _ s1 _ _ (by bv_omega) (by ecancel) (by exact h1)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk marshalSSZTo 10
  apply store_step_at _ _ (rsp.toBitVec + 24) _ _ _ s3 _ _ (by bv_omega) (by ecancel) (by exact h3)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  kat hk marshalSSZTo 11
  kat hk marshalSSZTo 12
  kat hk marshalSSZTo 13
  kat hk marshalSSZTo 14
  kat hk marshalSSZTo 15
  split
  case isFalse h =>
    exfalso
    rw [Encode.reserve_ge _ _ _ _ ?g1 ?g2] at h
    · exact h rfl
    · exact Encode.reserve_sub40a rcx rdi hcap
    · exact Encode.reserve_sub40b rcx rdi hcap hcap63
  simp only [Effects.All]
  klabel hk hf marshalSSZTo 48
  apply Eventually.done
  refine ⟨rfl, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?hmem⟩
  case hmem => ecancel
  all_goals first
    | with_reducible rfl
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (apply UInt64.toBitVec_inj.mp; eaddr)

end Prysm.Checkpoint.CapacityReserved
