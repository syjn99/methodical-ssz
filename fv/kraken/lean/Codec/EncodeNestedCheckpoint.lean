import Codec.EncodeSteps
import Codec.EncodeFieldHelpers

/-!
# The nested Checkpoint field of an encoder fast path

A field of type `*Checkpoint` in a fixed-size container encoder.
The Go source is:

    if a.Source == nil { a.Source = new(Checkpoint) }
    if dst, err = a.Source.MarshalSSZTo(dst); err != nil { … }

On the fast path the pointer is not nil, and the callee takes its fast path.
The compiled code (Go 1.26.10, `AttestationData.Source` and `.Target`) has three parts on this path:

    cmpq $0x0,d(%rB); jne l          -- the nil test, taken (`step_nil_check_taken`)
    l: …; callq fn                     -- the set-up of the arguments, then the call (`encode_nested_checkpoint_call`)
    test %rdi,%rdi; je lok             -- the error test, taken (`step_test_je_taken`)

The set-up of the arguments differs at the two sites, so the generator steps it directive by directive.
The call uses the callee only through `NestedCheckpointCalleeEncode fn S`.
This is the text of `Prysm.Checkpoint.Encode.fast_path_function_spec S` with the callee label as a parameter.
`Prysm.Checkpoint.Encode.fast_path_function_spec_holds` proves it from the machine code, with `MemmoveContract S`.
The `newobject` branch of a nil pointer and the error wrap of the call are not on this path.

The callee frame lives in the 120 bytes below the return slot and the `S` scratch bytes below them.
In the caller statement this is one block of `S + 120` bytes (`low block`).
`low_block_memmove_split` and `low_block_join` give the view of a `runtime.memmove` call of the caller.
That call uses the top `S` bytes of the block.
`low_block_callee_frame_split` gives the view of the callee frame.
-/

open Machine Runtime

namespace Codec

/-- `test %rS,%rS`. -/
def instrTestRegister (r : Reg64) : Directive :=
  Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
    (Operation.test (RegOrMem.reg (Reg.low r Width.W64)) (Operand.regOrMem (RegOrMem.reg (Reg.low r Width.W64)))))

/-- The one directive of the call: `callq fn`. -/
def callNestedEncoder (fn : String) : Program :=
  [Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.call (RelRegOrMem.rel ((ConstExpr.label fn).sub ConstExpr.after_current_instruction))))]

/-- Function specification form of a nested Checkpoint encoder at the label `fn`, fast path.
It is the text of `Prysm.Checkpoint.Encode.fast_path_function_spec S` with the label `fn`. -/
def NestedCheckpointCalleeEncode [Host] (fn : String) (S : Nat) : Prop :=
  ∀ (st : MachineData) (ret : Int64) (guard : UInt64) (p : BitVec 64)
    (cst e8 cC ctl root pre d0 d1 fp s2 l16 l24 l32 t40 t30 rslot scratch : List UInt8) (F : DataMem → Prop),
    cst.length = 8 → e8.length = 8 → cC.length = 8 → ctl.length = 32 → root.length = 32 → d0.length = 8 →
    d1.length = 32 → pre.length = st.regs.rcx.toNat → fp.length = 8 → s2.length = 8 → l16.length = 8 →
    l24.length = 8 → l32.length = 8 → t40.length = 16 → t30.length = 16 → rslot.length = 8 → scratch.length = S →
    guard.toNat < st.regs.rsp.toNat → 120 ≤ st.regs.rsp.toNat →
    st.regs.rcx.toNat + 40 ≤ st.regs.rdi.toNat → st.regs.rdi.toNat < 2 ^ 63 →
    (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (st.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (st.regs.rsp.toBitVec + 16))
      ⋆ Eq (l16.At (st.regs.rsp.toBitVec - 16)) ⋆ Eq (l24.At (st.regs.rsp.toBitVec - 24))
      ⋆ Eq (l32.At (st.regs.rsp.toBitVec - 32)) ⋆ Eq (t30.At (st.regs.rsp.toBitVec - 48))
      ⋆ Eq (t40.At (st.regs.rsp.toBitVec - 64))
      ⋆ Eq (rslot.At (st.regs.rsp.toBitVec - 120)) ⋆ Eq (scratch.At (st.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (st.regs.r14.toBitVec + 16))
      ⋆ Eq (cst.At st.regs.rax.toBitVec) ⋆ Eq (e8.At (st.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 p.toInt).At (st.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (st.regs.rax.toBitVec + 24)) ⋆ Eq (cC.At (st.regs.rax.toBitVec + 32))
      ⋆ Eq (ctl.At (st.regs.rax.toBitVec + 40)) ⋆ Eq (root.At p)
      ⋆ Eq (pre.At st.regs.rbx.toBitVec) ⋆ Eq (d0.At (st.regs.rbx.toBitVec + st.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (st.regs.rbx.toBitVec + st.regs.rcx.toBitVec + 8)) ⋆ F) st.dmem →
    Eventually (step1 Host.exe)
      (fun st' => st'.pc = ret ∧ st'.data.regs.rax = st.regs.rbx
        ∧ st'.data.regs.rbx.toNat = st.regs.rcx.toNat + 40 ∧ st'.data.regs.rcx = st.regs.rdi
        ∧ st'.data.regs.rdi = 0 ∧ st'.data.regs.rsi = 0
        ∧ st'.data.regs.rsp = st.regs.rsp + 8 ∧ st'.data.regs.rbp = st.regs.rbp ∧ st'.data.regs.r14 = st.regs.r14 ∧
        ∃ (t u scr rs' : List UInt8), t.length = 8 ∧ u.length = 16 ∧ scr.length = S ∧ rs'.length = 8 ∧
        (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 st.regs.rbp.toBitVec.toInt).At (st.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 st.regs.rbx.toBitVec.toInt).At (st.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 st.regs.rbx.toBitVec.toInt).At (st.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 st.regs.rdi.toBitVec.toInt).At (st.regs.rsp.toBitVec - 24))
          ⋆ Eq ((Int.toBytes 8 (st.regs.rcx.toBitVec + 40).toInt).At (st.regs.rsp.toBitVec - 32))
          ⋆ Eq (u.At (st.regs.rsp.toBitVec - 48)) ⋆ Eq (e8.At (st.regs.rsp.toBitVec - 64))
          ⋆ Eq (t.At (st.regs.rsp.toBitVec - 56))
          ⋆ Eq (rs'.At (st.regs.rsp.toBitVec - 120))
          ⋆ Eq (scr.At (st.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (st.regs.r14.toBitVec + 16))
          ⋆ Eq (cst.At st.regs.rax.toBitVec) ⋆ Eq (e8.At (st.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (st.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (st.regs.rax.toBitVec + 24)) ⋆ Eq (cC.At (st.regs.rax.toBitVec + 32))
          ⋆ Eq (ctl.At (st.regs.rax.toBitVec + 40)) ⋆ Eq (root.At p)
          ⋆ Eq (pre.At st.regs.rbx.toBitVec) ⋆ Eq (e8.At (st.regs.rbx.toBitVec + st.regs.rcx.toBitVec))
          ⋆ Eq (root.At (st.regs.rbx.toBitVec + st.regs.rcx.toBitVec + 8)) ⋆ F) st'.data.dmem)
      ⟨st, label fn⟩

/-- `cmpq $0,a; jne` is taken when the word at `a` is not 0. -/
theorem cmp_zero_nz_true (a : BitVec 64) (cf af of' : Bool) (h : a ≠ 0) :
    CondCode.nz.interp (StatusFlags.from_result (a - (0 : Int64).toBitVec) { cf := cf, af := af, of := of' }) = true := by
  simp [CondCode.interp, StatusFlags.from_result]
  exact h

/-- `test %r,%r; je` is taken when `r` is 0. -/
theorem test_zero_z_true (cf af of' : Bool) :
    CondCode.z.interp (StatusFlags.from_result ((0 : BitVec 64) &&& 0) { cf := cf, af := af, of := of' }) = true := by
  simp [CondCode.interp, StatusFlags.from_result]

/-- The length register after the call, as a bit vector: no overflow below `cap < 2 ^ 63`. -/
theorem nested_length_after_call (r : UInt64) (m cap : BitVec 64) (h : r.toNat = m.toNat + 40)
    (hcap : m.toNat + 40 ≤ cap.toNat) (hcap63 : cap.toNat < 2 ^ 63) : r.toBitVec = m + 40 := by
  apply BitVec.eq_of_toNat_eq
  have h40 : (40 : BitVec 64).toNat = 40 := rfl
  rw [UInt64.toNat_toBitVec, h, BitVec.toNat_add, h40]
  omega

/-- The prefix of a nested call as a bit-vector length: the prefix and the earlier fields have `len + n` bytes. -/
theorem nested_prefix_length (rcx rdi : UInt64) (n : Nat) (l : List UInt8) (h : l.length = rcx.toNat + n)
    (hcap : rcx.toNat + n ≤ rdi.toNat) : l.length = (rcx.toBitVec + BitVec.ofNat 64 n).toNat := by
  have := rdi.toBitVec.isLt
  rw [h, BitVec.toNat_add, BitVec.toNat_ofNat, UInt64.toNat_toBitVec]
  simp only [UInt64.toNat] at hcap ⊢
  omega

/-- The capacity premise of a nested call from the capacity premise of the function. -/
theorem nested_call_capacity (rcx rdi : UInt64) (n : Nat) (h : rcx.toNat + n + 40 ≤ rdi.toNat) (h63 : rdi.toNat < 2 ^ 63) :
    (rcx.toBitVec + BitVec.ofNat 64 n).toNat + 40 ≤ rdi.toBitVec.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  simp only [UInt64.toNat] at h h63 ⊢
  omega

/-- The stack premises of a nested call with its return slot at `rsp − n − 8`, from the guard premise of the function. -/
theorem nested_call_stack (r : UInt64) (g n a : Nat) (h : g + a < r.toNat) (hn : n + 8 + 120 ≤ a) :
    g < (r.toBitVec - BitVec.ofNat 64 n - 8).toNat ∧ 120 ≤ (r.toBitVec - BitVec.ofNat 64 n - 8).toNat := by
  simp only [UInt64.toNat] at h
  constructor <;> bv_omega

/-- **The low block as the view of a `runtime.memmove` call**: a block `lo` of `S + E` bytes at `a − S` is the
bottom `E` bytes at `a − S` and the top `S` bytes at `b − S`, with `a + E = b`. -/
theorem low_block_memmove_split (a b : BitVec 64) (S E : Nat) (hS : S < 2 ^ 60) (hE : E < 2 ^ 60)
    (hab : a + BitVec.ofNat 64 E = b) (lo : List UInt8) (hlo : lo.length = S + E) (F : DataMem → Prop) (m : DataMem)
    (H : (Eq (lo.At (a - BitVec.ofNat 64 S)) ⋆ F) m) :
    ∃ lo1 sc : List UInt8, lo1.length = E ∧ sc.length = S ∧
      (Eq (lo1.At (a - BitVec.ofNat 64 S)) ⋆ Eq (sc.At (b - BitVec.ofNat 64 S)) ⋆ F) m := by
  refine ⟨lo.take E, lo.drop E, by rw [List.length_take, hlo]; omega, by rw [List.length_drop, hlo]; omega, ?_⟩
  rw [← List.take_append_drop E lo] at H
  rw [at_app (lo.take E) (lo.drop E) (b := b - BitVec.ofNat 64 S)
    (by rw [List.length_take, hlo, Nat.min_eq_left (by omega), ← hab]; bv_omega)
    (by rw [← List.length_append, List.take_append_drop, hlo]; omega)] at H
  exact H

/-- **The low block, joined again** after a `runtime.memmove` call on its top `S` bytes. -/
theorem low_block_join (a b : BitVec 64) (S E : Nat) (hS : S < 2 ^ 60) (hE : E < 2 ^ 60)
    (hab : a + BitVec.ofNat 64 E = b) (lo1 sc : List UInt8) (h1 : lo1.length = E) (h2 : sc.length = S)
    (F : DataMem → Prop) (m : DataMem)
    (H : (Eq (lo1.At (a - BitVec.ofNat 64 S)) ⋆ Eq (sc.At (b - BitVec.ofNat 64 S)) ⋆ F) m) :
    (lo1 ++ sc).length = S + E ∧ (Eq ((lo1 ++ sc).At (a - BitVec.ofNat 64 S)) ⋆ F) m := by
  refine ⟨by rw [List.length_append, h1, h2]; omega, ?_⟩
  rw [at_app lo1 sc (b := b - BitVec.ofNat 64 S) (by rw [h1, ← hab]; bv_omega)
    (by rw [h1, h2]; omega)]
  exact H

/-- The `S + 120` bytes below the return slot of a nested Checkpoint encoder call, in the order of the callee frame:
scratch (`S`), the return slot of its `runtime.memmove` call, a gap of 48 bytes, `t40` and `t30` (16 bytes each), `l32`,
`l24`, `l16` and the saved frame pointer `fp`. -/
def encoderCalleeFrame (sc rs gap t40 t30 l32 l24 l16 fp : List UInt8) : List UInt8 :=
  sc ++ (rs ++ (gap ++ (t40 ++ (t30 ++ (l32 ++ (l24 ++ (l16 ++ fp)))))))

/-- Any list is an `encoderCalleeFrame` of its slices. -/
theorem encoderCalleeFrame_slices (y : List UInt8) (S : Nat) :
    y = encoderCalleeFrame (y.take S) ((y.drop S).take 8) (((y.drop S).drop 8).take 48)
      ((((y.drop S).drop 8).drop 48).take 16) (((((y.drop S).drop 8).drop 48).drop 16).take 16)
      ((((((y.drop S).drop 8).drop 48).drop 16).drop 16).take 8)
      (((((((y.drop S).drop 8).drop 48).drop 16).drop 16).drop 8).take 8)
      ((((((((y.drop S).drop 8).drop 48).drop 16).drop 16).drop 8).drop 8).take 8)
      ((((((((y.drop S).drop 8).drop 48).drop 16).drop 16).drop 8).drop 8).drop 8) := by
  simp only [encoderCalleeFrame, List.take_append_drop]

/-- **The low block as the callee frame of a nested Checkpoint encoder**: a block `y` of `S + 120` bytes at
`aRs − S` is the callee scratch (`S` bytes at `aRs − S`), the return slot of the `runtime.memmove` call of the callee
(8 bytes at `aRs`), a gap of 48 bytes, the temp chunks `t40` and `t30` (16 bytes each), the words `l32`, `l24`, `l16`
and the saved frame pointer `fp`. -/
theorem low_block_callee_frame_split (aRs aGap aT40 aT30 aL32 aL24 aL16 aFp : BitVec 64) (S : Nat) (hS : S < 2 ^ 60)
    (hGap : aRs + 8 = aGap) (hT40 : aRs + 56 = aT40) (hT30 : aRs + 72 = aT30) (hL32 : aRs + 88 = aL32)
    (hL24 : aRs + 96 = aL24) (hL16 : aRs + 104 = aL16) (hFp : aRs + 112 = aFp)
    (y : List UInt8) (hy : y.length = S + 120) (F : DataMem → Prop) (m : DataMem)
    (H : (Eq (y.At (aRs - BitVec.ofNat 64 S)) ⋆ F) m) :
    ∃ sc rs gap t40 t30 l32 l24 l16 fp : List UInt8, sc.length = S ∧ rs.length = 8 ∧ gap.length = 48 ∧
      t40.length = 16 ∧ t30.length = 16 ∧ l32.length = 8 ∧ l24.length = 8 ∧ l16.length = 8 ∧ fp.length = 8 ∧
      (Eq (sc.At (aRs - BitVec.ofNat 64 S)) ⋆ Eq (rs.At aRs) ⋆ Eq (gap.At aGap) ⋆ Eq (t40.At aT40)
        ⋆ Eq (t30.At aT30) ⋆ Eq (l32.At aL32) ⋆ Eq (l24.At aL24) ⋆ Eq (l16.At aL16) ⋆ Eq (fp.At aFp) ⋆ F) m := by
  subst hGap hT40 hT30 hL32 hL24 hL16 hFp
  rw [encoderCalleeFrame_slices y S] at H
  have l8 : ((((((((y.drop S).drop 8).drop 48).drop 16).drop 16).drop 8).drop 8).drop 8).length = 8 := by
    simp only [List.length_drop, hy]; omega
  have l7 : ((((((((y.drop S).drop 8).drop 48).drop 16).drop 16).drop 8).drop 8).take 8).length = 8 := by
    simp only [List.length_take, List.length_drop, hy]; omega
  have l6 : (((((((y.drop S).drop 8).drop 48).drop 16).drop 16).drop 8).take 8).length = 8 := by
    simp only [List.length_take, List.length_drop, hy]; omega
  have l5 : ((((((y.drop S).drop 8).drop 48).drop 16).drop 16).take 8).length = 8 := by
    simp only [List.length_take, List.length_drop, hy]; omega
  have l4 : (((((y.drop S).drop 8).drop 48).drop 16).take 16).length = 16 := by
    simp only [List.length_take, List.length_drop, hy]; omega
  have l3 : ((((y.drop S).drop 8).drop 48).take 16).length = 16 := by
    simp only [List.length_take, List.length_drop, hy]; omega
  have l2 : (((y.drop S).drop 8).take 48).length = 48 := by
    simp only [List.length_take, List.length_drop, hy]; omega
  have l1 : ((y.drop S).take 8).length = 8 := by
    simp only [List.length_take, List.length_drop, hy]; omega
  have l0 : (y.take S).length = S := by
    simp only [List.length_take, hy]; omega
  generalize ((((((((y.drop S).drop 8).drop 48).drop 16).drop 16).drop 8).drop 8).drop 8) = fp at H l8
  generalize ((((((((y.drop S).drop 8).drop 48).drop 16).drop 16).drop 8).drop 8).take 8) = l16 at H l7
  generalize (((((((y.drop S).drop 8).drop 48).drop 16).drop 16).drop 8).take 8) = l24 at H l6
  generalize ((((((y.drop S).drop 8).drop 48).drop 16).drop 16).take 8) = l32 at H l5
  generalize (((((y.drop S).drop 8).drop 48).drop 16).take 16) = t30 at H l4
  generalize ((((y.drop S).drop 8).drop 48).take 16) = t40 at H l3
  generalize (((y.drop S).drop 8).take 48) = gap at H l2
  generalize ((y.drop S).take 8) = rs at H l1
  generalize y.take S = sc at H l0
  refine ⟨sc, rs, gap, t40, t30, l32, l24, l16, fp, l0, l1, l2, l3, l4, l5, l6, l7, l8, ?_⟩
  simp only [encoderCalleeFrame] at H
  rw [at_app _ _ (b := aRs) (by rw [l0]; bv_omega) (by simp only [List.length_append, l0, l1, l2, l3, l4, l5, l6, l7, l8]; omega),
    at_app _ _ (b := aRs + 8) (by rw [l1]; rfl) (by simp only [List.length_append, l1, l2, l3, l4, l5, l6, l7, l8]; omega),
    at_app _ _ (b := aRs + 56) (by rw [l2]; bv_omega) (by simp only [List.length_append, l2, l3, l4, l5, l6, l7, l8]; omega),
    at_app _ _ (b := aRs + 72) (by rw [l3]; bv_omega) (by simp only [List.length_append, l3, l4, l5, l6, l7, l8]; omega),
    at_app _ _ (b := aRs + 88) (by rw [l4]; bv_omega) (by simp only [List.length_append, l4, l5, l6, l7, l8]; omega),
    at_app _ _ (b := aRs + 96) (by rw [l5]; bv_omega) (by simp only [List.length_append, l5, l6, l7, l8]; omega),
    at_app _ _ (b := aRs + 104) (by rw [l6]; bv_omega) (by simp only [List.length_append, l6, l7, l8]; omega),
    at_app _ _ (b := aRs + 112) (by rw [l7]; bv_omega) (by simp only [l7, l8]; omega)] at H
  simp only [Std.ExtHashMap.sep_assoc] at H ⊢
  exact H

variable [Host]

/-- **Step: `cmpq $0x0,disp(%rB); jne l` taken**: the 8 bytes at `a = base + disp` hold the pointer `p ≠ 0`; `jl` is the index
of the label `l`. The directives between the `jne` and `l` (the `newobject` branch) are not executed. -/
theorem step_nil_check_taken (rB : Reg64) (disp : Int64) (l : String) (q : Program) (j jl : Nat)
    (hq : q.IsInfixAt Host.prog j) (he : eraseNop q = [instrCompareMemoryImmediate rB disp 0, instrConditionalJump CondCode.nz l])
    (hl : label l = Host.addrOf jl)
    (base a p : BitVec 64) (ha : base + disp.toBitVec = a) (hp : p ≠ 0)
    (F : DataMem → Prop) (final : MachineState → Prop) (s : MachineData)
    (hb : s.regs.get64 rB = base) (hm : (Eq ((Int.toBytes 8 p.toInt).At a) ⋆ F) s.dmem)
    (hk : ∀ fl : StatusFlags, Eventually (step1 Host.exe) final
      ⟨{ regs := s.regs, zmms := s.zmms, status := fl, dmem := s.dmem }, Host.addrOf jl⟩) :
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf j⟩ := by
  subst ha hb
  window_skip_leading_nops hq
  have hd : [instrCompareMemoryImmediate rB disp 0].IsInfixAt Host.prog (j + nonNopIndex q 0) := window_directive_at hq he 0
  unfold instrCompareMemoryImmediate at hd
  apply Machine.eventually_step_directive hd
  unfold_step_keep_registers
  apply load_step_at _ _ (s.regs.get64 rB + disp.toBitVec) _ _ (Int.toBytes 8 p.toInt) _ _ rfl hm (Int.toBytes_length 8 _)
  unfold_step_keep_registers
  rw [Machine.ofInt_ofBytes_toBytes64]
  window_skip_nops hq he 0
  have hd2 : [instrConditionalJump CondCode.nz l].IsInfixAt Host.prog (j + nonNopIndex q 1) := window_directive_at hq he 1
  unfold instrConditionalJump at hd2
  apply Machine.eventually_step_directive hd2
  unfold_step_keep_registers
  rw [if_pos (cmp_zero_nz_true _ _ _ _ hp)]
  simp only [Effects.All]
  rw [hl]
  exact hk _

/-- **Step: `test %r,%r; je l` taken** (`r` = 0): control is at the label `l` (index `jl`). -/
theorem step_test_je_taken (r : Reg64) (l : String) (q : Program) (j jl : Nat) (hq : q.IsInfixAt Host.prog j)
    (he : eraseNop q = [instrTestRegister r, instrConditionalJump CondCode.z l]) (hl : label l = Host.addrOf jl)
    (final : MachineState → Prop) (s : MachineData) (hr : s.regs.get64 r = 0)
    (hk : ∀ fl : StatusFlags, Eventually (step1 Host.exe) final
      ⟨{ regs := s.regs, zmms := s.zmms, status := fl, dmem := s.dmem }, Host.addrOf jl⟩) :
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf j⟩ := by
  window_skip_leading_nops hq
  have hd : [instrTestRegister r].IsInfixAt Host.prog (j + nonNopIndex q 0) := window_directive_at hq he 0
  unfold instrTestRegister at hd
  apply Machine.eventually_step_directive hd
  unfold_step_keep_registers
  rw [hr]
  intro _
  window_skip_nops hq he 0
  have hd2 : [instrConditionalJump CondCode.z l].IsInfixAt Host.prog (j + nonNopIndex q 1) := window_directive_at hq he 1
  unfold instrConditionalJump at hd2
  apply Machine.eventually_step_directive hd2
  unfold_step_keep_registers
  rw [if_pos (test_zero_z_true _ _ _)]
  simp only [Effects.All]
  rw [hl]
  exact hk _

/-- **Encode call block of a nested Checkpoint field**: at `callq fn` (directive `jc`) with `rax` = the object `po`,
`rbx` = the `dst` pointer `d`, `rcx` = the length `m`, `rdi` = the capacity `cap`, and rsp = `sp`.
The callee frame is at fixed addresses below the return slot `sp − 8`; its scratch is at `aLo`.
The 40 bytes of the object (the epoch and the root) are written at `d + m`; control is at `jc + 1` with
`(d, m + 40, cap, nil)`; the object, the root, the prefix and the frame `R` are unchanged. -/
theorem encode_nested_checkpoint_call (fn : String) (S : Nat) (hC : NestedCheckpointCalleeEncode fn S)
    (jc : Nat) (hc : (callNestedEncoder fn).IsInfixAt Host.prog jc)
    (sp po pr d m cap m40 : BitVec 64) (hm40 : m + 40 = m40)
    (aRet aFp aS2 aL16 aL24 aL32 aT30 aT40 aT aRs aLo aD0 aD1 : BitVec 64)
    (hRet : sp - 8 = aRet) (hFp : sp - 16 = aFp) (hS2 : sp + 8 = aS2) (hL16 : sp - 24 = aL16)
    (hL24 : sp - 32 = aL24) (hL32 : sp - 40 = aL32) (hT30 : sp - 56 = aT30) (hT40 : sp - 72 = aT40)
    (hT : sp - 64 = aT) (hRs : sp - 128 = aRs) (hLo : sp - 128 - BitVec.ofNat 64 S = aLo)
    (hD0 : d + m = aD0) (hD1 : d + m + 8 = aD1)
    (guard : UInt64) (hg : guard.toNat < (sp - 8).toNat) (hsp : 120 ≤ (sp - 8).toNat)
    (hcap : m.toNat + 40 ≤ cap.toNat) (hcap63 : cap.toNat < 2 ^ 63)
    (cst e8 cC ctl root pre d0 d1 rslot fp s2 l16 l24 l32 t30 t40 rs scratch : List UInt8)
    (hcst : cst.length = 8) (he8 : e8.length = 8) (hcC : cC.length = 8) (hctl : ctl.length = 32)
    (hroot : root.length = 32) (hpre : pre.length = m.toNat) (hd0 : d0.length = 8) (hd1 : d1.length = 32)
    (hrslot : rslot.length = 8) (hfp : fp.length = 8) (hs2 : s2.length = 8) (hl16 : l16.length = 8)
    (hl24 : l24.length = 8) (hl32 : l32.length = 8) (ht30 : t30.length = 16) (ht40 : t40.length = 16)
    (hrs : rs.length = 8) (hsc : scratch.length = S)
    (R : DataMem → Prop) (s : MachineData)
    (hrsp : s.regs.rsp = { toBitVec := sp }) (hrax : s.regs.rax.toBitVec = po) (hrbx : s.regs.rbx.toBitVec = d)
    (hrcx : s.regs.rcx.toBitVec = m) (hrdi : s.regs.rdi.toBitVec = cap)
    (h_mem : s.dmem =⋆ Eq (rslot.At aRet) ⋆ Eq (fp.At aFp) ⋆ Eq (s2.At aS2) ⋆ Eq (l16.At aL16)
      ⋆ Eq (l24.At aL24) ⋆ Eq (l32.At aL32) ⋆ Eq (t30.At aT30) ⋆ Eq (t40.At aT40) ⋆ Eq (rs.At aRs)
      ⋆ Eq (scratch.At aLo) ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (cst.At po) ⋆ Eq (e8.At (po + 8)) ⋆ Eq ((Int.toBytes 8 pr.toInt).At (po + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (po + 24)) ⋆ Eq (cC.At (po + 32)) ⋆ Eq (ctl.At (po + 40)) ⋆ Eq (root.At pr)
      ⋆ Eq (pre.At d) ⋆ Eq (d0.At aD0) ⋆ Eq (d1.At aD1) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (jc + 1) ∧ st.data.regs.rax.toBitVec = d ∧ st.data.regs.rbx.toBitVec = m40
        ∧ st.data.regs.rcx.toBitVec = cap ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = { toBitVec := sp } ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (t u scr rs' : List UInt8), t.length = 8 ∧ u.length = 16 ∧ scr.length = S ∧ rs'.length = 8 ∧
        (Eq ((Int.toBytes 8 (Host.addrOf (jc + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At aFp) ⋆ Eq ((Int.toBytes 8 d.toInt).At aS2)
          ⋆ Eq ((Int.toBytes 8 d.toInt).At aL16) ⋆ Eq ((Int.toBytes 8 cap.toInt).At aL24)
          ⋆ Eq ((Int.toBytes 8 m40.toInt).At aL32) ⋆ Eq (u.At aT30) ⋆ Eq (e8.At aT40) ⋆ Eq (t.At aT)
          ⋆ Eq (rs'.At aRs) ⋆ Eq (scr.At aLo) ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (cst.At po) ⋆ Eq (e8.At (po + 8)) ⋆ Eq ((Int.toBytes 8 pr.toInt).At (po + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (po + 24)) ⋆ Eq (cC.At (po + 32)) ⋆ Eq (ctl.At (po + 40)) ⋆ Eq (root.At pr)
          ⋆ Eq (pre.At d) ⋆ Eq (e8.At aD0) ⋆ Eq (root.At aD1) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf jc⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp hrax hrbx hrcx hrdi h_mem ⊢
  subst rsp hrax hrbx hrcx hrdi hRet hFp hS2 hL16 hL24 hL32 hT30 hT40 hT hRs hLo hD0 hD1 hm40
  have hcall := hc
  unfold callNestedEncoder at hcall
  apply Machine.eventually_step_directive hcall
  clear hcall
  unfold_step
  apply store_step_at _ _ (sp - 8) _ _ _ rslot _ _ (by segment_addr) (by ecancel) (by exact hrslot)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  unfold_step
  try rw [show sp - 8#64 = sp - 8 from rfl] at *
  rw [show jc + 0 + 1 = jc + 1 from rfl] at H1
  refine eventually_trans _ _ _ _ (hC _ (Host.addrOf (jc + 1)) guard pr cst e8 cC ctl root pre d0 d1 fp s2
    l16 l24 l32 t40 t30 rs scratch _ hcst he8 hcC hctl hroot hd0 hd1 hpre hfp hs2 hl16 hl24 hl32 ht40 ht30 hrs hsc
    hg hsp hcap hcap63
    (by
      dsimp only
      rw [show sp - 8 - 8 = sp - 16 by segment_addr, show sp - 8 + 16 = sp + 8 by segment_addr,
        show sp - 8 - 16 = sp - 24 by segment_addr, show sp - 8 - 24 = sp - 32 by segment_addr,
        show sp - 8 - 32 = sp - 40 by segment_addr, show sp - 8 - 48 = sp - 56 by segment_addr,
        show sp - 8 - 64 = sp - 72 by segment_addr, show sp - 8 - 120 = sp - 128 by segment_addr]
      ecancel)) ?_
  rintro ⟨d5, pc5⟩ ⟨hpc5, hrax5, hrbx5, hrcx5, hrdi5, hrsi5, hrsp5, hrbp5, hr145, t, u, scr, rs', ht, hu, hscr, hrs',
    Hm5⟩
  dsimp only at hpc5 hrax5 hrbx5 hrcx5 hrdi5 hrsi5 hrsp5 hrbp5 hr145 Hm5
  apply Eventually.done
  refine ⟨hpc5, by rw [hrax5], nested_length_after_call _ _ _ hrbx5 hcap hcap63, by rw [hrcx5], hrdi5, hrsi5,
    ?_, hrbp5, hr145, t, u, scr, rs', ht, hu, hscr, hrs', ?_⟩
  · rw [hrsp5]; apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
  · rw [show sp - 8 - 8 = sp - 16 by segment_addr, show sp - 8 + 16 = sp + 8 by segment_addr,
      show sp - 8 - 16 = sp - 24 by segment_addr, show sp - 8 - 24 = sp - 32 by segment_addr,
      show sp - 8 - 32 = sp - 40 by segment_addr, show sp - 8 - 48 = sp - 56 by segment_addr,
      show sp - 8 - 64 = sp - 72 by segment_addr, show sp - 8 - 56 = sp - 64 by segment_addr,
      show sp - 8 - 120 = sp - 128 by segment_addr] at Hm5
    ecancel

end Codec
