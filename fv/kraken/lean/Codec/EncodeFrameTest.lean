import Codec.EncodeFieldHelpers

/-!
# The frame test in the epilogue of three encoders (`runtime.moveSliceNoCapNoScan` is not reached)

`PowBlock`, `HistoricalSummary` and `SigningData` `MarshalSSZTo` end with

    mov 0x48(%rsp),%rbx; mov %rbx,%rdx; sub %rsp,%rdx; lea 0x60(%rsp),%rsi; sub %rsp,%rsi; cmp %rsi,%rdx; jb L
    …
    L: mov $0x1,%eax; mov 0x30(%rsp),%rcx; callq runtime.moveSliceNoCapNoScan

The `jb` is taken when the result pointer points into the function's own frame (`ptr − rsp < 0x60`, unsigned).
There is no contract form for `runtime.moveSliceNoCapNoScan`, and none is introduced. On the fast path the
result pointer is the caller's `dst` pointer, and the premise of the fast-path statement separates the output
bytes (`pre` and the output chunks, at least 64 bytes from `ptr`) from the frame slots the function writes.
So the branch is NOT taken, and this is proved here from the separation alone:

* `sep_at_far`: two separated chunks are apart (`ys.length ≤ a − b` and `xs.length ≤ b − a`, as 64-bit
  differences);
* `frame50_ptr_far`: a chunk of at least 64 bytes at `p`, separated from the five 8-byte slots of the frame
  `0x50` that the fast path writes (`x − 40`, `x − 32`, `x − 16`, the saved rbp `x − 8`, the return slot `x`;
  `x` = entry rsp), has `96 ≤ p − (x − 88)`;
* `kstep_sub_rr`: the step `sub %rS,%rD`.
The lemma is for the frame `0x50` with these slots (the three observed functions). Another frame needs its
own instance of the same argument.
-/

open Machine Runtime

namespace Codec

/-- `sub %rS,%rD`. -/
def iSubRR (rD rS : Reg64) : Directive :=
  Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
    (Operation.sub (RegOrMem.reg (Reg.low rD Width.W64)) (Operand.regOrMem (RegOrMem.reg (Reg.low rS Width.W64)))))

/-- **Separated chunks are apart**: the first address of each chunk is outside the other chunk. -/
theorem sep_at_far (xs ys : List UInt8) (a b : BitVec 64) (F : DataMem → Prop) (m : DataMem)
    (h : (Eq (xs.At a) ⋆ Eq (ys.At b) ⋆ F) m) (hx : 0 < xs.length) (hy : 0 < ys.length) :
    ys.length ≤ (a - b).toNat ∧ xs.length ≤ (b - a).toNat := by
  obtain ⟨_, _, _, _, ⟨m1, m2, _, hd, h1, h2⟩, _⟩ := h
  subst h1 h2
  have hne : ∀ k : BitVec 64, ¬ (k ∈ xs.At a ∧ k ∈ ys.At b) := by
    intro k hk
    apply Std.ExtHashMap.eq_empty_iff_forall_not_mem.mp hd k
    rw [Std.ExtHashMap.inter_eq, Std.ExtHashMap.mem_inter_iff]
    exact hk
  refine ⟨?_, ?_⟩
  · apply Nat.le_of_not_lt
    intro hc
    have h_self : BitVec.ofNat 64 (a - b).toNat = a - b := BitVec.eq_of_toNat_eq (Nat.mod_eq_of_lt (BitVec.isLt _))
    exact hne a ⟨(mem_At_iff xs a a).mpr ⟨0, hx, by simp⟩,
      (mem_At_iff ys b a).mpr ⟨(a - b).toNat, hc, by rw [h_self]; bv_omega⟩⟩
  · apply Nat.le_of_not_lt
    intro hc
    have h_self : BitVec.ofNat 64 (b - a).toNat = b - a := BitVec.eq_of_toNat_eq (Nat.mod_eq_of_lt (BitVec.isLt _))
    exact hne b ⟨(mem_At_iff xs a b).mpr ⟨(b - a).toNat, hc, by rw [h_self]; bv_omega⟩,
      (mem_At_iff ys b b).mpr ⟨0, hy, by simp⟩⟩

/-- **Frame test, frame `0x50`**: a chunk of at least 64 bytes at `p` that is separated from the frame slots
`x − 40`, `x − 32`, `x − 16`, `x − 8` and `x` (8 bytes each; `x` = entry rsp) does not start inside the frame
`[x − 88, x + 8)`. -/
theorem frame50_ptr_far (o y1 y2 y3 y4 y5 : List UInt8) (p x : BitVec 64) (F : DataMem → Prop) (m : DataMem)
    (h : (Eq (o.At p) ⋆ Eq (y1.At (x - 40)) ⋆ Eq (y2.At (x - 32)) ⋆ Eq (y3.At (x - 16)) ⋆ Eq (y4.At (x - 8))
      ⋆ Eq (y5.At x) ⋆ F) m)
    (ho : 64 ≤ o.length) (h1 : y1.length = 8) (h2 : y2.length = 8) (h3 : y3.length = 8) (h4 : y4.length = 8)
    (h5 : y5.length = 8) :
    96 ≤ (p - (x - 88)).toNat := by
  have f1 := (sep_at_far o y1 p (x - 40) _ m (by ecancel) (by omega) (by omega)).2
  have f2 := (sep_at_far o y2 p (x - 32) _ m (by ecancel) (by omega) (by omega)).2
  have f3 := (sep_at_far o y3 p (x - 16) _ m (by ecancel) (by omega) (by omega)).2
  have f4 := (sep_at_far o y4 p (x - 8) _ m (by ecancel) (by omega) (by omega)).2
  have f5 := sep_at_far o y5 p x _ m (by ecancel) (by omega) (by omega)
  have g5 := f5.1
  have f5' := f5.2
  rw [h5] at g5
  bv_omega

variable [Host]

/-- **Step: `sub %rS,%rD`**; the status flags after it are not stated (`∀ fl`). -/
theorem kstep_sub_rr (rD rS : Reg64) (q : Program) (j e : Nat) (hq : q.IsInfixAt Host.prog j)
    (he : eraseNop q = [iSubRR rD rS]) (hend : j + q.length = e) (final : MachineState → Prop) (s : MachineData)
    (hk : ∀ fl : StatusFlags, Eventually (step1 Host.exe) final
      ⟨{ regs := s.regs.set64 rD (s.regs.get64 rD - s.regs.get64 rS), zmms := s.zmms, status := fl, dmem := s.dmem },
        Host.addrOf e⟩) :
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf j⟩ := by
  kwin hq
  have hd : [iSubRR rD rS].IsInfixAt Host.prog (j + nopPos q 0) := wat hq he 0
  unfold iSubRR at hd
  apply Machine.estep hd
  kunf
  kwend hq he 0 hend
  exact hk _

end Codec
