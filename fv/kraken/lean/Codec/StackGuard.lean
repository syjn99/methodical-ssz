import Machine.Flags

/-!
# Large-frame stack guard: `lea -N(%rsp),%r12; cmp 0x10(%r14),%r12; jbe`

Go functions with a frame above the small-frame limit compare `rsp - N` (not `rsp`) with the stack guard.
After the `lea` and the `cmp` the Kraken state holds the flags of `(rsp + d) - guard`, where `d` is the
two's-complement displacement (`d = -N`). The lemma below states once, over `N`, that the `jbe` is not
taken when `guard + N < rsp`. It is a thin wrapper of `Machine.cmp_be_false` (unchanged): the kernel checks one
application and a `Nat` inequality.

Why a lemma: closing the same fact in the machine context with
`simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega` fails in the kernel under
the memory limit; the costly subterm was not profiled. After `simp` the hypothesis holds `Int` arithmetic on
the literal `2^64 - N`; that this literal is the cost is an inference, not a measurement.

Use (taken branch `h` of the `split` after the `jbe` directive):
`rw [lea_cmp_be_false rsp.toBitVec _ guard.toBitVec _ _ N (by rfl) hguard] at h; exact Bool.noConfusion h`.
-/

namespace Codec

/-- `lea d(%x),%r; cmp g,%r; jbe` is not taken when `g + N < x`, where `d = -N`. `af` and `of'` are
arbitrary: `jbe` reads the carry and zero flags only. -/
theorem lea_cmp_be_false (x d g : BitVec 64) (af of' : Bool) (N : Nat) (hd : (-d).toNat = N)
    (h : g.toNat + N < x.toNat) :
    CondCode.be.interp (StatusFlags.from_result (x + d - g)
      { cf := BitVec.unsigned (x + d - g) != (x + d).unsigned - g.unsigned, af := af, of := of' }) = false := by
  have hs : (x + d).toNat = x.toNat - N := by
    have e : x + d = x - (-d) := by rw [BitVec.sub_eq_add_neg, BitVec.neg_neg]
    rw [e, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega), hd]
  exact Machine.cmp_be_false (x + d) g af of' (by omega)

end Codec
