import Runtime.Contracts
import Machine.Frame
import Machine.Bytes
import Prysm.ElfData.PrysmTarget

/-!
# Size reject of the hand `uint64` decoders: address and memory facts

The size reject path of `(*primitives.Epoch).UnmarshalSSZ` and `(*primitives.ValidatorIndex).UnmarshalSSZ` returns
`fmt.Errorf("expected buffer of length %d received %d", ...)`.
The two decoders have the same frame, so their proofs use these facts:
- `uint64_reject_eight_bytes`, `uint64_reject_format_len`: the static box of `8` and the length of the format string;
- `uint64_reject_eq`: the length check `x - 8 = 0` gives `x = 8`;
- `uint64_reject_call`, `uint64_reject_second_call`, `uint64_reject_ret`: the stack addresses of the two runtime calls;
- `uint64_reject_args`, `uint64_reject_join_spill`: the 32-byte argument array and the spill area as one chunk.
-/

open Machine Runtime
variable [Host]

namespace Codec

theorem uint64_reject_eight_bytes : ElfData.PrysmTarget.boxedEight = Int.toBytes 8 (8 : BitVec 64).toInt := by decide
theorem uint64_reject_format_len : ElfData.PrysmTarget.formatBufferLength.length = 40 := by decide
theorem uint64_reject_eq (x : BitVec 64) (h : x - 8#64 = 0#64) : x = 8 := by bv_omega
theorem uint64_reject_call (x : BitVec 64) : x - 8#64 - 72 - 8#64 = x - 88 := by bv_omega
theorem uint64_reject_second_call (x : BitVec 64) : x - 80 - 8#64 = x - 88 := by bv_omega
theorem uint64_reject_ret (x : BitVec 64) : ({ toBitVec := x - 88 } + 8 : UInt64) = { toBitVec := x - 80 } := by
  apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega

theorem uint64_reject_args (a b c d : List UInt8) (ha : a.length = 8) (hb : b.length = 8) (hc : c.length = 8)
    (hd : d.length = 8) (x : BitVec 64) (X : DataMem → Prop) :
    X ⋆ Eq (a.At x) ⋆ Eq (b.At (x + 8)) ⋆ Eq (c.At (x + 16)) ⋆ Eq (d.At (x + 24))
      = X ⋆ Eq ((a ++ b ++ c ++ d).At x) := by
  rw [at_app (a ++ b ++ c) d (b := x + 24) (by simp [ha, hb, hc] <;> bv_omega) (by simp [ha, hb, hc, hd]),
    at_app (a ++ b) c (b := x + 16) (by simp [ha, hb] <;> bv_omega) (by simp [ha, hb, hc]),
    at_app a b (b := x + 8) (by simp [ha] <;> rfl) (by simp [ha, hb])]
  simp only [Std.ExtHashMap.sep_assoc]

theorem uint64_reject_join_spill (a b : List UInt8) (ha : a.length = 8) (hb : b.length = 32) (x : BitVec 64) (X : DataMem → Prop) :
    X ⋆ Eq (a.At x) ⋆ Eq (b.At (x + 8)) = X ⋆ Eq ((a ++ b).At x) := by
  rw [at_app a b (b := x + 8) (by simp [ha] <;> rfl) (by simp [ha, hb])]
  simp only [Std.ExtHashMap.sep_assoc]

end Codec
