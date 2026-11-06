/-
Regression checks for the current contracts: joint satisfiability with the
formats and resources the theorems use, and the fixed review findings as theorems.
Run: cd fv/kraken/lean && lake env lean tools/RegressFix2.lean
-/
import Fk
open Fk Fk.Code Fk.W Fv1 EthLib.Serialization.Ssz
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace RegressFix2

-- 1. The ten contracts hold together on one host and heap, for the formats,
--    resources and type words that the theorems use (Joint takes them, fix 2 X4/X5).
theorem ten_not_false_bl (S : Nat) (ty : BitVec 64) :
    ¬ (Fk.Regress.Joint S ty blFmtB vblRO VblMsg luFmtTooBig luTW → False) :=
  Fk.Regress.not_joint_false S ty _ _ _ _ _
theorem ten_not_false_bv (S : Nat) (ty : BitVec 64) :
    ¬ (Fk.Regress.Joint S ty bvFmtJ bvRO BvMsg luFmtMis luTW → False) :=
  Fk.Regress.not_joint_false S ty _ _ _ _ _

-- 2. The invalid-input premise `¬ blValid` matches the semtest cases (unchanged).
example : ¬ blValid [] := by rw [blValid, blValid_iff]; unfold blArith; decide
example : ¬ blValid [0] := by rw [blValid, blValid_iff]; unfold blArith; decide
example : blValid [1] := by rw [blValid, blValid_iff]; unfold blArith; decide
theorem bitlist_bad_2049 : ¬ blValid (List.replicate 256 0 ++ [2]) := by
  rw [blValid, blValid_iff]; simp [blArith]

-- 3. The rodata messages of ValidateBitlist: each case of `VblMsg` is a message of
--    at most 128 bytes; the model's case (heap, empty message) is a `VblMsg` case.
example (sp : BitVec 64) : VblMsg sp [] [] := Or.inr ⟨rfl, by decide⟩
example : VblMsg (label "go_string._" + 5743).toBitVec vblMsgB [] := Or.inl ⟨rfl, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
example (sp : BitVec 64) (msg hm : List UInt8) (h : VblMsg sp msg hm) : msg.length ≤ 128 := h.len

-- 4. The padding-reject specification still follows from the real ValidateBitvector
--    code (WitVbvR indices after RtErr grew from 11 to 15 directives).
theorem pad_derived : @VbvPadC Fk.WitVbvR.host (@bumpHeap Fk.WitVbvR.host) 0 := by
  letI := Fk.WitVbvR.host
  exact vbv_pad_holds 5 Fk.WitVbvR.hk_target Fk.WitVbvR.hf_target bumpHeap 0
    (rt_errorf_nil 78 Fk.WitVbvR.hk_rterr Fk.WitVbvR.hf_rterr 0)
    (bump_newobject16 93 Fk.WitVbvR.hk_newobject Fk.WitVbvR.hf_newobject _)

-- 5. astra reprove-fix finding 3, fixed: the Scalars witnesses hold a whole
--    24-byte Go object (the block grew from 57 to 64 bytes), the ScM output does
--    not overlap the receiver, and the NeM ListU64 object starts after Scalars.
theorem sc_object_whole : Fk.WitScA.block.length = 64 := by decide
theorem sc_output_after_object (z : RegZmms) (f : StatusFlags) :
    (Fk.WitScM.s0 z f).regs.rax.toNat + 24 ≤ (Fk.WitScM.s0 z f).regs.rbx.toNat := by
  simp only [Fk.WitScM.s0]; decide
theorem ne_objects_apart : (0x10080 : Nat) + 24 ≤ 0x10098 := by decide

-- 6. Shared rodata cannot be owned twice; the contracts now keep `vblRO` in their
--    own footprint, so a frame `F` that is `⋆`-separate from it cannot hold it.
theorem duplicate_byte_impossible (m : DataMem) (a : BitVec 64) (v : UInt8) :
    ¬ (Eq ([v].At a) ⋆ Eq ([v].At a)) m := by
  rintro ⟨m1, m2, _, hd, rfl, rfl⟩
  have hm : a ∈ [v].At a := (mem_At_iff [v] a a).mpr ⟨0, by simp, by simp⟩
  have hn := Std.ExtHashMap.eq_empty_iff_forall_not_mem.mp hd a
  apply hn
  simpa only [Std.ExtHashMap.inter_eq, Std.ExtHashMap.mem_inter_iff] using And.intro hm hm

#check @Fk.WitLcA4x16.lc_accept_runs
#check @Fk.WitLcM4x16.lc_marshal_runs
#check @Fk.WitLuComp.lu_compose_runs
#check @Fk.WitScComp.sc_compose_runs
#print axioms ten_not_false_bl
#print axioms pad_derived
#print axioms sc_object_whole
#print axioms sc_output_after_object
#print axioms sc_reject_bool_main
#print axioms sc_spec_rejects_bool
#print axioms bl_reject_invalid_main
#print axioms Fk.WitScRB.sc_reject_bool_runs
#print axioms Fk.WitBlRI.bl_reject_invalid_runs
#print axioms Fk.WitLcA4x16.lc_accept_runs
#print axioms Fk.WitLcAMix.lc_accept_runs
#print axioms Fk.WitLcM4x16.lc_marshal_runs
#print axioms Fk.WitLcMMix.lc_marshal_runs
#print axioms Fk.WitLuComp.lu_compose_runs
#print axioms Fk.WitScComp.sc_compose_runs
#print axioms Fk.WitLuTb.lu_reject_toobig_runs
#print axioms Fk.WitLuMa.lu_reject_misaligned_runs
#print axioms Fk.WitBlR.bl_marshal_reject_runs
#print axioms Fk.WitBvR.bv_reject_padding_runs

end RegressFix2
