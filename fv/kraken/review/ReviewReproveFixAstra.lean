import Fk
open Fk Fk.Code Fk.W Fv1 EthLib.Serialization.Ssz
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace ReviewReproveFixAstra

theorem nine_not_false (S : Nat) (ty : BitVec 64) :
    ¬ (@Fk.Regress.Joint S ty → False) := Fk.Regress.not_joint_false S ty

theorem bitlist_bad_2049 : ¬ blValid (List.replicate 256 0 ++ [2]) := by
  rw [blValid, blValid_iff]; simp [blArith]

theorem pad_derived : @VbvPadC Fk.WitVbvR.host (@bumpHeap Fk.WitVbvR.host) 0 := by
  letI := Fk.WitVbvR.host
  exact vbv_pad_holds 5 Fk.WitVbvR.hk_target Fk.WitVbvR.hf_target bumpHeap 0
    (rt_errorf_nil 78 Fk.WitVbvR.hk_rterr Fk.WitVbvR.hf_rterr 0)
    (bump_newobject16 89 Fk.WitVbvR.hk_newobject Fk.WitVbvR.hf_newobject _)

theorem lc_four_runs (z : RegZmms) (f : StatusFlags) :
    @Eventually MachineState (step1 (@Host.exe Fk.WitLcA4.host))
      (fun st => st.pc = 0 ∧ st.data.regs.rax = 0)
      ⟨Fk.WitLcA4.s0 z f, @Host.addrOf Fk.WitLcA4.host 5⟩ :=
  Fk.WitLcA4.lc_accept_runs z f

theorem update_exists (m : DataMem) (a : BitVec 64) (ra ra2 : UInt64) :
    ∃ m2 : DataMem, ∀ F : DataMem → Prop,
      (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At a) ⋆ F) m →
      (Eq ((Int.toBytes 8 ra2.toBitVec.toInt).At a) ⋆ F) m2 := by
  refine ⟨m.storeInt a 8 ra2.toBitVec.toInt, ?_⟩
  intro F h
  exact Mem.storeInt_sep a 8 _ F m ⟨h, Int.toBytes_length 8 _⟩ _

-- Shared rodata cannot be owned twice with the current separating conjunction.
theorem duplicate_byte_impossible (m : DataMem) (a : BitVec 64) (v : UInt8) :
    ¬ (Eq ([v].At a) ⋆ Eq ([v].At a)) m := by
  rintro ⟨m1, m2, _, hd, rfl, rfl⟩
  have hm : a ∈ [v].At a := (mem_At_iff [v] a a).mpr ⟨0, by simp, by simp⟩
  have hn := Std.ExtHashMap.eq_empty_iff_forall_not_mem.mp hd a
  apply hn
  simpa only [Std.ExtHashMap.inter_eq, Std.ExtHashMap.mem_inter_iff] using And.intro hm hm

-- Scalars occupies 24 bytes in the pinned amd64 Go build.
theorem sc_object_short : Fk.WitScA.block.length = 57 := by decide
theorem sc_output_overlaps_object (z : RegZmms) (f : StatusFlags) :
    (Fk.WitScM.s0 z f).regs.rbx.toNat < (Fk.WitScM.s0 z f).regs.rax.toNat + 24 ∧
    (Fk.WitScM.s0 z f).regs.rax.toNat < (Fk.WitScM.s0 z f).regs.rbx.toNat + 16 := by
  simp only [Fk.WitScM.s0]
  decide

theorem ne_objects_overlap :
    0x10091 < (0x10080 : Nat) + 24 := by decide

#print axioms nine_not_false
#print axioms pad_derived
#print axioms lc_four_runs
#print axioms update_exists
#print axioms duplicate_byte_impossible
#print axioms sc_object_short
#print axioms sc_output_overlaps_object
#print axioms Fk.WitLcM4.lc_marshal_runs
#print axioms Fk.WitLcS4.lc_size_runs
#print axioms Fk.WitNeS16.ne_size_runs
#print axioms Fk.WitLuG.lum_grow_runs
#print axioms Fk.WitVbvR.vbv_reject_pad_runs
end ReviewReproveFixAstra
