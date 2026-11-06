import Fk
open Fk Fk.Code Fk.W Fv1 EthLib.Serialization.Ssz
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace ReviewReproveAstra
-- Check the two derived specifications on hosts with the real validator code.
theorem accept_spec_exists : @VbvAccC Fk.WitVbv.host :=
  @vbv_acc_holds Fk.WitVbv.host 5 Fk.WitVbv.hk_target Fk.WitVbv.hf_target

theorem byte_partition (b : UInt8) :
    (∃ v, deserialize bvDesc #[b] = .ok v) ↔ b.toNat < 16 := bv_spec_accepts_iff b

theorem reject_any_padding (b : UInt8) (hb : 16 ≤ b.toNat) (z : RegZmms) (f : StatusFlags) :
    @Eventually MachineState (step1 (@Host.exe Fk.WitBvR.host))
      (fun st => st.pc = 0 ∧ st.data.regs.rax ≠ 0)
      ⟨Fk.WitBvR.s0 b z f, @Host.addrOf Fk.WitBvR.host 5⟩ :=
  Fk.WitBvR.bv_reject_padding_runs b hb z f

theorem bitlist_2047 : blValid (List.replicate 255 0 ++ [255]) := by
  rw [blValid, blValid_iff]; simp [blArith]
theorem bitlist_2048 : blValid (List.replicate 256 0 ++ [1]) := by
  rw [blValid, blValid_iff]; simp [blArith]
theorem bitlist_2049 : ¬ blValid (List.replicate 256 0 ++ [2]) := by
  rw [blValid, blValid_iff]; simp [blArith]
theorem bitlist_empty : blValid [1] ∧ ¬ blValid [] ∧ ¬ blValid [0] := by
  simp [blValid, blValid_iff, blArith]

namespace LcSize
-- A direct witness for the empty case, absent from the submitted inventory.
def P : Program := ListCSizeSSZ
instance host : Host := mkHost P (by decide)
theorem hk : ListCSizeSSZ.IsInfixAt Host.prog 0 := ⟨[], by simp [P, Host.prog]⟩
theorem hf : LabelsFresh ListCSizeSSZ 0 := by intro i h; omega
abbrev bytes (v : Int) := Int.toBytes 8 v
def block : List UInt8 := bytes 0 ++ bytes 196608 ++ bytes 0
def state (z : RegZmms) (f : StatusFlags) : MachineData :=
  ⟨⟨0x20008,0,0,0,0,0,0x20000,0,0,0,0,0,0,0,0,0⟩,z,f,block.At 0x20000⟩
theorem mem_ok (z : RegZmms) (f : StatusFlags) :
    (Eq ((bytes 0).At (state z f).regs.rsp.toBitVec)
      ⋆ Eq ((bytes 196608).At (state z f).regs.rax.toBitVec)
      ⋆ Eq ((bytes 0).At ((state z f).regs.rax.toBitVec + 8)) ⋆ fun _ => True) (state z f).dmem := by
  have h : Eq (block.At (0x20000 : BitVec 64)) (state z f).dmem := rfl
  unfold block at h
  repeat rw [Mem.At_append_sep _ _ _ (by simp [bytes, Int.toBytes_length])] at h
  simp only [List.length_append, Int.toBytes_length, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at h
  apply sep_true (F := Std.ExtHashMap.emp)
  simp only [Std.ExtHashMap.sep_emp]
  simpa [state, bytes] using h
theorem runs (z : RegZmms) (f : StatusFlags) :
    Eventually (step1 Host.exe) (fun st => st.pc = 0 ∧ st.data.regs.rax.toNat = 4)
      ⟨state z f, Host.addrOf 0⟩ := by
  have h := lc_size_main 0 hk hf 0x30000 [] [] rfl (by decide) (by decide) (state z f) 0
    (fun _ => True) (mem_ok z f) (by intro i hi; simp at hi)
  exact eventually_mono h (fun _ h => ⟨h.1, h.2.1⟩)
end LcSize

#print axioms accept_spec_exists
#print axioms reject_any_padding
#print axioms bitlist_2047
#print axioms bitlist_2048
#print axioms bitlist_2049
#print axioms LcSize.runs
end ReviewReproveAstra
