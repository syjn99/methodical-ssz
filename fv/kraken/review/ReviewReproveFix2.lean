/-
Claude re-check of the re-proof fix 2 session (tip 7152188). Read-only checks:
contract satisfiability with the real arguments, rodata disjointness, the
EthLib side of the new Scalars reject path, conclusions of the new theorems,
and the axioms of every new declaration the report names.
Run: cd fv/kraken/lean && lake env lean <this file>
-/
import Fk
open Fk Fk.Code Fk.W Fv1 EthLib.Serialization.Ssz
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace ReviewFix2

-- 1. Joint satisfiability with exactly the arguments the theorems pass.
example (S : Nat) (ty : BitVec 64) : Fk.Regress.Joint S ty blFmtB vblRO VblMsg luFmtTooBig luTW :=
  Fk.Regress.joint_models S ty _ _ _ _ _
example (S : Nat) (ty : BitVec 64) : Fk.Regress.Joint S ty bvFmtJ bvRO BvMsg luFmtMis luTW :=
  Fk.Regress.joint_models S ty _ _ _ _ _
-- The model satisfies FmtErrorfWC for *every* RO and MsgIn, including ones that
-- do not put the message bytes anywhere: the contract does not tie MsgIn to RO.
example (S : Nat) (ty : BitVec 64) : Fk.Regress.Joint S ty [] (fun _ => True) (fun _ _ _ => True) [] 0 :=
  Fk.Regress.joint_models S ty _ _ _ _ _

-- 2. The three rodata messages of vblRO are pairwise disjoint address ranges
--    (so vblRO itself is satisfiable as a separating conjunction).
example : 5743 + vblMsgB.length ≤ 13272 ∧ 13272 + vblMsgZ.length ≤ 33605 := by
  rw [vblMsgB_len, vblMsgZ_len]; decide
-- blFmtB (go_string._+526) does not overlap them either.
example : 526 + blFmtB.length ≤ 5743 := by rw [blFmtB_len]; decide

-- 3. VblMsg: the rodata cases carry the right message; the `%d` case is bounded.
example : VblMsg (label "go_string._" + 33605).toBitVec vblMsgE [] := Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
example : VblMsg (label "go_string._" + 13272).toBitVec vblMsgZ [] := Or.inl ⟨rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
example (sp : BitVec 64) (msg : List UInt8) (h : msg.length ≤ 128) : VblMsg sp msg msg := Or.inr ⟨rfl, h⟩
-- A rodata case cannot claim heap bytes: hm = [] there.
example (sp : BitVec 64) (msg hm : List UInt8) (h : VblMsg sp msg hm) (hr : sp = (label "go_string._" + 33605).toBitVec)
    (hne : msg ≠ hm) : hm = [] := by
  rcases h with ⟨h1, _⟩ | ⟨rfl, _⟩
  · exact h1
  · exact absurd rfl hne

-- 4. Budgets of the new reject theorems are consistent with the contracts they call.
--    bl_reject_invalid_main: 16640 ≤ avail; ValidateBitlistErrC needs 8192 and may
--    consume up to 8192; the following FmtErrorfWC needs blFmtB.length + msg + 8192
--    with msg ≤ 128: 8192 + 5 + 128 + 8192 = 16517 ≤ 16640.
example : 8192 + blFmtB.length + 128 + 8192 ≤ 16640 := by rw [blFmtB_len]; decide

-- 5. The EthLib side of the Scalars bool reject path at a concrete input.
example (v : Value) : deserialize scDesc (([0] ++ [0, 0] ++ [0, 0, 0, 0] ++ [0, 0, 0, 0, 0, 0, 0, 0] ++ [2] : List UInt8)).toArray ≠ .ok v :=
  sc_spec_rejects_bool [0] [0, 0] [0, 0, 0, 0] [0, 0, 0, 0, 0, 0, 0, 0] 2 (by decide) rfl rfl rfl rfl v
-- And the boundary: byte 1 is not rejected by this theorem (premise 1 < e fails).
example : ¬ (1 < (1 : UInt8).toNat) := by decide

-- 6. BoxIn: a value < 256 is boxed in the static table, larger values on the heap.
example : BoxIn ((label "runtime.staticuint64s").toBitVec + 8 * 5) 5 [] := Or.inl ⟨rfl, by decide, rfl⟩
example (bx : BitVec 64) : BoxIn bx 300 (Int.toBytes 8 (300 : BitVec 64).toInt) := Or.inr rfl

-- 7. Shapes of the new conclusions (read in the output).
#check @sc_reject_bool_main
#check @bl_reject_invalid_main
#check @sc_unmarshal_then_marshal
#check @lu_unmarshal_then_marshal
#check @Fk.WitScComp.sc_compose_runs
#check @Fk.WitLuComp.lu_compose_runs

-- 8. Axioms.
#print axioms Fk.Regress.joint_models
#print axioms sc_reject_bool_main
#print axioms sc_spec_rejects_bool
#print axioms bl_reject_invalid_main
#print axioms sc_unmarshal_then_marshal
#print axioms lu_unmarshal_then_marshal
#print axioms sc_marshal_main
#print axioms lc_accept_main
#print axioms bl_accept_main
#print axioms ne_accept_main
#print axioms lu_reject_toobig_main
#print axioms lu_reject_misaligned_main
#print axioms bl_marshal_reject_main
#print axioms bv_reject_padding_main
#print axioms Fk.WitScRB.sc_reject_bool_runs
#print axioms Fk.WitBlRI.bl_reject_invalid_runs
#print axioms Fk.WitLcA1x1.lc_accept_runs
#print axioms Fk.WitLcA4x16.lc_accept_runs
#print axioms Fk.WitLcAMix.lc_accept_runs
#print axioms Fk.WitLcM1x1.lc_marshal_runs
#print axioms Fk.WitLcM4x16.lc_marshal_runs
#print axioms Fk.WitLcMMix.lc_marshal_runs
#print axioms Fk.WitLuComp.lu_compose_runs
#print axioms Fk.WitScComp.sc_compose_runs
#print axioms Fk.WitLuTb.lu_reject_toobig_runs
#print axioms Fk.WitLuMa.lu_reject_misaligned_runs
#print axioms Fk.WitBlR.bl_marshal_reject_runs
#print axioms Fk.WitScA.sc_accept_runs
#print axioms Fk.WitScM.sc_marshal_runs

end ReviewFix2
