import Fk
open Fk Fk.Code Fk.W Fv1 EthLib.Serialization.Ssz
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace ReviewFix2

theorem ten_not_false (S : Nat) (ty : BitVec 64) :
    ¬ (Fk.Regress.Joint S ty blFmtB vblRO VblMsg luFmtTooBig luTW → False) :=
  Fk.Regress.not_joint_false S ty _ _ _ _ _

section
variable [Host]
theorem vbl_message_owned (sp : BitVec 64) (msg hm : List UInt8) (m : DataMem)
    (hi : VblMsg sp msg hm) (hr : (Eq (hm.At sp) ⋆ vblRO) m) :
    ∃ F : DataMem → Prop, (Eq (msg.At sp) ⋆ F) m := by
  rcases hi with ⟨rfl, h⟩ | ⟨rfl, _⟩
  · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨Eq (([] : List UInt8).At (label "go_string._" + 33605).toBitVec) ⋆
        Eq (vblMsgZ.At (label "go_string._" + 13272).toBitVec) ⋆
        Eq (vblMsgB.At (label "go_string._" + 5743).toBitVec), ?_⟩
      unfold vblRO at hr
      ecancel
    · refine ⟨Eq (([] : List UInt8).At (label "go_string._" + 13272).toBitVec) ⋆
        Eq (vblMsgE.At (label "go_string._" + 33605).toBitVec) ⋆
        Eq (vblMsgB.At (label "go_string._" + 5743).toBitVec), ?_⟩
      unfold vblRO at hr
      ecancel
    · refine ⟨Eq (([] : List UInt8).At (label "go_string._" + 5743).toBitVec) ⋆
        Eq (vblMsgE.At (label "go_string._" + 33605).toBitVec) ⋆
        Eq (vblMsgZ.At (label "go_string._" + 13272).toBitVec), ?_⟩
      unfold vblRO at hr
      ecancel
  · exact ⟨vblRO, hr⟩

theorem bv_message_owned (sp : BitVec 64) (msg hm : List UInt8) (m : DataMem)
    (hi : BvMsg sp msg hm) (hr : (Eq (hm.At sp) ⋆ bvRO) m) :
    ∃ F : DataMem → Prop, (Eq (msg.At sp) ⋆ F) m := by
  rcases hi with ⟨rfl, rfl, rfl⟩
  exact ⟨Eq (([] : List UInt8).At (label "go_string._" + 27706).toBitVec), by unfold bvRO at hr; ecancel⟩
end

-- An existing rejection witness returns nil on an EthLib-invalid input.
theorem bool_two_returns_nil (z : RegZmms) (f : StatusFlags) :
    Eventually (step1 Fk.WitScRB.host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0)
      ⟨Fk.WitScRB.s0 2 z f, Fk.WitScRB.host.addrOf 5⟩ :=
  (Fk.WitScRB.sc_reject_bool_runs 2 (by decide) z f).2

example : 8 + 56 + 20 + 8192 = 8276 := by decide
example : 8 + 68 + 20 + 8192 = 8288 := by decide
example : 8192 + 5 + 128 + 8192 ≤ 16640 := by decide
example : 4 * 8 + 4 * 24 + 4 * 16 * 8 = 640 := by decide
example : [16, 148, 280, 412].map (fun x : Nat => x + 132) = [148, 280, 412, 544] := by decide
example : Fk.WitScA.block.length = 64 := by decide
example : (Fk.WitLuTb.block.drop (105888 - 65536)).take 48 = List.replicate 48 0 := by decide
example : (Fk.WitBlRI.block.drop (99184 - 65536)).take 48 = List.replicate 48 0 := by decide

#print axioms ten_not_false
#print axioms vbl_message_owned
#print axioms bv_message_owned
#print axioms bool_two_returns_nil
#print axioms Fk.WitLcA1x1.lc_accept_runs
#print axioms Fk.WitLcA4x16.lc_accept_runs
#print axioms Fk.WitLcAMix.lc_accept_runs
#print axioms Fk.WitLcM1x1.lc_marshal_runs
#print axioms Fk.WitLcM4x16.lc_marshal_runs
#print axioms Fk.WitLcMMix.lc_marshal_runs
#print axioms Fk.WitLuComp.lu_compose_runs
#print axioms Fk.WitScComp.sc_compose_runs
end ReviewFix2
