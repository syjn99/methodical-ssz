import E2eScal.P2Enc
import E2e.Code

/-!
# Code placement of the P2 encode template in the Checkpoint encoder (negative-test target)

`cp_enc_tmpl_at` is the template check that `cp_e2e_marshal_main_s` (`P2EncCp.lean`) does inside its
proof: the two blocks of `rootEncHead` / `rootEncTail` with the Checkpoint parameters are directives
36–41 and 55–62 of `E2e.Code.CpMarshal`, and `L_cf` is at k + 55. It exists so that code mutants of
the encode template run inside the negative suite's 300 s case limit (`P2EncCp` builds in about 730 s).
-/

open Fk E2e.Code
variable [Host]

namespace E2eScal

set_option maxRecDepth 100000 in
theorem cp_enc_tmpl_at (k : Nat) (hk : CpMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh CpMarshal k) :
    (rootEncHead "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo_108"
      "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo_cf" 16 24).IsInfixAt
        Host.prog (k + 36)
    ∧ (rootEncTail "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo_cf"
      88 80 96).IsInfixAt Host.prog (k + 55)
    ∧ label "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo_cf"
      = Host.addrOf (k + 55) := by
  refine ⟨infix_sub 36 hk ?_, infix_sub 55 hk ?_, Fk.label_at' hk hf (j := 55) ?_ ?_⟩
  · simp only [CpMarshal, rootEncHead, List.drop_succ_cons, List.drop_zero, List.length_cons,
      List.length_nil, List.take_succ_cons, List.take_zero]
  · simp only [CpMarshal, rootEncTail, List.drop_succ_cons, List.drop_zero, List.length_cons,
      List.length_nil, List.take_succ_cons, List.take_zero]
  · simp only [CpMarshal, List.getElem?_cons_succ, List.getElem?_cons_zero] <;> rfl
  · simp only [CpMarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide

end E2eScal
