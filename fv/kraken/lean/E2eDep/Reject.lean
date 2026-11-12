import E2eSeg.RejGInst
import E2eDep.Stmt

/-! Deposit size reject from the general lemma `E2eSeg.rej_size_g` (frame 88, size 1240). Statement: the frozen
`dep_reject_size_stmt`. -/

open Fk E2eSeg E2eDep.Code

namespace E2eDep

variable [Host]

abbrev depN (s : String) : String := "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ" ++ s

theorem dep_e2e_reject_size_main : dep_reject_size_stmt := by
  intro k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard hlen
  have hle := Fk.label_at' hk hf (j := 31)
    (by simp only [DepUnmarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [DepUnmarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  exact rej_size_g 88 1240 (by decide) (by decide) (depN "") ("L_" ++ depN "_0") ("L_" ++ depN "_246")
    ("L_" ++ depN "_85") k (k + 9) (k + 31)
    (E2eScal.infix_sub 0 hk (by simp only [DepUnmarshal, rejHead, depN, List.drop_succ_cons, List.drop_zero,
      List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero, Nat.reduceAdd] <;> first | rfl | decide))
    (glue_of hk (a := 8) (by simp only [DepUnmarshal, v32Nop, List.getElem?_cons_succ, List.getElem?_cons_zero]))
    (E2eScal.infix_sub 9 hk (by simp only [DepUnmarshal, rejCmp, depN, List.drop_succ_cons, List.drop_zero,
      List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero] <;> first | rfl | decide))
    (E2eScal.infix_sub 31 hk (by simp only [DepUnmarshal, rejErr, depN, List.drop_succ_cons, List.drop_zero,
      List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero] <;> first | rfl | decide))
    hle s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard (fun h => hlen (UInt64.toNat_inj.mp (by rw [h]; rfl)))

end E2eDep
