import E2eSeg.RejG
import E2eSeg.V32Hb
import E2eList.StmtSc
import E2eHb.StmtHb

/-!
# The SyncCommittee and HistoricalBatch size-reject statements re-derived from `E2eSeg.rej_size_g`

Each theorem has the frozen statement as its type (`sc_reject_size_stmt`, `hb_reject_size_stmt`); the proof is one
application of the general lemma with the block facts read from the real program. The hand proofs
(`ScReject.lean`, `HbReject.lean`) are unchanged.
-/

open Fk E2eList E2eHb E2eList.Code E2eHb.Code

namespace E2eSeg

variable [Host]

abbrev scN (s : String) : String := "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ" ++ s
abbrev hbN (s : String) : String := "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ" ++ s

macro "rej_infix" hk:term:max prog:ident a:num tmpl:ident : term => `(E2eScal.infix_sub $a $hk
  (by simp only [$prog:ident, $tmpl:ident, scN, hbN, List.drop_succ_cons, List.drop_zero, List.length_cons,
    List.length_nil, List.take_succ_cons, List.take_zero, Nat.reduceAdd] <;> first | rfl | decide))

theorem sc_reject_size_g : sc_reject_size_stmt := by
  intro k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard hlen
  have hle := Fk.label_at' hk hf (j := 30)
    (by simp only [ScUnmarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [ScUnmarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  exact rej_size_g 48 24624 (by decide) (by decide) (scN "") ("L_" ++ scN "_0") ("L_" ++ scN "_206")
    ("L_" ++ scN "_7d") k (k + 9) (k + 30) (rej_infix hk ScUnmarshal 0 rejHead)
    (glue_of hk (a := 8) (by simp only [ScUnmarshal, v32Nop, List.getElem?_cons_succ, List.getElem?_cons_zero]))
    (rej_infix hk ScUnmarshal 9 rejCmp) (rej_infix hk ScUnmarshal 30 rejErr) hle s ra guard e0 e1 fp s2 hfp h2 R
    h_mem hguard (fun h => hlen (UInt64.toNat_inj.mp (by rw [h]; rfl)))

theorem hb_reject_size_g : hb_reject_size_stmt := by
  intro k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard hlen
  have hle := Fk.label_at' hk hf (j := 30)
    (by simp only [HbUnmarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [HbUnmarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  exact rej_size_g 56 524288 (by decide) (by decide) (hbN "") ("L_" ++ hbN "_0") ("L_" ++ hbN "_2b0")
    ("L_" ++ hbN "_7b") k (k + 9) (k + 30) (rej_infix hk HbUnmarshal 0 rejHead)
    (glue_of hk (a := 8) (by simp only [HbUnmarshal, v32Nop, List.getElem?_cons_succ, List.getElem?_cons_zero]))
    (rej_infix hk HbUnmarshal 9 rejCmp) (rej_infix hk HbUnmarshal 30 rejErr) hle s ra guard e0 e1 fp s2 hfp h2 R
    h_mem hguard (fun h => hlen (UInt64.toNat_inj.mp (by rw [h]; rfl)))

end E2eSeg
