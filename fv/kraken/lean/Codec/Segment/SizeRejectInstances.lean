import Codec.Segment.SizeReject
import Codec.Segment.Bytes32LoopHistoricalBatch
import Prysm.SyncCommittee.Statements
import Prysm.HistoricalBatch.Statements

/-!
# The SyncCommittee and HistoricalBatch size-reject statements re-derived from `Codec.Segment.rej_size_g`

Each theorem has the frozen statement as its type (`Prysm.SyncCommittee.Decode.reject_size_statement`, `Decode.reject_size_statement`); the proof is one
application of the general lemma with the block facts read from the real program. The hand proofs
(`Prysm/SyncCommittee/DecodeRejectSize.lean`, `Prysm/HistoricalBatch/DecodeRejectSize.lean`) are unchanged.
-/

open Machine Runtime Prysm.HistoricalBatch Prysm.HistoricalBatch.Code

namespace Codec.Segment

variable [Host]

abbrev syncCommitteeSymbol (s : String) : String := "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ" ++ s
abbrev historicalBatchSymbol (s : String) : String := "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ" ++ s

macro "rej_infix" hk:term:max prog:ident a:num tmpl:ident : term => `(Codec.infix_sub $a $hk
  (by simp only [$prog:ident, $tmpl:ident, syncCommitteeSymbol, historicalBatchSymbol, List.drop_succ_cons, List.drop_zero, List.length_cons,
    List.length_nil, List.take_succ_cons, List.take_zero, Nat.reduceAdd] <;> first | rfl | decide))

theorem sync_committee_reject_size : Prysm.SyncCommittee.Decode.reject_size_statement := by
  intro k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard hlen
  have hle := Machine.label_at' hk hf (j := 30)
    (by simp only [Prysm.SyncCommittee.Code.unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [Prysm.SyncCommittee.Code.unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  exact rej_size_g 48 24624 (by decide) (by decide) (syncCommitteeSymbol "") ("L_" ++ syncCommitteeSymbol "_0") ("L_" ++ syncCommitteeSymbol "_206")
    ("L_" ++ syncCommitteeSymbol "_7d") k (k + 9) (k + 30) (rej_infix hk Prysm.SyncCommittee.Code.unmarshalSSZ 0 rejHead)
    (glue_of hk (a := 8) (by simp only [Prysm.SyncCommittee.Code.unmarshalSSZ, v32Nop, List.getElem?_cons_succ, List.getElem?_cons_zero]))
    (rej_infix hk Prysm.SyncCommittee.Code.unmarshalSSZ 9 rejCmp) (rej_infix hk Prysm.SyncCommittee.Code.unmarshalSSZ 30 rejErr) hle s ra guard e0 e1 fp s2 hfp h2 R
    h_mem hguard (fun h => hlen (UInt64.toNat_inj.mp (by rw [h]; rfl)))

theorem historical_batch_reject_size : Decode.reject_size_statement := by
  intro k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard hlen
  have hle := Machine.label_at' hk hf (j := 30)
    (by simp only [unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  exact rej_size_g 56 524288 (by decide) (by decide) (historicalBatchSymbol "") ("L_" ++ historicalBatchSymbol "_0") ("L_" ++ historicalBatchSymbol "_2b0")
    ("L_" ++ historicalBatchSymbol "_7b") k (k + 9) (k + 30) (rej_infix hk unmarshalSSZ 0 rejHead)
    (glue_of hk (a := 8) (by simp only [unmarshalSSZ, v32Nop, List.getElem?_cons_succ, List.getElem?_cons_zero]))
    (rej_infix hk unmarshalSSZ 9 rejCmp) (rej_infix hk unmarshalSSZ 30 rejErr) hle s ra guard e0 e1 fp s2 hfp h2 R
    h_mem hguard (fun h => hlen (UInt64.toNat_inj.mp (by rw [h]; rfl)))

end Codec.Segment
