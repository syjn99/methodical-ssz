import Codec.Segment.SizeRejectInstances
import Prysm.Deposit.Statements

/-! Deposit size reject from the general lemma `Codec.Segment.rej_size_g` (frame 88, size 1240). Statement: the frozen
`Decode.reject_size_statement`. -/

open Machine Runtime Codec.Segment Prysm.Deposit.Code

namespace Prysm.Deposit

variable [Host]

abbrev Decode.functionSymbol (s : String) : String := "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ" ++ s

theorem Decode.reject_size : Decode.reject_size_statement := by
  intro k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard hlen
  have hle := Machine.label_at' hk hf (j := 31)
    (by simp only [unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  exact rej_size_g 88 1240 (by decide) (by decide) (Decode.functionSymbol "") ("L_" ++ Decode.functionSymbol "_0") ("L_" ++ Decode.functionSymbol "_246")
    ("L_" ++ Decode.functionSymbol "_85") k (k + 9) (k + 31)
    (Codec.infix_sub 0 hk (by simp only [unmarshalSSZ, rejHead, Decode.functionSymbol, List.drop_succ_cons, List.drop_zero,
      List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero, Nat.reduceAdd] <;> first | rfl | decide))
    (glue_of hk (a := 8) (by simp only [unmarshalSSZ, v32Nop, List.getElem?_cons_succ, List.getElem?_cons_zero]))
    (Codec.infix_sub 9 hk (by simp only [unmarshalSSZ, rejCmp, Decode.functionSymbol, List.drop_succ_cons, List.drop_zero,
      List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero] <;> first | rfl | decide))
    (Codec.infix_sub 31 hk (by simp only [unmarshalSSZ, rejErr, Decode.functionSymbol, List.drop_succ_cons, List.drop_zero,
      List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero] <;> first | rfl | decide))
    hle s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard (fun h => hlen (UInt64.toNat_inj.mp (by rw [h]; rfl)))

end Prysm.Deposit
