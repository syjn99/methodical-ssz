import Codec.Bytes32Encode
import Prysm.Checkpoint.Code

/-!
# Code placement of the 32-byte field encode template in the Checkpoint encoder (negative-test target)

`Encode.bytes32_template_at` is the template check that `Encode.fast_path_from_bytes32_pattern` (`P2EncCp.lean`) does inside its
proof: the two blocks of `rootEncHead` / `rootEncTail` with the Checkpoint parameters are directives
36–41 and 55–62 of `Prysm.Checkpoint.Code.marshalSSZTo`, and `L_cf` is at k + 55. It exists so that code mutants of
the encode template run inside the negative suite's 300 s case limit (`P2EncCp` builds in about 730 s).
-/

open Machine Runtime TestTarget Prysm.Checkpoint.Code
variable [Host]

open Codec
namespace Prysm.Checkpoint

set_option maxRecDepth 100000 in
theorem Encode.bytes32_template_at (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k) :
    (rootEncHead "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo_108"
      "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo_cf" 16 24).IsInfixAt
        Host.prog (k + 36)
    ∧ (rootEncTail "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo_cf"
      88 80 96).IsInfixAt Host.prog (k + 55)
    ∧ label "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo_cf"
      = Host.addrOf (k + 55) := by
  refine ⟨infix_sub 36 hk ?_, infix_sub 55 hk ?_, Machine.label_at' hk hf (j := 55) ?_ ?_⟩
  · simp only [marshalSSZTo, rootEncHead, List.drop_succ_cons, List.drop_zero, List.length_cons,
      List.length_nil, List.take_succ_cons, List.take_zero]
  · simp only [marshalSSZTo, rootEncTail, List.drop_succ_cons, List.drop_zero, List.length_cons,
      List.length_nil, List.take_succ_cons, List.take_zero]
  · simp only [marshalSSZTo, List.getElem?_cons_succ, List.getElem?_cons_zero] <;> rfl
  · simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide

end Prysm.Checkpoint
