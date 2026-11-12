import E2eScal.E1Seg0
import E2eScal.GenE1Dec

/-!
# The generated offset-0 segment gives what the hand lemma gives (generator extension for a 32-byte field at SSZ offset 0)

`E1Seg0.lean` (hand) proved the DepositRoot segment of `Eth1Data.UnmarshalSSZ` with
`E2eScal.E1.rootdec_seg0`. `GenE1Dec.lean` is raw output of the extended generator (`rootdec_seg_z`).
Kernel-checked here: the template definition and the template lemma statement are the hand ones
(`rfl`), and the generated DepositRoot theorem yields, at the instance of `E1Accept.lean` (blocks at
`k + 13`, `k + 26`, the same parameters), exactly the conclusion of the hand lemma (one-line derivation).
`E1Accept.lean` is not changed.
-/

open Machine Runtime TestTarget E2eScal.E1Code

open Codec
namespace E2eScal.E1Gen

/-- The offset-0 template block is the hand block of `E1Seg0.lean`. -/
theorem rootDecMidZ_eq_hand : @Codec.rootDecMidZ = @E2eScal.E1.rootDecMid0 := rfl

/-- The offset-0 template lemma has the statement of the hand lemma. -/
theorem rootdec_seg_z_stmt_eq_hand : type_of% @Codec.rootdec_seg_z = type_of% @E2eScal.E1.rootdec_seg0 := rfl

variable [Host]

set_option linter.unusedVariables false in
/-- The generated DepositRoot theorem gives the conclusion of the hand lemma `rootdec_seg0` at the
instance used by `E1Accept.e1_e2e_accept_main` (`k + 13`, `k + 26`, parameters 48 56 24 8 16 24). -/
theorem e1_dec_DepositRoot_seg_hand (k : Nat) (hk : E1Unmarshal.IsInfixAt Host.prog k)
    (hf : LabelsFresh E1Unmarshal k)
    (hA : (Codec.rootDecHead "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ_75" 48 16 24).IsInfixAt Host.prog (k + 13))
    (hB : (E2eScal.E1.rootDecMid0 "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ_75" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ_b2" 48 56 24 8 16 24).IsInfixAt Host.prog (k + 26))
    (hl : label "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ_75" = Host.addrOf (k + 26)) :
    type_of% (E2eScal.E1.rootdec_seg0 "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ_75" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ_b2" 48 56 24 8 16 24 (k + 13) (k + 26) hA hB hl) :=
  E2eScal.Gen.e1_dec_DepositRoot_seg k hk hf

end E2eScal.E1Gen
