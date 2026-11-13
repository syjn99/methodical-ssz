import Prysm.Eth1Data.DecodeFieldSegmentOffsetZero
import Prysm.Eth1Data.GeneratedDecodeRootFieldSegments

/-!
# The generated offset-0 segment gives what the hand lemma gives (generator extension for a 32-byte field at SSZ offset 0)

`Prysm/Eth1Data/DecodeFieldSegmentOffsetZero.lean` (hand) proved the DepositRoot segment of `Eth1Data.UnmarshalSSZ` with
`Prysm.Eth1Data.rootdec_seg0`. `Prysm/Eth1Data/GeneratedDecodeRootFieldSegments.lean` is raw output of the extended generator (`rootdec_seg_z`).
Kernel-checked here: the template definition and the template lemma statement are the hand ones
(`rfl`), and the generated DepositRoot theorem yields, at the instance of `Prysm/Eth1Data/DecodeAccept.lean` (blocks at
`k + 13`, `k + 26`, the same parameters), exactly the conclusion of the hand lemma (one-line derivation).
`Prysm/Eth1Data/DecodeAccept.lean` is not changed.
-/

open Machine Runtime Prysm.Eth1Data.Code

open Codec
namespace Prysm.Eth1Data

/-- The offset-0 template block is the hand block of `Prysm/Eth1Data/DecodeFieldSegmentOffsetZero.lean`. -/
theorem rootDecMidZ_eq_hand : @Codec.rootDecMidZ = @Prysm.Eth1Data.rootDecMid0 := rfl

/-- The offset-0 template lemma has the statement of the hand lemma. -/
theorem rootdec_seg_z_stmt_eq_hand : type_of% @Codec.rootdec_seg_z = type_of% @Prysm.Eth1Data.rootdec_seg0 := rfl

variable [Host]

set_option linter.unusedVariables false in
/-- The generated DepositRoot theorem gives the conclusion of the hand lemma `rootdec_seg0` at the
instance used by ``Prysm/Eth1Data/DecodeAccept.lean`.e1_e2e_accept_main` (`k + 13`, `k + 26`, parameters 48 56 24 8 16 24). -/
theorem Decode.dec_DepositRoot_seg_hand (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh unmarshalSSZ k)
    (hA : (Codec.rootDecHead "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ_75" 48 16 24).IsInfixAt Host.prog (k + 13))
    (hB : (Prysm.Eth1Data.rootDecMid0 "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ_75" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ_b2" 48 56 24 8 16 24).IsInfixAt Host.prog (k + 26))
    (hl : label "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ_75" = Host.addrOf (k + 26)) :
    type_of% (Prysm.Eth1Data.rootdec_seg0 "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ_75" "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ_b2" 48 56 24 8 16 24 (k + 13) (k + 26) hA hB hl) :=
  Prysm.Eth1Data.Decode.generated_root_DepositRoot_seg k hk hf

end Prysm.Eth1Data
