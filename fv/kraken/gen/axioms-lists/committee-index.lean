import Prysm.CommitteeIndex.DecodeAccept
import Prysm.CommitteeIndex.WitnessDecodeAccept
import Prysm.CommitteeIndex.Uint64DecoderKindSameAsHand

/-! Hand list of the `CommitteeIndex` declarations for `gen/checks/axioms_gate.py`.
Each name must be in the declaration dump and use only the standard axioms. -/

#print axioms Prysm.CommitteeIndex.Decode.accept
#print axioms Prysm.CommitteeIndex.Decode.accept_function_spec_holds
#print axioms Prysm.CommitteeIndex.Witness.DecodeAccept.runs
#print axioms Prysm.CommitteeIndex.Witness.DecodeAccept.runs_function_spec
#print axioms Prysm.CommitteeIndex.Decode.accept_kind_anchor
