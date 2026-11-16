import Prysm.Slot.DecodeAccept
import Prysm.Slot.WitnessDecodeAccept
import Prysm.Slot.Uint64DecoderKindSameAsHand

/-! Hand list of the `Slot` declarations for `gen/checks/axioms_gate.py`.
Each name must be in the declaration dump and use only the standard axioms. -/

#print axioms Prysm.Slot.Decode.accept
#print axioms Prysm.Slot.Decode.accept_function_spec_holds
#print axioms Prysm.Slot.Witness.DecodeAccept.runs
#print axioms Prysm.Slot.Witness.DecodeAccept.runs_function_spec
#print axioms Prysm.Slot.Decode.accept_kind_anchor
