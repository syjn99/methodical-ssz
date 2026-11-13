import Prysm.DataColumnsByRootIdentifier.DecodeThenEncodeSpec
import Prysm.DataColumnsByRootIdentifier.SpecEquivalence
import Prysm.DataColumnsByRootIdentifier.EncodeGrowOneSite
import Prysm.DataColumnsByRootIdentifier.EncodeSpecGrowOneSite
import Prysm.DataColumnsByRootIdentifier.DecodeRejectSize
import Prysm.DataColumnsByRootIdentifier.DecodeAccept
import Prysm.DataColumnsByRootIdentifier.DecodeSpecAccept
import Prysm.DataColumnsByRootIdentifier.DecodeThenEncode
import Prysm.DataColumnsByRootIdentifier.WitnessDecodeAccept
import Prysm.DataColumnsByRootIdentifier.WitnessDecodeRejectSize

/-! Hand list of the DataColumnsByRootIdentifier decoder, round-trip and one-growth encoder theorems for
`gen/e2e/axioms_gate.py` ("must exist" names; every name also gets the axiom check). -/

#print axioms Prysm.DataColumnsByRootIdentifier.DecodeThenEncode.round_trip_spec
#print axioms Prysm.DataColumnsByRootIdentifier.DecodeThenEncode.round_trip_spec'
#print axioms Prysm.DataColumnsByRootIdentifier.encode_roundtrip
#print axioms Prysm.DataColumnsByRootIdentifier.spec_accepts_iff
#print axioms Prysm.DataColumnsByRootIdentifier.desc_deserialize_checker
#print axioms Prysm.DataColumnsByRootIdentifier.Encode.grow_iter
#print axioms Prysm.DataColumnsByRootIdentifier.Encode.grow_loop
#print axioms Prysm.DataColumnsByRootIdentifier.Encode.grow_tail
#print axioms Prysm.DataColumnsByRootIdentifier.Encode.grow_one_site
#print axioms Prysm.DataColumnsByRootIdentifier.Encode.grow_one_site_spec
#print axioms Prysm.DataColumnsByRootIdentifier.Decode.reject_size
#print axioms Prysm.DataColumnsByRootIdentifier.Decode.reject_offset
#print axioms Prysm.DataColumnsByRootIdentifier.Decode.iter
#print axioms Prysm.DataColumnsByRootIdentifier.Decode.loop
#print axioms Prysm.DataColumnsByRootIdentifier.Decode.accept
#print axioms Prysm.DataColumnsByRootIdentifier.Decode.accept_spec
#print axioms Prysm.DataColumnsByRootIdentifier.DecodeThenEncode.round_trip_scratch_bounded
#print axioms Prysm.DataColumnsByRootIdentifier.Witness.DecodeAccept.runs
#print axioms Prysm.DataColumnsByRootIdentifier.Witness.DecodeRejectSize.RejectSize.runs
#print axioms Prysm.DataColumnsByRootIdentifier.Witness.DecodeRejectSize.RejectOffset.runs
