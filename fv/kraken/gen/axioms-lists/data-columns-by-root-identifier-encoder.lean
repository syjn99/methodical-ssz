import Prysm.DataColumnsByRootIdentifier.EncodeFastPath
import Prysm.DataColumnsByRootIdentifier.EncodeGrowFirstSite
import Prysm.DataColumnsByRootIdentifier.EncodeRejectLength
import Prysm.DataColumnsByRootIdentifier.EncodeSpec
import Prysm.DataColumnsByRootIdentifier.EncodeSpecGrowFirstSite
import Prysm.DataColumnsByRootIdentifier.WitnessEncodeFastPath
import Prysm.DataColumnsByRootIdentifier.WitnessEncodeGrowFirstSite
import Prysm.DataColumnsByRootIdentifier.WitnessEncodeRejectLength

/-! Hand list of the DataColumnsByRootIdentifier encoder theorems for `gen/checks/axioms_gate.py` ("must exist" names;
every name also gets the axiom check). -/

#print axioms Prysm.DataColumnsByRootIdentifier.Encode.fast_path
#print axioms Prysm.DataColumnsByRootIdentifier.Encode.grow_first_site
#print axioms Prysm.DataColumnsByRootIdentifier.Encode.reject_length
#print axioms Prysm.DataColumnsByRootIdentifier.Encode.reject_too_big
#print axioms Prysm.DataColumnsByRootIdentifier.Encode.fast_path_spec
#print axioms Prysm.DataColumnsByRootIdentifier.Encode.grow_first_site_spec
#print axioms Prysm.DataColumnsByRootIdentifier.Encode.reject_length_spec
#print axioms Prysm.DataColumnsByRootIdentifier.Encode.reject_too_big_spec
#print axioms Prysm.DataColumnsByRootIdentifier.toValue_serialize
#print axioms Prysm.DataColumnsByRootIdentifier.Encode.iter
#print axioms Prysm.DataColumnsByRootIdentifier.Encode.exit
#print axioms Prysm.DataColumnsByRootIdentifier.Encode.loop
#print axioms Prysm.DataColumnsByRootIdentifier.Encode.tail_fit
#print axioms Prysm.DataColumnsByRootIdentifier.Witness.EncodeFastPath.runs_empty
#print axioms Prysm.DataColumnsByRootIdentifier.Witness.EncodeFastPath.runs_one_element
#print axioms Prysm.DataColumnsByRootIdentifier.Witness.EncodeFastPath.runs_maximum
#print axioms Prysm.DataColumnsByRootIdentifier.Witness.EncodeGrowFirstSite.runs_empty
#print axioms Prysm.DataColumnsByRootIdentifier.Witness.EncodeGrowFirstSite.runs_one_element
#print axioms Prysm.DataColumnsByRootIdentifier.Witness.EncodeGrowFirstSite.runs_maximum
#print axioms Prysm.DataColumnsByRootIdentifier.Witness.EncodeRejectLength.RejectLength.runs
#print axioms Prysm.DataColumnsByRootIdentifier.Witness.EncodeRejectLength.RejectTooBig.runs
