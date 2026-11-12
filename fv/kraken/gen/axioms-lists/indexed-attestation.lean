import Prysm.IndexedAttestation.DecodeRejectSize
import Prysm.IndexedAttestation.DecodeSpecReject
import Prysm.IndexedAttestation.DecodeLoop
import Prysm.IndexedAttestation.DecodeAccept
import Prysm.IndexedAttestation.DecodeSpecAccept
import Prysm.IndexedAttestation.SpecEquivalence
import Prysm.RuntimeModel.BumpAllocatorUint64AndStructDispatch
import Prysm.IndexedAttestation.WitnessDecodeAccept
import Prysm.IndexedAttestation.DecodeRejectAlignment
import Prysm.IndexedAttestation.DecodeSpecRejectErrorWordNonzero
import Prysm.IndexedAttestation.WitnessDecodeRejectAlignment
import Prysm.IndexedAttestation.WitnessDecodeRejectSize

/-! Hand list of the IndexedAttestation decoder theorems for `gen/e2e/axioms_gate.py` ("must exist" names;
every name also gets the axiom check). -/

#print axioms Prysm.IndexedAttestation.Decode.reject_size
#print axioms Prysm.IndexedAttestation.Decode.reject_offset
#print axioms Prysm.IndexedAttestation.Decode.reject_size_spec
#print axioms Prysm.IndexedAttestation.Decode.reject_offset_spec
#print axioms Prysm.IndexedAttestation.Decode.reject_cases
#print axioms Prysm.IndexedAttestation.Decode.iter
#print axioms Prysm.IndexedAttestation.Decode.exit
#print axioms Prysm.IndexedAttestation.Decode.loop
#print axioms Prysm.IndexedAttestation.Decode.accept
#print axioms Prysm.IndexedAttestation.Decode.accept_spec
#print axioms Prysm.IndexedAttestation.desc_deserialize_checker
#print axioms Prysm.RuntimeModel.bump_makeslice_uint64_dispatch_size1
#print axioms Prysm.RuntimeModel.bump_makeslice_uint64_dispatch_size8
#print axioms Prysm.RuntimeModel.bump_newobject_struct_dispatch_size72
#print axioms Prysm.RuntimeModel.bump_newobject_struct_dispatch_size96
#print axioms Prysm.IndexedAttestation.Witness.DecodeAccept.runs
#print axioms Prysm.IndexedAttestation.Decode.reject_alignment_error_word_nonzero
#print axioms Prysm.IndexedAttestation.Decode.reject_overflow_error_word_nonzero
#print axioms Prysm.IndexedAttestation.Decode.reject_alignment_spec_error_word_nonzero
#print axioms Prysm.IndexedAttestation.Decode.reject_overflow_spec_error_word_nonzero
#print axioms Prysm.IndexedAttestation.Decode.jg2048_true
#print axioms Prysm.IndexedAttestation.Witness.DecodeRejectAlignment.runs_alignment
#print axioms Prysm.IndexedAttestation.Witness.DecodeRejectAlignment.runs_overflow
#print axioms Prysm.IndexedAttestation.Witness.DecodeRejectSize.runs_size
#print axioms Prysm.IndexedAttestation.Witness.DecodeRejectSize.runs_offset
