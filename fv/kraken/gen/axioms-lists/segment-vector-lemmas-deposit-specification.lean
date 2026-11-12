import Codec.Segment.Bytes32VectorSpec
import Codec.Segment.TripleLoopSyncCommittee
import E2eDep.SpecK
import E2eDep.DescEq
import E2eDepW.WitR
import E2eDepW.WitA
import E2eHb.WitHbR

/-! Hand list for `gen/e2e/seg2axioms_gate.py` ("must exist" names; every name gets the axiom check). -/

#print axioms Codec.Segment.vN_serialize
#print axioms Codec.Segment.vN_of_bytes
#print axioms Codec.Segment.vtri_iter
#print axioms Codec.Segment.vtri_exit
#print axioms Codec.Segment.vtri_loop
#print axioms Codec.Segment.sc_loop_g
#print axioms E2eDep.dep_serialize
#print axioms E2eDep.dep_spec_accepts_iff
#print axioms E2eDep.dep_e2e_accept_spec_k
#print axioms E2eDep.dep_e2e_reject_size_spec
#print axioms E2eDep.dep_e2e_reject_complete
#print axioms E2eDep.prysmDepDesc_deserialize_checker
#print axioms E2eDepW.bump_newobject120
#print axioms E2eDepW.WitR.dep_reject_runs
#print axioms E2eDepW.WitA.dep_accept_runs
#print axioms E2eHb.WitHbR.hb_reject_runs
