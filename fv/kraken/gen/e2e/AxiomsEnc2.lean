import E2eEnc.SpecRT
import E2eEnc.DescEq
import E2eEnc.Once
import E2eEnc.SpecOnce
import E2eDec.Reject
import E2eDec.Accept
import E2eDec.SpecA
import E2eDec.Compose
import E2eDec.WitA
import E2eDec.WitR

/-! ENC2 hand list for `gen/e2e/encaxioms_gate2.py` ("must exist" names; every name also gets the axiom check). -/

#print axioms E2eEnc.dc_e2e_spec_roundtrip
#print axioms E2eEnc.dc_e2e_spec_roundtrip'
#print axioms E2eEnc.pdc_roundtrip
#print axioms E2eEnc.pdc_spec_accepts_iff
#print axioms E2eEnc.prysmDcDesc_deserialize_checker
#print axioms E2eEnc.dcg_iter
#print axioms E2eEnc.dcg_loop
#print axioms E2eEnc.dcg_tail
#print axioms E2eEnc.dc_e2e_marshal_once_main
#print axioms E2eEnc.dc_e2e_marshal_once_spec
#print axioms E2eDec.dcd_e2e_reject_size_main
#print axioms E2eDec.dcd_e2e_reject_offset_main
#print axioms E2eDec.dcd_iter
#print axioms E2eDec.dcd_loop
#print axioms E2eDec.dcd_e2e_accept_main
#print axioms E2eDec.dcd_e2e_accept_spec
#print axioms E2eDec.dc_e2e_unmarshal_then_marshal_s
#print axioms E2eDec.WitA.dcd_accept_runs
#print axioms E2eDec.WitR.D1.dcd_rsize_runs
#print axioms E2eDec.WitR.D2.dcd_roff_runs
