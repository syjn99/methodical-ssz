import E2eList.SaReject
import E2eList.SaAccept
import E2eList.SaSpecK
import E2eList.SaDescEq
import E2eList.WitSaA
import E2eList.ScReject
import E2eList.ScAccept
import E2eList.ScSpecK
import E2eList.ScDescEq
import E2eList.BumpT
import E2eList.WitScA

/-! Hand list for `gen/e2e/lvaxioms_gate.py` ("must exist" names; every name also gets the axiom check). -/

#print axioms E2eList.sa_e2e_reject_size_main
#print axioms E2eList.sa_e2e_accept_main
#print axioms E2eList.sa_e2e_accept_spec_k
#print axioms E2eList.sa_e2e_reject_size_spec
#print axioms E2eList.sa_e2e_reject_complete
#print axioms E2eList.prysmSaDesc_deserialize_checker
#print axioms E2eList.WitSaA.sa_accept_runs
#print axioms E2eList.sc_e2e_reject_size_main
#print axioms E2eList.sc_iter
#print axioms E2eList.sc_loop
#print axioms E2eList.sc_exit
#print axioms E2eList.sc_e2e_accept_main
#print axioms E2eList.sc_e2e_accept_spec_k
#print axioms E2eList.sc_e2e_reject_size_spec
#print axioms E2eList.sc_e2e_reject_complete
#print axioms E2eList.prysmScDesc_deserialize_checker
#print axioms E2eList.bump_makeslice_t1
#print axioms E2eList.bump_makeslice_t24
#print axioms E2eList.WitScA.sc_accept_runs
