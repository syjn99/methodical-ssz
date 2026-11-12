import E2eSeg.ListGInst
import E2eSeg.SegGInst
import E2eSeg.V32Hb
import E2eSeg.RejGInst
import E2eDep.Reject
import E2eDep.Accept

/-! SEG hand list for `gen/e2e/segaxioms_gate.py` ("must exist" names; every name also gets the axiom check). -/

#print axioms E2eSeg.flat_len
#print axioms E2eSeg.in_split
#print axioms E2eSeg.arr_split
#print axioms E2eSeg.arr_join
#print axioms E2eSeg.scIn_split'
#print axioms E2eSeg.hbA_join'
#print axioms E2eSeg.bytesdec_seg_g
#print axioms E2eSeg.bytesdec_seg_z_g
#print axioms E2eSeg.bytesdec_seg_nop_g
#print axioms E2eSeg.bytesdec_seg_inst
#print axioms E2eSeg.bytesdec_seg_z_inst
#print axioms E2eSeg.bytesdec_seg_z64_inst
#print axioms E2eSeg.bytes96dec_seg_nop_inst
#print axioms E2eSeg.bytes32dec_seg_nop_inst
#print axioms E2eSeg.glue_nop
#print axioms E2eSeg.glue_src
#print axioms E2eSeg.v32_iter
#print axioms E2eSeg.v32_exit
#print axioms E2eSeg.v32_loop
#print axioms E2eSeg.hb_loop1_g
#print axioms E2eSeg.hb_loop2_g
#print axioms E2eSeg.rej_size_g
#print axioms E2eSeg.sc_reject_size_g
#print axioms E2eSeg.hb_reject_size_g
#print axioms E2eDep.dep_e2e_reject_size_main
#print axioms E2eDep.dep_e2e_accept_main
