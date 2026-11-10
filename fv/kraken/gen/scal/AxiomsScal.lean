import E2eScal.P1Slot
import E2eScal.P2DecAd
import E2eScal.P2EncCp
import E2eScal.GenCi
import E2eScal.GenAdDec
import E2eScal.GenCpDec
import E2eScal.P2EncCpAt

-- prysm-e2e scalability stage S1-S2 (INBOX 011): the segment lemmas, the in-sample re-derivations, the
-- statement-identity checks and the generated instances. Checked with gen/e2e/axioms.py <log> <out> <this file>.
#print axioms E2eScal.infix_sub
#print axioms E2eScal.u64dec_accept
#print axioms E2eScal.rootdec_seg
#print axioms E2eScal.rootenc_seg
#print axioms E2eScal.sl_unmarshal_accept_main_s
#print axioms E2eScal.sl_same_stmt
#print axioms E2eScal.ad_e2e_root_s
#print axioms E2eScal.ad_root_same_stmt
#print axioms E2eScal.cp_e2e_marshal_main_s
#print axioms E2eScal.cp_marshal_same_stmt
#print axioms E2eScal.cp_enc_tmpl_at
#print axioms E2eScal.Gen.ci_unmarshal_accept_main_g
#print axioms E2eScal.Gen.ci_unmarshal_accept_main_g_same
#print axioms E2eScal.Gen.ad_dec_BeaconBlockRoot_seg
#print axioms E2eScal.Gen.cp_dec_Root_seg
