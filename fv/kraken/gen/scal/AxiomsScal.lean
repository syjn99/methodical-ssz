import E2eScal.P1Slot
import E2eScal.P2DecAd
import E2eScal.P2EncCp
import E2eScal.GenCi
import E2eScal.GenAdDec
import E2eScal.GenCpDec
import E2eScal.P2EncCpAt
import E2eScal.Kind
import E2eScal.KindAnchor
import E2eScal.WitVi
import E2eScal.BhSpecK
import E2eScal.WitBhA
import E2eScal.WitBhR

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
-- review fix-r1 M2/S1: frozen statement kinds, their lemma ties and anchors, and the generated `_kind` identities
#print axioms E2eScal.u64DecAcceptKind_of
#print axioms E2eScal.rootDecSegKind_of
#print axioms E2eScal.sl_kind_anchor
#print axioms E2eScal.ci_kind_anchor
#print axioms E2eScal.Gen.ci_unmarshal_accept_main_g_kind
#print axioms E2eScal.Gen.ad_dec_BeaconBlockRoot_seg_kind
#print axioms E2eScal.Gen.cp_dec_Root_seg_kind
-- S3 hold-out H1 (evaluation session, after scal/HOLDOUT-OPENED)
#print axioms E2eScal.Gen.vi_unmarshal_accept_main_g
#print axioms E2eScal.Gen.vi_unmarshal_accept_main_g_kind
#print axioms E2eScal.vi_uacc_holds
#print axioms E2eScal.WitVi.vi_wit_mem
#print axioms E2eScal.WitVi.vi_accept_runs
#print axioms E2eScal.WitVi.vi_spec_here
#print axioms E2eScal.Gen.bh_dec_ParentRoot_seg
#print axioms E2eScal.Gen.bh_dec_ParentRoot_seg_kind
#print axioms E2eScal.Gen.bh_dec_StateRoot_seg
#print axioms E2eScal.Gen.bh_dec_StateRoot_seg_kind
#print axioms E2eScal.Gen.bh_dec_BodyRoot_seg
#print axioms E2eScal.Gen.bh_dec_BodyRoot_seg_kind
#print axioms E2eScal.Bh.bh_e2e_head
#print axioms E2eScal.Bh.bh_e2e_accept_main
#print axioms E2eScal.Bh.bh_e2e_reject_size_main
#print axioms E2e.prysmBhDesc_checker
#print axioms E2e.prysmBhDesc_serialize_checker
#print axioms E2e.prysmBhDesc_deserialize_checker
#print axioms E2e.pbh_roundtrip
#print axioms E2e.pbh_spec_accepts_iff
#print axioms E2e.pbh_spec_rejects
#print axioms E2eScal.Bh.bh_e2e_accept_spec_k
#print axioms E2eScal.Bh.bh_e2e_reject_size_spec
#print axioms E2eScal.Bh.bh_e2e_reject_complete
#print axioms E2eScal.WitBhA.bh_accept_runs
#print axioms E2eScal.WitBhR.bh_reject_runs
