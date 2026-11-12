import E2eAd.Spec
import E2eAd.Prims
import E2eAd.WitSl
import E2eAd.WitCi
import E2eAd.WitCpSpecs
import E2eAd.WitCpMS
import E2eAd.AdSpecK
import E2eAd.WitAdA
import E2eAd.WitAdR

-- AttestationData set: every theorem of the E2eAd closure that the report names.
#print axioms E2e.prysmAdDesc_checker
#print axioms E2e.prysmAdDesc_serialize_checker
#print axioms E2e.prysmAdDesc_deserialize_checker
#print axioms E2e.pad_serialize
#print axioms E2e.pad_roundtrip
#print axioms E2e.pad_spec_accepts_iff
#print axioms E2e.pad_spec_rejects
#print axioms E2eAd.sl_unmarshal_accept_main
#print axioms E2eAd.sl_uacc_holds
#print axioms E2eAd.ci_unmarshal_accept_main
#print axioms E2eAd.ci_uacc_holds
#print axioms E2eAd.WitSl.sl_accept_runs
#print axioms E2eAd.WitSl.sl_spec_here
#print axioms E2eAd.WitCi.ci_accept_runs
#print axioms E2eAd.WitCi.ci_spec_here
#print axioms E2eAd.cp_uacc_holds
#print axioms E2eAd.cp_macc_holds
#print axioms E2eAd.WitCpSpecs.cpu_spec_here
#print axioms E2eAd.WitCpMS.cpm_spec_here
#print axioms E2eAd.ad_e2e_head
#print axioms E2eAd.ad_e2e_root
#print axioms E2eAd.ad_e2e_src
#print axioms E2eAd.ad_e2e_tgt
#print axioms E2eAd.ad_e2e_accept_main
#print axioms E2eAd.ad_e2e_reject_size_main
#print axioms E2eAd.ad_e2e_slot_err_unreachable
#print axioms E2eAd.ad_e2e_ci_err_unreachable
#print axioms E2eAd.ad_e2e_source_err_unreachable
#print axioms E2eAd.ad_e2e_target_err_unreachable
#print axioms E2eAd.ad_e2e_accept_spec_k
#print axioms E2eAd.ad_e2e_reject_size_spec
#print axioms E2eAd.ad_e2e_reject_complete
#print axioms E2eAd.bump_newobject72
#print axioms E2eAd.WitAdA.ad_accept_runs
#print axioms E2eAd.WitAdR.ad_reject_runs
