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
import E2eScal.WitBhU
import E2eScal.WitViR
import E2eScal.E1SpecK
import E2eScal.WitE1A
import E2eScal.WitE1R
import E2eScal.BhSpecM
import E2eScal.WitBhM
import E2eScal.BhEncBlock
import E2eScal.E1SpecM
import E2eScal.WitE1M
import E2eScal.WitBhMR
import E2eScal.P2DecZ
import E2eScal.KindZ
import E2eScal.GenE1Dec
import E2eScal.E1GenSame
import E2eScal.BiSpecK
import E2eScal.WitBiA
import E2eScal.WitBiR
import E2eScal.DmSpecK
import E2eScal.WitDmA
import E2eScal.WitDmR
import E2eScal.GenBiDec
import E2eScal.GenDmDec
import E2eScal.SegN
import E2eScal.KindN
import E2eScal.SegNRel
import E2eScal.U64Inline
import E2eScal.KindU64
import E2eScal.Compose
import E2eScal.Gen2Examples
import E2eScal.Gen2ComposeEx
import E2eScal.Gen2E1Dec
import E2eScal.Gen2BiDec
import E2eScal.Gen2DmDec
import E2eScal.BiAcceptG2
import E2eScal.DmAcceptG2
import E2eScal.Gen2BiAccept
import E2eScal.Gen2DmAccept
import E2eScal.Gen2E1Accept
import E2eScal.Gen2BhDecPartial
import E2eScal.H4Stmt
import E2eScal.Gen2DdDecPartial
import E2eScal.DdSpecK
import E2eScal.WitDdA
import E2eScal.WitDdR
import E2eScal.PwSpecK
import E2eScal.WitPwR

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
#print axioms E2eScal.Bh.bh_e2e_slot_err_unreachable
#print axioms E2eScal.Bh.bh_e2e_vi_err_unreachable
#print axioms E2eScal.WitBhU.bh_unreach_runs
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
#print axioms E2eScal.vi_unmarshal_reject_len_main
#print axioms E2eScal.WitViR.vir_runs
#print axioms E2eScal.WitViR.L9.vir_runs9
#print axioms E2eScal.WitViR.L300.vir_runs300
-- H2 hold-out (session 13): Eth1Data decoder; no generated theorem (the generator run emitted nothing)
#print axioms E2eScal.E1.rootdec_seg0
#print axioms E2eScal.E1.e1_e2e_head
#print axioms E2eScal.E1.e1_e2e_accept_main
#print axioms E2eScal.E1.e1_e2e_reject_size_main
#print axioms E2e.prysmE1Desc_checker
#print axioms E2e.prysmE1Desc_serialize_checker
#print axioms E2e.prysmE1Desc_deserialize_checker
#print axioms E2e.pe1_roundtrip
#print axioms E2e.pe1_spec_accepts_iff
#print axioms E2e.pe1_spec_rejects
#print axioms E2eScal.E1.e1_e2e_accept_spec_k
#print axioms E2eScal.E1.e1_e2e_reject_size_spec
#print axioms E2eScal.E1.e1_e2e_reject_complete
#print axioms E2eScal.WitE1A.e1_accept_runs
#print axioms E2eScal.WitE1R.e1_reject_runs
-- T-9 (fresh stream, after the H1/H2 hold-out sessions): BeaconBlockHeader encoder, fast path only (hand proof)
#print axioms E2eScal.lea_cmp_be_false
#print axioms E2eScal.Bh.bh_enc_a1
#print axioms E2eScal.Bh.bh_enc_a2
#print axioms E2eScal.Bh.bh_enc_b
#print axioms E2eScal.Bh.bh_enc_c
#print axioms E2eScal.Bh.bh_enc_d
#print axioms E2eScal.Bh.bh_enc_e
#print axioms E2eScal.Bh.bh_e2e_marshal_main
#print axioms E2eScal.Bh.bh_e2e_marshal_spec_k
#print axioms E2eScal.WitBhM.bhm_runs_empty
#print axioms E2eScal.WitBhM.bhm_runs_prefix
-- SG-1 extension (offset-0 form; after both hold-outs were opened, Eth1Data = development data)
#print axioms E2eScal.rootdec_seg_z
#print axioms E2eScal.rootDecSegZKind_of
#print axioms E2eScal.Gen.e1_dec_DepositRoot_seg
#print axioms E2eScal.Gen.e1_dec_DepositRoot_seg_kind
#print axioms E2eScal.Gen.e1_dec_BlockHash_seg
#print axioms E2eScal.Gen.e1_dec_BlockHash_seg_kind
#print axioms E2eScal.E1Gen.rootDecMidZ_eq_hand
#print axioms E2eScal.E1Gen.rootdec_seg_z_stmt_eq_hand
#print axioms E2eScal.E1Gen.e1_dec_DepositRoot_seg_hand

-- H3 hold-out (BlobIdentifier, DepositMessage UnmarshalSSZ): every new theorem.
#print axioms E2eScal.Gen.bi_dec_BlockRoot_seg
#print axioms E2eScal.Gen.bi_dec_BlockRoot_seg_kind
#print axioms E2eScal.Gen.dm_dec_WithdrawalCredentials_seg
#print axioms E2eScal.Gen.dm_dec_WithdrawalCredentials_seg_kind
#print axioms E2eScal.Bi.bi_e2e_head
#print axioms E2eScal.Bi.bi_e2e_accept_main
#print axioms E2eScal.Bi.bi_e2e_reject_size_main
#print axioms E2e.prysmBiDesc_checker
#print axioms E2e.prysmBiDesc_wellFormed
#print axioms E2e.prysmBiDesc_fixedSize
#print axioms E2e.prysmBiDesc_serialize_checker
#print axioms E2e.pbi_enc_size
#print axioms E2e.pbi_toValue_fits
#print axioms E2e.pbi_toValue_injective
#print axioms E2e.pbi_toValue_surjective
#print axioms E2e.pbi_toValue_surjective'
#print axioms E2e.pbi_serialize
#print axioms E2e.pbi_roundtrip
#print axioms E2e.pbi_accepted_is_enc
#print axioms E2e.pbi_spec_accepts_iff
#print axioms E2e.pbi_spec_rejects
#print axioms E2e.biChecker_wellFormed
#print axioms E2e.pbi_serialize_checker
#print axioms E2e.pbi_toValue_fits_checker
#print axioms E2e.prysmBiDesc_deserialize_checker
#print axioms E2eScal.Bi.bi_e2e_accept_spec_k
#print axioms E2eScal.Bi.bi_e2e_reject_size_spec
#print axioms E2eScal.Bi.bi_e2e_reject_complete
#print axioms E2eScal.WitBiA.P_len
#print axioms E2eScal.WitBiA.prog_eq
#print axioms E2eScal.WitBiA.hk9
#print axioms E2eScal.WitBiA.hk81
#print axioms E2eScal.WitBiA.hk87
#print axioms E2eScal.WitBiA.hf9
#print axioms E2eScal.WitBiA.hf87
#print axioms E2eScal.WitBiA.hf81
#print axioms E2eScal.WitBiA.label_bump
#print axioms E2eScal.WitBiA.label_wb
#print axioms E2eScal.WitBiA.lift_heap
#print axioms E2eScal.WitBiA.bi_accept_runs
#print axioms E2eScal.WitBiR.P_len
#print axioms E2eScal.WitBiR.hk1
#print axioms E2eScal.WitBiR.hf1
#print axioms E2eScal.WitBiR.label_err
#print axioms E2eScal.WitBiR.bi_reject_runs
#print axioms E2eScal.H3.bytes48dec_seg_z
#print axioms E2eScal.Dm.dm_e2e_head
#print axioms E2eScal.Dm.dm_e2e_accept_main
#print axioms E2eScal.Dm.dm_e2e_reject_size_main
#print axioms E2e.prysmDmDesc_checker
#print axioms E2e.prysmDmDesc_wellFormed
#print axioms E2e.prysmDmDesc_fixedSize
#print axioms E2e.prysmDmDesc_serialize_checker
#print axioms E2e.pdm_enc_size
#print axioms E2e.pdm_toValue_fits
#print axioms E2e.pdm_toValue_injective
#print axioms E2e.pdm_toValue_surjective
#print axioms E2e.pdm_toValue_surjective'
#print axioms E2e.pdm_serialize
#print axioms E2e.pdm_roundtrip
#print axioms E2e.pdm_accepted_is_enc
#print axioms E2e.pdm_spec_accepts_iff
#print axioms E2e.pdm_spec_rejects
#print axioms E2e.dmChecker_wellFormed
#print axioms E2e.pdm_serialize_checker
#print axioms E2e.pdm_toValue_fits_checker
#print axioms E2e.prysmDmDesc_deserialize_checker
#print axioms E2eScal.Dm.dm_e2e_accept_spec_k
#print axioms E2eScal.Dm.dm_e2e_reject_size_spec
#print axioms E2eScal.Dm.dm_e2e_reject_complete
#print axioms E2eScal.WitDmA.P_len
#print axioms E2eScal.WitDmA.prog_eq
#print axioms E2eScal.WitDmA.hk9
#print axioms E2eScal.WitDmA.hk118
#print axioms E2eScal.WitDmA.hk124
#print axioms E2eScal.WitDmA.hf9
#print axioms E2eScal.WitDmA.hf124
#print axioms E2eScal.WitDmA.hf118
#print axioms E2eScal.WitDmA.label_bump
#print axioms E2eScal.WitDmA.label_wb
#print axioms E2eScal.WitDmA.lift_heap
#print axioms E2eScal.WitDmA.dm_accept_runs
#print axioms E2eScal.WitDmR.P_len
#print axioms E2eScal.WitDmR.hk1
#print axioms E2eScal.WitDmR.hf1
#print axioms E2eScal.WitDmR.label_err
#print axioms E2eScal.WitDmR.dm_reject_runs

-- ENC stream (reuse-first encoder block; Eth1Data = development data): fast paths only
#print axioms E2eScal.enc32_call
#print axioms E2eScal.Bh.bh_call_at
#print axioms E2eScal.Bh.bh_enc_b_via_block
#print axioms E2eScal.Bh.bh_enc_c_via_block
#print axioms E2eScal.Bh.bh_enc_d_via_block
#print axioms E2eScal.E1.e1_call_at
#print axioms E2eScal.E1.e1_enc_a
#print axioms E2eScal.E1.e1_enc_m
#print axioms E2eScal.E1.e1_enc_e
#print axioms E2eScal.E1.e1_e2e_marshal_main
#print axioms E2eScal.E1.e1_e2e_marshal_spec_k
#print axioms E2eScal.WitE1M.e1m_runs_empty
#print axioms E2eScal.WitE1M.e1m_runs_prefix
#print axioms E2eScal.enc_reject_tail
#print axioms E2eScal.Bh.bh_rej_at
#print axioms E2eScal.Bh.bh_rej_b
#print axioms E2eScal.Bh.bh_rej_c
#print axioms E2eScal.Bh.bh_rej_d
#print axioms E2eScal.Bh.bh_e2e_marshal_reject1_main
#print axioms E2eScal.Bh.bh_e2e_marshal_reject2_main
#print axioms E2eScal.Bh.bh_e2e_marshal_reject3_main
#print axioms E2eScal.WitBhMR.bhr1_runs
#print axioms E2eScal.WitBhMR.bhr2_runs
#print axioms E2eScal.WitBhMR.bhr3_runs

-- GEN2 unit G2-L (lemmas, kinds, relations, examples, composition pieces; theorems and definitions)
#print axioms E2eScal.Gen2Ex.bi_dec_BlockRoot_seg
#print axioms E2eScal.Gen2Ex.bi_dec_BlockRoot_seg_kind
#print axioms E2eScal.Gen2Ex.bi_dec_Index_seg
#print axioms E2eScal.Gen2Ex.bi_dec_Index_seg_kind
#print axioms E2eScal.Gen2Ex.bi_e2e_accept_main_composed
#print axioms E2eScal.Gen2Ex.bi_e2e_accept_main_composed_type
#print axioms E2eScal.Gen2Ex.bi_lo
#print axioms E2eScal.Gen2Ex.dm_dec_Amount_seg
#print axioms E2eScal.Gen2Ex.dm_dec_Amount_seg_kind
#print axioms E2eScal.Gen2Ex.dm_dec_PublicKey_seg
#print axioms E2eScal.Gen2Ex.dm_dec_PublicKey_seg_kind
#print axioms E2eScal.Gen2Ex.dm_dec_WithdrawalCredentials_seg
#print axioms E2eScal.Gen2Ex.dm_dec_WithdrawalCredentials_seg_kind
#print axioms E2eScal.Gen2Ex.e1_dec_BlockHash_seg
#print axioms E2eScal.Gen2Ex.e1_dec_BlockHash_seg_kind
#print axioms E2eScal.Gen2Ex.e1_dec_DepositCount_seg
#print axioms E2eScal.Gen2Ex.e1_dec_DepositCount_seg_kind
#print axioms E2eScal.Gen2Ex.e1_dec_DepositRoot_seg
#print axioms E2eScal.Gen2Ex.e1_dec_DepositRoot_seg_kind
#print axioms E2eScal.U64InlineReg
#print axioms E2eScal.bytes48dec_seg_z_is_bytes48
#print axioms E2eScal.bytesDecHead
#print axioms E2eScal.bytesDecHead48_eq_bytes
#print axioms E2eScal.bytesDecMid
#print axioms E2eScal.bytesDecMidZ
#print axioms E2eScal.bytesDecMidZ48_eq_bytes
#print axioms E2eScal.bytesDecSegKind
#print axioms E2eScal.bytesDecSegKind_of
#print axioms E2eScal.bytesDecSegZKind
#print axioms E2eScal.bytesDecSegZKind_of
#print axioms E2eScal.bytesDecTailA
#print axioms E2eScal.bytesDecTailB
#print axioms E2eScal.bytesdec_seg
#print axioms E2eScal.bytesdec_seg_z
#print axioms E2eScal.bytesdec_tail_seg
#print axioms E2eScal.decEpi
#print axioms E2eScal.decHead
#print axioms E2eScal.decepi_seg
#print axioms E2eScal.dechead_seg
#print axioms E2eScal.rootDecHead_eq_bytes
#print axioms E2eScal.rootDecMidZ_eq_bytes
#print axioms E2eScal.rootDecMid_eq_bytes
#print axioms E2eScal.rootDecSegKind_eq_bytes
#print axioms E2eScal.rootDecSegZKind_eq_bytes
#print axioms E2eScal.rootdec_seg_is_bytes32
#print axioms E2eScal.rootdec_seg_z_is_bytes32
#print axioms E2eScal.u64DecInline
#print axioms E2eScal.u64DecInlineSegKind
#print axioms E2eScal.u64DecInlineSegKind_of
#print axioms E2eScal.u64dec_inline_seg

-- GEN2 unit G2-G (raw p2dec --gen2 segments and kinds, raw --compose accept theorems and identities, the _g2 theorems)
#print axioms E2eScal.G2.bi_e2e_accept_main_g2
#print axioms E2eScal.G2.bi_e2e_accept_main_g2_type
#print axioms E2eScal.G2.dm_e2e_accept_main_g2
#print axioms E2eScal.G2.dm_e2e_accept_main_g2_type
#print axioms E2eScal.Gen.bi_e2e_accept_main_gc
#print axioms E2eScal.Gen.bi_e2e_accept_main_gc_type
#print axioms E2eScal.Gen.bi_g2dec_BlockRoot_seg
#print axioms E2eScal.Gen.bi_g2dec_BlockRoot_seg_kind
#print axioms E2eScal.Gen.bi_g2dec_Index_seg
#print axioms E2eScal.Gen.bi_g2dec_Index_seg_kind
#print axioms E2eScal.Gen.dm_e2e_accept_main_gc
#print axioms E2eScal.Gen.dm_e2e_accept_main_gc_type
#print axioms E2eScal.Gen.dm_g2dec_Amount_seg
#print axioms E2eScal.Gen.dm_g2dec_Amount_seg_kind
#print axioms E2eScal.Gen.dm_g2dec_PublicKey_seg
#print axioms E2eScal.Gen.dm_g2dec_PublicKey_seg_kind
#print axioms E2eScal.Gen.dm_g2dec_WithdrawalCredentials_seg
#print axioms E2eScal.Gen.dm_g2dec_WithdrawalCredentials_seg_kind
#print axioms E2eScal.Gen.e1_e2e_accept_main_gc
#print axioms E2eScal.Gen.e1_e2e_accept_main_gc_type
#print axioms E2eScal.Gen.e1_g2dec_BlockHash_seg
#print axioms E2eScal.Gen.e1_g2dec_BlockHash_seg_kind
#print axioms E2eScal.Gen.e1_g2dec_DepositCount_seg
#print axioms E2eScal.Gen.e1_g2dec_DepositCount_seg_kind
#print axioms E2eScal.Gen.e1_g2dec_DepositRoot_seg
#print axioms E2eScal.Gen.e1_g2dec_DepositRoot_seg_kind
-- GEN2 unit G2-F (raw p2dec --gen2 --partial-out output for BeaconBlockHeader, 3 of 5 fields)
#print axioms E2eScal.Gen.bh_g2dec_BodyRoot_seg
#print axioms E2eScal.Gen.bh_g2dec_BodyRoot_seg_kind
#print axioms E2eScal.Gen.bh_g2dec_ParentRoot_seg
#print axioms E2eScal.Gen.bh_g2dec_ParentRoot_seg_kind
#print axioms E2eScal.Gen.bh_g2dec_StateRoot_seg
#print axioms E2eScal.Gen.bh_g2dec_StateRoot_seg_kind
-- H4 hold-out (Deposit_Data, PendingPartialWithdrawal UnmarshalSSZ): every new theorem (raw generated segments,
-- hand lemma, hand accept / reject / spec / witnesses). PendingPartialWithdrawal accept: not proved (bound).
#print axioms E2eScal.Gen.dd_g2dec_PublicKey_seg
#print axioms E2eScal.Gen.dd_g2dec_PublicKey_seg_kind
#print axioms E2eScal.Gen.dd_g2dec_Amount_seg
#print axioms E2eScal.Gen.dd_g2dec_Amount_seg_kind
#print axioms E2eScal.Gen.dd_g2dec_Signature_seg
#print axioms E2eScal.Gen.dd_g2dec_Signature_seg_kind
#print axioms E2eScal.H4.bytes32dec_seg_nop
#print axioms E2eScal.H4.dd_e2e_accept_main
#print axioms E2eScal.H4.dd_e2e_reject_size_main
#print axioms E2eScal.H4.pw_e2e_reject_size_main
#print axioms E2e.prysmDdDesc_checker
#print axioms E2e.prysmDdDesc_wellFormed
#print axioms E2e.prysmDdDesc_fixedSize
#print axioms E2e.prysmDdDesc_serialize_checker
#print axioms E2e.pdd_enc_size
#print axioms E2e.pdd_toValue_fits
#print axioms E2e.pdd_toValue_injective
#print axioms E2e.pdd_toValue_surjective
#print axioms E2e.pdd_serialize
#print axioms E2e.pdd_roundtrip
#print axioms E2e.pdd_accepted_is_enc
#print axioms E2e.pdd_spec_accepts_iff
#print axioms E2e.pdd_spec_rejects
#print axioms E2e.prysmDdDesc_deserialize_checker
#print axioms E2e.prysmPwDesc_checker
#print axioms E2e.prysmPwDesc_wellFormed
#print axioms E2e.prysmPwDesc_fixedSize
#print axioms E2e.prysmPwDesc_serialize_checker
#print axioms E2e.ppw_enc_size
#print axioms E2e.ppw_toValue_fits
#print axioms E2e.ppw_toValue_injective
#print axioms E2e.ppw_toValue_surjective
#print axioms E2e.ppw_serialize
#print axioms E2e.ppw_roundtrip
#print axioms E2e.ppw_accepted_is_enc
#print axioms E2e.ppw_spec_accepts_iff
#print axioms E2e.ppw_spec_rejects
#print axioms E2e.prysmPwDesc_deserialize_checker
#print axioms E2eScal.H4.dd_e2e_accept_spec_k
#print axioms E2eScal.H4.dd_e2e_reject_size_spec
#print axioms E2eScal.H4.dd_e2e_reject_complete
#print axioms E2eScal.H4.pw_e2e_reject_size_spec
#print axioms E2eScal.H4.pw_e2e_reject_complete
#print axioms E2eScal.WitDdA.dd_accept_runs
#print axioms E2eScal.WitDdR.dd_reject_runs
#print axioms E2eScal.WitPwR.pw_reject_runs
