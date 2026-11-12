import E2eScal.BiReject
import E2eScal.DmReject
import E2eScal.E1Reject
import E2eScal.BhReject
import E2eScal.DdReject
import E2eScal.PwReject
import E2eScal.SmReject
import E2eScal.PcReject
import E2eScal.PdReject
import E2eScal.PbReject
import E2eAd.AdReject
import E2eScal.RejectN

/-!
# GEN5 L3: ties of `decRejectKindN` to the committed size-reject theorems

The declared type of each committed theorem `*_e2e_reject_size_main` (the 11 flat development types and
AttestationData) is the kind instance; `with_reducible rfl` (the kind is an `abbrev` and the text is the same).
-/

open Fk

namespace E2eScal

theorem bi_reject_is_kindN : ∀ (h : Host), type_of% (@E2eScal.Bi.bi_e2e_reject_size_main h)
    = @decRejectKindN h E2eScal.H3Code.BiUnmarshal 40 := by
  intro h; with_reducible rfl

theorem dm_reject_is_kindN : ∀ (h : Host), type_of% (@E2eScal.Dm.dm_e2e_reject_size_main h)
    = @decRejectKindN h E2eScal.H3Code.DmUnmarshal 88 := by
  intro h; with_reducible rfl

theorem e1_reject_is_kindN : ∀ (h : Host), type_of% (@E2eScal.E1.e1_e2e_reject_size_main h)
    = @decRejectKindN h E2eScal.E1Code.E1Unmarshal 72 := by
  intro h; with_reducible rfl

theorem bh_reject_is_kindN : ∀ (h : Host), type_of% (@E2eScal.Bh.bh_e2e_reject_size_main h)
    = @decRejectKindN h E2eScal.BhCode.BhUnmarshal 112 := by
  intro h; with_reducible rfl

theorem dd_reject_is_kindN : ∀ (h : Host), type_of% (@E2eScal.H4.dd_e2e_reject_size_main h)
    = @decRejectKindN h E2eScal.H4Code.DdUnmarshal 184 := by
  intro h; with_reducible rfl

theorem pw_reject_is_kindN : ∀ (h : Host), type_of% (@E2eScal.H4.pw_e2e_reject_size_main h)
    = @decRejectKindN h E2eScal.H4Code.PwUnmarshal 24 := by
  intro h; with_reducible rfl

theorem sm_reject_is_kindN : ∀ (h : Host), type_of% (@E2eScal.H5.sm_e2e_reject_size_main h)
    = @decRejectKindN h E2eScal.H5Code.SmUnmarshal 144 := by
  intro h; with_reducible rfl

theorem pc_reject_is_kindN : ∀ (h : Host), type_of% (@E2eScal.H5.pc_e2e_reject_size_main h)
    = @decRejectKindN h E2eScal.H5Code.PcUnmarshal 16 := by
  intro h; with_reducible rfl

theorem pd_reject_is_kindN : ∀ (h : Host), type_of% (@E2eScal.H6.pd_e2e_reject_size_main h)
    = @decRejectKindN h E2eScal.H6Code.PdUnmarshal 192 := by
  intro h; with_reducible rfl

theorem pb_reject_is_kindN : ∀ (h : Host), type_of% (@E2eScal.H6.pb_e2e_reject_size_main h)
    = @decRejectKindN h E2eScal.H6Code.PbUnmarshal 96 := by
  intro h; with_reducible rfl

theorem cp_reject_is_kindN : ∀ (h : Host), type_of% (@E2e.cp_e2e_reject_size_main h)
    = @decRejectKindN h E2e.Code.CpUnmarshal 40 := by
  intro h; with_reducible rfl

theorem ad_reject_is_kindN : ∀ (h : Host), type_of% (@E2eAd.ad_e2e_reject_size_main h)
    = @decRejectKindN h E2eAd.Code.AdUnmarshal 128 := by
  intro h; with_reducible rfl

end E2eScal
