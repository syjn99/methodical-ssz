import E2eList.ScAccept
import E2eList.ScReject
import E2eList.ScSpec

/-!
# Spec alignment of the real SyncCommittee decoder

The text of `SaSpecK.lean` with the SyncCommittee statement. The statements are the frozen `sc_accept_spec_stmt`,
`sc_reject_size_spec_stmt` and `sc_reject_complete_stmt` (`StmtSc.lean`).
-/

open Machine Runtime TestTarget EthLib.Serialization.Ssz E2eList.Code
variable [Host]

namespace E2eList

theorem psc_pks_length (g : PSc) : g.pks.length = 512 := by simp [PSc.pks]

theorem psc_pks_elem (g : PSc) : ∀ e ∈ g.pks, e.length = 48 := by
  intro e he
  simp only [PSc.pks, List.mem_map] at he
  obtain ⟨p, -, rfl⟩ := he
  simp

theorem sc_e2e_accept_spec_k : sc_accept_spec_stmt := by
  intro k hk hf bsA v hd s ra guard fp s1 s2 l18 l20 l28 spl rslot lo ast aP1 aL1 aC1 aP2 aL2 aC2
    hfp h1 h2 hl18 hl20 hl28 hspl hrs hast haP1 haL1 haC1 haP2 haL2 haC2 R S hlo Heap avail Pm hguard hlen hav
    hms hmsA hmm
  obtain ⟨g, rfl, hb⟩ := psc_accepted_is_enc hd
  refine ⟨g, rfl, hb, ?_⟩
  have h24624 : s.regs.rcx = 24624 := by
    apply UInt64.toNat_inj.mp; rw [hlen, hb, psc_enc_size]; rfl
  exact sc_e2e_accept_main k hk hf g.pks g.aggregatePubkey.toList (psc_pks_length g) (psc_pks_elem g) (by simp)
    s ra guard fp s1 s2 l18 l20 l28 spl rslot lo ast aP1 aL1 aC1 aP2 aL2 aC2
    hfp h1 h2 hl18 hl20 hl28 hspl hrs hast haP1 haL1 haC1 haP2 haL2 haC2
    R S hlo Heap avail (Pm g hb) hguard h24624 hav hms hmsA hmm

theorem sc_e2e_reject_size_spec : sc_reject_size_spec_stmt := by
  intro k hk hf bs hbs s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard hlen
  exact ⟨psc_spec_rejects bs hbs, sc_e2e_reject_size_main k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard
    (fun h => hbs (by rw [← hlen, h]; rfl))⟩

theorem sc_e2e_reject_complete : sc_reject_complete_stmt :=
  fun bs h h24624 => h ((psc_spec_accepts_iff bs).mpr h24624)

end E2eList
