import E2eDep.Accept
import E2eDep.Reject
import E2eDep.Spec

/-!
# Spec alignment of the real Deposit decoder

The text of `E2eHb.HbSpecK` with the Deposit statement. The statements are the frozen `dep_accept_spec_stmt`,
`dep_reject_size_spec_stmt` and `dep_reject_complete_stmt` (`SpecStmt.lean`).
-/

open Machine Runtime TestTarget E2e EthLib.Serialization.Ssz E2eDep.Code
variable [Host]

namespace E2eDep

theorem dep_proofs_length (g : PDep) : g.proofs.length = 33 := by simp [PDep.proofs]

theorem dep_proofs_elem (g : PDep) : ∀ e ∈ g.proofs, e.length = 32 := by
  intro e he
  simp only [PDep.proofs, List.mem_map] at he
  obtain ⟨p, -, rfl⟩ := he
  simp

theorem dep_e2e_accept_spec_k : dep_accept_spec_stmt := by
  intro k hk hf kd hkd hfd bsA v hd s ra guard fp s1 s2 s4 lI1 lD lI lP spl rslot lo ast aP aL aC aD
    hfp h1 h2 h4 hlI1 hlD hlI hlP hspl hrs hast haP haL haC haD R Sd hSd hlo Heap avail Pm hguard hlen hav
    hmsA hms hmm hno hmsD hmmD
  obtain ⟨g, rfl, hb⟩ := dep_accepted_is_enc hd
  refine ⟨g, rfl, hb, ?_⟩
  have hsz : s.regs.rcx = 1240 := by
    apply UInt64.toNat_inj.mp; rw [hlen, hb, dep_enc_size]; rfl
  exact dep_e2e_accept_main k hk hf kd hkd hfd g.proofs (dep_proofs_length g) (dep_proofs_elem g)
    g.data.pubkey.toList g.data.withdrawalCredentials.toList (uintBytes 8 g.data.amount.toNat).toList
    g.data.signature.toList (by simp) (by simp) (by simp [Spec.uintBytes_size]) (by simp)
    s ra guard fp s1 s2 s4 lI1 lD lI lP spl rslot lo ast aP aL aC aD
    hfp h1 h2 h4 hlI1 hlD hlI hlP hspl hrs hast haP haL haC haD R Sd hSd hlo Heap avail (Pm g hb) hguard hsz hav
    hmsA hms hmm hno hmsD hmmD

theorem dep_e2e_reject_size_spec : dep_reject_size_spec_stmt := by
  intro k hk hf bs hbs s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard hlen
  exact ⟨dep_spec_rejects bs hbs, dep_e2e_reject_size_main k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard
    (fun h => hbs (by rw [← hlen, h]; rfl))⟩

theorem dep_e2e_reject_complete : dep_reject_complete_stmt :=
  fun bs h h1240 => h ((dep_spec_accepts_iff bs).mpr h1240)

end E2eDep
