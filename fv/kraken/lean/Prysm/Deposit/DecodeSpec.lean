import Prysm.Deposit.DecodeAccept
import Prysm.Deposit.DecodeRejectSize
import Prysm.Deposit.Spec

/-!
# Spec alignment of the real Deposit decoder

The text of `Prysm.HistoricalBatch.DecodeSpec` with the Deposit statement. The statements are the frozen `Decode.accept_spec_statement`,
`Decode.reject_size_spec_statement` and `Decode.reject_complete_statement` (`Prysm/Deposit/StatementsSpec.lean`).
-/

open Machine Runtime EthLib.Serialization.Ssz Prysm.Deposit.Code
variable [Host]

namespace Prysm.Deposit

theorem proofs_length (g : SszValue) : g.proofs.length = 33 := by simp [SszValue.proofs]

theorem proofs_elem (g : SszValue) : ∀ e ∈ g.proofs, e.length = 32 := by
  intro e he
  simp only [SszValue.proofs, List.mem_map] at he
  obtain ⟨p, -, rfl⟩ := he
  simp

theorem Decode.accept_spec : Decode.accept_spec_statement := by
  intro k hk hf kd hkd hfd bsA v hd s ra guard fp s1 s2 s4 lI1 lD lI lP spl rslot lo ast aP aL aC aD
    hfp h1 h2 h4 hlI1 hlD hlI hlP hspl hrs hast haP haL haC haD R Sd hSd hlo Heap avail Pm hguard hlen hav
    hmsA hms hmm hno hmsD hmmD
  obtain ⟨g, rfl, hb⟩ := accepted_is_encode hd
  refine ⟨g, rfl, hb, ?_⟩
  have hsz : s.regs.rcx = 1240 := by
    apply UInt64.toNat_inj.mp; rw [hlen, hb, encode_size]; rfl
  exact Decode.accept k hk hf kd hkd hfd g.proofs (proofs_length g) (proofs_elem g)
    g.data.pubkey.toList g.data.withdrawalCredentials.toList (uintBytes 8 g.data.amount.toNat).toList
    g.data.signature.toList (by simp) (by simp) (by simp [Spec.uintBytes_size]) (by simp)
    s ra guard fp s1 s2 s4 lI1 lD lI lP spl rslot lo ast aP aL aC aD
    hfp h1 h2 h4 hlI1 hlD hlI hlP hspl hrs hast haP haL haC haD R Sd hSd hlo Heap avail (Pm g hb) hguard hsz hav
    hmsA hms hmm hno hmsD hmmD

theorem Decode.reject_size_spec : Decode.reject_size_spec_statement := by
  intro k hk hf bs hbs s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard hlen
  exact ⟨spec_rejects bs hbs, Decode.reject_size k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard
    (fun h => hbs (by rw [← hlen, h]; rfl))⟩

theorem Decode.reject_complete : Decode.reject_complete_statement :=
  fun bs h h1240 => h ((spec_accepts_iff bs).mpr h1240)

end Prysm.Deposit
