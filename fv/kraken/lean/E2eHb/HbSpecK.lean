import E2eHb.HbAccept
import E2eHb.HbReject
import E2eHb.HbSpec

/-!
# Spec alignment of the real HistoricalBatch decoder

The text of `E2eList.ScSpecK` with the HistoricalBatch statement. The statements are the frozen
`hb_accept_spec_stmt`, `hb_reject_size_spec_stmt` and `hb_reject_complete_stmt` (`StmtHb.lean`).
-/

open Machine Runtime TestTarget EthLib.Serialization.Ssz E2eList E2eHb.Code
variable [Host]

namespace E2eHb

theorem phb_v32_length (v : Vector (Vector UInt8 32) 8192) : (v.toList.map (·.toList)).length = 8192 := by simp

theorem phb_v32_elem (v : Vector (Vector UInt8 32) 8192) : ∀ e ∈ v.toList.map (·.toList), e.length = 32 := by
  intro e he
  simp only [List.mem_map] at he
  obtain ⟨p, -, rfl⟩ := he
  simp

theorem hb_e2e_accept_spec_k : hb_accept_spec_stmt := by
  intro k hk hf bsA v hd s ra guard fp s1 s2 l18 l20 l28 l30 spl rslot lo aP1 aL1 aC1 aP2 aL2 aC2
    hfp h1 h2 hl18 hl20 hl28 hl30 hspl hrs haP1 haL1 haC1 haP2 haL2 haC2 R S hlo Heap avail Pm hguard hlen hav
    hms hmsA hmm
  obtain ⟨g, rfl, hb⟩ := phb_accepted_is_enc hd
  refine ⟨g, rfl, hb, ?_⟩
  have hsz : s.regs.rcx = 524288 := by
    apply UInt64.toNat_inj.mp; rw [hlen, hb, phb_enc_size]; rfl
  exact hb_e2e_accept_main k hk hf g.brs g.srs (phb_v32_length _) (phb_v32_elem _) (phb_v32_length _)
    (phb_v32_elem _) s ra guard fp s1 s2 l18 l20 l28 l30 spl rslot lo aP1 aL1 aC1 aP2 aL2 aC2
    hfp h1 h2 hl18 hl20 hl28 hl30 hspl hrs haP1 haL1 haC1 haP2 haL2 haC2
    R S hlo Heap avail (Pm g hb) hguard hsz hav hms hmsA hmm

theorem hb_e2e_reject_size_spec : hb_reject_size_spec_stmt := by
  intro k hk hf bs hbs s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard hlen
  exact ⟨phb_spec_rejects bs hbs, hb_e2e_reject_size_main k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard
    (fun h => hbs (by rw [← hlen, h]; rfl))⟩

theorem hb_e2e_reject_complete : hb_reject_complete_stmt :=
  fun bs h h524288 => h ((phb_spec_accepts_iff bs).mpr h524288)

end E2eHb
