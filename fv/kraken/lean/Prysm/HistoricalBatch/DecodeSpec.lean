import Prysm.HistoricalBatch.DecodeAccept
import Prysm.HistoricalBatch.DecodeRejectSize
import Prysm.HistoricalBatch.Spec

/-!
# Spec alignment of the real HistoricalBatch decoder

The text of `Prysm.SyncCommittee.DecodeSpec` with the HistoricalBatch statement. The statements are the frozen
`Decode.accept_spec_statement`, `Decode.reject_size_spec_statement` and `Decode.reject_complete_statement` (`Prysm/HistoricalBatch/Statements.lean`).
-/

open Machine Runtime TestTarget EthLib.Serialization.Ssz Prysm.HistoricalBatch.Code
variable [Host]

namespace Prysm.HistoricalBatch

theorem v32_length (v : Vector (Vector UInt8 32) 8192) : (v.toList.map (·.toList)).length = 8192 := by simp

theorem v32_elem (v : Vector (Vector UInt8 32) 8192) : ∀ e ∈ v.toList.map (·.toList), e.length = 32 := by
  intro e he
  simp only [List.mem_map] at he
  obtain ⟨p, -, rfl⟩ := he
  simp

theorem Decode.accept_spec : Decode.accept_spec_statement := by
  intro k hk hf bsA v hd s ra guard fp s1 s2 l18 l20 l28 l30 spl rslot lo aP1 aL1 aC1 aP2 aL2 aC2
    hfp h1 h2 hl18 hl20 hl28 hl30 hspl hrs haP1 haL1 haC1 haP2 haL2 haC2 R S hlo Heap avail Pm hguard hlen hav
    hms hmsA hmm
  obtain ⟨g, rfl, hb⟩ := accepted_is_encode hd
  refine ⟨g, rfl, hb, ?_⟩
  have hsz : s.regs.rcx = 524288 := by
    apply UInt64.toNat_inj.mp; rw [hlen, hb, encode_size]; rfl
  exact Decode.accept k hk hf g.brs g.srs (v32_length _) (v32_elem _) (v32_length _)
    (v32_elem _) s ra guard fp s1 s2 l18 l20 l28 l30 spl rslot lo aP1 aL1 aC1 aP2 aL2 aC2
    hfp h1 h2 hl18 hl20 hl28 hl30 hspl hrs haP1 haL1 haC1 haP2 haL2 haC2
    R S hlo Heap avail (Pm g hb) hguard hsz hav hms hmsA hmm

theorem Decode.reject_size_spec : Decode.reject_size_spec_statement := by
  intro k hk hf bs hbs s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard hlen
  exact ⟨spec_rejects bs hbs, Decode.reject_size k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard
    (fun h => hbs (by rw [← hlen, h]; rfl))⟩

theorem Decode.reject_complete : Decode.reject_complete_statement :=
  fun bs h h524288 => h ((spec_accepts_iff bs).mpr h524288)

end Prysm.HistoricalBatch
