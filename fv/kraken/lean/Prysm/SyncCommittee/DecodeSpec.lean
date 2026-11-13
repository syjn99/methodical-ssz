import Prysm.SyncCommittee.DecodeAccept
import Prysm.SyncCommittee.DecodeRejectSize
import Prysm.SyncCommittee.Spec

/-!
# Spec alignment of the real SyncCommittee decoder

The text of `Prysm/SyncAggregate/DecodeSpec.lean` with the SyncCommittee statement. The statements are the frozen `Decode.accept_spec_statement`,
`Decode.reject_size_spec_statement` and `Decode.reject_complete_statement` (`Prysm/SyncCommittee/Statements.lean`).
-/

open Machine Runtime EthLib.Serialization.Ssz Prysm.SyncCommittee.Code
variable [Host]

namespace Prysm.SyncCommittee

theorem pubkeyBytes_length (g : SszValue) : g.pubkeyBytes.length = 512 := by simp [SszValue.pubkeyBytes]

theorem pubkeyBytes_element (g : SszValue) : ∀ e ∈ g.pubkeyBytes, e.length = 48 := by
  intro e he
  simp only [SszValue.pubkeyBytes, List.mem_map] at he
  obtain ⟨p, -, rfl⟩ := he
  simp

theorem Decode.accept_spec : Decode.accept_spec_statement := by
  intro k hk hf bsA v hd s ra guard fp s1 s2 l18 l20 l28 spl rslot lo ast aP1 aL1 aC1 aP2 aL2 aC2
    hfp h1 h2 hl18 hl20 hl28 hspl hrs hast haP1 haL1 haC1 haP2 haL2 haC2 R S hlo Heap avail Pm hguard hlen hav
    hms hmsA hmm
  obtain ⟨g, rfl, hb⟩ := accepted_is_encode hd
  refine ⟨g, rfl, hb, ?_⟩
  have h24624 : s.regs.rcx = 24624 := by
    apply UInt64.toNat_inj.mp; rw [hlen, hb, encode_size]; rfl
  exact Decode.accept k hk hf g.pubkeyBytes g.aggregatePubkey.toList (pubkeyBytes_length g) (pubkeyBytes_element g) (by simp)
    s ra guard fp s1 s2 l18 l20 l28 spl rslot lo ast aP1 aL1 aC1 aP2 aL2 aC2
    hfp h1 h2 hl18 hl20 hl28 hspl hrs hast haP1 haL1 haC1 haP2 haL2 haC2
    R S hlo Heap avail (Pm g hb) hguard h24624 hav hms hmsA hmm

theorem Decode.reject_size_spec : Decode.reject_size_spec_statement := by
  intro k hk hf bs hbs s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard hlen
  exact ⟨spec_rejects bs hbs, Decode.reject_size k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard
    (fun h => hbs (by rw [← hlen, h]; rfl))⟩

theorem Decode.reject_complete : Decode.reject_complete_statement :=
  fun bs h h24624 => h ((spec_accepts_iff bs).mpr h24624)

end Prysm.SyncCommittee
