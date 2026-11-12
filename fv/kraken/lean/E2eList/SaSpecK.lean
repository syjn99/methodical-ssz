import E2eList.SaAccept
import E2eList.SaReject
import E2eList.SaSpec

/-!
# Spec alignment of the real SyncAggregate decoder

The text of `E2eScal`'s `DdSpecK.lean` with the SyncAggregate statement. The statements are the frozen
`sa_accept_spec_stmt`, `sa_reject_size_spec_stmt` and `sa_reject_complete_stmt` (`StmtSa.lean`).
- `sa_e2e_accept_spec_k`: if EthLib accepts `bsA` (`prysmSaDesc`) as `v`, there is `g : PSa` with `g.toValue = v`
  and `bsA = psaEnc g`; with the input chunks of that `g` the machine code returns nil and the receiver holds `g`.
- `sa_e2e_reject_size_spec`: `bs.size ≠ 160` → EthLib rejects, and the machine code returns `ssz.ErrSize`.
- `sa_e2e_reject_complete`: every input that EthLib rejects has `size ≠ 160`.
-/

open Fk E2e EthLib.Serialization.Ssz E2eList.Code
variable [Host]

namespace E2eList

theorem sa_e2e_accept_spec_k : sa_accept_spec_stmt := by
  intro k hk hf bsA v hd s ra guard fp s1 s2 spl l18 rslot lo ast aP1 aL1 aC1 aP2 aL2 aC2
    hfp h1 h2 hspl hl18 hrs hast haP1 haL1 haC1 haP2 haL2 haC2 R S hlo Heap avail Pm hguard hlen hav hms hmm
  obtain ⟨g, rfl, hb⟩ := psa_accepted_is_enc hd
  refine ⟨g, rfl, hb, ?_⟩
  have h160 : s.regs.rcx = 160 := by
    apply UInt64.toNat_inj.mp; rw [hlen, hb, psa_enc_size]; rfl
  exact sa_e2e_accept_main k hk hf _ _ (by simp) (by simp) s ra guard
    fp s1 s2 spl l18 rslot lo ast aP1 aL1 aC1 aP2 aL2 aC2
    hfp h1 h2 hspl hl18 hrs hast haP1 haL1 haC1 haP2 haL2 haC2
    R S hlo Heap avail (Pm g hb) hguard h160 hav hms hmm

theorem sa_e2e_reject_size_spec : sa_reject_size_spec_stmt := by
  intro k hk hf bs hbs s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard hlen
  exact ⟨psa_spec_rejects bs hbs, sa_e2e_reject_size_main k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard
    (fun h => hbs (by rw [← hlen, h]; rfl))⟩

theorem sa_e2e_reject_complete : sa_reject_complete_stmt :=
  fun bs h h160 => h ((psa_spec_accepts_iff bs).mpr h160)

end E2eList
