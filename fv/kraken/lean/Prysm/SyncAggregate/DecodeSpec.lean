import Prysm.SyncAggregate.DecodeAccept
import Prysm.SyncAggregate.DecodeRejectSize
import Prysm.SyncAggregate.Spec

/-!
# Spec alignment of the real SyncAggregate decoder

The text of `Prysm/Deposit_Data/DecodeSpec.lean` with the SyncAggregate statement. The statements are the frozen
`Decode.accept_spec_statement`, `Decode.reject_size_spec_statement` and `Decode.reject_complete_statement` (`Prysm/SyncAggregate/Statements.lean`).
- `Decode.accept_spec`: if EthLib accepts `bsA` (`desc`) as `v`, there is `g : SszValue` with `g.toValue = v`
  and `bsA = SszValue.encode g`; with the input chunks of that `g` the machine code returns nil and the receiver holds `g`.
- `Decode.reject_size_spec`: `bs.size ≠ 160` → EthLib rejects, and the machine code returns `ssz.ErrSize`.
- `Decode.reject_complete`: every input that EthLib rejects has `size ≠ 160`.
-/

open Machine Runtime EthLib.Serialization.Ssz Prysm.SyncAggregate.Code
variable [Host]

namespace Prysm.SyncAggregate

theorem Decode.accept_spec : Decode.accept_spec_statement := by
  intro k hk hf bsA v hd s ra guard fp s1 s2 spl l18 rslot lo ast aP1 aL1 aC1 aP2 aL2 aC2
    hfp h1 h2 hspl hl18 hrs hast haP1 haL1 haC1 haP2 haL2 haC2 R S hlo Heap avail Pm hguard hlen hav hms hmm
  obtain ⟨g, rfl, hb⟩ := accepted_is_encode hd
  refine ⟨g, rfl, hb, ?_⟩
  have h160 : s.regs.rcx = 160 := by
    apply UInt64.toNat_inj.mp; rw [hlen, hb, encode_size]; rfl
  exact Decode.accept k hk hf _ _ (by simp) (by simp) s ra guard
    fp s1 s2 spl l18 rslot lo ast aP1 aL1 aC1 aP2 aL2 aC2
    hfp h1 h2 hspl hl18 hrs hast haP1 haL1 haC1 haP2 haL2 haC2
    R S hlo Heap avail (Pm g hb) hguard h160 hav hms hmm

theorem Decode.reject_size_spec : Decode.reject_size_spec_statement := by
  intro k hk hf bs hbs s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard hlen
  exact ⟨spec_rejects bs hbs, Decode.reject_size k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard
    (fun h => hbs (by rw [← hlen, h]; rfl))⟩

theorem Decode.reject_complete : Decode.reject_complete_statement :=
  fun bs h h160 => h ((spec_accepts_iff bs).mpr h160)

end Prysm.SyncAggregate
