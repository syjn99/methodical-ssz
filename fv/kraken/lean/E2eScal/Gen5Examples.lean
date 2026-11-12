import E2eScal.Gen5ExPd
import E2eScal.Gen5ExSm
import E2eScal.Gen5ExVe
import E2eScal.Gen5ExPb
import E2eScal.Gen5ExRej

/-!
# Worked examples of generated-style accept theorems, one per frame / field-mix class

| module | type | class | frame | fields | statement |
| --- | --- | --- | --- | --- | --- |
| `Gen5ExPd` | PendingDeposit | callee + runtime | `0x40` | bytes 48, bytes 32, uint64, bytes 96, callee Slot | kind instance = `H6.pd_accept_stmt` |
| `Gen5ExSm` | SyncCommitteeMessage | callee + runtime | `0x60` | callee Slot, bytes 32, callee ValidatorIndex, bytes 96 | kind instance = `H5.sm_accept_stmt` |
| `Gen5ExVe` | VoluntaryExit | callee only | `0x48` | callee Epoch, callee ValidatorIndex | kind instance (no hand statement) |
| `Gen5ExPb` | PowBlock | runtime only | `0x20` | bytes 32 three times | kind instance = `H6.pb_accept_stmt` |

Each module: `*_g5_head` (`decHeadKindN`), `*_g5_f<i>` per field (`decFieldKindN`), `*_g5_epi`
(`decEpiKindN`), `*_e2e_accept_g5` (`decAcceptKindN`), each with its `_kind` line, and, where a hand
statement exists, `*_e2e_accept_g5_stmt : <hand statement>`.

The texts were produced from one description per type by a scratch emitter of the lemma unit (not in the
repository; it is not the generator). They are development data (in-sample). The independent checks of
the statements are the `rfl` ties of `AcceptTies.lean`.

`Gen5ExRej`: size-reject theorems of PendingDeposit and VoluntaryExit from `decrej_seg`
(`decRejectKindN`).

`g5_examples_accept` collects the four accept theorems under their kinds.
-/

open Fk

namespace E2eScal.Gen5

variable [Host]

/-- The four generated-style accept theorems, stated by their kinds. -/
theorem g5_examples_accept :
    decAcceptKindN E2eScal.H6Code.PdUnmarshal (layMix40 [E2eAd.Code.SlUnmarshal] 131 2)
        [.bytes 48, .bytes 32, .u64, .bytes 96, .u64]
    ∧ decAcceptKindN E2eScal.H5Code.SmUnmarshal
        (layMix60 [E2eAd.Code.SlUnmarshal, E2eScal.BhCode.ViUnmarshal] 141 1) [.u64, .bytes 32, .u64, .bytes 96]
    ∧ decAcceptKindN E2eScal.H6Code.VeUnmarshal
        (layCal [E2e.Code.EpUnmarshal, E2eScal.BhCode.ViUnmarshal] 56) [.u64, .u64]
    ∧ decAcceptKindN E2eScal.H6Code.PbUnmarshal (layRt false 104 3) [.bytes 32, .bytes 32, .bytes 32] :=
  ⟨pd_e2e_accept_g5, sm_e2e_accept_g5, ve_e2e_accept_g5, pb_e2e_accept_g5⟩

end E2eScal.Gen5
