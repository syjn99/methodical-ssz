import Prysm.PendingDeposit.DecodeAcceptExample
import Prysm.SyncCommitteeMessage.DecodeAcceptExample
import Prysm.VoluntaryExit.DecodeAcceptExample
import Prysm.PowBlock.DecodeAcceptExample
import Prysm.PendingDeposit.DecodeRejectSizeExample

/-!
# Worked examples of generated-style accept theorems, one per frame / field-mix class

| module | type | class | frame | fields | statement |
| --- | --- | --- | --- | --- | --- |
| `Prysm/PendingDeposit/DecodeAcceptExample.lean` | PendingDeposit | callee + runtime | `0x40` | bytes 48, bytes 32, uint64, bytes 96, callee Slot | kind instance = `Decode.accept_statement` |
| `Prysm/SyncCommitteeMessage/DecodeAcceptExample.lean` | SyncCommitteeMessage | callee + runtime | `0x60` | callee Slot, bytes 32, callee ValidatorIndex, bytes 96 | kind instance = `Prysm.SyncCommitteeMessage.Decode.accept_statement` |
| `Prysm/VoluntaryExit/DecodeAcceptExample.lean` | VoluntaryExit | callee only | `0x48` | callee Epoch, callee ValidatorIndex | kind instance (no hand statement) |
| `Prysm/PowBlock/DecodeAcceptExample.lean` | PowBlock | runtime only | `0x20` | bytes 32 three times | kind instance = `Prysm.PowBlock.Decode.accept_statement` |

Each module: `*_g5_head` (`decHeadKindN`), `*_g5_f<i>` per field (`decFieldKindN`), `*_g5_epi`
(`decEpiKindN`), `*_e2e_accept_g5` (`decAcceptKindN`), each with its `_kind` line, and, where a hand
statement exists, `*_e2e_accept_g5_stmt : <hand statement>`.

The texts were produced from one description per type by a scratch emitter of the lemma unit (not in the
repository; it is not the generator). They are development data (in-sample). The independent checks of
the statements are the `rfl` ties of `Codec/Kind/DecodeAcceptAnyFrameInstances.lean`.

`Prysm/PendingDeposit/DecodeRejectSizeExample.lean`: size-reject theorems of PendingDeposit and VoluntaryExit from `decrej_seg`
(`decRejectKindN`).

`Decode.example_accept_all` collects the four accept theorems under their kinds.
-/

open Machine Runtime

open Codec
namespace Prysm.PendingDeposit

variable [Host]

/-- The four generated-style accept theorems, stated by their kinds. -/
theorem Decode.example_accept_all :
    decAcceptKindN Prysm.PendingDeposit.Code.unmarshalSSZ (layMix40 [Prysm.AttestationData.Code.slotUnmarshalSSZ] 131 2)
        [.bytes 48, .bytes 32, .u64, .bytes 96, .u64]
    ∧ decAcceptKindN Prysm.SyncCommitteeMessage.Code.unmarshalSSZ
        (layMix60 [Prysm.AttestationData.Code.slotUnmarshalSSZ, Prysm.ValidatorIndex.Code.unmarshalSSZ] 141 1) [.u64, .bytes 32, .u64, .bytes 96]
    ∧ decAcceptKindN Prysm.VoluntaryExit.Code.unmarshalSSZ
        (layCal [Prysm.Epoch.Code.unmarshalSSZ, Prysm.ValidatorIndex.Code.unmarshalSSZ] 56) [.u64, .u64]
    ∧ decAcceptKindN Prysm.PowBlock.Code.unmarshalSSZ (layRt false 104 3) [.bytes 32, .bytes 32, .bytes 32] :=
  ⟨Decode.example_accept, Prysm.SyncCommitteeMessage.Decode.example_accept, Prysm.VoluntaryExit.Decode.example_accept, Prysm.PowBlock.Decode.example_accept⟩

end Prysm.PendingDeposit
