import Prysm.Checkpoint.EncodeFastPathExample
import Prysm.BeaconBlockHeader.EncodeFastPathExample
import Prysm.Eth1Data.EncodeFastPathExample
import Prysm.ValidatorBalance.EncodeFastPathExample
import Prysm.DepositMessage.EncodeFastPathExample
import Prysm.HistoricalSummary.EncodeFastPathExample

/-!
# Worked examples of generated-style encoder fast-path theorems, one per frame / field-mix class

| module | type | guard | frame | fields | epilogue | statement |
| --- | --- | --- | --- | --- | --- | --- |
| `Prysm/Checkpoint/EncodeFastPathExample.lean` | Checkpoint | small | `sub $0x68` | uint64 (stack temp), bytes 32 | reloads | kind instance; `Prysm.Checkpoint.Encode.fast_path`'s statement by `Encode.fast_path_of_kind` |
| `Prysm/BeaconBlockHeader/EncodeFastPathExample.lean` | BeaconBlockHeader | large, 32 | `sub $0x98` | uint64 (temp) twice, bytes 32 three times | reloads | kind instance = `Prysm.BeaconBlockHeader.Encode.fast_path`'s statement (`rfl`) |
| `Prysm/Eth1Data/EncodeFastPathExample.lean` | Eth1Data | large, 8 | `add $-0x80` | bytes 32, uint64, bytes 32 | reloads, `sub $-0x80` | kind instance = `Prysm.Eth1Data.Encode.fast_path`'s statement (`rfl`) |
| `Prysm/ValidatorBalance/EncodeFastPathExample.lean` | ValidatorBalance | small | `sub $0x68` | uint64 (temp), uint64 | register moves, no `memmove` | kind instance (no hand statement) |
| `Prysm/DepositMessage/EncodeFastPathExample.lean` | DepositMessage | large, 8 | `add $-0x80` | bytes 48, bytes 32, uint64; no `state` word | no reload | kind instance (no hand statement) |
| `Prysm/HistoricalSummary/EncodeFastPathExample.lean` | HistoricalSummary | small | `sub $0x50` | bytes 32 twice | frame test (`Codec/EncodeFrameTest.lean`), reloads | kind instance (no hand statement) |

Each module: `Encode.example_head` (`encHeadKindAnyFrame`), `Encode.example_f<i>` per field (`encFieldKindAnyFrame`), `Encode.example_epilogue`
(`encEpilogueKindAnyFrame`), `Encode.example_fast` (`encFastPathKindAnyFrame`), each with its `_kind` line, and, where a hand theorem
exists, `Encode.example_fast_same_statement : type_of% <the hand theorem>`.

**Fast path only** in every theorem: `len(dst) + SizeSSZ ≤ cap(dst)` and every byte-vector field of its exact
length. No `runtime.growslice` directive is stepped. Not covered: growslice branches, length rejects, morestack.

The texts were produced from the `.S` files and the IR by a scratch emitter (not in the
repository; it is not the generator). They are development data (in-sample). The independent checks of the
statements are the ties of `Prysm/<Type>/EncodeFastPathKindInstances.lean` (BeaconBlockHeader, Eth1Data, Checkpoint).

`Encode.example_fast_all` collects the six theorems under their kinds. `Encode.example_bytes32_call_of_size`: the committed block
`encode32_memmove_call` (statement as committed) follows from `encode_memmove_call`.
-/

open Machine Runtime

open Codec
namespace Prysm.Checkpoint

variable [Host]

/-- The six generated-style fast-path theorems, stated by their kinds. -/
theorem Encode.example_fast_all :
    encFastPathKindAnyFrame Prysm.Checkpoint.Code.marshalSSZTo encodeLayout [.u64, .bytes 32]
    ∧ encFastPathKindAnyFrame Prysm.BeaconBlockHeader.Code.marshalSSZTo Prysm.BeaconBlockHeader.encodeLayout [.u64, .u64, .bytes 32, .bytes 32, .bytes 32]
    ∧ encFastPathKindAnyFrame Prysm.Eth1Data.Code.marshalSSZTo Prysm.Eth1Data.encodeLayout [.bytes 32, .u64, .bytes 32]
    ∧ encFastPathKindAnyFrame Prysm.ValidatorBalance.Code.marshalSSZTo Prysm.ValidatorBalance.Encode.example_layout [.u64, .u64]
    ∧ encFastPathKindAnyFrame Prysm.DepositMessage.Code.marshalSSZTo Prysm.DepositMessage.Encode.example_layout [.bytes 48, .bytes 32, .u64]
    ∧ encFastPathKindAnyFrame Prysm.HistoricalSummary.Code.marshalSSZTo Prysm.HistoricalSummary.Encode.example_layout [.bytes 32, .bytes 32] :=
  ⟨Encode.example_fast, Prysm.BeaconBlockHeader.Encode.example_fast, Prysm.Eth1Data.Encode.example_fast, Prysm.ValidatorBalance.Encode.example_fast, Prysm.DepositMessage.Encode.example_fast,
    Prysm.HistoricalSummary.Encode.example_fast⟩

/-- The committed 32-byte call block has the statement of the `n`-byte block at `n = 32`. -/
theorem Encode.example_bytes32_call_of_size : type_of% (@Codec.encode32_memmove_call ‹Host›) := by
  intro jc hc sp d p aRet aLo S hRet hLo root e rslot scratch hroot he hrs hsc R s hrsp hrax hrbx hrcx h_mem hmm
  exact encode_memmove_call jc hc sp d p aRet aLo S hRet hLo root e rslot scratch (by rw [he, hroot]) hrs hsc R s hrsp hrax
    hrbx (by rw [hroot]; exact hrcx) h_mem hmm

end Prysm.Checkpoint
