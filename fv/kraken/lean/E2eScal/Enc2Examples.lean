import E2eScal.Enc2ExCp
import E2eScal.Enc2ExBh
import E2eScal.Enc2ExE1
import E2eScal.Enc2ExVb
import E2eScal.Enc2ExDm
import E2eScal.Enc2ExHs

/-!
# ENC2 L2: worked examples of generated-style encoder fast-path theorems, one per frame / field-mix class

| module | type | guard | frame | fields | epilogue | statement |
| --- | --- | --- | --- | --- | --- | --- |
| `Enc2ExCp` | Checkpoint | small | `sub $0x68` | uint64 (stack temp), bytes 32 | reloads | kind instance; `E2e.cp_e2e_marshal_main`'s statement by `cp_marshal_of_kind` |
| `Enc2ExBh` | BeaconBlockHeader | large, 32 | `sub $0x98` | uint64 (temp) twice, bytes 32 three times | reloads | kind instance = `Bh.bh_e2e_marshal_main`'s statement (`rfl`) |
| `Enc2ExE1` | Eth1Data | large, 8 | `add $-0x80` | bytes 32, uint64, bytes 32 | reloads, `sub $-0x80` | kind instance = `E1.e1_e2e_marshal_main`'s statement (`rfl`) |
| `Enc2ExVb` | ValidatorBalance | small | `sub $0x68` | uint64 (temp), uint64 | register moves, no `memmove` | kind instance (no hand statement) |
| `Enc2ExDm` | DepositMessage | large, 8 | `add $-0x80` | bytes 48, bytes 32, uint64; no `state` word | no reload | kind instance (no hand statement) |
| `Enc2ExHs` | HistoricalSummary | small | `sub $0x50` | bytes 32 twice | frame test (`EncFrameTest.lean`), reloads | kind instance (no hand statement) |

Each module: `*_g6_head` (`encHeadKindN`), `*_g6_f<i>` per field (`encFieldKindN`), `*_g6_epi`
(`encEpiKindN`), `*_e2e_marshal_g6` (`encFastKindN`), each with its `_kind` line, and, where a hand theorem
exists, `*_e2e_marshal_g6_stmt : <declared type of the hand theorem>`.

**Fast path only** in every theorem: `len(dst) + SizeSSZ ≤ cap(dst)` and every byte-vector field of its exact
length. No `runtime.growslice` directive is stepped. Not covered: growslice branches, length rejects, morestack.

The texts were produced from the `.S` files and the IR by a scratch emitter of the lemma unit (not in the
repository; it is not the generator). They are development data (in-sample). The independent checks of the
statements are the ties of `EncTies.lean`.

`g6_examples_fast` collects the six theorems under their kinds. `enc32_call_of_n`: the committed block
`enc32_call` (statement as committed) follows from `encn_call`.
-/

open Fk

namespace E2eScal.Gen6

variable [Host]

/-- The six generated-style fast-path theorems, stated by their kinds. -/
theorem g6_examples_fast :
    encFastKindN E2e.Code.CpMarshal layEncCp [.u64, .bytes 32]
    ∧ encFastKindN E2eScal.BhCode.BhMarshal layEncBh [.u64, .u64, .bytes 32, .bytes 32, .bytes 32]
    ∧ encFastKindN E2eScal.E1Code.E1Marshal layEncE1 [.bytes 32, .u64, .bytes 32]
    ∧ encFastKindN E2eScal.Enc2Code.VbMarshal layEncVb [.u64, .u64]
    ∧ encFastKindN E2eScal.Enc2Code.DmMarshal layEncDm [.bytes 48, .bytes 32, .u64]
    ∧ encFastKindN E2eScal.Enc2Code.HsMarshal layEncHs [.bytes 32, .bytes 32] :=
  ⟨cp_e2e_marshal_g6, bh_e2e_marshal_g6, e1_e2e_marshal_g6, vb_e2e_marshal_g6, dm_e2e_marshal_g6,
    hs_e2e_marshal_g6⟩

/-- The committed 32-byte call block has the statement of the `n`-byte block at `n = 32`. -/
theorem enc32_call_of_n : type_of% (@E2eScal.enc32_call ‹Host›) := by
  intro jc hc sp d p aRet aLo S hRet hLo root e rslot scratch hroot he hrs hsc R s hrsp hrax hrbx hrcx h_mem hmm
  exact encn_call jc hc sp d p aRet aLo S hRet hLo root e rslot scratch (by rw [he, hroot]) hrs hsc R s hrsp hrax
    hrbx (by rw [hroot]; exact hrcx) h_mem hmm

end E2eScal.Gen6
