# DESIGN-HB: `HistoricalBatch.UnmarshalSSZ` hand proof design (SyncCommittee port)

This file is committed before the proofs. It is a plan. It does not claim that the proofs are possible.
The theorem statements are in `lean/E2eHb/StmtHb.lean`.
The purpose is to measure the reuse quantity of the `SyncCommittee` proofs.

## 1. Inputs

| Item | Value |
| --- | --- |
| Go source | `prysm/_generated/mainnet/phase0.ssz.go` lines 2693–2729 |
| `.S` and data | `lv/link-hb/norm`, `lv/link-hb/data` (`gen/e2e/hblink.py`, `link/conv.py --norm`, `link/check.py` `PASS all`, bundle `66e6154a…`) |
| Directive count | 182 lines (counted from 0, labels included). 164 instructions |
| Receiver layout | `prysm/ir/ir-mainnet.json` `go_fields`: native struct, size 48. `BlockRoots` 0, `StateRoots` 24 (ptr, len, cap) |
| ELF | same as SyncCommittee (`c6403c02…911e`). The objdump sha256 `580b0da9…` is the same as `build-ids.txt` |

## 2. Paths

| Path | Go condition | Return | Directives | Goal |
| --- | --- | --- | --- | --- |
| size reject | `len ≠ 524288` | `ssz.ErrSize` | 2–10, 30–35 | K goal `hb_reject_size_stmt` |
| accept | `len = 524288` | nil | 2–29, loop 1 (40–84, 36–39), 86–103, loop 2 (108–153, 104–107), 155–159 | K goal `hb_accept_stmt` |
| morestack, write barrier on | — | — | 170–181, 22–25 and others | N, out of scope (premises `guard < rsp`, `writeBarrier = 0`) |

There is one reject path. The four `panicBounds` calls are not error returns. The proof shows in each iteration that they are not taken.

## 3. Callee table

| Directive | Target | Handling | Form |
| --- | --- | --- | --- |
| 16, 89 | `runtime.makeslice` | contract | `MakesliceC Heap lvSliceType_addr 24 S` (cnt 8192) |
| 57, 125 | `runtime.makeslice` | contract | `MakesliceC Heap e2eU8Type_addr 1 S` (len 0, cap 32) |
| 63, 132 | `runtime.memmove` | contract | `MemmoveC S` (n = 32) |
| 23, 80, 97, 149 | `runtime.gcWriteBarrier2` | excluded | premise `writeBarrier = 0` |
| 161, 164, 166, 168 | `runtime.panicBounds` | (a) not-taken proof | section 4 below |
| 175 | `runtime.morestack_noctxt.abi0` | excluded | premise `guard < rsp` |

The contract instances are the same three as SyncCommittee. There is no new contract form and no new instance value.
The operand of `lvSliceType` (`type__+337600`) is the same as SyncCommittee. `hblink.py data` asserts that they are the same.
Thus `E2eList.Data.lvSliceType_addr` is used as is. There is no new `Data` module.

## 4. Differences from SyncCommittee

| Item | SyncCommittee | HistoricalBatch | Effect on the proof |
| --- | --- | --- | --- |
| frame | `sub $0x30` | `sub $0x38` | one constant of the reject proof |
| local slots | 3 (i, 3i, pointer) | 4 (i + 1, 32i, i, pointer) | one more invariant slot |
| loops | 512 iterations, 1 | 8192 iterations, 2 | two one-iteration proofs |
| element | 48 bytes | 32 bytes | constant |
| tail field | AggregatePubkey (48) | none | `sc_agg_seg` is not used |
| index computation | `lea (%rdx,%rdx,2)`, `shl $4` | `shl $5`, `lea 0x1(%rsi)`, `shl $5` | the step sequence is different |
| bounds check | 1 per iteration (`jae`) | 2 per iteration (`jb` overflow, `jae` len) | a new `jb` not-taken proof is necessary |
| loop 2 source | — | `lea 0x40000(%rbx)` | one more directive |
| receiver | protoc (size 88, `state` 0) | native (size 48) | the field offsets are different |
| last call | directive 100 | directive 132 | return slot value `k + 133` |
| heap | 36912 | 917504 | constant |

The step sequences of loop 1 and loop 2 are also not the same. The `nop` positions are different (48, 74 / 116, 136).
Thus each loop gets its own one-iteration theorem. The directive numbers are not parameters.

## 5. Loop invariant

The head of loop 1 is `L_a0` (directive 40). `sp` = entry rsp − 64.
Invariant (i ≤ 8192):

- Registers: rax = i, rsp = sp, rbp, r14 = entry values.
- Slots: sp + 72 = receiver, sp + 80 = buf. The values of the four locals (sp + 24, 32, 40, 48) are not specified.
- Receiver: `+0` = A1, `+8` = 8192 (the bounds check reads it in each iteration).
- Array A1: `lvHdrs 32 ps ++ zz (24·(8192 − i))`.
- Elements: `lvElems ps (brs.take i)`.
- Heap: `Heap (avail − 32·i)` (from the value before the loop entry).

Loop 2 has the same form at `L_1c0` (108). Receiver `+24` = A2, `+32` = 8192, the input is buf + 262144.
The one-iteration proof follows the order of SyncCommittee `sc_iter`. The induction has the form of SyncCommittee `sc_loop` (`i + j = 8192`).

## 6. Specification side

- Hand `Desc` (`E2eHb/Defs.lean`): `container [block_roots: vector (byteVector 32) 8192, state_roots: same]`.
- Limit: in this task, the producer `Desc` file was printed before the hand `Desc`. Unlike SyncCommittee, the independence is weaker.
- `PHb`: two sets of 8192 32-byte vectors. `phbEnc g` = `g.brs.flatten ++ g.srs.flatten`.
- Specification bridge: it follows the order of SyncCommittee `ScSpec`. Lemmas that are not tied to the element width are imported.
- Producer `Desc`: `lv/desc/prysm_v1alpha1.HistoricalBatch.desc.json` (sha256 `05642f50…`, same as the checker record).
- `lvdescterm.py` renders it to make `E2eHb/HbSpecChecker.lean`.

## 7. Witness plan

- HistoricalBatch has a fixed size. The witness is one theorem for all inputs and three concrete inputs (0, representative, 0xff).
- Host: data labels, `HbUnmarshal`, `E2eList.BumpAllocT`, `RtCopy`. The SyncCommittee models are imported.
- `bump_makeslice_t1` and `bump_makeslice_t24` use the same type word. Thus they match as is.

## 8. Risks

- The induction of the 8192-iteration loop uses the same method as SyncCommittee. The loop is not unrolled.
- The witness memory is about 1.45 MB. The `simp` sorting cost can be larger than SyncCommittee. This is not known before a measurement.
- The `jb` not-taken proof is a step that SyncCommittee did not have. It needs a `toNat` expression for `shl`.
