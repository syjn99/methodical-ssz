# DESIGN-T3: `IndexedAttestation.UnmarshalSSZ` hand proof design

This file is committed before the proofs. It is a plan. It does not claim that the proofs are possible.
The theorem statements are in `lean/E2eList/StmtIa.lean`. The list is in `STATEMENTS-T3.md`.

## 1. Inputs

| Item | Value |
| --- | --- |
| Go source | `prysm/_generated/mainnet/phase0.ssz.go` lines 2819–2864 |
| `.S` and data | `lv/link-t3/norm`, `lv/link-t3/data` (after the `conv.py` fix for finding LV-1, the wrapped negative displacement, `check.py` `PASS all`, bundle `393eade6…`) |
| Directive count | 279 lines (counted from 0) |
| Receiver layout | `prysm/ir/ir-mainnet.json` `go_fields`: `state` 0, `AttestingIndices` 8 (ptr, len, cap), `Data` 32 (pointer), `Signature` 40 (ptr, len, cap), `unknownFields` 64 (24), `sizeCache` 88 (4), size 96 |
| AttestationData object | size 96 (Size_ = 0x60, Kind = 25 in `lvAdType.data`) |

## 2. Paths

| Path | Go condition | Return | Directives | Goal |
| --- | --- | --- | --- | --- |
| size reject | `len < 228` | `ssz.ErrSize` | 2–10, 137–142 | K goal `ia_reject_size_stmt` |
| offset reject | first offset ≠ 228 | `ssz.ErrInvalidVariableOffset` | 11–17, 131–136 | K goal `ia_reject_offset_stmt` |
| alignment reject | `(len − 228) % 8 ≠ 0` | `fmt.Errorf("misaligned bytes: … %d … %w", len − 228, ssz.ErrIncorrectListSize)` | 18–26, 94–130 | K goal `ia_reject_misaligned_stmt` |
| overflow reject | `numElem > 2048` | `fmt.Errorf("ssz-max exceeded: … %d … %w", numElem, ssz.ErrListTooBig)` | 27–30, 57–93 | K goal `ia_reject_toobig_stmt` |
| accept | none of the above, and the delegate accepts | nil | 31–56, 143–165 loop, 166–189, 217–260 | K goal `ia_accept_stmt` |
| delegate error | `c.Data.UnmarshalSSZ` returns an error | `fmt.Errorf("Data: %w", err)` | 190–216 | not reached (below) |
| morestack, write barrier on | — | — | 268–278, 46–49 and others | N, out of scope (premises `guard < rsp − 48`, `writeBarrier = 0`) |

The contract forms for the alignment reject and the overflow reject exist (section 3). Thus both are K goals. No path is "blocked because a contract is missing".

Delegate error: the input of the delegate call is always `buf[4:132]`, 128 bytes (directives 182–186: rbx = buf + 4, rcx = 0x80).
`E2eAd.ad_e2e_accept_main` gives rax = 0, rbx = 0 on all 128-byte inputs. It has no premise on the content.
Thus under the premises of the accept path, the `test %rax,%rax; je` of 188–189 is always taken. The delegate error is not reached.
This fact is not a separate theorem. The proof of `ia_accept_stmt` shows it when it settles that branch.
EthLib also accepts all 128-byte `data` (`E2e.pad_spec_accepts_iff`). Thus there is no specification reject that matches the delegate error.

## 3. Callee table

| Directive | Target | Path | Handling | Form or theorem |
| --- | --- | --- | --- | --- |
| 39 | `runtime.makeslice` | accept | contract | `MakesliceC Heap lvU64Type_addr 8 S` (len = cap = numElem ≤ 2048) |
| 47, 177, 231, 250 | `runtime.gcWriteBarrier2` | — | excluded | premise `writeBarrier = 0` |
| 62 | `runtime.convT64` | overflow reject | contract | `ConvT64C Heap S`, v = numElem |
| 79 | `fmt.errorf` | overflow reject | contract | `FmtErrorfDWC Heap lvFmtTooBig e2eIntType_addr S` (format 73 bytes, rdi = rsi = 2) |
| 84 | `runtime.newobject` | overflow reject | excluded | `errors.New` when errorf is nil. The DWC conclusion rax ≠ 0 blocks it |
| 99 | `runtime.convT64` | alignment reject | contract | `ConvT64C Heap S`, v = len − 228 |
| 116 | `fmt.errorf` | alignment reject | contract | `FmtErrorfDWC Heap lvFmtMis e2eIntType_addr S` (format 83 bytes) |
| 121 | `runtime.newobject` | alignment reject | excluded | same as 84 |
| 168 | `runtime.newobject` | accept | contract | `NewobjectC Heap lvAdType_addr 96 S` (`c.Data = new(AttestationData)`) |
| 187 | `AttestationData.UnmarshalSSZ` | accept | proved theorem | `E2eAd.ad_e2e_accept_main` (the machine code is in the Host. Section 4) |
| 202 | `fmt.errorf` | delegate error | not reached | format `"Data: %w"`. The `FmtErrorfWC` form exists but is not used |
| 207 | `runtime.newobject` | delegate error | not reached | errorf nil branch |
| 223 | `runtime.makeslice` | accept | contract | `MakesliceC Heap e2eU8Type_addr 1 S` (len 0, cap 96) |
| 240 | `runtime.memmove` | accept | contract | `MemmoveC S`, n = 96, source buf + 132 |
| 262 | `runtime.panicBounds` | accept loop | (a) not-taken proof | index check of `c.AttestingIndices[i]` (163–164: `cmp %rdi,%r9; jb`, rdi = len of the receiver) |
| 264 | `runtime.panicBounds` | accept loop | (a) not-taken proof | low ≤ high check of `sszSlice0[i*8:(1+i)*8]` (158–159) |
| 266 | `runtime.panicBounds` | accept loop | (a) not-taken proof | high ≤ cap check of the same expression (154–155: `(i+1)*8 ≤ cap − 228`). The premise `len ≤ cap` is necessary |
| 273 | `runtime.morestack_noctxt.abi0` | — | excluded | premise `guard + 48 < rsp` |

Four newobject calls: 168 (accept, Data object), 84 and 121 (overflow reject and alignment reject, errorf nil branch), 207 (delegate error, errorf nil branch). Only 168 is in the accept path.
Three panicBounds calls: all are in the element loop of the accept path. The proof shows in each iteration that they are not taken. No premise blocks them.

All contract instances are of existing forms. New values: `lvU64Type_addr` (esz 8), `lvAdType_addr` (sz 96), `lvFmtMis`, `lvFmtTooBig`.
The `tw` of DWC is `E2e.Data.e2eIntType_addr`. It is the same method as `FmtErrorfDDC` of the Epoch reject (same form, new format and type word).

## 4. AttestationData call (premises of `ad_e2e_accept_main`)

| Premise | At the call site |
| --- | --- |
| Code location | `AdUnmarshal`, `SlUnmarshal`, `CiUnmarshal`, `CpUnmarshal`, `EpUnmarshal` are in the Host (`kA … kE` of the statement) |
| Entry rsp | x − 184 (the same position as the return slot of our runtime calls) |
| Registers | rax = new object `pd`, rbx = buf + 4, rcx = 128, rdi = cap − 4 |
| Receiver slots | the 96-byte 0 block of the new object is divided into eight 8-byte slots and 32 bytes (R) |
| Input | `in0 … troot` are at buf + 4 … buf + 100 |
| Stack | the callee spill slots x − 176, x − 168, x − 152 are in our 40-byte spill. Everything below them (fp, l68, sp0–2, rslot, lo) is in our scratch `S = Sd + 224` |
| Guard | `guard + 224 < x − 184`, that is `guard + 408 < x` |
| Contracts | `MakesliceC u8 1 Sd`, `MemmoveC Sd`, `MakesliceC u8 1 (Sd + 96)`, `MemmoveC (Sd + 96)`, `NewobjectC adCpType_addr 72 (Sd + 96)` are accepted as hypotheses of the statement |
| Heap | 240 bytes |

The result (rax = 0, rbx = 0, object content, `Heap (avail − 240)`) goes as is into our postcondition.

## 5. Element loop

The loop head is `L_28a` (directive 147). An iteration is 147–165 and 143–146.
The backing array of `[]uint64` is one contiguous block. Thus no per-element predicate is used (`lvElems` is also not used).
Invariant `IaInv i` (`i ≤ n`, `n ≤ 2048`):

- Registers: rax = i, rdx = n, rcx = cap − 228 (bytes), rbx = buf + 228, rsi = receiver, rsp = x − 176.
- Array A: `ib.take (8·i) ++ replicate (8·(n − i)) 0`. It is the same form as Go 1.26.3 `lu_iter`.
- Receiver: `+8` = A, `+16` = n (the bounds check reads it in each iteration), `+24` = n.
- The input `ib` (8n bytes), the remaining frame and `R` stay the same.

One iteration: (i+1)·8 ≤ cap − 228 (266 not taken, premise `len ≤ cap`), i·8 ≤ (i+1)·8 (264), 8-byte read, i < receiver len (262), 8-byte write.
Loop end: at i = n, `jge` is taken (148–149).
If n = 0, there is no iteration. In that case, the rbx value is buf (when cap = 228) or buf + 228. It is not read.

## 6. Specification side

- Hand `Desc` (`DefsIa.lean`): `container [attesting_indices: list (uint 8) 2048, data: E2e.prysmAdDesc, signature: byteVector 96]`.
- `PIa`: index list (length ≤ 2048, field `hidx`), `E2e.PAd`, 96-byte signature. `piaEnc` = iaOff ‖ padEnc ‖ sig ‖ u64Bytes.
- Theorems (later units): `ia_accept_spec_stmt` (the `spec_k` form of SyncAggregate and SyncCommittee), four reject specifications (size reject, offset reject, alignment reject, overflow reject), `ia_reject_cases_stmt`.
- `Desc` = producer `Desc`: render the producer file `lv/desc/prysm_v1alpha1.IndexedAttestation.desc.json` (sha256 `91e4d752…`). `lvdescterm.py` already renders `list` and nested `container`. Show that only the names differ.
- Reject completeness: `ia_reject_cases_stmt` is a pure EthLib statement. It states "if EthLib rejects, one of the conditions of the size reject, the offset reject, the alignment reject and the overflow reject holds".
- That statement becomes the reject completeness of the machine code only when all four reject paths are K. If the alignment reject or the overflow reject stays N, the claim does not get that name. The claim is then only "reject under the size reject and offset reject conditions". The delegate error has no EthLib-side reject, so it is not a condition of completeness.

## 7. Witness plan

- Accept: n = 0 (len 228), n = 1 (len 236), n = 2048 (len 16612).
- Host: `IaUnmarshal`, `AdUnmarshal`, `SlUnmarshal`, `CiUnmarshal`, `CpUnmarshal`, `EpUnmarshal`, makeslice model, newobject model, `RtCopy`.
- makeslice: one Host needs both esz 8 (`lvU64Type_addr`) and esz 1 (`e2eU8Type_addr`). `BumpAllocT` is esz 24/1. Thus a new file needs an esz 8/1 branch model (the form of `BumpAllocT`, one type-word comparison).
- newobject: one Host needs both sz 96 (`lvAdType_addr`) and sz 72 (`adCpType_addr`, the Checkpoint in AttestationData). Each existing model (16/24/32, the 72 of E2eAd) has one size. Thus a new file needs a 96/72 branch model.
- Reject witnesses: the size reject and the offset reject have no contract. The alignment reject and the overflow reject use `rt_convT64` and `rt_errorf_dw` (the format and `tw` are parameters).

## 8. Risks and judgments

- The stack guard has the form `lea -0x30(%rsp),%r12`. Finding T-9 showed a kernel memory problem with this form. `E2eScal.lea_cmp_be_false` (`StackGuard.lean`) closes it.
- The first offset read is 32-bit (`mov (%rbx),%edx`). The statement uses a 4-byte list `off` and `off ≠ iaOff`.
- The slice pointer computation (18–24: `neg`, `sar`, `and`) depends on the sign of cap − 228. The statement has `cap < 2^63`.
- The postcondition of `ad_e2e_accept_main` is long. Our postcondition contains that object content as is.
- The `rbx` return value of the alignment reject and the overflow reject is not in the DWC conclusion. The statement states only rax ≠ 0 (the same as the existing reject theorems).

## Where the two trust items are used (after the accept proof)

- `hcap : len ≤ cap`: used to show that `cmp %rcx,%rdi; ja L_475` (154–155, panicBounds 266) of one loop iteration is not taken. The premise `8n ≤ cap − 228` of `ia_loop` comes from it.
- `hcap63 : cap < 2^63`: used by `sar $0x3f` of the slice pointer computation (18–24) to see the sign (`ia_sar63`, `ia_p0`). If cap ≥ 2^63 + 228, the pointer becomes buf + 0. Then the conclusion of the statement is wrong.
- The proof needed both. No removable item was found.

## Addition to section 6 (2026-11-12)

- The machine-side theorems of the alignment reject and the overflow reject are the `_nz` statements (`StmtIaNz.lean`). The premise `e0 ≠ 0` was added.
- Thus the machine-side reject completeness for the alignment reject and overflow reject branches of `ia_reject_cases` holds only when `e0 ≠ 0`.
- `ia_reject_cases` itself is an EthLib-only statement. This addition does not change that statement.
