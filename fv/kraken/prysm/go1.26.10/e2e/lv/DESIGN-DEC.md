# DESIGN-DEC: `DataColumnsByRootIdentifier.UnmarshalSSZ` and round-trip design

This file is committed before the proofs. It is a plan. It does not claim that the proofs are possible.
The theorem statements are in `lean/E2eDec/StmtDec.lean` and `lean/E2eDec/StmtComp.lean`.
It follows the form of the IndexedAttestation decoder (`DESIGN-T3.md`).

## 1. Inputs

| Item | Value |
| --- | --- |
| Go source | `prysm/_generated/mainnet/fulu.ssz.go` lines 1778–1816 |
| `.S` and data | `lv/link-dec` (`check.py` PASS all, bundle `7b8d6500…`) |
| Directive count | 229 lines. The directive number is the line number − 1 |
| New data | two format strings (63, 74 bytes). `encdeclink.py` checks that the rest is the same as the existing names |

## 2. Paths

| Path | Condition | Directives | Statement |
| --- | --- | --- | --- |
| size reject | `len < 36` | 2–10, 175–179 | `dcd_reject_size_stmt` |
| offset reject | buf[32:36] ≠ 36 | 11–15, 169–173 | `dcd_reject_offset_stmt` |
| accept | `len = 36 + 8n`, n ≤ 128 | 16–37, 43–55, 62–82, 87–93, 185–203 and 180–184 loop, 204–208 | `dcd_accept_stmt` |
| accept specification | EthLib accepts | — | `dcd_accept_spec_stmt` |
| alignment reject | `(len − 36) mod 8 ≠ 0` | 67, 131–167 | no statement (section 5) |
| overflow reject | n > 128 | 71, 94–130 | no statement (section 5) |
| round trip | encoder fast path after the accept | — | `dc_unmarshal_then_marshal_stmt` |

## 3. Callees

| Directive | Target | Form |
| --- | --- | --- |
| 23 | `runtime.makeslice` | `MakesliceC Heap e2eU8Type_addr 1 S` (len 0, cap 32) |
| 47 | `runtime.memmove` | `MemmoveC S` (buf → new block, 32 bytes) |
| 75 | `runtime.makeslice` | `MakesliceC Heap lvU64Type_addr 8 S` (len = cap = n) |
| 40, 58, 84 | `runtime.gcWriteBarrier2` | premise `writeBarrier = 0`. Prove that the branch is not taken |
| 211, 213, 215 | `runtime.panicBounds` | prove in each loop iteration that it is not taken (the form of the IndexedAttestation `ia_iter`) |
| 99, 136 | `runtime.convT64` | alignment reject, overflow reject. `ConvT64C` |
| 116, 153 | `fmt.errorf` | alignment reject, overflow reject. `FmtErrorfDWC` |
| 121, 158 | `runtime.newobject` | when errorf is nil. The rax ≠ 0 of DWC blocks it |
| 222 | `runtime.morestack_noctxt.abi0` | premise `guard + 16 < rsp` |

There is no new contract form.

## 4. Element loop

The loop head is `L_320` (directive 185). An iteration is 185–203 and 180–184.
It has the same instruction order as the IndexedAttestation `ia_iter` (147–165, 143–146). Only the registers and slots differ.
rax = i, rdx = n, rcx = cap − 36, rdi = buf + 36, rsi = receiver. Receiver slots: c + 32 = array pointer, c + 40 = len.
The array of the invariant = `ib.take (8i) ++ replicate (8(n − i)) 0` (same as IndexedAttestation).

## 5. Alignment reject and overflow reject

- The Go decoder allocates BlockRoot and writes it to the receiver before it checks alignment and overflow.
- Thus the alignment reject and overflow reject statements must have all of the makeslice, memmove, receiver write and write-barrier premises.
- The IndexedAttestation alignment reject and overflow reject are before the allocation, so this form cannot use them as is.
- The round trip is the main goal, so the alignment reject and the overflow reject stay N first. If time remains, they get frozen in a new statement file.

## 6. Round trip

- Machine: after the decoder accepts, call the encoder fast path (`dc_e2e_marshal_fast_main`) with the same receiver.
- The encoder return slot x − 144 is the first 8 bytes of the decoder spill area.
- The encoder scratch is the `S + 8` bytes that join the decoder scratch and return slot.
- Specification: `dc_e2e_spec_roundtrip` (an input that EthLib accepts serializes again to the same bytes).

## 7. Witness plan

- Size reject: lengths 0, 35. Offset reject: offset 0. Accept: n = 0, 1, 128.
- The accept Host needs both esz 1 and esz 8 makeslice. A model that branches on the type word goes into a new `.S` (the form of `BumpAllocT.S` of the list/vector work).
