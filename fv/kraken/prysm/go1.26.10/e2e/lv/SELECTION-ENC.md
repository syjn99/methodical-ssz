# SELECTION-ENC: first variable-length encoder hand proof target (ENC stream)

This file is committed before the proofs.
The target and paths do not change after this commit.

## 1. Base

| Item | Value |
| --- | --- |
| Base commit | `1b5f524` (the head of `claude/ssz-fv-list-vector-20261112`) |
| Branch | `syjn99/ssz-fv-enc` |
| Target ELF sha256 | `c6403c02a110ffd6fe6d31a3c89cd395ac457b5d62e60e2e611b8ab9a8dd911e` (the same ELF as the list/vector work) |
| objdump sha256 | `580b0da9…` (same as `build-ids.txt`) |
| Author model | `claude-opus-5-5` (implementer) |

## 2. Base conditions (task instruction)

- There is exactly one variable-length field.
- That field should be a uint64 list or a list of fixed-size byte vectors.
- `MarshalSSZTo` does not call a prohibited function.
- It is not a prohibited type.

## 3. Candidate table (`MarshalSSZTo` only)

The instruction counts and calls are the output of `gen/e2e/enclink.py callgraph` (`lv/callgraph-enc.json`).

| Type | Fields | Instructions | Calls | Verdict |
| --- | --- | --- | --- | --- |
| `DataColumnsByRootIdentifier` (fulu) | `block_root` Bytes32, `columns` List[uint64, 128] | 107 | growslice 3, memmove 1, morestack 1 | **selected** |
| `DataColumnSidecarsByRangeRequest` (fulu) | two uint64, `columns` List[uint64, 128] | 126 | growslice 4, morestack 1 | reserve. Same form as the selected target |
| `IndexedAttestation` (phase0) | List[uint64, 2048], AttestationData, Bytes96 | 173 | `AttestationData.MarshalSSZTo` 1, growslice 3, newobject 2, fmt.errorf 1, gcWriteBarrier2 1, memmove 1, morestack 1 | excluded |

`IndexedAttestation` check:

- `AttestationData.MarshalSSZTo` is not inlined.
- The objdump has `CALL …(*AttestationData).MarshalSSZTo(SB)` once.
- Thus it is excluded, as the task instruction specifies.

`DataColumnsByRootIdentifier` is not in the list of prohibited types.
The `.S`, IR and proof files of prohibited types other than this type were not opened.

## 4. Go source of the selected target

`prysm/_generated/mainnet/fulu.ssz.go` lines 1754–1776:

    func (c *DataColumnsByRootIdentifier) MarshalSSZTo(dst []byte) ([]byte, error) {
        offset := 36
        if len(c.BlockRoot) != 32 { return nil, ssz.ErrBytesLength }
        dst = append(dst, c.BlockRoot...)
        dst = ssz.WriteOffset(dst, offset)
        offset += len(c.Columns) * 8
        if len(c.Columns) > 128 { return nil, ssz.ErrListTooBig }
        for _, o := range c.Columns { dst = binary.LittleEndian.AppendUint64(dst, o) }
        return dst, err
    }

`ssz.WriteOffset` and `AppendUint64` are inlined.
Thus each of the three `append` sites can call `runtime.growslice`.

## 5. Callees and contract instances

| Directive | Target | Path | Class | Instance |
| --- | --- | --- | --- | --- |
| 23 | `runtime.growslice` | `append(dst, BlockRoot...)`, capacity too small | (b) | `GrowsliceC Heap e2eU8Type_addr 1 S`, num 32 |
| 36 | `runtime.memmove` | BlockRoot 32-byte copy | (b) | `MemmoveC S`, n = 32 |
| 49 | `runtime.growslice` | `WriteOffset`, capacity too small | (b) | same form, num 4 |
| 94 | `runtime.growslice` | `AppendUint64` of the loop, capacity too small | (b) | same form, num 8 |
| 112 | `runtime.morestack_noctxt.abi0` | stack too small | (c) | premise `guard + 8 < rsp` |

- The type word of all three growslice sites is `type__+387072` (uint8). `enclink.py data` checks it.
- That word is the same as the type word of the Checkpoint encoder (`E2e.Data.e2eU8Type_addr`).
- All element sizes are 1. They are the same as the modeled esz 1 (`rt_growslice`). No new model is necessary.
- There are no `fmt.errorf`, `newobject`, `panicBounds` or write-barrier calls.
- The directive number is the line number of the normalized `.S` minus 1.

## 6. Paths (goals)

| Path | Condition | Goal |
| --- | --- | --- |
| fast path | `len + 36 + 8n ≤ cap` | K |
| first-site grow path | `cap < len + 32`, the new capacity holds the rest | K |
| any-site grow path | the other capacity cases | outside the goals. Recorded as N |
| bytes-length reject | `len(BlockRoot) ≠ 32` | K |
| too-big reject | `len(Columns) > 128`, capacity sufficient at the first two sites | K |
| morestack | stack too small | N, the premises block it |

## 7. Composition (obligation 7)

The repo has no decoder accept specification for this type.
Thus the composition of decode then encode is N.

## 8. Limits

- This table is a selection. It does not state that the proofs are possible.
- The host is darwin/arm64. x86-64 machine code was not executed.
