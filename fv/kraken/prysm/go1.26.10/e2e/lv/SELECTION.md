# SELECTION: list/vector hand proof targets (list/vector work)

This file is committed before the proofs start.
The targets and paths do not change after this commit.
The draft theorem statements are committed separately in `STATEMENTS.md` and `lean/E2eList/Stmt*.lean`.

## 1. Base

| Item | Value |
| --- | --- |
| Base commit | `6a78c591e8bcd698b7b9313b1c09cb25f3986911` (remote head of `syjn99/ssz-fv-reuse-milestone`) |
| Branch | `claude/ssz-fv-list-vector-20261112` |
| Target ELF sha256 | `c6403c02a110ffd6fe6d31a3c89cd395ac457b5d62e60e2e611b8ab9a8dd911e` |
| ELF rebuild | Made again on this machine. The sha256, build ID, objdump sha256 and nm sha256 are the same as in `build-ids.txt` |
| Selection author model | `claude-fable-5-2` (planner) |

## 2. Basis files

- `prysm/TYPES.md`: kind, field count, instruction count, call set.
- `prysm/SCOPE-P6.json`: first failure kind, new pattern kind, missing contracts.
- `prysm/_generated/mainnet/*.ssz.go`: generated Go source.
- `conv.py --norm` output of the rebuilt ELF: the line count and the `callq` targets of `UnmarshalSSZ`.

## 3. Candidate table (`UnmarshalSSZ` only)

The line count is the line count of the normalized `.S`.
"Contract" means whether the function calls only callees that have a form in `CONTRACTS.md`.

| Type | list/vector form | `.S` lines | Callees | Contract | Verdict |
| --- | --- | --- | --- | --- | --- |
| `SyncAggregate` | bitvector 512 (64 bytes), bytes96 | 106 | makeslice 2, memmove 2 | yes | **selected** |
| `SyncCommittee` | vector[512] of bytes48 (`[][]byte`), bytes48 | 137 | makeslice 3, memmove 2, panicBounds 1 | yes | **selected** |
| `IndexedAttestation` | list[uint64] max 2048, delegate `AttestationData`, bytes96 | 279 | fmt.errorf 3, AttestationData.UnmarshalSSZ 1, convT64 2, makeslice 2, memmove 1, newobject 4, panicBounds 3 | yes for the accept path. The fmt paths are checked per format | **selected (if time remains)** |
| `HistoricalBatch` | two vector[8192] of bytes32 | 182 | makeslice 4, memmove 2, panicBounds 4 | yes | excluded: same form as SyncCommittee and larger |
| `Deposit` | vector[33] of bytes32, delegate `Deposit_Data` | 156 | fmt.errorf 1, Deposit_Data.UnmarshalSSZ 1, others | the repo has no `Deposit_Data` decoder specification | excluded |
| `Attestation` | bitlist, delegate, bytes96 | 218 | ValidateBitlist 1, growslice 1, fmt.errorf 2, others | the contracts are based on Go 1.26.3 | excluded: postponed until after the three selected types |
| `PendingAttestation` | bitlist, hand-written Slot and ValidatorIndex | 256 | same as above, and more | same as above | excluded |

Check of the excluded targets (task instruction section 2):

- The three selected types do not use `gen/scal/*`.
- The three selected types do not target `AttestationData.MarshalSSZTo`. IndexedAttestation uses only the already proved `AttestationData.UnmarshalSSZ` specification.
- The three selected types are not in the held-out evaluation (H6) target group. The 64-byte bitvector of SyncAggregate and the `[][]byte` of SyncCommittee are not field forms of that group.
- The `.S`, IR and proofs of the H6 target group were not opened.

`SCOPE-P6` classifies `SyncAggregate` and `SyncCommittee` as "missing contract (moveSlice*)".
The `.S` of `UnmarshalSSZ` has no `moveSlice*` call.
That classification is for all three functions of the type. The encoders are out of the scope of this task.

## 4. Targets and paths

| Target | Function | Paths | Order |
| --- | --- | --- | --- |
| `SyncAggregate` | `UnmarshalSSZ` | size reject (`len ≠ 160`), accept, EthLib specification correspondence, witness | 1 |
| `SyncCommittee` | `UnmarshalSSZ` | size reject (`len ≠ 24624`), accept (512-iteration loop invariant), EthLib specification correspondence, witness | 2 |
| `IndexedAttestation` | `UnmarshalSSZ` | size reject (`len < 228`), offset reject (`≠ 228`), accept (element loop), alignment and overflow rejects only if the contracts fit | 3 |

Out of scope: `MarshalSSZTo`, `SizeSSZ`, `HashTreeRoot` of the three types, the morestack paths, the paths with the write barrier on.
The out-of-scope paths are reported as "not proved (N)".

## 5. Limits

- This table is a selection. It does not state that the proofs are possible.
- The host is darwin/arm64. x86-64 machine code was not executed.
- The contracts are the result of a read of the Go 1.26.3 runtime source. For the Go 1.26.10 runtime, only the scope of `e2e/RUNTIME-1.26.10.md` is checked.
