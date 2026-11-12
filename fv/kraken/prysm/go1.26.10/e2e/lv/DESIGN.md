# DESIGN: list/vector hand proof design (SyncAggregate, SyncCommittee)

This file is committed before the proofs start.
The theorem statements are in `STATEMENTS.md` and `lean/E2eList/Stmt*.lean`.
This file is a plan. It does not claim that the proofs are possible.

## 1. Inputs

| Item | Value | Basis |
| --- | --- | --- |
| Base commit | `6a78c591e8bcd698b7b9313b1c09cb25f3986911` | `SELECTION.md` |
| Target ELF sha256 | `c6403c02a110ffd6fe6d31a3c89cd395ac457b5d62e60e2e611b8ab9a8dd911e` | `prysm/go1.26.10/build-ids.txt` |
| `.S` and data | `lv/link/norm`, `lv/link/data` | `gen/e2e/lvlink.py`, `link/conv.py --norm`, `link/check.py` (`lv/link/RESULT`) |
| Receiver layout | `go_fields` of `prysm/ir/ir-mainnet.json` | size 88 for both types |
| Specification | EthLib `deserialize`, hand `Desc` (`lean/E2eList/Desc.lean`) | consensus-specs altair |
| Producer `Desc` | `lv/desc/*.desc.json` | the sha256 is the same as the record in `gen/desc/results/main.result.json` |

## 2. Items used as is

- The contract forms `MakesliceC`, `MemmoveC` (`lean/Fk/Contracts.lean`). There is no new contract form.
- `E2e.Data.e2eU8Type_addr`, `E2e.Data.e2eErrSize_addr`. `lvlink.py` checks that they are the same operands.
- Kraken step tactics: `kat`, `klabel`, `load_step`, `store_step_at`, `kunfold`, `ecancel`, `eaddr`.
- Reject proof: the body of `E2eScal.H4.dd_e2e_reject_size_main`. Only the directive numbers change.
- Specification bridge: `deserialize_enc`, `accepted_is_enc` of `Fv1.Transfer`. It follows the order of `DdSpec.lean`.
- SyncAggregate head: `E2eScal.dechead_seg` (`Compose.lean`). The frame is `sub $0x20`, spill slots `0x38`, `0x30`. It is the same as the SyncAggregate `.S`.
- SyncAggregate tail: `E2eScal.decepi_seg` (`sub`/`add $0x20`).
- SyncCommittee AggregatePubkey field: `E2eScal.bytesdec_seg` (`SegN.lean`), n = 48, src = 24576.
- Pointer tail: `E2eScal.bytesdec_tail_seg`.

## 3. Items that need parameters

- `bytesdec_seg_z` of `SegN.lean` accepts only `hn : n = 32 ∨ n = 48 ∨ n = 96`.
- SyncAggregate SyncCommitteeBits is n = 64, src = 0. The existing lemmas do not cover it.
- Plan: add a lemma for the case n = 64 in a new file. `SegN.lean` does not change.
- SyncAggregate SyncCommitteeSignature is n = 96. At `.S` directive 50, a `nop` is between `mov $0x60,%ecx` and `callq`.
- That form is the same as the `nop` form of `DdSegNop.lean`. But that lemma is fixed to n = 32.
- Plan: add a lemma for the n = 96 `nop` form in a new file.
- The SyncCommittee head and tail are `sub $0x30`, spill slots `0x48`, `0x40`. The `decHead` and `decEpi` templates are fixed to `0x20`.
- Plan: prove the SyncCommittee head and tail with hand steps. Do not add parameters to the templates.

## 4. New items

### 4.1 SyncCommittee loop invariant

The loop head is `L_a0` (directive 40). The entry rsp is x.
The invariant `ScInv i` states the items below for `i ≤ 512`.

- Registers: rax = i, rsp = x − 56, rbp = x − 8, r14 = entry value.
- Receiver: `+8` = A, `+16` = 512, `+24` = 512. The three AggregatePubkey slots keep their entry values.
- Array A: `lvHdrs 48 (ps.take i) ++ replicate (24·(512 − i)) 0`. `ps` is the i pointers received so far.
- Elements: `lvElems ps (pks.take i)`.
- Heap: `Heap (avail − 12288 − 48·i)`.
- Stack: x − 32, x − 24, x − 16 are 8 bytes, and their values are not specified. The same applies to the 24-byte spill slots and `lo`.
- Spill slots x + 8 = receiver, x + 16 = buf. The input, `R`, `writeBarrier = 0` and the stack guard stay the same.

One iteration (`sc_iter`, directives 40–71, 36–39) goes from `ScInv i` to `ScInv (i + 1)`.

- makeslice(uint8, len 0, cap 48): new block p, 48 bytes of 0, heap −48.
- memmove(p, buf + 48i, 48): writes the i-th 48-byte slice of `pks.flatten`. A slice split lemma is necessary.
- Bounds check `cmp %rsi,%rdi; jae`: rsi = receiver `+16` = 512, rdi = i < 512. Prove that the branch is not taken.
- Header store: 48 at A + 24i + 8 and + 16, p at A + 24i. It changes the i-th 24 bytes of the 0 block.

Exit (directives 41–42): at i = 512, `jge` is taken. After that come the AggregatePubkey field and the tail.
It follows the induction method of Go 1.26.3 `lu_loop` and `fv_loop` (induction on `j`, `i + j = n`).
The loop is not unrolled 512 times.
The `⋆ fun _ => True` tail of LcLoop is not used.

### 4.2 Contract instances

| Call site | Contract | ty | esz | cnt | Stack window |
| --- | --- | --- | --- | --- | --- |
| SyncAggregate 16, 51 | `MakesliceC` | `e2eU8Type_addr` (`type__+387072`) | 1 | 64, 96 | return x − 48, spill x − 40 (24), scratch S |
| SyncAggregate 31, 67 | `MemmoveC` | | | n = 64, 96 | return x − 48, scratch S |
| SyncCommittee 16 | `MakesliceC` | `lvSliceType_addr` (`type__+337600`) | 24 | 512 | return x − 64, spill x − 56 (24), scratch S |
| SyncCommittee 48, 84 | `MakesliceC` | `e2eU8Type_addr` | 1 | 48 | same as above |
| SyncCommittee 57, 100 | `MemmoveC` | | | n = 48 | return x − 64, scratch S |

`MakesliceC Heap ty 24 S` is an instance of the existing form. It is not a new form.
The repo has no abstract model for esz 24 (of the `bump_makeslice` kind). It has only esz 8 and esz 1.
Thus the SyncCommittee witness needs an esz 24 model. That model is a small assembly that satisfies the existing contract form.
The addition of the model is decided again in the witness unit.
The abi.Type bytes of `lvSliceType` are in `lv/link/data/lvSliceType.data`. The contract does not read the type descriptor.

### 4.3 Excluded paths

- `runtime.morestack_noctxt.abi0`: premise guard < rsp. Prove that `jbe` is not taken.
- `runtime.gcWriteBarrier2`: premise `writeBarrier = 0`. Prove the branch.
- `runtime.panicBounds` (SyncCommittee 124): class (a). Prove that the bounds check in each iteration is not taken.

### 4.4 Specification bridge

- SyncAggregate: the bit field of `PSa.toValue` is `unpackBits bits 512`. 512 % 8 = 0, so there is no padding check.
- SyncAggregate `accepted_is_enc` needs `packBits (unpackBits b 512) 64 = b` on 64 bytes.
- This equation has 2^512 cases, so `decide` cannot solve it. A general lemma is necessary.
EthLib `Proofs/Ssz/Codec/CanonicalBits.lean` and other files have candidate names. Whether they are usable was not checked.
- SyncCommittee: show that `vectorSlices` divides 24576 bytes into 512 slices of 48 bytes. Then solve `deserializeEach`.
- For both types, reject completeness comes from "EthLib accepts ⇔ the size is correct".

## 5. Frame table

| Slot | SyncAggregate (`sub $0x20`) | SyncCommittee (`sub $0x30`) |
| --- | --- | --- |
| return address | x | x |
| rbp save | x − 8 | x − 8 |
| rax spill | x + 8 | x + 8 |
| rbx spill | x + 16 | x + 16 |
| locals | x − 16 (pointer) | x − 32 (i), x − 24 (3i), x − 16 (pointer) |
| callee spill | x − 40 (24) | x − 56 (24) |
| callee return slot | x − 48 | x − 64 |
| scratch | x − 48 − S | x − 64 − S |
| return slot value at the end | `addrOf (k + 68)` | `addrOf (k + 101)` |

The directive number is the line number in the `.S` file, counted from 0. Label lines are also counted.

## 6. Witness plan

`fv/AGENTS.md` requires a witness of a concrete state for each main theorem.
SyncAggregate and SyncCommittee have a fixed size. There is one witness for each type.
The witness makes a Host in the method of `WitDd*`. `bump_makeslice1` and `rt_memmove` fill the contracts.
SyncCommittee has no esz 24 makeslice model (4.2). Without a witness, SyncCommittee is not complete.

## 6a. The length of `lvElems` (review r1 S6)

- If the two lists have different lengths, `lvElems ps es` discards the remainder and ends with `emp` (`| _, _ => emp` of `Defs.lean`).
- All current statements fix the two lengths to 512. The conclusion has `ps.length = 512`, and the premises have `pks.length = 512` (`PSc` is `Vector … 512`).
- Thus in the current statements, no element is dropped.
- A use for a list with a variable length needs a new definition with a condition that the lengths are equal. This definition is not used as is.

## 7. Limits

- The host is darwin/arm64. x86-64 machine code was not executed.
- The hand `Desc` was written without a copy of the consensus-specs source text. A visual check confirmed that it differs from the producer `Desc` only in names. No theorem has checked this yet.
- The `.S` of `IndexedAttestation` is not committed. Link check (d) failed with the clang of this machine (`ATTEMPTS.md`).
- There are no theorem statements for IndexedAttestation. The repo has no function specification form (`AdUAccC`) for `AttestationData.UnmarshalSSZ`.
