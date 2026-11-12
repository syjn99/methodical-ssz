# DESIGN-ENC: `DataColumnsByRootIdentifier.MarshalSSZTo` hand proof design

This file is committed before the proofs. It is a plan. It does not claim that the proofs are possible.
The theorem statements are in `lean/E2eEnc/StmtEnc.lean`.
`SELECTION-ENC.md` gives the selection reasons.

## 1. Inputs

| Item | Value |
| --- | --- |
| Go source | `prysm/_generated/mainnet/fulu.ssz.go` lines 1754–1776 |
| `.S` | `lv/link-enc/norm` (`check.py` (a)–(f) PASS, bundle `f7cdf5e5…`) |
| Directive count | 118 lines. The directive number is the line number − 1 |
| Receiver layout | `state` 0, `BlockRoot` 8 (ptr, len, cap), `Columns` 32 (ptr, len, cap), `unknownFields` 56, `sizeCache` 80, size 88 |
| Receiver slots read | c + 8, c + 16, c + 32, c + 40 |
| Arguments | rax = c, rbx = dst.ptr, rcx = len, rdi = cap |
| Result | rax, rbx, rcx = result slice. rdi, rsi = the two error words |

## 2. Paths

| Path | Condition | Directives | Theorem statement |
| --- | --- | --- | --- |
| fast path | `bl = 32`, `n ≤ 128`, `len + 36 + 8n ≤ cap` | 2–15, 29–44, 50–60, 82–89, 79–81 loop, 100–105 | `dc_marshal_fast_stmt` |
| first-site grow path | `len ≤ cap < len + 32`, `len + 36 + 8n ≤ nextSliceCap (len + 32) cap` | adds 16–28 to the fast path | `dc_marshal_grow_stmt` |
| bytes-length reject | `bl ≠ 32` | 2–11, 70–78 | `dc_reject_bytes_stmt` |
| too-big reject | `bl = 32`, `len + 36 ≤ cap`, `128 < n < 2^63` | 2–15, 29–44, 50–55, 61–69 | `dc_reject_toobig_stmt` |
| fast path specification | same as the fast path | — | `dc_marshal_spec_stmt` |
| first-site grow path specification | same as the first-site grow path | — | `dc_marshal_grow_spec_stmt` |
| bytes-length reject specification | BlockRoot length ≠ 32 | — | `dc_spec_reject_bytes_stmt` |
| too-big reject specification | element count > 128 | — | `dc_spec_reject_toobig_stmt` |
| any-site grow path | site 2, site 3 (any iteration), more than one grow | 45–49, 90–99 | no statement. N |
| morestack | `guard + 8 ≥ rsp` | 106–117 | N. The premise `guard + 8 < rsp` blocks it |

- `bl` is the BlockRoot length word at c + 16. `n` is the Columns length word at c + 40.
- The `jg` of the too-big reject is a signed comparison. Thus `n < 2^63` is a premise. Go `len` is in that range.
- The too-big reject covers only the case where the first two sites do not grow. The too-big reject with a grow is N.
- In the too-big reject, 36 bytes are already written to dst. The postcondition states those bytes.

## 3. Frame (x = entry rsp)

| Position | Writing directive | Path | Name in the statement |
| --- | --- | --- | --- |
| x | return address | all | `ra` |
| x − 8 | 5 (`push %rbp`) | all | `fp` |
| x + 8 | 12 (rax) | fast path, first-site grow path, too-big reject | `s1` |
| x + 16 | 8 (rbx) | all | `s2` |
| x + 24 | 16 (rcx) | first-site grow path | `s3` |
| x − 16 | 17 (root pointer) | first-site grow path | `l16` |
| x − 24 | 58 (Columns pointer) | fast path, first-site grow path | `l24` |
| x − 32 | 31 (dst pointer) | fast path, first-site grow path, too-big reject | `l32` |
| x − 40 | 56 (n) | fast path, first-site grow path | `l40` |
| x − 48 | 90 (i) | any-site grow path only | not in the statements |
| x − 56 | 32 (cap) | fast path, first-site grow path, too-big reject | `l56` |
| x − 64 | 30 (len + 32) | fast path, first-site grow path, too-big reject | `l64` |
| x − 72 | 91 (element word) | any-site grow path only | not in the statements |
| x − 136 | growslice spill 40 bytes | first-site grow path | `spl` |
| x − 144 | call return slot | fast path, first-site grow path, too-big reject | `rslot` |
| x − 144 − S | scratch `S` | fast path, first-site grow path, too-big reject | `scratch` |

- Each statement has as premises only the slots that its path uses. The rest is in `R` and does not change.
- The postcondition states the exact values of x + 8 and x + 16 (rax, rbx).
- In the postcondition, the local slots, the return slot and the scratch are existential variables with only the length specified.

## 4. Element loop (in the fast path and the first-site grow path)

The loop head is `L_13a` (directive 82).
One iteration is 82–89 and 79–81.
Invariant `DcInv i` (`i ≤ n ≤ 128`):

- rax = block pointer `bp`, rbx = len + 36 + 8i, rcx = block capacity, rdx = Columns pointer pc, rsi = i, r8 = n.
- rsp = x − 136, rbp = x − 8.
- Block: `pre ‖ root ‖ dcOff ‖ cb.take (8i)` at `bp`, then `rest.drop (8i)`, which is not written yet.
- Capacity: len + 36 + 8n ≤ capacity. Thus the `jae` of 89 is always taken. It does not reach growslice 94.
- The input `cb`, the receiver slots, the frame and `R` stay the same.

One iteration: 83–84 `cmp %r8,%rsi; jge` is not taken because i < n (the form of `jge_false512`).
85 rbx += 8, 86 `mov (%rdx,%rsi,8),%r9` reads 8 bytes.
88–89 `cmp %rbx,%rcx; jae` is taken by the capacity premise.
80 `mov %r9,-0x8(%rbx,%rax,1)` writes 8 bytes at bp + len + 36 + 8i. 81 rsi += 1.
Loop end: at i = n, the `jge` of 84 goes to L_17e (100).
If n = 0, there is no iteration.

The proof form is the same as `E2eList/IaLoop.lean` (`ia_iter`, `ia_exit`, `ia_loop`).
The forms of `Fk.block_split` and `out_step` are used again. The written block is `cb.take (8i) ++ rest.drop (8i)`.

## 5. Written bytes and offsets

| Directive | Address | Bytes |
| --- | --- | --- |
| 36 memmove | dst.ptr + len | BlockRoot 32 bytes |
| 51 `movl $0x24,-0x4(%rbx,%rax,1)` | dst.ptr + len + 32 | `dcOff` = 24 00 00 00 (offset 36) |
| 80 (iteration i) | dst.ptr + len + 36 + 8i | the 8 bytes of Columns[i] |

- The `movl` of 51 is a 32-bit immediate store. The 4 bytes `Int.toBytes 4 36` = `dcOff`.
- The 8-byte read and write of the loop are the same bytes (`toBytes_ofInt_ofBytes`).
- Specification side: `pdcEnc g = root ‖ dcOff ‖ u64Bytes cols`, and show `serialize prysmDcDesc g.toValue = .ok (pdcEnc g)`.
- That proof uses again the forms of `E2eList.pia_serialize`, `Fv1.serializeEach_u64`, `Fv1.inl_*`.

## 6. First-site grow path

- The `jae` of 15 is not taken (cap < len + 32).
- 16–23: rcx goes to x + 24, and rdx (root pointer) goes to x − 16. growslice (rax = dst.ptr, rbx = len + 32, rcx = cap, rdi = 32, rsi = uint8 type).
- Contract `GrowsliceC Heap e2eU8Type_addr 1 S`: old block `pre` (len bytes), new block `pre ++ tail`, `nextSliceCap ≤ newCap`.
- 24–28: recovers rdx, rdi = newCap, r8 = len + 32, rcx = len, rbx = new pointer. It continues to 29 (L_7c).
- After that, the code is the same as the fast path. Only the block pointer and the capacity differ.
- `hfit` gives that sites 2 and 3 do not grow.
- Thus the fast-path lemmas have the block pointer and the capacity as parameters. The fast path and the first-site grow path use them together.

## 7. Any-site grow path (no statement, N)

- growslice can be called at site 2 or in any loop iteration.
- To cover those cases, the invariant must state "block = bytes written before ++ tail" independently of the block pointer.
- After each grow, the old block stays in the postcondition. Their count differs for each path.
- Thus the postcondition needs an existential predicate (garbage blocks). The heap budget must also depend on the grow count.
- This unit does not write it as a statement. The report records it as an obstacle.

## 8. Witness plan

- Fast path: n = 0, 1, 128. The Host is `DcMarshal` and the `rt_memmove` model.
- First-site grow path: n = 0, 1, 128. Add the `rt_growslice` (esz 1) model to the Host. A large cap is necessary to hold capacity 128 (example: cap 4000, len 3970).
- Bytes-length reject: bl ∈ {0, 31, 33}. Too-big reject: n = 129.
- If the models do not fit the existing Host forms (`Fk.WHost`, `E2e.WitCpMR`), record that fact.

## 9. Risks and judgments

- The stack guard has the form `lea -0x8(%rsp),%r12`. `E2eScal.lea_cmp_be_false` (N = 8) closes it.
- `add $-0x80,%rsp` and `sub $-0x80,%rsp` are negative immediates. The first build shows whether Kraken reads them as −128.
- The `movl` form of 51 (a 32-bit immediate stored at an indexed address) may not be in the existing proofs. If it blocks, record it in the Kraken request list.
- Large `simp` sorting can use time in the witnesses (section 4 of the list/vector work report). In that case, measure the cause and then add a setting.
