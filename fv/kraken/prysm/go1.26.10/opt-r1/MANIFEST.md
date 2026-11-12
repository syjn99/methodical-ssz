# MANIFEST: OPT-R1 new ELF (Checkpoint encoder capacity reservation)

This directory is the target-binary record of the optimization test OPT-R1. It is a separate namespace.
The baseline ELF `c6403c02…911e` and its theorems, tables and records do not change.
The old theorems are about the old ELF. They do not carry over to the new ELF.

## 1. What changed

- Generator: branch `claude/ssz-gen-opt-r1`, commit `ca191bb` (parent `698c202`).
- New optional flag `--reserve-marshal=<type>`. The default is off.
- Off: the 16 generated files are byte-identical to the `698c202` output (`../../_generated/`).
- On (`Checkpoint` only in the `phase0.yaml` run): only one function body is different. It is `Checkpoint.MarshalSSZTo` of mainnet and minimal (`generated.diff`).
- One statement is added. If `cap(dst)-len(dst) < 40`, it appends 40 bytes one time and restores the length.
- `gen-wrap.sh` adds the flag only to the `phase0.yaml` run. `fv/kraken/gen/prysm-gen.sh` is unchanged.
- The `ssz/` runtime did not change. The Prysm `replace` points to the `698c202` tree.

## 2. Target

| Item | Value |
| --- | --- |
| Build | `GOOS=linux GOARCH=amd64 GOAMD64=v1 CGO_ENABLED=0 go build -p 2 -tags purego -trimpath`, Go 1.26.10 linux/arm64 host |
| Package | `fvphase1c/p1cbin` (the same `main.go` as the baseline, `../p1cbin-main.go.txt`) |
| ELF sha256 | `3ef7ac890ba1a797fb90877b84ad1a6ffe0ac283f77c10b09ffb2c8cd7b7f602`, 23486305 bytes. Not committed |
| Reproducibility | The second build used an empty GOCACHE. The sha256 and the build ID are the same (`build-ids.txt`) |
| Control build | A build of the same tree with the off output gives the baseline ELF `c6403c02…911e` |
| Link check | `link/RESULT`: PASS all. We used the existing tools (`gen/e2e/e2elink.py`, `link/conv.py`, `link/check.py`) with no changes |

## 3. Machine code of the new function (`link/norm/…Checkpoint.MarshalSSZTo.S`)

- 126 instructions, 574 bytes (baseline 85, 341).
- Frame `sub $0x90,%rsp` (baseline `$0x68`). The stack check has the form `lea -0x18(%rsp),%r12`.
- Runtime calls: `growslice` at three sites, `memmove` at two sites, `panicBounds` at one site, `morestack_noctxt` at one site.
- `panicBounds` is the `[:len(dst)]` bounds check. It has no contract. The theorem must prove that the branch is not taken.
- The zero array is filled with `movups %xmm15`. The theorem does not assume X15 = 0.
- The `.S` files of the other 6 functions and the 10 data items have the same sha256 as the baseline `../e2e/link/`.

## 4. Rebuild

1. Build the generator `ca191bb` with Go 1.26.10 and `-trimpath`.
2. `OPTR1_GEN=<generator> sh fv/kraken/gen/prysm-gen.sh <prysm-tree> fv/kraken/prysm/go1.26.10/opt-r1/gen-wrap.sh <out> gen`.
3. Put `<out>/gen/*/phase0*.ssz.go` in a copy of the baseline temporary tree (`../MANIFEST.md` §3).
4. Build `./fvphase1c/p1cbin` with the flags above. The object dump is the same as the regular expression of `fv/kraken/gen/prysm-elf.sh`.
5. `python3 -I -B fv/kraken/gen/e2e/e2elink.py filter <link-out> <objdump> <elf> <nm>`, `conv.py --norm`, `e2elink.py data`, `link/check.py`.

All steps ran one at a time inside the heavy-job gate.

## 5. Theorems and checks (Lean modules `fv/kraken/lean/E2e/OptR1/`)

The theorems are about the machine code of the new ELF. The old theorems did not change.

| Theorem | Range | Conclusion |
| --- | --- | --- |
| `E2e.OptR1.cpo_marshal_main` | `len + 40 ≤ cap < 2^63` | `(dst.ptr, len + 40, cap, nil)`. Writes only `dst[len..len+40]`. Does not use the heap |
| `E2e.OptR1.cpo_marshal_reject_main` | same range, Root length ≠ 32 | `(nil, ErrBytesLength)`. Writes only `dst[len..len+8]` (C-1: the epoch bytes are written before the Root length check) |
| `E2e.OptR1.cpo_marshal_grow_main` | `len ≤ cap < len + 40` | One new block. The caller array `pre ++ spare` is unchanged |
| `E2e.OptR1.cpo_marshal_reject_grow_main` | same range, Root length ≠ 32 | `(nil, ErrBytesLength)`. One new block. The caller array is unchanged |
| `E2e.OptR1.cpo_marshal_spec_k` | fast path | The same conclusion as the baseline `cp_e2e_marshal_spec_k`. The premise is the new frame |
| `E2e.OptR1.cpo_marshal_cover` | all `len ≤ cap` | Returns `pre ++ serialize`. There is no second growslice branch |
| `E2e.OptR1.cpo_marshal_reject_cover` | all `len ≤ cap` | `(nil, ErrBytesLength)` |

- Contract hypotheses: `GrowsliceC`, `MemmoveC` (existing forms). For `panicBounds` and `morestack`, the proof shows that the branch is not taken.
- There is no new premise form. The stack-check premise is `guard + 24 < rsp` (form of `E2eScal.lea_cmp_be_false`).
- The two reject theorems have the additional premise `cap < 2^63`. The baseline reject theorems do not have it. The cause is the signed comparison.
- The contract dependence of the reject path changed (item S1 of the review of OPT-R1).
- For `8 ≤ spare < 40`, the reject proof depends on `GrowsliceC`, `MemmoveC` and the heap budget.
- The baseline reject theorem (`spare ≥ 8`) is proved with no contract.
- `cpo_marshal_reject_cover` has the premise `MemmoveC`, which the baseline reject cover did not have.
- The covers have no frame. The two covers end with `⋆ True` (S2).
- The baseline has a cover with a frame (`E2e/CpWCoverF.lean`). This set does not have one.
- The four main theorems are exact for each range. Together, the four cover all `len ≤ cap`.
- Witnesses: `WitO` (fast path), `WitOW`·`WitOWR` (covers, spare 0, 7, 8, 39, 40, 41 and nil dst). There is a receiver Go value check.
- Only `cpo_marshal_main`, `cpo_marshal_cover` and `cpo_marshal_reject_cover` have direct witnesses (S4).
- `cpo_marshal_spec_k`, `cpo_marshal_grow_main`, `cpo_marshal_reject_main` and `cpo_marshal_reject_grow_main` are reached only through the cover witnesses.
- Negative tests: `negcases.json`, result `negative.json`. 21 of 23 passed. The two store mutations timed out. They do not count as passed.
- We ran the two store mutations again, one time each, with a case limit of 900 seconds (item S3, OPT-R1 integration). There is no third run.
- `o-tail-fit-store`: classification `outside`, not a pass. It ended at 484 seconds.
- The first error is at line 125 inside the theorem. `ecancel` fails at a store address shifted by one slot.
- Later there are heartbeat timeouts at lines 217 and 38. Line 38 is the `set_option … in` line before the theorem. It is outside the range.
- `o-tail-fit-val`: classification `timeout_heartbeat`, not a pass. It ended at 488 seconds.
- The first error is the heartbeat timeout at line 217. Neither run had a wall-clock timeout.
- Thus no passed negative test showed the epoch-store sensitivity of `tail_fit`.
- `negative.json` is the record of the 300-second run. The results of the second runs are in `RESULT.json` `negatives.s3_rerun_int3`.
- Axioms gate: `axioms-gate.json` PASS, 3860 declarations. Declaration drift: `decl-drift.txt`, 377 ADDED, all in `E2e.OptR1`.
- `axioms-gate.json` is the record of the test-branch tree (`5821b19`).
- The record of the integration tree is `../e2e/axioms-gate.json`. PASS, declarations 4519 = 4142 + 377.
- Go differential (arm64, Go semantics only): `diff/`. Benchmarks (arm64 only): `bench/`.
- The new `.S` is not a Lake input. If the `.S` changes, rebuild `E2e.OptR1` from clean.

## 6. Error-path effects and benchmarks (items S5, S6 of the review of OPT-R1)

- The error-path effects changed (contract item 6).
- If the Root is not valid and `8 ≤ spare < 40`, the new code allocates one block. The old code does not allocate.
- In the same case, the new code does not write the caller spare. The old code does the C-1 write.
- The return values are the same. They are `(nil, ErrBytesLength)`.
- The benchmarks ran only on linux/arm64. There are no x86-64 results. The values are in `bench/bench-summary.json`.
- B2 (nil dst): allocations 2 → 1, 56 → 48 B. ns is faster. The size of the change is different in each run.
- B3 (cap 8): the expected 2 → 1 allocations did not occur. Both are 2.
- Reason: at cap 8 the old code fits the epoch, so it grows only one time. An escaping `make` adds one allocation on both sides.
- B5 (fast-path reuse): the new code is slower. 1.92 → 2.19 ns, +14 %.
- B8 (1000 appends): allocations 18 → 17. ns did not improve. +3.4 %.
- B9 (invalid Root, spare 16): allocations 0 → 1, 0 → 48 B. ns also became worse.
- `MarshalSSZ()` (B1) and nested AttestationData (B7) did not change.
- A partial rerun by the reviewer (only B2, B5, B8, B9, not the full procedure) showed the following.
- B5 +12.6 % reproduced (1.90 → 2.14 ns, the ranges do not overlap).
- The allocation counts and B/op reproduced.
- In the allocating cases, ns varied by up to about 35 % between rounds. B2-new 24.96 and 16.94 ns, B9-new 24.02 and 15.92 ns.
- B2-old was 26.4 ns (worker run 38.6 ns). Thus we do not give a fixed percentage for B2.
- Conclusion: the re-verification that keeps correctness was shown. A general speed improvement was not shown. The results are mixed.

## Addendum (2026-11-12, integration of the `--gen5` work, item S1 of the review of the `--gen4` and H6 integration)

- The value 4519 in "The record of the integration tree" above is the value at the OPT-R1 integration. We do not change that line.
- The record of the integration tree now is also `../e2e/axioms-gate.json`. After the `--gen5` integration it is PASS, 9758 declarations.
- The `E2e.OptR1` declarations are included in that number. The `axioms-gate.json` (3860) of this directory stays as the record of the pilot-branch tree.
