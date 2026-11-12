# DIRECTION: direction of the codec verification (2026-11-06)

This document gives the direction that the next sessions follow. The detailed rules are in `fv/AGENTS.md`, and the current status is in `REPORT.md`.

## 1. Goal

Prove on Kraken x64 that the x86-64 code that methodical-ssz generates accepts, rejects and encodes as the EthLib SSZ specification says. The proofs are a means to show generator defects (the sszgen fixes F1, F2, G1–G3 and H1 are examples). The next goal is automatic proofs for all Prysm Fulu types (1c). Produce results quickly. Put the production of results before the improvement of checkers.
On 2026-11-12, the test-type evidence was removed from the tree (`HISTORY.md` section 13). The goal is the Prysm generated code, so the test-type evidence is no longer part of the goal.

## 2. Current status (0ef30e3)

At `0ef30e3`, gate 1 was not passed. That gate had 55 main theorems for the decoders, encoders and size functions of the 9 test types, 80 witness declarations, 16 negative tests and 0 nonstandard axioms.
The three reviews (re-proof, fix, fix 2) all identified this item: the link checks (g)(h) read the spelling of the Lean and Go sources, so mutations got through them.
The gate 1 evidence was removed on 2026-11-12. Tag `archive/fv-before-workflow` holds it. No one evaluated gate 1 again on the current tree. The current status is in `REPORT.md`.

## 3. Trust base (TCB) and decisions

| Item | Now | Decision |
| --- | --- | --- |
| Lean kernel, Kraken x64 semantics, EthLib specification, Kraken = real CPU | Trusted | Keep. Shared base |
| ELF → Lean program (objdump, conv.py, include) | Cross-check of three independent decoders + symbol and displacement checks (a)–(e) | Keep. Stricter than con-agua, and it was never broken |
| Rebuild tracking (f) SHash | Hash file + source text comparison | **Delete.** Register the `.S` files and data files as `input_file` in the library `needs` of `lakefile.toml` (the method of con-agua `ConAgua/AsmFile/Include.lean` lines 37–39). The file contents go into the module input hash, and Lake rebuilds |
| Hand-written constants + (g)(h) + role classification + golits.go | Regular expressions on Lean and Go sources | **Delete.** The converter extracts rodata, itabs, type descriptors and `staticuint64s` from the ELF into byte files and includes them like code. The theorems use those definitions instead of hand constants. "Lean constant = ELF bytes" becomes part of the same hash binding as (a). This is the same structure as the `ldc` item in con-agua DESIGN.md (the constants are part of the program term, and the reality of the bytes is trust in the converter) |
| Go value checks (goval, layout.go) | Python, go/types table. Both were removed on 2026-11-12 (`lean/tools/wit/`) | In 1c X2, move them to Lean predicates and read the layout from the included abi.Type |
| Go runtime contracts | Abstract model, consistency only | Keep. Proofs of runtime functions come after stage 2 (HTR) |

Principle: Make a Lean theorem of all that can be said about the bytes of the binary. Keep only one external tool: "the converter that moves the bytes into Lean". Do not make changes that make the Python checkers smarter.

## 4. Order

1. **Cleanup session** (ssz-fv-cleanup, half a day): reduce the code, comments, reports and artifacts. Do not change theorem statements.
2. **Fix 3 = link redesign** (ssz-fv-reprove-fix3, 1 day) ∥ **1c** (ssz-fv-phase1c, 5 days). Both branch from the same point. For the first two days, 1c does work that does not touch `lean/Fk` or `link/` (Prysm Fulu type list and instruction statistics, `Desc` checker, generator skeleton). After fix 3 is in-review, 1c rebases onto it and makes X1 and X2 with the include design.
3. Scope of fix 3: `input_file` registration and SHash deletion, data include and the deletion of (g)(h)/role classification/golits.go, real type descriptors and initialized error globals in the error witnesses, Scalars non-nil reject theorem, postcondition remainder (NeMarshal R, ListC stack, sc_size, r14), ListC element offset order reject, gate table correction (astra fix 2 review section 8).

## 5. Fixed baseline

Generator source `698c202`, merge base `2d0150b`. Go 1.26.3 linux/amd64 GOAMD64=v1 purego trimpath CGO_ENABLED=0. Kraken `6064eec`, EthLib `8621856`, Lean nightly-2026-09-21. ELF `9c850c97…c501`. The two reduced Prysm types are from v7.1.8 `51b5a75`. The Prysm source of 1c is `ab15ff70c72a568c870b2de662474685a95de294` (slice + `ssz-size`), fork Fulu, and generation occurs only in temporary worktrees. We do not claim that it is equal to the fixed-array pin. The target compiler of 1c is Go 1.26.10. It is a new experiment baseline with a separate namespace (`prysm/go1.26.10/MANIFEST.md`, ELF `c6403c02…911e`). The theorems for the Go 1.26.3 ELF `9c850c97…c501` do not transfer to this machine code. Replaced history: 1c pin `5ac1d028f5` (pin branch `45394e5`, not available from `syjn99/prysm`), 1c compiler Go 1.26.3. The values of fix 3 (the Go 1.26.3 and the ELF in the sentence above) do not change.

## 6. Rules (summary, full text in fv/AGENTS.md)

Do not change `sszgen/`, `ssz/`, Kraken, gohashtree or `fv/<project>/upstream`. Hashes are contracts. Do not use `sorry`/`axiom`/`native_decide`/`bv_decide`. One Lean build at a time. Deletion is better than addition. At the end of a session, set in-review and a one-line comment.
