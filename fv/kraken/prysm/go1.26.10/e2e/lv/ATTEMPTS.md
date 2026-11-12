# ATTEMPTS: list/vector work attempt record

Each line records one fact.
The attempt limit is 3 per obligation.
`STEPS.tsv` has the table of commands and exit codes. The logs are in `logs/` of the local work directory and are not committed.

## Environment (at the start of the link unit)

- Host: darwin/arm64. x86-64 machine code is not executed.
- The planner made the ELF again in Docker (linux/arm64). The sha256 `c6403c02…911e`, the build ID and the objdump and nm sha256 are the same as in `build-ids.txt`.
- Heavy-job gate: the `heavy.py` that the task instruction specified (lock, log, cap 40960 MB, time cap).
- `gen/tools/memcap.py` of the repo needs `/proc`. macOS does not have it, so it was not used.
- `link/check.py` finds the LLVM tools with `shutil.which`, and if they are not there, with `xcrun --find`.
- The `llvm-objdump` and `clang` of this machine are Apple LLVM 21.0.0 from Xcode. Their version may differ from the LLVM of earlier runs.

## Link

- `lvlink.py callgraph`: three functions (SyncAggregate, SyncCommittee, IndexedAttestation), 0 unclassified calls, 0 missing functions. Result `lv/callgraph.json`.
- Producer `Desc` output: the sha256 of the three v1alpha1 files is the same as the record in `gen/desc/results/main.result.json`. Result `lv/desc/`.
- Three-function link, attempt 1 (log 05): `conv.py` ended with exit 1. The output directory `norm/` did not exist. It was a setup mistake (wrong-target).
- Three-function link, attempt 2 (logs 06–08): `conv.py` exit 0. The three new `.S` files are byte-identical to the scratch copies of the planner.
- The `check.py` of the same attempt is exit 1. (a), (b), (c), (e), (f) are PASS.
- The failure is (d). clang rejected `lea 0xffffff1c(%rdi),%rdx` on line 19 of the IndexedAttestation `.S`.
- clang error: `displacement 4294967068 is not within [-2147483648, 2147483647]`.
- That operand is the displacement −228 that GNU objdump wrote as a 32-bit unsigned number.
- The other committed `.S` files (e2e, ad, h4, Go 1.26.3) have no such displacement (`grep 0xffffff`).
- Cause class: tool gap. The displacement notation of `conv.py` does not match the Apple clang 21.0.0 of this machine.
- The LLVM version that the earlier link checks used was not checked.
- Whether Kraken reads this operand as −228 or as 4294967068 was not checked. It must be checked before the IndexedAttestation proof.
- Decision: the committed link set is only SyncAggregate and SyncCommittee. `lvlink.py` got a `--t3` option.
- SyncAggregate and SyncCommittee link (logs 09–12): filter, conv, data, check all exit 0. The end of `lv/link/RESULT` is `PASS all`.
- Bundle hash: `BUNDLE sha256 5c1666068e5d37550b3ac967e27d22c2038814a4163ee6a234cec3075a5e744f`.
- All 6 DIFF lines of (d) are padding (`nop` normalization). There are 0 other differences.
- abi.Type of `lvSliceType.data`: Size_ = 24, Kind_ = 23 (slice). A direct read of the bytes confirmed it.

## Statements

- The producer `Desc` was printed after the hand `Desc` (`E2eList/Desc.lean`) was written. The two terms differ only in field names.
- `E2eScal.H5.sm_accept_stmt`, which the task instruction gave as the model, is not in the repo (`git grep` result 0). `E2eScal.H4.dd_accept_stmt` was used as the model instead.
- Only two `input_dir`s (`lv_norm_S`, `lv_data`) and the `lean_lib` `E2eList` were appended to `lakefile.toml`. The existing entries did not change.
- The new data reader `lv_data_include` (`E2eList/Include.lean`) is the text of `E2e/Include.lean`. `gen/e2e/lvcheck_include.py` gave four SAME, exit 0.
- Statement module builds (logs 13, 14): `E2eList.StmtSa` exit 0, 12.5 s, `E2eList.StmtSc` exit 0, 8.3 s. 0 errors.
- The only warnings of the `E2eList` modules are the unused-variable-name linter and the `module` advisory. The statements are `def … : Prop` without proofs, so the names are not used.
- `lake build --no-build E2e E2eAd E2eScal E2eList.StmtSa E2eList.StmtSc` (log 15): exit 0, `All targets up-to-date (998 jobs)`.
- `E2eList/*.lean` has no `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, `maxHeartbeats`, `maxRecDepth` (`grep` exit 1).
- Measurement method: the wall clock of `heavy.py` and the sum of 1-second sampled RSS. n = 1.

## Proof units

### SyncAggregate size reject `sa_e2e_reject_size_main : sa_reject_size_stmt`

- Attempt 1 (log 16): exit 0. Only the directive numbers (88–93) changed in the proof text of `DdReject.lean`.
- It passed without `maxHeartbeats` and `maxRecDepth` settings. The `set_option` of the model was not transferred.

### SyncCommittee size reject `sc_e2e_reject_size_main : sc_reject_size_stmt`

- Attempt 1 (log 17): exit 0. Only the directive numbers (30–35) and the frame size 48 (`sub $0x30`) changed. It passed without settings.

### SyncAggregate segment lemmas `E2eList.Seg`

- Attempt 1 (log 18): exit 0. `bytesdec_seg_z64` (the local macro text of SegN, n = 64) and `bytes96dec_seg_nop` (`DdSegNop` text, 32 → 96).
- The `set_option maxHeartbeats 16000000`/`4000000` of the model was not transferred. It passed at the default limit.

### SyncAggregate accept `sa_e2e_accept_main : sa_accept_stmt`

- Attempt 1 (log 20): exit 1. The last `ecancel` failed.
- Cause: the postcondition of `bytesdec_seg_z64` has the form `Int.toBytes 8 (OfNat.ofNat n)`. Its syntax differs from `Int.toBytes 8 64` of the statement.
- Fix: a wrapper lemma `sa_bits_seg` with the size 64 written as a literal, like the generated `Gen.dd_g2dec_PublicKey_seg`, was added. The proof is `with_reducible exact bytesdec_seg_z64 64 rfl …`.
- Attempt 2 (log 21): exit 0. It passed without settings.

### SyncAggregate specification bridge `E2eList.SaSpec` and three specification theorems `SaSpecK`

- Attempt 1 (log 22): exit 1. The goal `64 + z.size < 4294967296` remained in `psa_serialize`. The second `simp` did not have `hz`.
- Attempt 2 (log 23): exit 0. `hz` was added to the second `simp`.
- The EthLib `packBits_unpackBits` (the padding premise is empty because 512 = 8·64) and `unpackBits_packBits` were used as is.
- `SaSpecK` (log 24): `sa_e2e_accept_spec_k`, `sa_e2e_reject_size_spec`, `sa_e2e_reject_complete`. Exit 0 at attempt 1.

### SyncAggregate hand `Desc` = producer `Desc` (verdict 1)

- The new script `gen/e2e/lvdescterm.py` converts the producer files of `lv/desc/` to Lean (`SaSpecChecker.lean`, `ScSpecChecker.lean`).
- `SaDescEq.lean` (log 25): `prysmSaDesc_checker` (only the names differ, `rfl`), `prysmSaDesc_deserialize_checker` (the accepted inputs and the values are the same). Exit 0 at attempt 1. It is a kernel check (K).

### SyncAggregate witness `WitSaA.sa_accept_runs`

- Attempt 1 (log 26): exit 1. `whnf` went over the default limit of 200000 heartbeats.
- Profile (log 27, scratch copy, `profiler true`, run to the end with a raised limit): two `simp`s are 7.03 s and 2.08 s. The `simp` total of the declaration is 9.16 s.
- Cause: the `simp` that closes the memory premises sorts a separation-logic formula of 22 pieces with `sep_comm`, `sep_comm_l`.
- Action: `set_option maxHeartbeats 16000000 in` is only on the one declaration `sa_accept_runs`. The value is the same as the model witness `WitDdA.dd_accept_runs`. The earlier value is the default 200000.
- Attempt 2 (log 28): exit 0. The three `example`s for the three inputs (0, representative value, 0xff) also passed.

### Attempt count (judgment)

- One attempt is one proof strategy. In the same strategy, a build fixed after reading an error message counts as a development step of the same attempt.
- Thus the build log count and the attempt count differ. `STEPS.tsv` has all builds.
- `sorry` was not used to see intermediate proof goals. Incomplete proofs were built, and the open goals in the errors were read.

### SyncCommittee loop helpers `E2eList.ScLemmas`

- Logs 29–31: exit 1, 1, 0. Cause 1: `⋆` is left-associative, so a `sep_assoc` theorem was necessary at the end. Cause 2: `simp` folded `take ++ getElem :: drop` back into `pks`. It was changed to `rw [List.flatten_append, List.flatten_cons]`.

### SyncCommittee one iteration `sc_iter` and loop `sc_loop`, `sc_exit` (attempt 1)

- Logs 32–40: development steps of one strategy (invariant `ScInv i`, DESIGN 4.1). In log 40, `sc_iter` became exit 0.
- Block 1 (logs 35–36): `ecancel` failure on the memmove premise. Cause: the bounds proof term of `pks[i]` had different syntax at two places. `generalize hE : pks[i] = e` fixed it.
- Block 2 (logs 38–39): the bounds check branch. `Int.ofBytes (Int.toBytes 8 512) = 512` was supplied with `decide` and closed with `omega`.
- The `runtime.panicBounds` branch (directive 63 `jae`) is blocked by a proof in each iteration. It is not blocked by a premise (verdict 7).
- Logs 41–42: `sc_exit`, `sc_loop` (induction on j). The name `eventually_mono` does not exist, so it was changed to `eventually_trans` and `Eventually.done`. Exit 0.
- It passed without settings (`maxHeartbeats`, `maxRecDepth`).

### SyncCommittee accept `sc_e2e_accept_main : sc_accept_stmt` (attempt 1)

- Log 43: `sc_agg_seg` (a `bytesdec_seg 48` wrapper with the size 48 written as a literal, src 24576). Exit 0.
- Logs 44–52: development steps of the head (hand steps), loop, AggregatePubkey, pointer tail and tail (hand steps). Exit 0 in log 52.
- Block: `bv_omega`/`kaddr` did not resolve `Width.W64.bits`. A `laddr` macro with `Width.bits` was used.
- Block: `decide` on `rbx ≤ cnt` of `MakesliceC` is rejected because the expected type has free variables. `Nat.le_refl _` closed it.
- It passed without settings. `#print axioms` (log 53): `sc_iter`, `sc_loop`, `sc_e2e_accept_main` all `[propext, Classical.choice, Quot.sound]`.

### SyncCommittee specification bridge `E2eList.ScSpec`, three specification theorems `ScSpecK`, `Desc` equality `ScDescEq`

- Vector[Bytes48, 512] is not unrolled per element. Lemmas for an arbitrary list of 48-byte vectors (`serializeEach_bv48`, `assemble_inline_ok`, `concatParts_v48`) were used.
- The EthLib `headOf_inline`, `bodiesOf_inline`, `concatParts_size`, `concat_fixed_slices` were used as is.
- Attempt 1 (logs 54–56): three development steps. Causes: the empty-list cases of `serializeEach` and `Value.allFit` did not reduce with `rfl`. The chunk size proof did not have `i < 512` (it changed to `toV48`, and `List.map_congr_left` supplied the bound). Exit 0 in log 56.
- `ScSpecK`, `ScDescEq` (log 57): exit 0 at attempt 1.

### SyncCommittee witness model `E2eList.BumpT` (verdict 2)

- One Host has only one `runtime.makeslice`. The SyncCommittee witness needs both `MakesliceC … lvSliceType_addr 24 S` and `MakesliceC … e2eU8Type_addr 1 S`.
- Thus an esz-24-only model (`bump_makeslice` form) cannot be in one Host with `bump_makeslice1`.
- Action: `BumpAllocT.S` adds one type-word comparison to `BumpAlloc1.S`. If rax is `type__+337600`, it moves 24·cnt, otherwise cnt.
- Two theorems: `bump_makeslice_t24` (esz 24), `bump_makeslice_t1` (esz 1 if the type word is not `lvSliceType_addr`). The proof text is `bump_makeslice1`.
- Attempt 1 (logs 58–62): development steps. Cause: `omega` on the branch condition did not resolve label arithmetic. `BitVec.sub_add_cancel` and `BitVec.sub_self` closed it. Exit 0 in log 62.
- This model is only non-vacuity evidence. Go `makeslice` reads `et.Size_`. This model compares with one address.

### SyncCommittee witness `WitScA.sc_accept_runs`

- Attempt 1 (log 63): the helper name of `u8_ne_slice` did not exist (`BitVec.add_sub_cancel_left`). Log 64: changed to `bv_omega`, exit 0. The witness body passed from the first build.
- `maxHeartbeats 16000000` is only on this one declaration. A scratch copy without the setting (log 65) went over the default limit in `whnf` (after `simp` 2.3 s). The cause is the same as the SyncAggregate witness (log 27).
- The three `example`s for the three inputs (0, representative value, 0xff) passed. Each input is 512 chunks of 48 bytes.

## Verification (task instruction section 6)

- Full build (log 67): `lake build E2eList` exit 0, 682 jobs. `--no-build E2e E2eAd E2eScal E2eList` (log 68): exit 0, `All targets up-to-date (1035 jobs)`.
- Axioms gate (log 69): new file `gen/e2e/lvaxioms_gate.py` (imports the existing `axioms_gate.py`, `E2eList` in ROOTS, `gen/e2e/AxiomsLv.lean` in the hand list). PASS, declarations 5632, theorems 4684, hand list 462, nonstandard 0, `sorryAx` 0. Result `lv/axioms-gate-lv.json`. The existing `axioms-gate.json` was not overwritten.
- Axioms gate control (logs 79–82): a scratch module `E2eList.Planted` (one `sorry` theorem) outside the repository was added. FAIL, `sorryAx ['E2eList.Planted.planted_sorry']`. Result `lv/axioms-gate-lv-plant.json`. The added `.olean` was deleted immediately.
- Log 79: `lake env lean -o` exit 1. Cause: the source file is outside the root directory (wrong-target). Log 81 ran it again with `--root`.
- Log 80: exit 2. Cause: if the first `LEAN_PATH` entry has an `E2eList` directory, Lean also looks for the other `E2eList` modules there (wrong-target). Log 82 ran it again with an empty path and a temporary `.olean` in the build directory.
- Declaration drift: the base `6a78c591…` was extracted to scratch with `git archive`, and the current `.lake` was copied (APFS clone). `--no-build E2e E2eAd E2eScal` of the base tree was exit 0 (log 70).
- Limit: the `.olean` files of the base were not made separately in the base tree. Lake tracking decided that the sources and inputs are the same.
- Log 72: `decl_drift.py` rejected with exit 2 (the roots of the dumps differ). Logs 73–74: the current tree was dumped again with the same roots (E2e, E2eAd, E2eScal). drift 0, base 5007 = head 5007.
- The `E2eList` declarations are a new root, so they are outside the drift comparison. (Review r1 S3 fixed the line below. The "622" written first was a wrong count.)
- Recounted value (name comparison of the dump of log 69 and the base dump): 625 new lines, 0 lines removed from the base. Of the 625, 434 start with `E2eList.`. 623 have `E2eList` in the name (`_private.E2eList.…`, `_aux_E2eList_…` included).
- The remaining 2 are `E2e.Data.e2eU8Type_addr.eq_1` and `commandLv_data_include_`. The first is an equation lemma that an `E2eList` module (`simp only [E2e.Data.e2eU8Type_addr]` of `WitScA.u8_ne_slice`) made automatically in the `E2e.Data` namespace. The second is the syntax kind name of the new command `lv_data_include`. Both are additions. They do not change existing declarations.
- Drift control (logs 75–78): `0 + 0` was planted in `E2eScal.WitBhU.s0` of the scratch base copy. drift exit 1, `CHANGED E2eScal.WitBhU.s0 value`. The file was reverted, and that module was built again.
- The skill `SKILL.md` states "the first run of `decl_dump.lean` on the Kraken tree is a separately gated unit". This run is that first run. The control showed that the check can fail.
- Negative tests (logs 83–84): new file `gen/e2e/lvnegative.py` (imports the existing `negative.py`, inlines the statement module, limits time with a process group without memcap). Cases `lv/negcases-lv.json`, result `lv/negative-lv.json`.
- Result: 17 of 18 passed (control_pass 4, inside 13). `lv-sa-bitslen63` is outside. The error is in `sa_bits_seg` before the main theorem. After that, the case `lv-sa-bitslen63-seg` that aims the same mutation at `sa_bits_seg` was added (inside). The first result stays as is.
- Stale check (log 85): `stale_olean.py` exit 0, flagged 0.
- Go differential test: not run. It needs the Prysm Go build environment (the Docker of the planner) and a new Go harness. This machine is arm64, so a run on it is not evidence for the x86-64 ELF.

## IndexedAttestation displacement check (verdict: value only, no proof)

- Log 66: `lea 0xffffff1c(%rdi),%rdx` of a scratch `.S` was read with the Kraken `include_x64_rt` and printed with `#print`. Result `disp := ↑4294967068`. `lea -0xe4(%rdi),%rdx` of the same file is `disp := ↑(-228)`.
- The machine sign-extends the 32-bit displacement (−228). Thus if Kraken gets this notation as is, it computes a different address. This is execution evidence (X).
- The other committed `.S` files have no `0xffffff..(%` form (`git grep`, result 0).

## Review r1 fixes (review `fbf729a`)

### Logs

- The numbered logs (`logs/NN-*.log`) and the `heavy.py` records (`.json`) are only in the local work directory. They are not committed.
- The lines that the report relies on are copied below as is (the paths are shortened).
- Log 08 (`check.py`, IndexedAttestation included): `FAIL clang: <tmp>/re.S:738:18: error: displacement 4294967068 is not within [-2147483648, 2147483647]`, then the next line `  lea 0xffffff1c(%rdi),%rdx`.
- Log 26 (`WitSaA` attempt 1): `error: E2eList/WitSaA.lean:87:0: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached`.
- Log 27 (profile): `simp took 2.08s`, `simp took 7.03s`, total `simp 9.16s`.
- Log 65 (`WitScA`, scratch copy without the setting): `WitScANoHb.lean:97:0: error: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached`, before it `simp took 2.3s`.
- Log 66 (IndexedAttestation displacement): `disp := ↑4294967068` (`lea 0xffffff1c(%rdi),%rdx`) and `disp := ↑(-228)` (`lea -0xe4(%rdi),%rdx`).

### M1: `maxRecDepth`

- `set_option maxRecDepth 100000` without a recorded cause was in `E2eList/WitSaA.lean:26` and `E2eList/WitScA.lean:27`. These lines were transferred from the witness model (`WitDdA.lean`).
- The line in `WitSaA.lean:26` was deleted. Log 86: `lake build E2eList.WitSaA` exit 0.
- The line in `WitScA.lean:27` was deleted, and the file was built. Log 87: exit 1. All 4 errors are `maximum recursion depth has been reached`, and they are in the `by simp` of the first `example` (line 125) and the third `example` (line 131). `sc_accept_runs` and the second `example` passed.
- Cause: when `simp` shows the length and the element lengths of `List.replicate 512 …` (a list of 512 elements), it goes over the default recursion limit.
- Action (r1): `set_option maxRecDepth 100000 in` was put only on those two `example`s. File `E2eList/WitScA.lean`, lines 126 and 134 ("line 127" written in r1 was wrong), value 100000. Log 88 was a syntax error (wrong-target) because of the order around the docstring. Exit 0 in log 89.
- Review r2 M1 changed this action. See "Review r2 fixes" below. Now `E2eList` has no `maxRecDepth` setting.

### S5: `lakefile.toml`

- `input_dir` `lv_lean_S` (path `E2eList`, `.S` only) was appended and added to the `needs` of `E2eList`. It has the same form as `e2e_ad_lean_S`. The other entries did not change.
- Log 90: `lake build E2eList` exit 0, 683 jobs (the `needs` changed, so the full library was built again). Log 91: `--no-build E2e E2eAd E2eScal E2eList` exit 0, 1036 jobs.

### S4: added negative tests

- `inline` (a list of modules to inline) was added to `gen/e2e/lvnegative.py`. It inlines `Desc.lean` and `Defs.lean` to mutate `Desc`. The earlier cases run as before.
- Added cases: `lv-sc-rej-control`, `lv-sc-rej-errword` (SyncCommittee size reject), `lv-sa-desc-control`, `lv-sa-desc-sig95`, `lv-sc-desc-control`, `lv-sc-desc-n511` (size mutation, first target `*_fixedSize`), `lv-sa-desc-kind`, `lv-sc-desc-kind` (kind mutation with the same size, targets `psa_toValue_fits`, `psc_toValue_fits`).
- Logs 92, 93: all 8 added cases passed. Log 94: all 26 ran again with the new runner. 25 passed (control_pass 7, inside 18), 1 outside (`lv-sa-bitslen63`, same as the earlier record).

### Checks run again

- Axioms gate (log 95): PASS, declarations 5632, theorems 4684, hand list 462, nonstandard 0, `sorryAx` 0. Result `lv/axioms-gate-lv-r1.json`. The name set is the same as log 69.
- The work directory paths in lines 71 and 76 of `STEPS.tsv` were changed to `<scratch base copy>` (S1).

## Review r2 fixes (review `d169e4b`)

### M1: `maxRecDepth` removal

- The two lines `set_option maxRecDepth 100000 in` (lines 126, 134) of `WitScA.lean` and their cause comments were deleted.
- The `(by simp) (by simp)` of the first and third `example` changed to term proofs: `List.length_replicate` and `fun e he => by rw [List.eq_of_mem_replicate he]; exact List.length_replicate`. It is the same idea as the variant that the reviewer wrote.
- Attempt 1 (log 97): `lake build E2eList.WitScA` exit 0. `E2eList/*.lean` has no `maxRecDepth` (`grep`, result 0).

### S5: blank lines

- The double blank lines after `namespace` in `WitSaA.lean` and `WitScA.lean` were reduced to one.

### S1: `maxHeartbeats` thresholds

- Values that the reviewer measured (review r2, reviewer run): `WitSaA.sa_accept_runs` fails in `whnf` at 200000 and 400000, and passes at 1000000. `WitScA.sc_accept_runs` fails at 200000, 400000, 1000000, and passes at 2000000.
- The values were lowered: `WitSaA` 16000000 → 2000000, `WitScA` 16000000 → 4000000 (two times the reviewer pass value). The two values passed in the build of this worker (logs 96, 97, 98).
- This worker did not measure the thresholds again. The thresholds are the values that the reviewer measured. The comments next to the settings in the two files state the same.

### Checks run again

- Log 98: `lake build E2eList` exit 0, 683 jobs, wall clock 19.9 s (WitSaA 13 s, WitScA 17 s).
- Log 99: `lake build --no-build E2e E2eAd E2eScal E2eList` exit 0, 1036 jobs up to date.
- Log 100: axioms gate PASS, declarations 5632, theorems 4684, hand list 462, nonstandard 0, `sorryAx` 0. Result `lv/axioms-gate-lv-r2.json`. The gate dump is byte-identical to the r1 dump (log 95) (`cmp`).
- Logs 101–102: the current dump of the base roots (E2e, E2eAd, E2eScal) is byte-identical to the dump before the review (log 73) (`cmp`). `decl_drift.py` base against current: exit 0, `SUMMARY base=5007 head=5007 drift=0 allowed=0`.
- Only the `example`s, the settings and the comments changed. An `example` makes no declaration. Thus the equal dumps agree with the expectation.

## Fix for finding LV-1, the wrapped negative displacement (user approval, `link/conv.py` only)

- Change (`93b3f2a`): `--norm` writes some memory displacements in signed form. The condition: exactly 8 hexadecimal digits, the top bit set and `(%` immediately after the displacement. Example: `0xffffff1c(%rdi)` → `-0xe4(%rdi)`.
- Immediates (`$0x…`), branch targets and `%rip` operands do not change. It also covers the base+index form `(%r,%r,s)`.
- Five cases were added to `selftest()`: change with `--norm`, no change without `--norm`, no change for the immediate `$0xffffff1c`, no change for the positive `0x7fffffff(%rax)`, change for the base+index form `0x80000000(%rsi,%rcx,8)`. `conv.py` runs the selftest first at each run. The runs of logs 104, 109, 106 are all exit 0.
- It passed at attempt 1.

### Verification

- (a) Logs 103 (old `conv.py`, `29683a8`), 104 (new `conv.py`): the full objdump and nm were converted with `--norm` into two scratch locations. Both exit 0, 641 function files and `all.S`.
- Log 105 (counts only, the `.S` contents were not opened): 104 changed files, 161 changed lines. All changed lines differ only in the displacement token. A script applied the same substitution to the old lines and compared them with the new lines (0 mismatches).
- (b) The new output has 0 wrapped forms (`0x[89a-f][0-9a-f]{7}\(%`). The old output has 161.
- (c) Log 106: this ELF has 7 committed sets made with `--norm` (`e2e/link`, `e2e/ad/link`, `e2e/bh/link`, `e2e/e1/link`, `e2e/h3/link`, `e2e/h4/link`, `e2e/lv/link`). The new `conv.py` made them again in scratch from the committed `target.objdump`. 37 files (`all.S` included) are byte-identical to the committed files.
- Log 107: `prysm/go1.26.10/link/norm`, which has no committed `target.objdump`, was compared with the full conversion. 136 function files are the same, and 136 function blocks of `all.S` are the same.
- `opt-r1/link` is a different ELF (`3ef7ac89…`), so it was not compared.
- The `.S` files of the held-out evaluation types were not opened or printed. Only the byte comparisons and counts of the script were used.
- (d) IndexedAttestation link (logs 108–111, scratch): `lvlink.py filter --t3` exit 0, `conv.py --norm` exit 0, `lvlink.py data --t3` exit 0, `check.py` exit 0.
- `check.py` result: (a) 3 functions PASS (IndexedAttestation 253 instructions, 1197 bytes). (b) 28 lines PASS. (c) PASS (49 labels). (d) PASS: 473 instructions, 461 bytes the same, encoding 0, padding 12. (e) PASS (522 directives). (f) 9 files PASS. `PASS all`, bundle hash `393eade69a88fd79e6b6a6a50a09387cb3e5892ebe8777e8933b5f6742954e0d`.
- If IndexedAttestation goes into `lv/link`, the `RESULT`, `all.S` and `target.objdump` of that directory change. Thus it was committed in a new sibling directory `lv/link-t3/` (`dc7bd56`). `git diff dfc8b93 -- lv/link` is empty.
- The SyncAggregate and SyncCommittee `.S` files and the data files of `lv/link-t3/` are the same as those of `lv/link`. The IndexedAttestation `.S` differs from the one of the earlier attempt (log 06) only in the displacement token on line 19.
- (e) Log 113: `lea -0xe4(%rdi),%rdx` on line 19 of the new IndexedAttestation `.S` was read with the Kraken `include_x64_rt` and printed with `#print`. `disp := ↑(-228)`. In log 112, I chose line 20 by mistake, so it was not a comparison target (wrong-target).
- (f) selftest: it ran first at each run above and passed.
- Call set of the IndexedAttestation normalized `.S`: `fmt.errorf` 3, `AttestationData.UnmarshalSSZ` 1, `runtime.convT64` 2, `runtime.gcWriteBarrier2` 4, `runtime.makeslice` 2, `runtime.memmove` 1, `runtime.morestack_noctxt.abi0` 1, `runtime.newobject` 4, `runtime.panicBounds` 3. 279 lines.
- The IndexedAttestation Lean statements and proofs were not started.

## IndexedAttestation design and statements

- New files: `E2eList/IncludeIa.lean` (a copy of the `lv_data_include` text, prefix `lvt3`, path `lv/link-t3/data`), `gen/e2e/lvt3check_include.py` (four SAME, exit 0), `CodeIa.lean`, `DataIa.lean`, `DefsIa.lean`, `StmtIa.lean`.
- `lakefile.toml`: two `input_dir`s (`lv_t3_norm_S`, `lv_t3_data`) were appended and added to the `needs` of the `E2eList` made in this branch. The other entries did not change. This goes on the user decision list.
- Log 114: `lake build E2eList.StmtIa` exit 1. `NewobjectC` is in `Fk.FunSpecs` (missing import).
- Logs 115, 116: exit 0. Log 117: `lake build E2eList` exit 0, 705 jobs. Log 118: `--no-build E2e E2eAd E2eScal E2eList` exit 0, 1048 jobs.
- A scratch generation script wrote the statement text of `StmtIa.lean` (to avoid a repetition of the same frame text). The script is not committed. The resulting Lean file is the statement.
- The new files have no `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, `maxHeartbeats`, `maxRecDepth` (`grep` exit 1).

## IndexedAttestation proofs

### Size reject `ia_e2e_reject_size_main`, offset reject `ia_e2e_reject_offset_main` (attempt 1)

- Logs 119–123: development steps of one strategy. Three blocks.
- 1. `simp only [E2e.errSize_addr_eq] at … ⊢` and `simp only [UInt64.size] at *` reached the recursion limit. They were changed so that they do not touch the goal and `hk` (`dsimp only`, `simp` only on named hypotheses).
- 2. The `simp` of `kat` unfolds the program literal of 279 directives (`IaUnmarshal`) and stops at the default `maxRecDepth` (512) (log 123, first `kat`).
- Measurement (log 124): at 1024, 2048 and 4096 that error went away. The only remaining errors were the incomplete branches of the offset reject. Thus the value is 1024. Each of the two theorems has `set_option maxRecDepth 1024 in` with the cause next to it.
- 3. The `jne` not-taken branch of the offset reject: if the 32-bit value `ofInt 32 (ofBytes off)` is 228, then `off = iaOff`. `toBytes_ofInt_ofBytes` and `isLt` closed it (logs 125–127 are development steps for names and arithmetic theorems).
- Log 128: `lake build E2eList.IaReject` exit 0.

### IndexedAttestation specification bridge `IaSpec`, size reject and offset reject specification, reject cases (attempt 1)

- `IaSpec.lean`: `pia_serialize`, `pia_roundtrip`, `pia_accepted_is_enc`, `iaChecks` (the order of the four Go checks), `pia_spec_accepts_iff`, `pia_spec_rejects`. The list side used the Go 1.26.3 ListU64 lemmas (`serializeEach_u64`, `inl_*`, `luElems`, `u64Bytes_luElems`), the data side used `E2e.pad_*`, and the join used EthLib `extract_join`.
- Logs 129–133: development steps of one strategy. Blocks: the size condition of the list `assemble` (`h8`), `Desc.isFixed` does not unfold (four `rfl` facts given to `simp`), `set` without Mathlib, array join.
- Log 134: `ia_e2e_reject_size_spec`, `ia_e2e_reject_offset_spec`, `ia_e2e_reject_cases` of `IaSpecR.lean` exit 0. They passed without settings.

### Alignment reject and overflow reject (stopped)

- The proof was not started.
- The frozen statements `ia_reject_misaligned_stmt` and `ia_reject_toobig_stmt` do not have the premise `e0 ≠ 0`.
- Directives 103–106 (alignment reject) and 66–69 (overflow reject) are `test %rcx,%rcx; je`. If e0 = 0, itab+8 is not read, and the argument word is 0. `FmtErrorfDWC` requires that word to be `ity`.
- The Kraken `Host` layout is arbitrary, so the itab label can be 0. Thus the judgment was that the statements as written cannot be proved.
- This was reported to the planner. The work waits for new names and a verdict.

### Accept `ia_e2e_accept_main` (attempt 1)

- New files: `E2eList/IaLoop.lean` (`ia_iter`, `ia_exit`, `ia_loop`), `E2eList/IaAccept.lean` (12 lemmas and `ia_e2e_accept_main : ia_accept_stmt`).
- `ia_iter` is one iteration. It proves that the three panicBounds branches (155 `ja`, 159 `jb`, 164 `jb` not taken → 165) are not taken. It does not assume it.
- `ia_loop` is a recursion on the remaining iteration count `j` (`i + j = n`). n = 0 is `j = 0, i = 0`.
- `E2eAd.ad_e2e_accept_main` closed the data call. The callee entry rsp is x − 184, and the scratch is `Sd`.
- Logs 135–140: `IaLoop`. It passed from the first build. Without `maxRecDepth`, the first `kat` of `ia_iter` (log 136) and `ia_exit` (log 139) stops at the recursion limit. Thus both have 1024 with the cause recorded.
- Logs 141–145, 152, 155–183: development steps of `IaAccept`. It is one strategy (hand steps + contracts + loop + callee). The blocks are below.
- 1. `sar $0x3f` leaves undefined flags. `kshl64 63` closed it. The AF of `and` was closed with `intro _`.
- 2. Logs 147, 148, 152, 153: with `simp [BitVec.toNat_add]; omega` on `c + -228`, the kernel stops with "deep recursion". Each run was 235–309 s, sampled RSS 16–20 GiB. Log 153 is a 90 s timeout on that one line alone (exit 124).
- Thus it was changed to `ia_sub228` (`BitVec.sub_eq_add_neg`, `toNat_sub_of_le`). It is 3.1 s (log 154). The two constants were proved with the `toNat` simp set (log 151). `decide` was not used.
- 3. Logs 158–160: after directive 35, `ecancel` stopped with "maximum recursion depth". It was the same at 2048 and 8192. Thus the judgment was that it is not a limit problem.
- Probable cause: the AC normalization does not end on the raw `sar`/`and` expression that directive 34 wrote to memory. When `generalize` gave that expression the names `P`, `C`, `Q`, the problem went away (log 161). The limit was set back to 1024.
- 4. Logs 172–174: two words of the callee postcondition (saved rbp, rdi spill) did not match structurally the terms of the same form that I wrote. A per-atom test (log 173) found them. `generalize` gave them the names `vb`, `v4`. Both stay only in the existentially quantified frame.
- 5. Logs 175, 176: `replicate (1 * 96)` of the `makeslice` postcondition. `Nat.one_mul` closed it. Two stores with the old value as `_` used all heartbeats. They were changed to explicit values.
- 6. Logs 181, 182: final memory. The source address of the `memmove` postcondition is `132 + rbx`. A per-atom test found it.
- Log 183: exit 0.
- Measurement (logs 184, 185): without `maxRecDepth`, the `kat` of directive 0 stops. `maxHeartbeats` 400000 is a `whnf` timeout, 800000 and 1200000 pass. The value is 1600000, two times the pass value. The cause and the threshold are next to the option.
- Logs 186, 187: `lake build E2eList.IaLoop E2eList.IaAccept` exit 0. Log 187 is after the unused name in `ia_exit` was changed to `_hn`.
- The two files have no `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide` (`grep` found nothing).
- Logs 147, 148 are scratch files (`lake env lean`). Their RSS values are not related to the proofs of this commit.

### Accept specification `ia_e2e_accept_spec` (attempt 1)

- New file: `E2eList/IaSpecA.lean`. It gets `g` with `pia_accepted_is_enc` and uses `ia_e2e_accept_main` with n = `g.idx.length`. It is the text of `E2eAd/AdSpecK.lean`.
- Log 188: `lake build E2eList.IaSpecA` exit 0. It passed without settings.

### Desc equality `prysmIaDesc_deserialize_checker` (attempt 1)

- `python3 gen/e2e/lvdescterm.py prysm/go1.26.10/e2e/lv/desc/prysm_v1alpha1.IndexedAttestation.desc.json iaCheckerDesc > lean/E2eList/IaSpecChecker.lean`, exit 0.
- The sha256 of the producer file is `91e4d752…`. It is the same as the IndexedAttestation row (`PASS`) of `gen/desc/results/main.result.json`.
- New file: `E2eList/IaDescEq.lean`. `E2e.serializeFields_congr` and `E2e.prysmAdDesc_serialize_checker` closed the nested container.
- Log 189: `lake build E2eList.IaDescEq` exit 0. It passed without settings.

### Alignment reject and overflow reject verdict (2026-11-12)

- The planner approved the `_nz` statements. The user also agreed explicitly (as relayed by the planner).
- `STATEMENTS-T3.md` section 5 records the gap, the precedent (`lu_reject_misaligned_main` of `Fk/LuRejectCall.lean`, premises `e0 ≠ 0` and `e0 = itab`) and the real ELF value (`0xd28520`, check (b) of `lv/link-t3/RESULT`).
- The corrected premise is stronger than the frozen statement. The original four are N (they cannot be proved as written).

### Accept witness `WitIaA.ia_accept_runs` (all n ≤ 2048)

- New files: `E2eList/BumpAllocT3.S`, `E2eList/BumpNewT3.S`, `E2eList/BumpT3.lean`, `E2eList/WitIaA.lean`.
- `BumpAllocT3` branches on the type word. If it is `type__+387456` (uint64), it grows by 8·cnt, otherwise by cnt. `BumpNewT3` gives 96 if the word is `type__+1464512` (AttestationData), otherwise 72. The offsets come from the files of `lv/link-t3/data`.
- The two `.S` files are in the existing Lake `input_dir` `lv_lean_S` (all `.S` of `E2eList/`). The lakefile did not change.
- Log 190: `BumpT3` exit 0. The four theorems (`bump_makeslice_t3_1`, `_t3_8`, `bump_newobject_t3_72`, `_t3_96`) passed without settings.
- Memory layout: the input is at the end of the block. Thus the length of `ib` does not change other addresses. The heap is fixed at 16816 bytes (8·2048 + 432).
- Strategy 1 (logs 191, 192): the `WitScA` text as is. Log 192 is a failure. `whnf` timeout at `maxHeartbeats 64000000`, 1471 s, sampled RSS 2.75 GiB. Planner verdict: do not raise this value again.
- Diagnosis (logs 193–197): `wit_split` alone stops at the default limit (log 193). If `ib = []`, it passes. With a symbolic length `ib` (or an opaque `L`), it stops (logs 194, 196). The `iaOff` unfolding is not related. The diagnostic output (log 195) shows about 392000 unfoldings of Nat `HAdd`/`HMul`.
- Strategy 2 (log 196): the length was generalized to a variable `L`. Failure.
- Strategy 3 (logs 198–214): one explicit rewrite removes `ib` first. Its side conditions are proved directly with `block.length = 17616` and `hib`. Only literal lengths stay in the remaining block. The split became 18 s.
- The four register facts were proved with `show` and `UInt64.toNat_ofNat_of_lt'` instead of `simp [cs0]` (logs 202, 205).
- `ecancel` was tried as the closing step (logs 204–208). A test of the 36 atoms one at a time matches all of them (log 207). The whole fails, with 56 internal tactic PANICs. Depth 8192 is the same (log 208). Kraken is not changed (tool boundary). Thus the work went back to the AC `simp` + `exact` of `WitScA`.
- Measurement: `maxHeartbeats` 3000000, 4000000 fail (log 211). 5000000 passes (log 211). 6000000, 8000000, 12000000, 16000000 pass (logs 209, 210). The value is 10000000, two times the pass value.
- Measurement: file-level `maxRecDepth`. The default and 1024 stop at the host facts (`rfl`/`decide` of the 884-directive program) (log 212). 2048 passes.
- Three examples: n = 0 (`ib = []`), n = 1, n = 2048 (`List.replicate (8 * 2048) 0xff`). The length proof is a `List.length_replicate` term. `decide` and large literals were not used.
- Log 214: `lake build E2eList.WitIaA` exit 0, 68.8 s, sampled RSS 2.73 GiB (whole file, n = 2048 example included).
- Verdict: the general-n witness is K. The fallback path (concrete-n witnesses only) was not used.

### Alignment reject `ia_e2e_reject_misaligned_nz`, overflow reject `ia_e2e_reject_toobig_nz`, two specifications (attempt 1)

- The statements are the four `_nz` statements (frozen in `714989f`). New files: `E2eList/IaRejectCall.lean`, `E2eList/IaSpecRNz.lean`.
- The proof is the text of `Fk.lu_reject_misaligned_main`. The head 0–26 is the same as `IaAccept.lean`.
- `he0nz` refutes `je` (105, 68). Only the address of the itab word read changes to `he0` (`load_step_at`). At first, `rw [he0]` also changed the `e0` of the postcondition (found with the per-atom tests of logs 225–227).
- The new lemma `ia_jg2048_true` showed the `jg` (30) branch of the overflow reject.
- Logs 216–231: development steps of one strategy. Blocks: the `movups` address form, the base address of `at_app` must be explicit, `Int.toBytes_length` is not in the default `simp` set, folding `StaticBox C` back into `SB`.
- Measurement (log 233): without `maxRecDepth` in the two theorems, the first `kat` stops. 1024 passes (logs 231, 232).
- Log 234: `lake build E2eList.IaRejectCall E2eList.IaSpecRNz` exit 0. There is no heartbeat setting.

### Alignment reject and overflow reject witnesses: `WitIaR.ia_misaligned_runs` (alignment reject), `WitIaR.ia_toobig_runs` (overflow reject) (attempt 1)

- New file: `E2eList/WitIaR.lean`. It is the text of `Fk/WitLuMa.lean`. The generator that made that file is not in the repository. A scratch script computed the layout (not committed).
- `e0` is the itab label address 0x1012b (not 0). `he0` was shown with `label_itab`, and `he0nz` with `decide`.
- The contracts were closed with `rt_convT64` and `rt_errorf_dw` of `Fk.RtErr`. The frame `R` is `fun _ => True` (`sep_true`, same as the precedent).
- Alignment reject: len = 229 (the box is 1 of the static table). Overflow reject: len = 228 + 8 · 2049 (the box is on the heap).
- Blocks (logs 236–243): a symbolic form difference (`66560#64`), a `decide` goal with `zmms`, after `bumpHeap` is made no single hypothesis has all atoms (as in the precedent, an explicit list `H2` is proved with `ecancel`), the `sep_emp` rewrite binds the frame variable of `sep_true` to `emp`.
- Measurement (log 245): without `maxRecDepth`, it stops at the host facts. 1024 passes. There is no heartbeat setting.
- Log 246: `lake build E2eList.WitIaR` exit 0, 26.0 s, sampled RSS 5.56 GiB.

### IndexedAttestation verification

- Logs 247, 252: `lake build E2eList` exit 0 (252 is 765 jobs, 100.1 s, sampled RSS 7.71 GiB. The IndexedAttestation modules were built again).
- Logs 248, 254: `lake build --no-build E2e E2eAd E2eScal E2eList` exit 0 (254 is 1080 jobs).
- Axioms gate: a new hand list `gen/e2e/AxiomsLvT3.lean` (23 IndexedAttestation names) and a new wrapper `gen/e2e/lvt3axioms_gate.py` (the text of `lvaxioms_gate.py`, two lists in `LISTS`). selftest PASS, hand list names 485.
- Logs 249, 255: PASS. Declarations 6402, theorems 5341, hand list 485, missing 0, nonstandard 0, `sorryAx` 0. Result: `axioms-gate-lv-t3.json` (log 255).
- Declaration drift (log 250, base `6a78c591`, roots E2e, E2eAd, E2eScal): 0 (5007 = 5007). Result: `decl-drift-lv-t3.txt`.
- Negative tests: the 8 cases of `negcases-lv-t3.json`. In log 251, one control failed. The reason: `IaAccept` imported `StmtIa` twice through `IaReject` (the runner inlines the statement module).
- Thus the `iaaddr` macro moved to a new module `E2eList/IaAddr.lean`. `IaAccept` imports `IaAddr` and `StmtIa` directly. The theorem statements did not change.
- Log 253: all 8 passed (control 2, inside 6). Result: `negative-lv-t3.json`.
- Cases: size statement 227/228 (`< 229`), size code (`cmp $0xe5,%rcx`), offset byte (`cmp $0xe5,%rdx`), alignment (`test $0xf`), 2048 limit (`cmp $0x7ff`), accept postcondition (`Heap (avail - (8 * n + 431))`).
- Link: `git diff dc7bd56 -- lv/link-t3 lv/link` is empty. The link check was not run again (the inputs are the same).
- Not run: the separate build of the base tree, the gate control, the drift control, `stale_olean.py`, the Go differential test, the hardware comparison.

### Review r4 suggested fixes (S1, S3, S4, S5, S8)

- S1: new file `E2eList/WitIaR2.lean`. `ia_size_runs` (all len < 228, examples 0, 227) and `ia_offset_runs` (all len ≥ 228, offset bytes `e5 00 00 00`, examples 228, 228 + 8 · 2049). It is the text of `E2e/WitCpR.lean`.
- Host of S1: the `WitIaR` host has no `ssz.ErrSize` and `ssz.ErrInvalidVariableOffset` labels. There is also no lemma that gives the address of a missing label. Thus a separate small host with the two labels and the real IndexedAttestation decoder was made.
- S1 measurement: without `maxRecDepth`, only `P_len` stops (log 259). Only `P_len` has 1024 (logs 260, 262 pass). There is no heartbeat setting.
- S3: in a build without options, only `P_len` and `hk284` of WitIaR and only `P_len` and `hk288` … `hk869` of WitIaA stop (log 260).
- `hk288` of WitIaA passes with 1024. `P_len` and `hk531` … `hk869` stop at 1024 (log 261) and pass at 2048 (log 262). The option is only on those declarations.
- S4: the runner appends to the result file. Thus the old result was deleted, and then it ran once (log 264). There is one `prechecks` entry.
- S8: 6 cases were added (control 3, mutation 3).
  - (a) `he0nz` removed from the `_nz` misaligned statement → fails at the `intro` in `ia_e2e_reject_misaligned_nz`.
  - (b) the offset constant of the offset reject specification statement (`≠ iaOff` → `≠ [0xe5, 0, 0, 0]`) → fails in `ia_e2e_reject_offset_spec`.
  - (c) the heap budget of `ia_accept_spec_stmt` (`+ 432` → `+ 431`) → fails at the `omega` in `ia_e2e_accept_spec`.
- For (b) and (c), the `inline` of the runner inlined the dependency modules (`StmtIa`, `IaReject` / `StmtIa`, `IaLoop`, `IaAccept`). Without inlining, `StmtIa` is imported twice (the same cause as log 251).
- (b) is a statement mutation, not a code mutation. A code mutation fails first in the proof of the inlined `IaReject` (outside the target theorem).
- Log 263: the first mutation of (c) (`Heap … + 431` of the postcondition) failed in the target theorem, but it was a recursion-limit error. The runner classifies this as a resource error (FAIL). Thus it was changed to the premise `hav`.
- Log 264: all 14 passed (control 5, inside 9). Result: `negative-lv-t3.json`.
- S5: the times of rows 105, 107, 108 were wrong. The rows were not changed, and three correction rows were appended (log file modification times).
- Runs again: log 265 `lake build E2eList` exit 0 (767 jobs, already up to date). Log 266 `--no-build` four libraries exit 0 (1082 jobs).
- Log 267: gate PASS, declarations 6451, theorems 5378, hand list 487, nonstandard 0, `sorryAx` 0. Result: `axioms-gate-lv-t3-r4.json`.
- Log 268: drift 0 (5007 = 5007). Appended to `decl-drift-lv-t3.txt`.

### Review r5 suggested fixes (review r5 target 2 items T2-S1, T2-S2)

- T2-S1: `lv-ia-nz-mis-no-he0nz` fails at `intro` because of the binder count. Thus it does not test that `e0 ≠ 0` is necessary. That case stays, and a new case was added.
- New case `lv-ia-nz-mis-he0nz-trivial`: it replaces `(he0nz : e0 ≠ 0)` with a premise of the same form that is true but useless, `(he0nz : e0 = e0)`. It fails at `exact he0nz …` (line 460 of the mutation file), which refutes `je` in `ia_e2e_reject_misaligned_nz`.
- T2-S2: new case `lv-ia-stmt-offset229`: it replaces `(hoff : off ≠ iaOff)` of `ia_reject_offset_stmt` with `≠ [0xe5, 0, 0, 0]`. It fails at the `decide` (line 820 of the mutation file) in `ia_e2e_reject_offset_main`.
- Log 270: the old result was deleted, and it ran once. All 16 passed (control 5, inside 11). There is one `prechecks` entry. Result: `negative-lv-t3.json`.
