# GENERATOR-FINDINGS: generator 698c202 and Prysm ab15ff70 (phase 1c)

We did not change the generator. This file records only the reproduction inputs. The user makes the upstream PRs.
There are four lists. Do not mix them.

## 1. New generator defects

### D1. In the IR, the field keys of a nested container are the container name, not the field names

- Location: the `case *types.Struct:` branch of `FieldParser.expand` in `sszgen/representer.go`. `container.Append(f.name, rep)`.
  `f.name` is the name of the outer definition (for example `Checkpoint`). The field name is `field.Name()`.
  The top-level path above (`ParseTypeDef`) is correct, because there `f.name` is the field name. Only the nested path is wrong.
- Minimal reproduction (gate log `logs/09-repro-ir-keys.log`, output copy in the run directory `artifacts/repro-ir-attestationdata.go.txt`):

  ```sh
  # methodical-ssz worktree root, Go 1.26.10
  ssz-698c202 ir --output=/tmp/ir.go --type-names=AttestationData \
      github.com/OffchainLabs/methodical-ssz/fv/kraken/target/prysm
  ```

  Expected: the field keys of the `Checkpoint` of `Source` are `Epoch`, `Root`.
  Actual: `{Key: "Checkpoint", Value: &types.ValueOverlay{Name: "Epoch", ...}}, {Key: "Checkpoint", Value: &types.ValueVector{Size: 32, ...}}`.
- Effect: there is no effect on the output code of this run (observation). The renderer always delegates a nested container to a method call of that type (`render/marshal.go` `marshalOp.Container`, `render/unmarshal.go` `unmarshalOp.Container`).
  Affected: the `ssz ir` output, `testutil.RenderIntermediate`, and tools that read the IR (for example the 1c `Desc` generator).
  The 1c tools cut below delegated fields (`gen/inventory.py reduce`), so they do not use these keys.
- Verdict: defect (IR only). It is not an output-code defect. Severity low (not a guess: the three known commits explain all 232 blocks of the Fulu output diff).

### Observations (not counted as defects)

- O1. The package name is empty in the log, as in `Generating methods for /StatusV2` (`logs/03-prysm-gen.log`).
  `packages.Config.Mode` in `sszgen/importer.go` has no `NeedName`, so `PkgPath` is an empty string (cause found by reading the source).
  The output files are byte-identical to the smoke run. There is no effect on the output.
- O2. Hand-written delegation: `Slot`, `Epoch`, `ValidatorIndex`, `Gwei` and `CommitteeIndex` in Prysm `consensus-types/primitives` have hand-written SSZ methods.
  The generated code delegates these fields to those methods (for example `c.FinalizedEpoch.MarshalSSZTo(dst)` in `StatusV2.MarshalSSZTo`).
  `Slot.MarshalSSZTo` makes a new slice and then does `append`. The `UnmarshalSSZ` error is `fmt.Errorf("%d")`.
  The generator behavior is as designed. But the 1c proofs need a specification of the Go code of 5 types that is not generated (24 functions) (`TYPES.md` section 5).
  The existing reduced Prysm types (`fv/kraken/target/prysm`) use a local `Slot` with no methods, so they do not have this path.

## 2. Generator change compatibility: three error-message test regressions (quoted)

Source: `/workspace/agent-runs/prysm-fv-pin-smoke/REPORT.md` section 6, reproduction `repro/partsmetadata-bitlist-limit.sh`, logs `logs/63` (new output), `logs/70` (baseline).

- `consensus-types/blocks`: `TestMarshalPartsMetadata/available_too_large`, `/requests_too_large`, `TestPartialDataColumn_PartsMetadata/marshal_error_due_max_bitlist_size`.
- Cause: `280b752`. The encoder checks a Bitlist with `ssz.ValidateBitlist(x, 4096)` (bits), not with the byte length. Too-large inputs are still rejected. Only the error message is different from the test expectation.
- Classification: not a generator defect. It is a compatibility problem of the generator change. We did not weaken the tests and did not change them.
- Rerun in this session: see "Rerun results" at the end of the document.

## 3. Baseline failures of the minimal tag (quoted, separate from section 2)

Source: smoke REPORT section 6, logs `logs/64`·`71`, `logs/66`·`73`.

- `consensus-types/blocks` `-tags minimal`: the test files fail to compile. It is the same with the committed files (baseline).
- `encoding/ssz/detect` `-tags minimal`: `TestByState` panic. It is the same in the baseline.
- It has no relation to the generated code. It is the same with or without the new output.

## 4. Tool gaps outside the generator (candidates for Kraken and converter requests)

- K1. `%riz`: GNU objdump writes the SIB byte of a `%r12` base address as `0x10(%r12,%riz,1)`. The Kraken runtime parser rejects it with `unknown register: riz`.
  Because of this, 13 generated functions of I do not parse (`go1.26.10/kparse.json`). Diagnostic copies with `%riz` removed all parse (`go1.26.10/kparse-riz-diag.json`).
  The address is the same as `(%r12)`. The fix location is the normalization in `link/conv.py` or the Kraken parser. Neither is a path of this stream. The proposal is in `OUTBOX.md` of the run directory.
- K2. `bsr`: only in `ssz.ValidateBitlist` (the same as the existing Kraken request).

## Rerun results

This session ran the same test commands as the smoke run on a tree with all 8 configurations (phase0..fulu, engine) generated again.
The smoke run changed only the two fulu files. Thus we ran the tests again. The raw data is `tests/prysm-tests.json`, and the log copies are `tests/prysm-tests-1{0,1}-log.txt`.

| Package | Preset | Result |
| --- | --- | --- |
| `proto/prysm/v1alpha1` (`-run 'Fulu\|PartialDataColumns'`) | mainnet, minimal | passed |
| `consensus-types/blocks` (smoke `-run`) | mainnet | failed: the 3 subtests of section 2 |
| `consensus-types/blocks` (smoke `-run`) | minimal | test build failed (same as section 3) |
| `encoding/ssz/detect` (smoke `-run`) | mainnet | passed |
| `encoding/ssz/detect` (smoke `-run`) | minimal | `TestByState` panic (same as section 3) |
| All four packages (no `-run`) | mainnet | `v1alpha1`, `engine/v1`, `detect` passed. In `blocks`, only the 3 of section 2 failed |

- The only failed subtests are the three of section 2. There are 0 new failures (`failed_subtests_not_in_smoke_known_3` = []).
- In the first full run (`logs/10`), the `head` in my script cut the output, and the rc was 141. `logs/11` replaces it.
- This session did not run the baseline (committed files) again. "It is the same in the baseline" in section 3 is a quotation.
- We did not run the spec `ssz_static` tests, the Bazel tests or other Prysm packages.
- Item S7 of the first phase 1c review: the run above used `go test -p 2`. The rule is `-p 1`. We ran the same 7 commands again with `gen/prysm-tests.sh` (`-p 1`, `set -o pipefail`, full output kept) (run `logs/28`). The results are the same: the only failed subtests are the three of section 2, and the two minimal failures are also the same. Raw data `tests/prysm-tests-p1.json`, summary `tests/prysm-tests-p1-summary.txt`. This replaces the basis of the table above.
- Item N4 of the second phase 1c review: the exit code of `gen/prysm-tests.sh` is now the verdict of the committed classifier `gen/prysm_tests_classify.py` (0 if there are only known failures). We applied the classifier to the output of `logs/28`: verdict "only known failures", 0 unexpected (`tests/prysm-tests-p1-classified.json`). A control with an unknown failure added ends with 1. We did not run the Prysm tests themselves again (the 7 outputs are from `logs/28`).
- Item R3-S5 of the third phase 1c review: the classifier also uses package-level `FAIL` lines and `panic` for the verdict (allowed only when a known failure of that run explains them). The two controls (`FAIL …/engine/v1` added to t7, `panic` added to t1) end with 1 (`tests/classifier-controls/`). The same fix also corrected a regular-expression error: `^FAIL\s+` matched the word `FAIL` across lines. We ran `prysm-tests.sh` with the changed exit code in the gate (`go test -p 1`, run `logs/40`): gate exit code 0, verdict "only known failures", 0 unexpected (`tests/prysm-tests-r3-classified.json`).
