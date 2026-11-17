# Differential fuzzing against EthLib

This module compares the code that methodical-ssz generates with [EthLib](https://github.com/ethereum/EthLib).
EthLib is an SSZ specification in Lean 4 with proofs. It is the oracle.
The module is separate, so the main module gets no Lean or cgo dependency.

## What a target checks

Each target takes one Prysm type and the EthLib container that it stands for.
For each input:

1. `UnmarshalSSZ` and EthLib must agree on accept or reject.
2. If both accept, `MarshalSSZ` must equal the EthLib encoding.
3. If both accept, `HashTreeRoot` must equal the EthLib root.

The Go fuzzer sees only the coverage of Go code. EthLib is not instrumented.
So the harness gives accept and each EthLib decode error code its own Go branch (`signal` in `codes_test.go`).
An input that reaches a new EthLib rejection reason is then new coverage, and the fuzzer keeps it.

An input that starts with `value:` holds no SSZ bytes. It tells how to change a value (`values_test.go`):

1. `UnmarshalSSZ` decodes one of the seeds.
2. The changes set lists, byte strings and bitfields to lengths at the edges of their type: 0, 1, the limit, the limit plus 1.
   They also flip bits of bitfields: the padding bits and the bitlist delimiter first.
3. `MarshalSSZ` encodes the changed value. If it refuses the value, the input passes.
4. EthLib must accept the bytes, and `HashTreeRoot` of the value must equal the EthLib root.
   The bytes must then pass the checks 1 to 3 above.

This tests `MarshalSSZ` and `HashTreeRoot` on values that no decode gives.
The seed corpus holds one value input for each seed that decodes.

A difference fails the target. Go saves the input in `testdata/fuzz/<target>/`.
The two presets share that directory. A saved input shows its difference only at the preset that found it.

`targets_test.go` lists the targets: the Prysm types of Fulu and Gloas that have an EthLib container.
A target skips itself if EthLib answers with code 0 (no such container at the fork).
Code 0 is not a verdict on the bytes, so the harness never reads it as a rejection.

## Setup

You need Go, `elan` (Lean), `rsync` and about 9 GB of disk space.

```sh
./gen.sh                  # copy the pinned Prysm to .prysm, regenerate its *.ssz.go
./seeds.sh                # get the ssz_static vectors (seed corpus) into .seeds
eval "$(./ethlib.sh)"     # build EthLib at the pinned commit, set the cgo flags
go test .                 # run each target on its seeds and saved inputs
```

The first EthLib build took 6 minutes on an 18-core machine. Later runs use the build in `$ETHLIB_DIR`.
The build covers the SSZ export and the modules that it imports, not the proofs.

## Fuzz

```sh
./fuzzall.sh                          # each target for 5 minutes, mainnet preset
PRESET=minimal ./fuzzall.sh           # minimal preset
FUZZTIME=1h ./fuzzall.sh BeaconState  # only the targets that match
```

A target stops at its first difference.
The harness skips the inputs whose difference matches a line in `known.txt`.
That file lists the classes of differences that are recorded.
To fail on every difference, set `STRICT=1`:

```sh
STRICT=1 ./fuzzall.sh
```

To fuzz one target by hand: `go test -run '^$' -fuzz '^FuzzCheckpoint$' -fuzzminimizetime 5s .`

To see which EthLib verdicts the corpus of each target reaches, give `-codes`.
Each target then prints one line for each fork and skips itself.
The corpus is the seeds, `testdata/fuzz/` and the fuzz cache.

```sh
go test -v -run '^Fuzz' . -args -codes | grep '^Fuzz'
# FuzzEngineExecutionRequests fusaka inputs=14 both-accept=6 accept=6 SCOPE_TOO_SMALL=1 SCOPE_UNDIVIDED=4 FIRST_OFFSET=1 OFFSET_PAST_SCOPE=2
```

`both-accept` counts the inputs that EthLib and `UnmarshalSSZ` both accept.
A verdict that does not show is not tested yet.
The default cache is the one of `go test -fuzz`. For the cache of `fuzzall.sh`, add `-test.fuzzcachedir` after `-codes`
with the path that `fuzzall.sh` sets in `CACHE`.

Use the minimal preset for large containers.
A mainnet `BeaconState` is 2.7 MB, so a random mutation rarely hits a given field.

## Recorded differences

`testdata/fuzz/` holds one small input for each class of difference found.
`known.txt` lists these classes, so `go test .` passes.
`STRICT=1 go test .` and `STRICT=1 go test -tags minimal .` fail on the inputs of their preset while the generator has the difference.

| Class | Input | Status |
| --- | --- | --- |
| The decoder accepts a byte list longer than `ssz-max` | `FuzzEngineExecutionPayloadHeaderDeneb/bytelist-over-max` | Bug. Fix proposed in PR #27 |
| The decoder accepts set padding bits in a Bitvector | `FuzzAttestationElectra/bitvector-padding-minimal` (minimal preset) | Bug. Fix proposed in PR #27 |
| `MarshalSSZ` encodes a Bitlist above its limit (F2) | `FuzzAttestationElectra/value-bitlist-over-max` | Bug. Fix proposed in PR #27 |
| The decoder rejects a Gloas progressive list or bitlist above its `ssz-max` tag | `FuzzEngineExecutionRequestsGloas/progressive-list-over-tag` | Policy of the generator (soft limit). The SSZ type has no limit |

When a fix removes a class, remove its line from `known.txt`.

## Continuous integration

`.github/workflows/ethlib-fuzz.yaml` runs on pull requests that change the generator, the runtime or this module.
It regenerates the Prysm types with the generator of the pull request and runs `go test` for both presets.
It does not fuzz.

## Test a different generator

`gen.sh` uses the generator and the runtime of the repository in `$GEN`.
The default is the repository that holds this module.

```sh
GEN=/path/to/another/methodical-ssz ./gen.sh
```

## Pins

| What | Where | Value |
| --- | --- | --- |
| EthLib | `ethlib.sh` | `f4c856c8` |
| Prysm | `gen.sh` | develop `2e8dd0ffd7` |
| consensus-spec-tests | `seeds.sh` | `v1.7.0-beta.4` |
