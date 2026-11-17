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

An input that starts with `value:` also tells how to change a value (`values_test.go`).
The harness first checks it as SSZ bytes, like every other input. Then:

1. `UnmarshalSSZ` decodes one of the seeds.
2. The changes set lists, byte strings and bitfields to lengths at the edges of their type: 0, 1, the limit, the limit plus 1.
   They also flip bits of bitfields: the padding bits and the bitlist delimiter first.
3. `MarshalSSZ` encodes the changed value. If it refuses the value, `HashTreeRoot` must return an error.
4. EthLib must accept the bytes, and `HashTreeRoot` of the value must equal the EthLib root.
   If EthLib rejects the bytes, the message also tells if `HashTreeRoot` gave a root.
   The bytes must then pass the checks 1 to 3 above.

A panic in `HashTreeRoot` is a difference with its own message.

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

```sh
go test -v -run '^Fuzz' . -args -codes | grep '^Fuzz'
# FuzzCheckpoint fusaka entries=23 value-entries=11 marshal-refused=0 calls=34 both-accept=22 accept=22 SCOPE=12
```

- `entries` counts corpus entries: the seed corpus (with the value seeds), `testdata/fuzz/` and the fuzz cache.
  Identical entries from two sources count twice.
- The verdict counts count EthLib calls, as the fuzz function makes them.
  Each entry gives one call for its bytes. A value entry gives one more call for its encoding, unless `MarshalSSZ` refuses it (`marshal-refused`).
- `both-accept` counts the calls where `UnmarshalSSZ` accepts too.
- A verdict that does not show is not tested yet.

The default cache is the one of `go test -fuzz`. For the cache of `fuzzall.sh`, add `-test.fuzzcachedir` after `-codes`
with the path that `fuzzall.sh` sets in `CACHE`.

Use the minimal preset for large containers.
A mainnet `BeaconState` is 2.7 MB, so a random mutation rarely hits a given field.

## Recorded differences

`testdata/fuzz/` holds one small input for each class of difference found.
`known.txt` lists these classes, so `go test .` passes.
`STRICT=1 go test .` and `STRICT=1 go test -tags minimal .` fail on the inputs of their preset while the generator has the difference.
The expected number of failing inputs with `STRICT=1`:

| Generator | mainnet | minimal |
| --- | --- | --- |
| main `c3f77ce4` | 5 | 7 |
| PR #27 `628a50c6` | 4 | 5 |

| Class | Input | Status |
| --- | --- | --- |
| The decoder accepts a byte list longer than `ssz-max` | `FuzzEngineExecutionPayloadHeaderDeneb/bytelist-over-max` | Bug. Fix proposed in PR #27 |
| The decoder accepts set padding bits in a Bitvector | `FuzzAttestationElectra/bitvector-padding-minimal` (minimal preset) | Bug. Fix proposed in PR #27 |
| `MarshalSSZ` encodes a Bitlist above its limit (F2) | `FuzzAttestationElectra/value-bitlist-over-max` | Bug. Fix proposed in PR #27 |
| `MarshalSSZ` encodes a Bitlist with no delimiter bit | `FuzzAttestationElectra/value-bitlist-no-delimiter` | Bug. Fix proposed in PR #27 |
| `MarshalSSZ` encodes set padding bits in a Bitvector | `FuzzAttestationElectra/value-bitvector-padding-minimal` (minimal preset) | Bug. Fix proposed in PR #27 |
| `HashTreeRoot` gives a root for a value that `MarshalSSZ` refuses: a Bitlist above its limit, a Bitlist with a zero last byte, a Bitvector with set padding bits | The three `value-` inputs above. On main, `MarshalSSZ` encodes these values, and the encoder message adds "and HashTreeRoot gives a root" | Bug. No fix proposed yet |
| `HashTreeRoot` panics on a progressive Bitlist with a zero last byte (`parseBitlistProgressive` in `ssz/htr.go`) | `FuzzAttestationGloas/value-progressive-bitlist-zero-byte` | Bug. No fix proposed yet |
| The decoder rejects a Gloas progressive list or bitlist above its `ssz-max` tag | `FuzzEngineExecutionRequestsGloas/progressive-list-over-tag` | Policy of the generator (soft limit). The SSZ type has no limit |

When a fix removes a class, remove its line from `known.txt`.

## Continuous integration

`.github/workflows/ethlib-fuzz.yaml` runs on pull requests that change the generator, the runtime or this module.
It regenerates the Prysm types with the generator of the pull request and runs `go test` for both presets.
It does not fuzz.

`.github/workflows/ethlib-fuzz-nightly.yaml` fuzzes once a day, and on demand.
It uses the setup steps and the cache keys of `ethlib-fuzz.yaml`, so the two workflows share their caches.
It runs `fuzzall.sh` on the minimal preset: 4 targets at a time, 1 worker each, 45 seconds for each target.
A difference that `known.txt` does not list fails the job. The job then uploads the logs and `testdata/fuzz/`.

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
