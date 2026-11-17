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

The first EthLib build takes about 30 minutes. Later runs use the build in `$ETHLIB_DIR`.

## Fuzz

```sh
./fuzzall.sh                          # each target for 5 minutes, mainnet preset
PRESET=minimal ./fuzzall.sh           # minimal preset
FUZZTIME=1h ./fuzzall.sh BeaconState  # only the targets that match
```

A target stops at its first difference.
To fuzz past a class of differences that is already recorded, give its message as a regular expression.
The harness then skips those inputs:

```sh
KNOWN='paddingBits|ssz-max exceeded' ./fuzzall.sh
```

To fuzz one target by hand: `go test -run '^$' -fuzz '^FuzzCheckpoint$' -fuzzminimizetime 5s .`

Use the minimal preset for large containers.
A mainnet `BeaconState` is 2.7 MB, so a random mutation rarely hits a given field.

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
