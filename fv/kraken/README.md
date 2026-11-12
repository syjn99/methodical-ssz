# kraken: proofs on the Kraken x86-64 model

This project proves that the x86-64 machine code of the SSZ methods that `sszgen` emits for Prysm types agrees with the EthLib SSZ specification.
Prysm is an Ethereum consensus client. Kraken is a Lean 4 model of x86-64 instructions.
The design principles are in `../README.md`. The rules are in `../AGENTS.md`.

The per-method state of the proofs is the generated table `prysm/proof-inventory.md`.
Do not copy its numbers into other documents. Run the inventory again instead (section 5).

## 1. Targets

The project has two target binaries. Their proofs are separate, because a proof about one ELF does not transfer to another.

**The Prysm target.** This is the main target.

- The source is a pinned Prysm commit, with the generated files of the pinned generator.
- The binary is a small Go `main` package that keeps the SSZ methods of all inventory types in the ELF.
- The compiler is Go 1.26.10. It cross-compiles to `GOOS=linux GOARCH=amd64 GOAMD64=v1 CGO_ENABLED=0`, with `-tags purego -trimpath`.
- The ELF identity is its sha256 `c6403c02a110ffd6fe6d31a3c89cd395ac457b5d62e60e2e611b8ab9a8dd911e`.
  The file `prysm/go1.26.10/build-ids.txt` records it, with the Go build ID and the sha256 of the symbol listing and the disassembly.
- The ELF is about 23 MB. It is not in the repository. Section 3 tells how to build it again.

**The test target.** This is an older binary of small test types, compiled with Go 1.26.3.

- The Go types are in `target/`. The `main` package is `cmd/p1bin/`.
- The ELF, its symbol listing and its disassembly are in `link/out/`. Their sha256 values are in `link/out/build-ids.txt`.
- The `TestTarget` Lean library proves some theorems on this binary. The Prysm proofs also use some of its declarations.
- `link/build.sh` builds this ELF again from the repository root.

## 2. Pinned versions

Read each pin from the file that holds it. Do not copy the values into other files.

| Pin | File that holds it |
| --- | --- |
| Generator commit (`sszgen/`, `ssz/`) and Prysm source commit | This file: generator `698c2025a73a296b55b95744a8408f3b03b2546b`, Prysm `ab15ff70c72a568c870b2de662474685a95de294` |
| Go version, build flags, ELF sha256 of the Prysm target | `prysm/go1.26.10/build-ids.txt` |
| Go version, ELF sha256 and generated file hashes of the test target | `link/out/build-ids.txt` |
| Kraken commit and EthLib commit | `lean/lakefile.toml` (`rev`) and `lean/lake-manifest.json` |
| Lean toolchain | `lean/lean-toolchain` |
| Go module versions of the test target | `../../go.mod` |
| Sources of derived evidence files and their licenses | `THIRD-PARTY-NOTICES.md` |

## 3. Build the Prysm target again

You need Go 1.26.10, a clean Prysm tree at the pinned commit, and a generator binary built from the pinned generator commit.
Run heavy jobs one at a time, under a memory limit.

1. Add the `replace` line of `prysm/go1.26.10/prysm-go.mod.diff` to the Prysm `go.mod`. Change its path to your generator tree.
2. Generate the SSZ files and the generator IR with `sh fv/kraken/gen/prysm-gen.sh <prysm-tree> <generator-binary> <out>`.
3. Copy the generated files from `<out>/gen/` into the Prysm tree.
4. Write the `main` package with `python3 -I fv/kraken/gen/keepalive.py fv/kraken/prysm/inventory.json <prysm-tree>/fvphase1c/p1cbin/main.go`.
5. Build and dump the ELF with `sh fv/kraken/gen/prysm-elf.sh <prysm-tree> <elf-out> <empty-gocache-dir>`.
6. Compare the sha256 of the ELF with `prysm/go1.26.10/build-ids.txt`. If they differ, stop. The proofs do not apply.

The IR (intermediate representation) is the type description that the generator reads.
The generator binary is built from the pinned generator commit with Go 1.26.10 and `-trimpath`.
After step 2, these commands make the IR, the inventory, the function list, the parser record and the type documents again:

```sh
python3 -I fv/kraken/gen/type_inventory.py reduce <out>/ir-mainnet.json fv/kraken/prysm/ir/ir-mainnet.json   # the same for minimal
python3 -I fv/kraken/gen/type_inventory.py build fv/kraken/prysm
python3 -I fv/kraken/gen/mnemonics.py <elf-out>/p1cbin-amd64.objdump fv/kraken/lean/.lake/packages/Kraken/Kraken/X64/Parser/Basic.lean fv/kraken/link/conv.py fv/kraken/prysm/inventory.json fv/kraken/prysm/go1.26.10/functions.json
python3 -I fv/kraken/link/conv.py <elf-out>/p1cbin-amd64.objdump <elf-out>/p1cbin-amd64.nm <norm-out> --norm
cd fv/kraken/lean && KPARSE_LIST=<.S list> lake env lean ../gen/kparse/KParse.lean
python3 -I fv/kraken/gen/kparse/summ.py <kparse log> fv/kraken/prysm/go1.26.10/functions.json fv/kraken/prysm/go1.26.10/kparse.json
python3 -I fv/kraken/gen/type_list_document.py fv/kraken/prysm
python3 -I fv/kraken/gen/type_scope.py fv/kraken
```

The tracked file `prysm/go1.26.10/kparse-log.txt` is the parser log of the pinned ELF. `kparse/summ.py` makes `kparse.json` from it.

## 4. Directory layout

| Directory | Content |
| --- | --- |
| `cmd/p1bin/` | The `main` package of the test target |
| `target/` | The Go test types, two reduced Prysm types and their generated code (test target) |
| `link/` | The converter, the data extractor and the link check (see `link/README.md`) |
| `link/out/` | The test target ELF, its listings, the converted `.S` files, the data files and the link result |
| `lean/` | The Lean project: specifications, contracts and proofs (see `lean/README.md`) |
| `gen/` | Generators and check tools (see `gen/README.md`) |
| `prysm/` | The Prysm target: inventory, IR, generated Go, link sets and check records (see `prysm/README.md`) |

## 5. Build and check

Run the commands from the repository root, unless a command starts with `cd`.
Each item says what the command needs.

**Lean only.** Lake fetches Kraken and EthLib at the pinned commits on the first run.

```sh
cd fv/kraken/lean && lake build Machine Runtime Codec Spec TestTarget Prysm E2eScal E2eList E2eHb E2eDep E2eDepW E2eEnc E2eDec
cd fv/kraken/lean && lake build E2eList.SaReject    # one module
```

`lake build` without arguments builds only the default libraries `Spec`, `Machine`, `Runtime` and `TestTarget`.
After a build, `lake build --no-build <libraries>` must exit 0. `lake env lean` does not check that the build is current.

**Lean and Python.** These scripts call Lean through Lake.

```sh
python3 -I -B fv/kraken/gen/e2e/axioms_gate.py run <scratch>/gate.json <scratch>/dump.tsv
python3 -I -B fv/kraken/gen/e2e/negative.py <cases.json> <work-dir> <scratch>/result.json <case-id>
python3 -I -B .claude/skills/maintaining-methodical-fv/scripts/decl_drift.py <base.tsv> <head.tsv>
```

- The axioms gate covers every library of `lean/lakefile.toml`. It reads the library names from the lakefile when it runs.
- The gate needs Lean and a built tree. First it runs `lake build --no-build` on all modules. If that fails, the gate stops with exit 2.
- The gate writes a declaration dump. It checks that every declaration uses only `propext`, `Classical.choice` and `Quot.sound`.
- The gate also checks that each name of the hand lists in `gen/axioms-lists/` is in the dump. Each `*.lean` file of that directory is a hand list.
- A new library or a new hand list needs no change to the gate.
- The gate overwrites its JSON argument. Give a scratch path, unless you intend to update a committed record.
- The negative test files are `gen/e2e/negcases.json`, `gen/scal/negcases-*.json` and the `negcases-*.json` files under `prysm/go1.26.10/e2e/`.
  Run one case per job. The E2eList cases use `gen/e2e/lvnegative.py` with the same arguments.
- The drift check compares a dump with the dump of a reviewed tree.

**Python only.** These use only tracked files.

```sh
python3 -B fv/kraken/link/data.py --check fv/kraken/link/out
python3 -I -B fv/kraken/gen/scal/kindcheck.py --selftest
python3 -I -B fv/kraken/gen/scal/kindcheck.py fv/kraken/lean/E2eScal/GenCi.lean
python3 -I -B fv/kraken/gen/e2e/axioms_gate.py --selftest
```

`gen/README.md` tells how to regenerate a generated Lean file and compare it with the tracked file.

**The test target ELF and LLVM tools.** The ELF is in the repository. The check also needs `llvm-objdump` and `clang`.

```sh
python3 -B fv/kraken/link/check.py fv/kraken/link/out
python3 -B fv/kraken/link/check.py --selftest fv/kraken/link/out
```

**The Prysm target ELF.** You must build it first (section 3). Then these checks can run:

- The link check of each Prysm link set. The `gen/e2e/*link.py` scripts filter the disassembly and write the data files. Then `link/check.py` runs on the set.
- The method list of the inventory: `python3 -I -B fv/kraken/gen/tools/proof_inventory.py methods <nm-listing> <scratch>/ssz-methods.json`. Compare the output with `prysm/go1.26.10/ssz-methods.json`.

**A Prysm tree and Go 1.26.10.** The Go differential scripts `gen/e2e/*diff.py` write test cases. A Go program in a temporary Prysm tree runs them.
These runs check Go semantics on the host. They do not run the amd64 machine code.

## 6. Known limits

- Nothing ran on x86-64 hardware. No test compares Kraken with a real CPU.
- The runtime contracts are hypotheses. No proof shows that the compiled Go runtime satisfies them.
- The stack growth path and the write barrier path are excluded by premises. They are not proved.
- After a slice growth, the contract gives only an upper bound on the remaining heap. One encoder state after a second growth is not proved.
- There are no theorems for the hash tree root methods.
- Some converted `.S` directories that proofs include are not Lake inputs. A change in them does not make Lake build the proofs again.
- The Prysm ELF and its symbol listing are not in the repository. The Prysm link checks need them.
- The details and the state of each limit are in `FINDINGS.md`.
