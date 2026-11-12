# gen: generators and check tools

This directory holds the programs that write Lean files and records, and the programs that check them.
A path that starts with `lean/`, `link/` or `prysm/` is relative to `fv/kraken/`. Any other path is relative to `fv/kraken/gen/`.
A command that starts with `fv/kraken/` runs from the repository root.
The design principles are in `../../README.md`.

## 1. Principles

- A generator is untrusted. Lean checks every proof that a generator writes.
- The statement of a generated theorem is checked separately, by a frozen kind (section 4) or by an identity with a hand statement.
- A generated Lean file must be equal to the output of its generator. Do not edit a generated file by hand.
  The header comment of a generated file names its generator. Some headers also give the sha256 of the inputs.
- A generator does not write to `lean/Fk`, `link/` or `gen/frozen/`.
- The Python programs use only the standard library. Run them with `python3 -I`.
- A generator refuses an input that it does not match. It writes nothing, or it marks a partial output as partial.

## 2. Generators

| Program | Reads | Writes |
| --- | --- | --- |
| `scal/scalgen.py`, with `scal/gen5.py` and `scal/gen6enc.py` | A converted `.S` file and the IR entry of one type | `lean/E2eScal/Gen*.lean`: segment, accept, size reject and encoder fast path theorems |
| `scal/gen.sh` | | Runs `scalgen.py` once for each committed generated file |
| `e2e/descterm.py`, `e2e/lvdescterm.py` | A `Desc` JSON file that the checker accepted | `*SpecChecker.lean`: the checker `Desc` as Lean |
| `e2e/layout.py`, `e2e/adlayout.py` | `prysm/ir/ir-mainnet.json` | `lean/E2e/Layout.lean`, `lean/E2eAd/Layout.lean` |
| `desc/producer.py` | The reduced IR | One `Desc` JSON file for each type |
| `inventory.py` | The raw IR of the generator | `prysm/ir/*.json` (`reduce`) and `prysm/inventory.json` (`build`) |
| `types_md.py`, `scope6.py` | `prysm/inventory.json` | `prysm/TYPES.md`, `prysm/SCOPE-P6.json`, `prysm/SCOPE-P6.md` |
| `keepalive.py` | `prysm/inventory.json` | The `main.go` of the Prysm target |
| `tools/inventory.py` | The symbol listing of the ELF and a declaration list from Lean | `prysm/go1.26.10/ssz-methods.json`, `prysm/INVENTORY.md`, `prysm/INVENTORY.json` |
| `e2e/*link.py` | The Prysm ELF, its disassembly and symbol listing | One link set: the filtered disassembly and the data files |
| `e2e/callgraph.py` and the `callgraph` mode of `e2e/*link.py` | A filtered disassembly | `callgraph*.json` files |
| `e2e/*diff.py` | Nothing, or a Go output file | Go differential cases, and their comparison with the Go output |
| `frozen/build_lists.py` | The inventory and the generated Go | `frozen/THEOREMS.json`, `frozen/ASSUMPTIONS.json` |
| `kparse/summ.py` | A log of `kparse/KParse.lean` | `prysm/go1.26.10/kparse.json`: which functions the Kraken parser reads |
| `prysm-gen.sh`, `prysm-elf.sh` | A Prysm tree and the generator binary | Generated Go, the IR and the Prysm ELF (needs Go) |

The tools for the 24 other flat types are in `prysm/go1.26.10/e2e/f24/tools/` and `prysm/go1.26.10/e2e/f24/gen/part1.sh`.
The encoder specification and witness emitter of the flat types is `prysm/go1.26.10/e2e/scal/e2c/e2cemit.py`.

## 3. Check that a generated file is the generator output

Use `regen_check.sh` of the project skill. It runs the generator two times into scratch files and compares them with the tracked file.
Exit 0 means the same bytes. Run it from `fv/kraken`:

```sh
sh ../../.claude/skills/maintaining-methodical-fv/scripts/regen_check.sh lean/E2eScal/GenCi.lean -- sh -c 'python3 -I gen/scal/scalgen.py p1 --S prysm/go1.26.10/e2e/ad/link/norm/github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.UnmarshalSSZ.S --const CiUnmarshal --name ci_unmarshal_accept_main_g --same-as E2eAd.ci_unmarshal_accept_main --imports E2eScal.P1,E2eAd.Prims --open E2eAd.Code > "$REGEN_OUT"'
```

For the other files, take the command from `scal/gen.sh` or from the file header. Replace the output redirect with `> "$REGEN_OUT"`.
The check compares bytes only. It does not show that the output is correct.

## 4. The kind check

A generated theorem `t` is followed by a line `t_kind`.
It states that the full type of `t`, with all hypotheses, is equal to a frozen kind with parameters.
The kinds are hand text in `lean/E2eScal/Kind*.lean`. Each kind has a proof from its lemma.
Lean checks the identity. So a hypothesis that the generator adds, removes or changes makes `t_kind` fail.

Lean does not check which kind the line names. A line that compares `t` with itself also compiles.
`scal/kindcheck.py` closes this gap. It checks by text that every `t_kind` names a frozen kind and has the fixed proof line.
It also checks that the kind files are at their pinned git blobs.

```sh
python3 -I -B fv/kraken/gen/scal/kindcheck.py --selftest
python3 -I -B fv/kraken/gen/scal/kindcheck.py fv/kraken/lean/E2eScal/GenCi.lean
python3 -I -B fv/kraken/gen/scal/kindcheck.py --partial fv/kraken/lean/E2eScal/Gen2BhDecPartial.lean
```

Run Lean and `kindcheck.py` together on every generated file. Each one alone lets a defect through.
`kindcheck.py` does not check the kind parameters. Only the proof checks them, through its code facts.
A partial file gives exit 3, never 0. Exit 3 is not a full-coverage result.
A kind identity is not a witness. It does not show that the premises can hold.

## 5. The independent `Desc` checker

`desccheck/DescCheck.lean` is a Lean program that runs EthLib functions. It shares no code with `desc/producer.py`.
So a defect in the producer or in the IR does not also hide in the checker.
`desc/run_desccheck.sh` runs it (needs Lean). The result is `desc/results/main.result.json`.

- The set of expected types is closed. It is the table of hand cases in the checker plus the keys of `prysm/inventory.json`.
- Before it parses a file, the checker limits the file size and the nesting depth.
- For a hand case, the checker compares the `Desc` with the EthLib specification in `lean/Fv1/`.
- For a Prysm type, the checker compares the `Desc` only with the inventory. This is a consistency check, not a specification check.

Thus the Prysm theorems use a hand `Desc` written from consensus-specs, and a theorem shows that it has the same codec as the checker `Desc`.

## 6. Python-only checks

These run without Lean, Go or the Prysm ELF:

- `scal/kindcheck.py`, and the `--selftest` mode of `e2e/axioms_gate.py` and the other gate scripts.
- `python3 -B fv/kraken/link/data.py --check fv/kraken/link/out`.
- `regen_check.sh` with `scal/scalgen.py`, `e2e/descterm.py`, `e2e/lvdescterm.py`, `e2e/layout.py` and `e2e/adlayout.py`.
- `inventory.py reduce` and `build`, `types_md.py`, `scope6.py`, `keepalive.py`, `kparse/summ.py`.
- `frozen/test_frozen.py <repo-root> <scratch>`, which runs `frozen/build_lists.py` and compares the two frozen lists.
- `desc/test_desc.py prepare` writes the `Desc` files. The checker run after it needs Lean.

These need more than Python:

- `e2e/negative.py` and the axioms gates need Lean.
- The link checks need the ELF and the LLVM tools.
- The differential checks need Go and a Prysm tree.
- `tools/inventory.py` needs the symbol listing of the Prysm ELF and Lean.

## 7. Known limits

These generated outputs do not reproduce from the tracked tree today:

- `frozen/ASSUMPTIONS.json`: the file has a hand edit. `frozen/test_frozen.py` exits 1.
- 11 of the 18 files that `e2e/descterm.py` writes have hand-added or edited header lines.
- 2 of the 14 call graphs (`e2e/callgraph.py` and the `callgraph` mode of `e2e/*link.py`): one needs a compiler log that is not tracked, and one needs the full ELF disassembly.

Other limits:

- The specification and witness files of five flat types (`Hs`, `Sa`, `Sd`, `Vb`, `Ve`) have no tracked generator script.
- The commands of 12 generated files are not in `scal/gen.sh`. Their headers give the commands.
- The encoder loop of `scal/gen.sh` and `prysm/go1.26.10/e2e/f24/gen/part1.sh` uses the GNU `sed` form `\U`. BSD `sed` on macOS writes wrong file names.
- `prysm/go1.26.10/e2e/f24/gen/part1.sh` calls a job wrapper that is not tracked. Run its `scalgen.py` commands directly.
- Six `*SpecChecker.lean` headers name a path where the `Desc` file is not. The file is in a subdirectory of `prysm/go1.26.10/e2e/`.
- `kindcheck.py` does not bind the code constant of a theorem to the `.S` file of the header. It does not check the `.S` label against the IR type.
