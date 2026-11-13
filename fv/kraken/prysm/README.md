# prysm: the Prysm target and its evidence files

This directory holds the Prysm target: the type inventory, the generator IR, the generated Go, the link set and the check records.
Paths in section 1 and section 4 are relative to this directory. Paths in the tables of sections 2 and 3 are relative to `go1.26.10/` and `go1.26.10/evidence/`.
A path that starts with `gen/` or `lean/` is relative to `fv/kraken/`.
How to build the target ELF again is in `../README.md` section 3.

## 1. Content

| Path | Content | Written by |
| --- | --- | --- |
| `ir/ir-mainnet.json`, `ir/ir-minimal.json` | The reduced generator IR (intermediate representation) of each type, with the Go field layout `go_fields` | `gen/type_inventory.py reduce` |
| `inventory.json` | The type inventory: every generated type, its fields and its delegations | `gen/type_inventory.py build` |
| `TYPES.md`, `type-scope.json`, `type-scope.md` | Type lists and a scope classification of the inventory | `gen/type_list_document.py`, `gen/type_scope.py` |
| `proof-inventory.md`, `proof-inventory.json` | The per-method table of theorems, witnesses and paths not proved | `gen/tools/proof_inventory.py run` (with the outputs of `inventory_decls.lean` and of an axioms gate run on the built tree) |
| `_generated/` | The Go files that the pinned generator wrote for Prysm, with `SHA256SUMS` | `gen/prysm-gen.sh` |
| `diff/` | A classification of the differences between these files and the Prysm files | `gen/gendiff.py` |
| `go1.26.10/` | The target namespace of the Go 1.26.10 ELF (section 2) | |

## 2. The target namespace `go1.26.10/`

All files here belong to one ELF. Do not mix them with the files of another ELF.

| Path | Content |
| --- | --- |
| `build-ids.txt` | The Go version, the build flags and the sha256 of the ELF, its disassembly and its symbol listing |
| `p1cbin-main.go.txt`, `prysm-go.mod.diff` | The `main` package of the binary and the `go.mod` change in the Prysm tree |
| `ssz-methods.json` | Every SSZ method of the ELF. It is the denominator of the inventory |
| `functions.json`, `kparse.json`, `kparse-log.txt` | The functions with a converted `.S` file, which of them the Kraken parser reads, and the parser log that `gen/kraken-parser/summ.py` reads |
| `link/` | A link table of 136 functions of this ELF. No current theorem includes it |
| `link-set/` | The one link set of the proved functions: `target.objdump`, `norm/*.S`, `norm/all.S`, `data/*.data` and `RESULT`. `gen/checks/link_set.py` writes it. Its `RESULT` replaces the `RESULT` files of the 16 earlier link sets. `data-ids-old-new.tsv` maps the data ids of the earlier link sets and records to the present ids |
| `evidence/` | The check records, negative case lists and generator records of the proved types (section 3) |
| `capacity-reserved/` | A separate ELF of a generator option that reserves the encoder output once. The option is not adopted. `lean/Prysm/Checkpoint/CapacityReserved*.lean` prove theorems about it |

## 3. Records under `go1.26.10/evidence/`

The code and data files of all these types are in the one link set `link-set/` (section 2).
This table says what each subdirectory holds.

| Subdirectory | Types or content |
| --- | --- |
| `negative/` | `Checkpoint` and `primitives.Epoch`, and the negative test results of their theorems |
| `attestation-data/` | `AttestationData`, `primitives.Slot`, `primitives.CommitteeIndex` |
| `beacon-block-header/` | `BeaconBlockHeader`, `primitives.ValidatorIndex` |
| `eth1-data/` | `Eth1Data` |
| `blob-identifier-and-deposit-message/` | `BlobIdentifier`, `DepositMessage` decoders |
| `deposit-data-and-pending-partial-withdrawal/` | `Deposit_Data`, `PendingPartialWithdrawal` decoders |
| `pending-consolidation-and-sync-committee-message/` | `SyncCommitteeMessage`, `PendingConsolidation` decoders |
| `pending-deposit-and-pow-block/` | `PendingDeposit`, `PowBlock` decoders (the link script `gen/checks/seven_flat_decoders_link.py` also covers the five types of `five-flat-types/`) |
| `five-flat-types/` | `Desc` files, Go differential cases and negative case lists of five flat decoders |
| `flat-types/` | The 24 other flat fixed-size types, with their generator tools |
| `lists-and-vectors/` | Lists and vectors: `SyncAggregate`, `SyncCommittee`, `IndexedAttestation`, `HistoricalBatch`, `Deposit`, `DataColumnsByRootIdentifier`. The negative case lists of each group |
| `generator-cases/` | The negative case lists of the generated proofs, the encoder specification emitter `encode-spec/encode_spec_emitter.py` and two check scripts |

Other files in `evidence/`: `axioms-gate.json` and `e2e.json` are records of runs before the restructuring.
They name files and libraries that are no longer in the tree.
`axioms-gate.json` is the record of an axioms gate run. `e2e.json` binds the include files and the link inputs of that time by sha256.
`gen/checks/axioms.py` writes `axioms.json` from `AXIOMS.txt`. `gen/checks/differential.py check` writes `differential.json`. `gen/checks/negative.py` writes `negative/result.json`.

## 4. Files that are inputs of checks

Do not edit these files by hand. Make them again with their generator.

- The `.S` and `.data` files of the link set. Lean includes them, and the link check compares them with the ELF.
- `ir/*.json` and `inventory.json`. The generators, the `Desc` checker and the frozen lists read them. `gen/frozen/THEOREMS.json` pins the sha256 of `inventory.json`.
- The `*.desc.json` files. The `Desc` checker accepted them, and the header of each `*SpecChecker.lean` gives their sha256.
- The negative case lists `negcases*.json`. The negative test scripts read them.
- `go1.26.10/build-ids.txt` and `go1.26.10/ssz-methods.json`. `gen/tools/proof_inventory.py` reads them. It checks the symbol listing against the sha256 in `build-ids.txt`.

The other JSON files and the `RESULT` files are records of check runs. A new run writes them again. Do not edit them to change a result.
