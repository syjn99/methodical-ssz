# Prysm Fulu type list

`fv/kraken/gen/type_list_document.py` makes this file from the saved JSON. Do not change it by hand.
The program counts all numbers. The scope classification is a first pass (provisional). It is not a proof.

## 1. Summary

- Inventory set I: 135 generated types. Config types A: 124, Fulu-reachable B: 50 (generated 45, hand-written 5).
- In scope: 132, out of scope: 3 (provisional). Reasons for out of scope: deep nesting 3.
- For B only: in scope 44, out of scope 1.
- "In scope" means that the first-pass rules did not remove the type. It does not mean that a proof is possible. It also does not mean that the type fits the hand proof patterns.
  The in-scope rule accepts these field shapes. The types of I together have 46 `vector[bytesN]` fields, 31 `list[bytesN]` fields and 7 `vector[uint64]` fields. The depth is the inline depth (it does not follow delegation).
  The classification by what the proofs need is in `type-scope.md`.
- Hand-written delegate targets (`consensus-types/primitives`): 5. Types that call them: 52.
- Generated functions: 405 (types × 3), instructions: 116889, maximum for each function: 2890.
- Mnemonic level: 405/405 generated functions use only names that the Kraken runtime parser accepts.
- Real parser run: 392 generated functions OK, 13 ERR. All ERR are `%riz` operands (section 4).
- We ran all files that failed because of `%riz` (18, including functions outside I) again as diagnostic copies with only `%riz` removed. 18 are OK. This is only a diagnosis, not a conversion result.
- Differences from the committed Prysm files: 232 changed blocks, 232 classified, 0 not classified.
- Types with a different IR in the minimal preset: 41. Types with a changed scope classification: 0.

## 2. Fixed values

| Item | Value |
| --- | --- |
| Prysm source | `ab15ff70c72a568c870b2de662474685a95de294` (slice + `ssz-size`). It replaced the old pin `5ac1d028f5`/`45394e5` |
| Generator and runtime | `698c2025a73a296b55b95744a8408f3b03b2546b` |
| Target compilation | Cross-compiled for linux/amd64 with `go version go1.26.10 linux/arm64` (host binary), `GOOS=linux GOARCH=amd64 GOAMD64=v1 CGO_ENABLED=0 go build -p 2 -tags purego -trimpath` |
| Host | Linux aarch64 (generation is arm64 native. No x86-64 hardware) |
| ELF | sha256 `c6403c02a110ffd6fe6d31a3c89cd395ac457b5d62e60e2e611b8ab9a8dd911e`, 23486009 bytes. Not committed (`../README.md` section 3 tells how to build it again) |
| Reproducibility | Second build with an empty GOCACHE: sha256 `c6403c02a110ffd6fe6d31a3c89cd395ac457b5d62e60e2e611b8ab9a8dd911e` |
| Kraken / EthLib / Lean | `6064eec` / `8621856` / `nightly-2026-09-21` |

Go 1.26.10 is a new experiment baseline. The 55 theorems for the Go 1.26.3 ELF `9c850c97…c501` do not transfer to this machine code.

## 3. Method

1. `gen/prysm-gen.sh` runs the generator in a temporary Prysm tree. The flags are the same as in Prysm `build/gen/ssz.go`.
2. The same script uses `gen/inventory-tool` to extract the IR of the front end of the generator itself (`config`, `TypeDefs`, `ParseTypeDef`, delegate interface set) as JSON.
3. `gen/type_inventory.py reduce` cuts the parts below delegated fields and makes `ir/ir-{mainnet,minimal}.json`.
4. `gen/type_inventory.py build` writes the sets, kinds, depths and scopes to `inventory.json`.
5. `gen/prysm-elf.sh` builds the ELF two times and extracts objdump and nm. `gen/keepalive.py` makes `main`.
6. `gen/mnemonics.py` counts the instructions, mnemonics and call kinds for each function (`go1.26.10/functions.json`).
7. `link/convert_objdump.py --norm` (read only) makes the `.S` files, and `gen/kraken-parser/ParserRun.lean` runs the Kraken runtime parser (`go1.26.10/kparse.json`).

- `fork_configs`: ['proto/prysm/v1alpha1/phase0.yaml', 'proto/prysm/v1alpha1/altair.yaml', 'proto/prysm/v1alpha1/bellatrix.yaml', 'proto/prysm/v1alpha1/capella.yaml', 'proto/prysm/v1alpha1/deneb.yaml', 'proto/prysm/v1alpha1/electra.yaml', 'proto/prysm/v1alpha1/fulu.yaml']
- `set_A`: every type configured in a fork config (phase0..fulu)
- `set_B`: named types reached from the fulu.yaml roots through fields; a delegated field is followed into its type's own IR
- `set_I`: inventory set: generated types in the closure of A (A is closed under fields only through I; B is a subset because the fulu.yaml roots are in A)
- `fulu_reachable`: strict sense: B. The classification covers I and marks in_B per type
- `hand_written_delegate`: a named type in the field closure of A with SSZ methods that no config generates (its methods are hand-written Go)
- `inline_depth`: list/vector levels the type's own code walks; bytesN and delegated fields count 0
- `scope_in`: first-pass rule: not excluded, i.e. not progressive, no union, inline depth <= 1, and every field one of: uint8..64, bool, bytesN, bitvector, bitlist (ValidateBitlist contract), vector of a uint/bool, of bytesN or of a delegated type, list[byte], list[uint64] (a list of another uint is out), list of bytesN or of a delegated container, a delegated container or a delegated hand-written type. Depth is the inline depth (delegated fields are not followed). 'in' is neither provability nor a match with a hand proof pattern (see SCOPE-P6)
- `preset`: mainnet is primary; minimal differences are listed separately

How we decide "does Kraken accept it":

- Mnemonic level: the 186 branch strings of `parseInstr` in `Kraken/X64/Parser/Basic.lean` of the fixed Kraken, and `j`/`set`/`cmov` + 30 `parseCondCode?` condition codes. The 10 `convert_objdump.py` NORM forms count as `nop`.
- Real parser level: we ran `Kraken.X64.Parser.parse`, which `include_x64_code` uses, on each file (log copy `go1.26.10/kparse-log.txt`). This is the verdict criterion.
- We did not examine the semantics level (`kstep` and theorems). This table is a classification, not a proof.

## 4. Numbers

| Item | Value |
| --- | --- |
| `configs_parsed` | 14 |
| `set_A` | 124 |
| `set_B` | 50 |
| `set_B_generated` | 45 |
| `set_B_hand_written` | 5 |
| `A_minus_B` | 86 |
| `B_generated_minus_A` | 7 |
| `set_I` | 135 |
| `I_minus_A` | 11 |
| `I_hand_written` | 5 |
| `roots` | 12 |
| `B_scope_in` | 44 |
| `B_scope_out` | 1 |
| `scope_in` | 132 |
| `scope_out` | 3 |
| `out_reason_types` | {"deep nesting": 3} |
| `out_primary_reason` | {"deep nesting": 3} |
| `kind` | {"fixed container": 46, "variable container": 89} |
| `go_file_kind` | {"native": 12, "protobuf": 123} |
| `field_shape` | {"bitlist": 6, "bitvector": 10, "bool": 1, "bytesN": 195, "delegated container (fixed)": 120, "delegated container (variable)": 78, "delegated overlay CommitteeIndex": 2, "delegated overlay Epoch": 15, "delegated overlay Gwei": 6, "delegated overlay Slot": 39, "delegated overlay ValidatorIndex": 29, "list[byte]": 18, "list[bytesN]": 31, "list[container]": 89, "list[list[byte]]": 3, "list[uint64]": 16, "uint64": 65, "vector[ValidatorIndex]": 1, "vector[bytesN]": 46, "vector[uint64]": 7} |
| `types_calling_hand_written` | 52 |
| `scope_in_calling_hand_written` | 52 |
| `minimal_differs` | 41 |
| `minimal_scope_changes` | 0 |
| `not_fulu_types` | 91 |
| `functions_dumped` | 641 |
| `generated_functions_inventory` | 405 |
| `generated_functions_not_inventory` | 210 |
| `hand_written_functions` | 24 |
| `missing_generated` | 0 |
| `generated_instructions` | 116889 |
| `generated_functions_all_supported` | 405 |
| `hand_written_instructions` | 792 |
| `all_dumped_unsupported` | {"bsr": 1} |
| `functions_per_call_kind` | {"ValidateBitlist": 10, "ValidateBitvector": 14, "convT64": 36, "fmt": 217, "generated method": 224, "growslice": 150, "hand-written primitives method": 52, "makeslice": 124, "memmove": 246, "morestack_noctxt": 339, "moveSlice* (stack-backed result to heap)": 8, "newobject": 286, "panic*": 54, "write barrier": 292} |
| `kparse` | {"generated (not inventory): ERR": 5, "generated (not inventory): OK": 205, "hand-written: OK": 24, "inventory: ERR": 13, "inventory: OK": 392, "runtime/ssz: ERR": 1, "runtime/ssz: OK": 1} |
| `kparse_riz_diag` | OK 18, ERR 0 |

Parser ERR list:

- `github.com/OffchainLabs/methodical-ssz/ssz.ValidateBitlist` (runtime/ssz): line 22: unsupported instruction: bsr
- `proto/engine/v1.(*ExecutionPayloadDenebAndBlobsBundle).MarshalSSZTo` (generated (not inventory)): line 61: unknown register: riz
- `proto/engine/v1.(*ExecutionPayloadDenebAndBlobsBundleV2).MarshalSSZTo` (generated (not inventory)): line 61: unknown register: riz
- `proto/prysm/v1alpha1.(*BeaconBlockBodyAltair).MarshalSSZTo` (inventory): line 314: unknown register: riz
- `proto/prysm/v1alpha1.(*BeaconBlockBodyBellatrix).MarshalSSZTo` (inventory): line 313: unknown register: riz
- `proto/prysm/v1alpha1.(*BlindedBeaconBlockBodyBellatrix).MarshalSSZTo` (inventory): line 313: unknown register: riz
- `proto/prysm/v1alpha1.(*BeaconBlockBodyCapella).MarshalSSZTo` (inventory): line 313: unknown register: riz
- `proto/prysm/v1alpha1.(*BlindedBeaconBlockBodyCapella).MarshalSSZTo` (inventory): line 313: unknown register: riz
- `proto/prysm/v1alpha1.(*BeaconBlockBodyDeneb).MarshalSSZTo` (inventory): line 313: unknown register: riz
- `proto/prysm/v1alpha1.(*BlindedBeaconBlockBodyDeneb).MarshalSSZTo` (inventory): line 313: unknown register: riz
- `proto/prysm/v1alpha1.(*BeaconBlockBodyElectra).MarshalSSZTo` (inventory): line 313: unknown register: riz
- `proto/prysm/v1alpha1.(*BeaconStateElectra).MarshalSSZTo` (inventory): line 1525: unknown register: riz
- `proto/prysm/v1alpha1.(*BlindedBeaconBlockBodyElectra).MarshalSSZTo` (inventory): line 313: unknown register: riz
- `proto/prysm/v1alpha1.(*BeaconStateFulu).MarshalSSZTo` (inventory): line 1523: unknown register: riz
- `proto/prysm/v1alpha1.(*BeaconBlockBodyGloas).MarshalSSZTo` (generated (not inventory)): line 313: unknown register: riz
- `proto/prysm/v1alpha1.(*BuilderConfig).UnmarshalSSZ` (generated (not inventory)): line 68: unknown register: riz
- `proto/prysm/v1alpha1.(*BeaconBlockBodyHeze).MarshalSSZTo` (generated (not inventory)): line 313: unknown register: riz
- `proto/prysm/v1alpha1.(*BeaconBlockBody).MarshalSSZTo` (inventory): line 321: unknown register: riz
- `proto/prysm/v1alpha1.(*BeaconState).MarshalSSZTo` (inventory): line 1417: unknown register: riz

`%riz` is the spelling that GNU objdump uses for a SIB byte without an index (when `%r12` is the base register). The address is the same as `(%r12)`.
It is not a generator defect. It is a gap in the converter or in the Kraken parser (`../FINDINGS.md`, entry "Kraken cannot parse some operand and instruction forms").

Mnemonic frequency of the generated functions (I only):

`add` 4054, `and` 267, `callq` 8540, `cmovne` 1, `cmp` 3268, `cmpb` 1, `cmpl` 1624, `cmpq` 914, `data16 nop` 599, `imul` 195, `inc` 306, `ja` 149, `jae` 1032, `jb` 724, `jbe` 388, `je` 2103, `jg` 211, `jge` 426, `jl` 41, `jle` 66, `jmp` 1432, `jmpq` 1282, `jne` 3355, `lea` 10288, `mov` 54433, `movb` 4, `movl` 89, `movq` 2502, `movups` 1420, `movzbl` 17, `mul` 76, `neg` 252, `nop` 3014, `nopl` 1446, `nopw` 270, `or` 1, `pop` 2239, `push` 339, `retq` 2305, `sar` 267, `shl` 379, `shr` 139, `sub` 796, `test` 2145, `xor` 3490

## 5. Set differences

- 7 generated types in B are not in A: `proto/engine/v1.ConsolidationRequest`, `proto/engine/v1.DepositRequest`, `proto/engine/v1.ExecutionPayloadDeneb`, `proto/engine/v1.ExecutionPayloadHeaderDeneb`, `proto/engine/v1.ExecutionRequests`, `proto/engine/v1.Withdrawal`, `proto/engine/v1.WithdrawalRequest`.
- 11 types in I are not in A: `proto/engine/v1.ConsolidationRequest`, `proto/engine/v1.DepositRequest`, `proto/engine/v1.ExecutionPayload`, `proto/engine/v1.ExecutionPayloadCapella`, `proto/engine/v1.ExecutionPayloadDeneb`, `proto/engine/v1.ExecutionPayloadHeader`, `proto/engine/v1.ExecutionPayloadHeaderCapella`, `proto/engine/v1.ExecutionPayloadHeaderDeneb`, `proto/engine/v1.ExecutionRequests`, `proto/engine/v1.Withdrawal`, `proto/engine/v1.WithdrawalRequest`.
- 86 types in A are not in B. The names are in `inventory.json` `sets.A_minus_B`.

Configs that are not Fulu:

| Config | Type count | Reason |
| --- | --- | --- |
| `proto/prysm/v1alpha1/gloas.yaml` | 41 | later fork (after Fulu) |
| `proto/prysm/v1alpha1/heze.yaml` | 9 | later fork (after Fulu) |
| `proto/prysm/v1alpha1/non-core.yaml` | 13 | not a fork config and no type reached from the Fulu roots |
| `proto/eth/v1/gateway.yaml` | 20 | not a fork config and no type reached from the Fulu roots |
| `proto/ssz_query/response.yaml` | 3 | not a fork config and no type reached from the Fulu roots |
| `proto/ssz_query/testing/test_containers.yaml` | 5 | not a fork config and no type reached from the Fulu roots |

Hand-written delegate targets (SSZ methods that the generator does not make):

| Type | Count of calling types |
| --- | --- |
| `consensus-types/primitives.CommitteeIndex` | 2 |
| `consensus-types/primitives.Epoch` | 10 |
| `consensus-types/primitives.Gwei` | 2 |
| `consensus-types/primitives.Slot` | 38 |
| `consensus-types/primitives.ValidatorIndex` | 28 |

The types with a different IR in minimal are in `inventory.json` `minimal_differences`. The scope classification changes are as in the numbers above.

## 6. Type table

Columns: config, B (Fulu-reachable), kind, field count, depth, scope (reasons), delegate calls (generated/hand), instruction count M/S/U (MarshalSSZTo/SizeSSZ/UnmarshalSSZ), count of mnemonic kinds, mnemonics that Kraken does not support, parser (M/S/U), runtime calls (union of the three functions).
Call abbreviations: VBl=ValidateBitlist, VBv=ValidateBitvector, cT64=convT64, fmt=fmt, gen=generated method, grow=growslice, hand=hand-written primitives method, mks=makeslice, mm=memmove, stk=morestack_noctxt, new=newobject, pan=panic*, wb=write barrier, mvS=moveSlice* (stack-backed result to heap), rt?=runtime other, oth?=other, ind=indirect.

| Type | Config | B | Kind | Fields | Depth | Scope | Delegates | M/S/U | Mnemonics | Not supported | Parser | Calls |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `ConsolidationRequest` | engine | B | fixed container | 3 | 0 | in | 0/0 | 139/2/127 | 22 | - | OK/OK/OK | grow mks mm mvS stk wb |
| `DepositRequest` | engine | B | fixed container | 5 | 0 | in | 0/0 | 160/2/133 | 24 | - | OK/OK/OK | grow mks mm stk wb |
| `ExecutionPayload` | engine |  | variable container | 14 | 2 | out (deep nesting) | 0/0 | 520/17/714 | 38 | - | OK/OK/OK | cT64 fmt grow mks mm new pan stk wb |
| `ExecutionPayloadCapella` | engine |  | variable container | 15 | 2 | out (deep nesting) | 1/0 | 603/19/919 | 40 | - | OK/OK/OK | cT64 fmt gen grow mks mm new pan stk wb |
| `ExecutionPayloadDeneb` | engine | B | variable container | 17 | 2 | out (deep nesting) | 1/0 | 628/19/924 | 40 | - | OK/OK/OK | cT64 fmt gen grow mks mm new pan stk wb |
| `ExecutionPayloadHeader` | engine |  | variable container | 14 | 1 | in | 0/0 | 432/3/395 | 29 | - | OK/OK/OK | grow mks mm stk wb |
| `ExecutionPayloadHeaderCapella` | engine |  | variable container | 15 | 1 | in | 0/0 | 465/3/428 | 29 | - | OK/OK/OK | grow mks mm stk wb |
| `ExecutionPayloadHeaderDeneb` | engine | B | variable container | 17 | 1 | in | 0/0 | 491/3/433 | 29 | - | OK/OK/OK | grow mks mm stk wb |
| `ExecutionRequests` | engine | B | variable container | 3 | 1 | in | 3/0 | 617/11/677 | 40 | - | OK/OK/OK | cT64 fmt gen grow mks mm new pan stk wb |
| `Withdrawal` | engine | B | fixed container | 4 | 0 | in | 0/1 | 117/2/105 | 25 | - | OK/OK/OK | fmt grow hand mks mm new stk wb |
| `WithdrawalRequest` | engine | B | fixed container | 3 | 0 | in | 0/0 | 107/2/98 | 22 | - | OK/OK/OK | grow mks mm stk wb |
| `BeaconBlockAltair` | altair |  | variable container | 5 | 0 | in | 1/2 | 215/32/228 | 30 | - | OK/OK/OK | fmt gen grow hand mks mm new stk wb |
| `BeaconBlockBodyAltair` | altair |  | variable container | 9 | 1 | in | 7/0 | 979/99/1554 | 40 | - | ERR(riz)/OK/OK | cT64 fmt gen grow mks mm new pan stk wb |
| `BeaconStateAltair` | altair |  | variable container | 24 | 1 | in | 6/1 | 1720/18/1746 | 40 | - | OK/OK/OK | VBv cT64 fmt gen grow hand mks mm new pan stk wb |
| `ContributionAndProof` | altair |  | fixed container | 3 | 0 | in | 1/1 | 142/2/141 | 24 | - | OK/OK/OK | fmt gen grow hand mks mm new stk wb |
| `LightClientBootstrapAltair` | altair |  | fixed container | 3 | 1 | in | 2/0 | 287/2/187 | 29 | - | OK/OK/OK | fmt gen grow mks mm new pan stk wb |
| `LightClientFinalityUpdateAltair` | altair |  | fixed container | 5 | 1 | in | 2/1 | 344/2/298 | 28 | - | OK/OK/OK | fmt gen grow hand mks mm new pan stk wb |
| `LightClientHeaderAltair` | altair |  | fixed container | 1 | 0 | in | 1/0 | 77/2/73 | 24 | - | OK/OK/OK | fmt gen new stk wb |
| `LightClientOptimisticUpdateAltair` | altair |  | fixed container | 3 | 0 | in | 2/1 | 227/2/191 | 26 | - | OK/OK/OK | fmt gen grow hand mks mm new stk wb |
| `LightClientUpdateAltair` | altair |  | fixed container | 7 | 1 | in | 3/1 | 543/2/405 | 28 | - | OK/OK/OK | fmt gen grow hand mks mm new pan stk wb |
| `SignedBeaconBlockAltair` | altair |  | variable container | 2 | 0 | in | 1/0 | 153/48/128 | 30 | - | OK/OK/OK | fmt gen grow mks mm new stk wb |
| `SignedContributionAndProof` | altair |  | fixed container | 2 | 0 | in | 1/0 | 115/2/111 | 25 | - | OK/OK/OK | fmt gen grow mks mm new stk wb |
| `SyncAggregate` | altair | B | fixed container | 2 | 0 | in | 0/0 | 105/2/96 | 23 | - | OK/OK/OK | grow mks mm mvS stk wb |
| `SyncAggregatorSelectionData` | altair |  | fixed container | 2 | 0 | in | 0/1 | 67/2/66 | 21 | - | OK/OK/OK | fmt grow hand new stk |
| `SyncCommittee` | altair | B | fixed container | 2 | 1 | in | 0/0 | 133/2/124 | 26 | - | OK/OK/OK | grow mks mm mvS pan stk wb |
| `SyncCommitteeContribution` | altair |  | fixed container | 5 | 0 | in | 0/1 | 162/2/161 | 26 | - | OK/OK/OK | fmt grow hand mks mm new stk wb |
| `SyncCommitteeMessage` | altair |  | fixed container | 4 | 0 | in | 0/2 | 142/2/163 | 25 | - | OK/OK/OK | fmt grow hand mks mm new stk wb |
| `BeaconBlockBellatrix` | bellatrix |  | variable container | 5 | 0 | in | 1/2 | 215/32/228 | 30 | - | OK/OK/OK | fmt gen grow hand mks mm new stk wb |
| `BeaconBlockBodyBellatrix` | bellatrix |  | variable container | 10 | 1 | in | 8/0 | 1055/134/1629 | 40 | - | ERR(riz)/OK/OK | cT64 fmt gen grow mks mm new pan stk wb |
| `BeaconStateBellatrix` | bellatrix |  | variable container | 25 | 1 | in | 7/1 | 1818/51/1772 | 39 | - | OK/OK/OK | VBv cT64 fmt gen grow hand mks mm new pan stk wb |
| `BlindedBeaconBlockBellatrix` | bellatrix |  | variable container | 5 | 0 | in | 1/2 | 215/32/228 | 30 | - | OK/OK/OK | fmt gen grow hand mks mm new stk wb |
| `BlindedBeaconBlockBodyBellatrix` | bellatrix |  | variable container | 10 | 1 | in | 8/0 | 1049/119/1629 | 40 | - | ERR(riz)/OK/OK | cT64 fmt gen grow mks mm new pan stk wb |
| `SignedBeaconBlockBellatrix` | bellatrix |  | variable container | 2 | 0 | in | 1/0 | 153/48/128 | 30 | - | OK/OK/OK | fmt gen grow mks mm new stk wb |
| `SignedBlindedBeaconBlockBellatrix` | bellatrix |  | variable container | 2 | 0 | in | 1/0 | 153/48/128 | 30 | - | OK/OK/OK | fmt gen grow mks mm new stk wb |
| `BLSToExecutionChange` | capella | B | fixed container | 3 | 0 | in | 0/1 | 120/2/130 | 26 | - | OK/OK/OK | fmt grow hand mks mm new stk wb |
| `BeaconBlockBodyCapella` | capella |  | variable container | 11 | 1 | in | 9/0 | 1139/140/1832 | 40 | - | ERR(riz)/OK/OK | cT64 fmt gen grow mks mm new pan stk wb |
| `BeaconBlockCapella` | capella |  | variable container | 5 | 0 | in | 1/2 | 215/32/228 | 30 | - | OK/OK/OK | fmt gen grow hand mks mm new stk wb |
| `BeaconStateCapella` | capella |  | variable container | 28 | 1 | in | 8/2 | 2018/53/2066 | 39 | - | OK/OK/OK | VBv cT64 fmt gen grow hand mks mm new pan stk wb |
| `BlindedBeaconBlockBodyCapella` | capella |  | variable container | 11 | 1 | in | 9/0 | 1129/123/1832 | 40 | - | ERR(riz)/OK/OK | cT64 fmt gen grow mks mm new pan stk wb |
| `BlindedBeaconBlockCapella` | capella |  | variable container | 5 | 0 | in | 1/2 | 215/32/228 | 30 | - | OK/OK/OK | fmt gen grow hand mks mm new stk wb |
| `BuilderBidCapella` | capella |  | variable container | 3 | 0 | in | 1/0 | 168/32/161 | 30 | - | OK/OK/OK | fmt gen grow mks mm new stk wb |
| `HistoricalSummary` | capella | B | fixed container | 2 | 0 | in | 0/0 | 105/2/94 | 22 | - | OK/OK/OK | grow mks mm mvS stk wb |
| `LightClientBootstrapCapella` | capella |  | variable container | 3 | 1 | in | 2/0 | 327/48/209 | 33 | - | OK/OK/OK | fmt gen grow mks mm new pan stk wb |
| `LightClientFinalityUpdateCapella` | capella |  | variable container | 5 | 1 | in | 2/1 | 432/88/343 | 33 | - | OK/OK/OK | fmt gen grow hand mks mm new pan stk wb |
| `LightClientHeaderCapella` | capella |  | variable container | 3 | 1 | in | 2/0 | 207/32/208 | 33 | - | OK/OK/OK | fmt gen grow mks mm new pan stk wb |
| `LightClientOptimisticUpdateCapella` | capella |  | variable container | 3 | 0 | in | 2/1 | 268/48/210 | 30 | - | OK/OK/OK | fmt gen grow hand mks mm new stk wb |
| `LightClientUpdateCapella` | capella |  | variable container | 7 | 1 | in | 3/1 | 641/88/451 | 33 | - | OK/OK/OK | fmt gen grow hand mks mm new pan stk wb |
| `SignedBLSToExecutionChange` | capella | B | fixed container | 2 | 0 | in | 1/0 | 115/2/111 | 25 | - | OK/OK/OK | fmt gen grow mks mm new stk wb |
| `SignedBeaconBlockCapella` | capella |  | variable container | 2 | 0 | in | 1/0 | 153/48/128 | 30 | - | OK/OK/OK | fmt gen grow mks mm new stk wb |
| `SignedBlindedBeaconBlockCapella` | capella |  | variable container | 2 | 0 | in | 1/0 | 153/48/128 | 30 | - | OK/OK/OK | fmt gen grow mks mm new stk wb |
| `SignedBuilderBidCapella` | capella |  | variable container | 2 | 0 | in | 1/0 | 158/48/128 | 30 | - | OK/OK/OK | fmt gen grow mks mm new stk wb |
| `BeaconBlockBodyDeneb` | deneb |  | variable container | 12 | 1 | in | 9/0 | 1227/144/2014 | 40 | - | ERR(riz)/OK/OK | cT64 fmt gen grow mks mm new pan stk wb |
| `BeaconBlockContentsDeneb` | deneb |  | variable container | 3 | 1 | in | 1/0 | 279/57/444 | 37 | - | OK/OK/OK | cT64 fmt gen grow mks mm new pan stk wb |
| `BeaconBlockDeneb` | deneb |  | variable container | 5 | 0 | in | 1/2 | 215/32/228 | 30 | - | OK/OK/OK | fmt gen grow hand mks mm new stk wb |
| `BeaconStateDeneb` | deneb |  | variable container | 28 | 1 | in | 8/2 | 2018/53/2066 | 39 | - | OK/OK/OK | VBv cT64 fmt gen grow hand mks mm new pan stk wb |
| `BlindedBeaconBlockBodyDeneb` | deneb |  | variable container | 12 | 1 | in | 9/0 | 1218/126/2014 | 40 | - | ERR(riz)/OK/OK | cT64 fmt gen grow mks mm new pan stk wb |
| `BlindedBeaconBlockDeneb` | deneb |  | variable container | 5 | 0 | in | 1/2 | 215/32/228 | 30 | - | OK/OK/OK | fmt gen grow hand mks mm new stk wb |
| `BlobIdentifier` | deneb |  | fixed container | 2 | 0 | in | 0/0 | 72/2/65 | 21 | - | OK/OK/OK | grow mks mm stk wb |
| `BlobSidecar` | deneb |  | fixed container | 6 | 1 | in | 1/0 | 255/2/243 | 29 | - | OK/OK/OK | fmt gen grow mks mm new pan stk wb |
| `BlobSidecars` | deneb |  | variable container | 1 | 1 | in | 1/0 | 110/4/229 | 36 | - | OK/OK/OK | cT64 fmt gen grow mks new pan stk wb |
| `BuilderBidDeneb` | deneb |  | variable container | 4 | 1 | in | 1/0 | 247/36/341 | 36 | - | OK/OK/OK | cT64 fmt gen grow mks mm new pan stk wb |
| `LightClientBootstrapDeneb` | deneb |  | variable container | 3 | 1 | in | 2/0 | 327/48/209 | 33 | - | OK/OK/OK | fmt gen grow mks mm new pan stk wb |
| `LightClientFinalityUpdateDeneb` | deneb |  | variable container | 5 | 1 | in | 2/1 | 432/88/343 | 33 | - | OK/OK/OK | fmt gen grow hand mks mm new pan stk wb |
| `LightClientHeaderDeneb` | deneb |  | variable container | 3 | 1 | in | 2/0 | 207/32/208 | 33 | - | OK/OK/OK | fmt gen grow mks mm new pan stk wb |
| `LightClientOptimisticUpdateDeneb` | deneb |  | variable container | 3 | 0 | in | 2/1 | 268/48/210 | 30 | - | OK/OK/OK | fmt gen grow hand mks mm new stk wb |
| `LightClientUpdateDeneb` | deneb |  | variable container | 7 | 1 | in | 3/1 | 641/88/451 | 33 | - | OK/OK/OK | fmt gen grow hand mks mm new pan stk wb |
| `SignedBeaconBlockContentsDeneb` | deneb |  | variable container | 3 | 1 | in | 1/0 | 259/39/444 | 37 | - | OK/OK/OK | cT64 fmt gen grow mks mm new pan stk wb |
| `SignedBeaconBlockDeneb` | deneb |  | variable container | 2 | 0 | in | 1/0 | 153/48/128 | 30 | - | OK/OK/OK | fmt gen grow mks mm new stk wb |
| `SignedBlindedBeaconBlockDeneb` | deneb |  | variable container | 2 | 0 | in | 1/0 | 153/48/128 | 30 | - | OK/OK/OK | fmt gen grow mks mm new stk wb |
| `SignedBuilderBidDeneb` | deneb |  | variable container | 2 | 0 | in | 1/0 | 158/51/128 | 31 | - | OK/OK/OK | fmt gen grow mks mm new stk wb |
| `AggregateAttestationAndProofElectra` | electra |  | variable container | 3 | 0 | in | 1/1 | 159/32/164 | 29 | - | OK/OK/OK | fmt gen grow hand mks mm new stk wb |
| `AttestationElectra` | electra | B | variable container | 4 | 1 | in | 1/0 | 234/3/224 | 30 | - | OK/OK/OK | VBl fmt gen grow mks mm new stk wb |
| `AttesterSlashingElectra` | electra | B | variable container | 2 | 0 | in | 1/0 | 177/52/160 | 31 | - | OK/OK/OK | fmt gen grow new stk wb |
| `BeaconBlockBodyElectra` | electra | B | variable container | 13 | 1 | in | 10/0 | 1313/172/2023 | 40 | - | ERR(riz)/OK/OK | cT64 fmt gen grow mks mm new pan stk wb |
| `BeaconBlockContentsElectra` | electra |  | variable container | 3 | 1 | in | 1/0 | 279/57/444 | 37 | - | OK/OK/OK | cT64 fmt gen grow mks mm new pan stk wb |
| `BeaconBlockElectra` | electra | B | variable container | 5 | 0 | in | 1/2 | 215/32/228 | 30 | - | OK/OK/OK | fmt gen grow hand mks mm new stk wb |
| `BeaconStateElectra` | electra |  | variable container | 37 | 1 | in | 11/4 | 2463/63/2806 | 40 | - | ERR(riz)/OK/OK | VBv cT64 fmt gen grow hand mks mm new pan stk wb |
| `BlindedBeaconBlockBodyElectra` | electra | B | variable container | 13 | 1 | in | 10/0 | 1304/154/2023 | 40 | - | ERR(riz)/OK/OK | cT64 fmt gen grow mks mm new pan stk wb |
| `BlindedBeaconBlockElectra` | electra |  | variable container | 5 | 0 | in | 1/2 | 215/32/228 | 30 | - | OK/OK/OK | fmt gen grow hand mks mm new stk wb |
| `BuilderBidElectra` | electra |  | variable container | 5 | 1 | in | 2/0 | 329/64/406 | 37 | - | OK/OK/OK | cT64 fmt gen grow mks mm new pan stk wb |
| `IndexedAttestationElectra` | electra | B | variable container | 3 | 1 | in | 1/0 | 173/4/253 | 36 | - | OK/OK/OK | cT64 fmt gen grow mks mm new pan stk wb |
| `LightClientBootstrapElectra` | electra |  | variable container | 3 | 1 | in | 2/0 | 327/48/209 | 33 | - | OK/OK/OK | fmt gen grow mks mm new pan stk wb |
| `LightClientFinalityUpdateElectra` | electra |  | variable container | 5 | 1 | in | 2/1 | 432/88/343 | 33 | - | OK/OK/OK | fmt gen grow hand mks mm new pan stk wb |
| `LightClientUpdateElectra` | electra |  | variable container | 7 | 1 | in | 3/1 | 641/88/451 | 33 | - | OK/OK/OK | fmt gen grow hand mks mm new pan stk wb |
| `PendingConsolidation` | electra | B | fixed container | 2 | 0 | in | 0/1 | 74/2/97 | 22 | - | OK/OK/OK | fmt grow hand new stk |
| `PendingDeposit` | electra | B | fixed container | 5 | 0 | in | 0/1 | 168/2/166 | 26 | - | OK/OK/OK | fmt grow hand mks mm new stk wb |
| `PendingPartialWithdrawal` | electra | B | fixed container | 3 | 0 | in | 0/2 | 93/2/99 | 21 | - | OK/OK/OK | fmt grow hand new stk |
| `SignedAggregateAttestationAndProofElectra` | electra |  | variable container | 2 | 0 | in | 1/0 | 158/49/128 | 30 | - | OK/OK/OK | fmt gen grow mks mm new stk wb |
| `SignedBeaconBlockContentsElectra` | electra |  | variable container | 3 | 1 | in | 1/0 | 259/39/444 | 37 | - | OK/OK/OK | cT64 fmt gen grow mks mm new pan stk wb |
| `SignedBeaconBlockElectra` | electra |  | variable container | 2 | 0 | in | 1/0 | 153/48/128 | 30 | - | OK/OK/OK | fmt gen grow mks mm new stk wb |
| `SignedBlindedBeaconBlockElectra` | electra |  | variable container | 2 | 0 | in | 1/0 | 153/48/128 | 30 | - | OK/OK/OK | fmt gen grow mks mm new stk wb |
| `SignedBuilderBidElectra` | electra |  | variable container | 2 | 0 | in | 1/0 | 138/32/128 | 29 | - | OK/OK/OK | fmt gen grow mks mm new stk wb |
| `SingleAttestation` | electra |  | fixed container | 4 | 0 | in | 1/2 | 168/2/180 | 25 | - | OK/OK/OK | fmt gen grow hand mks mm new stk wb |
| `BeaconBlockContentsFulu` | fulu | B | variable container | 3 | 1 | in | 1/0 | 279/57/444 | 37 | - | OK/OK/OK | cT64 fmt gen grow mks mm new pan stk wb |
| `BeaconStateFulu` | fulu | B | variable container | 38 | 1 | in | 11/4 | 2540/63/2890 | 41 | - | ERR(riz)/OK/OK | VBv cT64 fmt gen grow hand mks mm new pan stk wb |
| `BlindedBeaconBlockFulu` | fulu | B | variable container | 5 | 0 | in | 1/2 | 215/32/228 | 30 | - | OK/OK/OK | fmt gen grow hand mks mm new stk wb |
| `DataColumnSidecar` | fulu | B | variable container | 6 | 1 | in | 1/0 | 400/12/667 | 37 | - | OK/OK/OK | cT64 fmt gen grow mks mm new pan stk wb |
| `DataColumnsByRootIdentifier` | fulu | B | variable container | 2 | 1 | in | 0/0 | 107/4/208 | 35 | - | OK/OK/OK | cT64 fmt grow mks mm new pan stk wb |
| `PartialDataColumnHeader` | fulu | B | variable container | 3 | 1 | in | 1/0 | 214/5/316 | 37 | - | OK/OK/OK | cT64 fmt gen grow mks mm new pan stk wb |
| `PartialDataColumnPartsMetadata` | fulu | B | variable container | 2 | 1 | in | 0/0 | 195/4/211 | 29 | - | OK/OK/OK | VBl fmt grow mm new stk wb |
| `PartialDataColumnSidecar` | fulu | B | variable container | 4 | 1 | in | 1/0 | 422/23/771 | 39 | - | OK/OK/OK | VBl cT64 fmt gen grow mks mm new pan stk wb |
| `SignedBeaconBlockContentsFulu` | fulu | B | variable container | 3 | 1 | in | 1/0 | 259/39/444 | 37 | - | OK/OK/OK | cT64 fmt gen grow mks mm new pan stk wb |
| `SignedBeaconBlockFulu` | fulu | B | variable container | 2 | 0 | in | 1/0 | 153/48/128 | 30 | - | OK/OK/OK | fmt gen grow mks mm new stk wb |
| `SignedBlindedBeaconBlockFulu` | fulu | B | variable container | 2 | 0 | in | 1/0 | 153/48/128 | 30 | - | OK/OK/OK | fmt gen grow mks mm new stk wb |
| `StatusV2` | fulu | B | fixed container | 6 | 0 | in | 0/2 | 190/2/227 | 26 | - | OK/OK/OK | fmt grow hand mks mm new stk wb |
| `AggregateAttestationAndProof` | phase0 |  | variable container | 3 | 0 | in | 1/1 | 159/32/164 | 29 | - | OK/OK/OK | fmt gen grow hand mks mm new stk wb |
| `Attestation` | phase0 |  | variable container | 3 | 1 | in | 1/0 | 197/3/198 | 30 | - | OK/OK/OK | VBl fmt gen grow mks mm new stk wb |
| `AttestationData` | phase0 | B | fixed container | 5 | 0 | in | 1/2 | 218/2/220 | 25 | - | OK/OK/OK | fmt gen grow hand mks mm new stk wb |
| `AttesterSlashing` | phase0 |  | variable container | 2 | 0 | in | 1/0 | 177/52/160 | 31 | - | OK/OK/OK | fmt gen grow new stk wb |
| `BeaconBlock` | phase0 |  | variable container | 5 | 0 | in | 1/2 | 215/32/228 | 30 | - | OK/OK/OK | fmt gen grow hand mks mm new stk wb |
| `BeaconBlockBody` | phase0 |  | variable container | 8 | 1 | in | 6/0 | 834/99/1505 | 40 | - | ERR(riz)/OK/OK | cT64 fmt gen grow mks mm new pan stk wb |
| `BeaconBlockHeader` | phase0 | B | fixed container | 5 | 0 | in | 0/2 | 182/2/198 | 26 | - | OK/OK/OK | fmt grow hand mks mm new stk wb |
| `BeaconState` | phase0 |  | variable container | 21 | 1 | in | 6/1 | 1491/36/2099 | 41 | - | ERR(riz)/OK/OK | VBv cT64 fmt gen grow hand mks mm new pan stk wb |
| `Checkpoint` | phase0 | B | fixed container | 2 | 0 | in | 0/1 | 85/2/98 | 24 | - | OK/OK/OK | fmt grow hand mks mm new stk wb |
| `Deposit` | phase0 | B | fixed container | 2 | 1 | in | 1/0 | 257/2/140 | 29 | - | OK/OK/OK | fmt gen grow mks mm new pan stk wb |
| `DepositMessage` | phase0 |  | fixed container | 3 | 0 | in | 0/0 | 107/2/99 | 23 | - | OK/OK/OK | grow mks mm stk wb |
| `Deposit_Data` | phase0 | B | fixed container | 4 | 0 | in | 0/0 | 144/2/130 | 23 | - | OK/OK/OK | grow mks mm stk wb |
| `ENRForkID` | phase0 |  | fixed container | 3 | 0 | in | 0/1 | 109/2/116 | 23 | - | OK/OK/OK | fmt grow hand mks new stk wb |
| `Eth1Data` | phase0 | B | fixed container | 3 | 0 | in | 0/0 | 110/2/98 | 23 | - | OK/OK/OK | grow mks mm stk wb |
| `Fork` | phase0 | B | fixed container | 3 | 0 | in | 0/1 | 109/2/116 | 23 | - | OK/OK/OK | fmt grow hand mks new stk wb |
| `ForkData` | phase0 |  | fixed container | 2 | 0 | in | 0/0 | 102/2/92 | 24 | - | OK/OK/OK | grow mks mm mvS stk wb |
| `HistoricalBatch` | phase0 |  | fixed container | 2 | 1 | in | 0/0 | 157/2/164 | 27 | - | OK/OK/OK | grow mks mm mvS pan stk wb |
| `IndexedAttestation` | phase0 |  | variable container | 3 | 1 | in | 1/0 | 173/4/253 | 36 | - | OK/OK/OK | cT64 fmt gen grow mks mm new pan stk wb |
| `PendingAttestation` | phase0 |  | variable container | 4 | 1 | in | 1/2 | 210/3/233 | 30 | - | OK/OK/OK | VBl fmt gen grow hand mm new stk wb |
| `PowBlock` | phase0 |  | fixed container | 3 | 0 | in | 0/0 | 140/2/128 | 23 | - | OK/OK/OK | grow mks mm mvS stk wb |
| `ProposerSlashing` | phase0 | B | fixed container | 2 | 0 | in | 1/0 | 136/2/120 | 24 | - | OK/OK/OK | fmt gen new stk wb |
| `SignedAggregateAttestationAndProof` | phase0 |  | variable container | 2 | 0 | in | 1/0 | 158/49/128 | 30 | - | OK/OK/OK | fmt gen grow mks mm new stk wb |
| `SignedBeaconBlock` | phase0 |  | variable container | 2 | 0 | in | 1/0 | 153/48/128 | 30 | - | OK/OK/OK | fmt gen grow mks mm new stk wb |
| `SignedBeaconBlockHeader` | phase0 | B | fixed container | 2 | 0 | in | 1/0 | 115/2/111 | 25 | - | OK/OK/OK | fmt gen grow mks mm new stk wb |
| `SignedVoluntaryExit` | phase0 | B | fixed container | 2 | 0 | in | 1/0 | 115/2/109 | 25 | - | OK/OK/OK | fmt gen grow mks mm new stk wb |
| `SigningData` | phase0 |  | fixed container | 2 | 0 | in | 0/0 | 106/2/95 | 23 | - | OK/OK/OK | grow mks mm mvS stk wb |
| `Status` | phase0 |  | fixed container | 5 | 0 | in | 0/2 | 172/2/192 | 26 | - | OK/OK/OK | fmt grow hand mks mm new stk wb |
| `Validator` | phase0 | B | fixed container | 8 | 0 | in | 0/1 | 209/2/249 | 31 | - | OK/OK/OK | fmt grow hand mks mm new stk wb |
| `ValidatorBalance` | phase0 |  | fixed container | 2 | 0 | in | 0/1 | 67/2/66 | 21 | - | OK/OK/OK | fmt grow hand new stk |
| `VoluntaryExit` | phase0 | B | fixed container | 2 | 0 | in | 0/2 | 74/2/97 | 22 | - | OK/OK/OK | fmt grow hand new stk |

Field shape frequency (all of I): bitlist 6, bitvector 10, bool 1, bytesN 195, delegated container (fixed) 120, delegated container (variable) 78, delegated overlay CommitteeIndex 2, delegated overlay Epoch 15, delegated overlay Gwei 6, delegated overlay Slot 39, delegated overlay ValidatorIndex 29, list[byte] 18, list[bytesN] 31, list[container] 89, list[list[byte]] 3, list[uint64] 16, uint64 65, vector[ValidatorIndex] 1, vector[bytesN] 46, vector[uint64] 7.
