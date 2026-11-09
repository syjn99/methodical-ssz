# TYPES: Prysm Fulu 타입 목록 (phase1c X1)

이 파일은 `fv/kraken/gen/types_md.py`가 저장된 JSON에서 만든다. 손으로 고치지 않는다.
수치는 모두 프로그램이 센다. 범위 분류는 1차(잠정)다. 증명이 아니다. 게이트 1c 통과가 아니다.

## 1. 요약

- 목록 집합 I: 생성 타입 135개. 설정 타입 A 124개, Fulu 도달 B 50개(생성 45, 손 작성 5).
- 범위 안 132개, 범위 밖 3개(잠정). 범위 밖 이유: deep nesting 3.
- B만 보면 범위 안 44개, 범위 밖 1개.
- 손 작성 위임 대상(`consensus-types/primitives`) 5개. 이것을 부르는 타입 52개.
- 생성 함수 405개(타입 × 3), 명령어 116889개, 함수당 최대 2890개.
- 니모닉 수준: 생성 함수 405/405개가 Kraken 런타임 파서가 받는 이름만 쓴다.
- 실제 파서 실행: 생성 함수 392개 OK, 13개 ERR. ERR는 모두 `%riz` 피연산자다(4절).
- `%riz` 때문에 실패한 파일 전부(18개, I 밖 함수 포함)를 `%riz`만 지운 진단 사본으로 다시 돌렸다. 18개 OK다. 진단일 뿐 변환 결과가 아니다.
- 커밋된 Prysm 파일과의 차이: 변경 블록 232개, 분류 232개, 미분류 0개.
- minimal 프리셋에서 IR이 다른 타입 41개. 범위 분류가 바뀐 타입 0개.

## 2. 고정 값

| 항목 | 값 |
| --- | --- |
| Prysm 소스 | `ab15ff70c72a568c870b2de662474685a95de294` (slice + `ssz-size`). 옛 핀 `5ac1d028f5`/`45394e5`은 대체됐다 |
| 생성기·런타임 | `698c2025a73a296b55b95744a8408f3b03b2546b` |
| 대상 컴파일 | `go version go1.26.10 linux/arm64`(호스트 바이너리)로 linux/amd64 교차 컴파일, `GOOS=linux GOARCH=amd64 GOAMD64=v1 CGO_ENABLED=0 go build -p 2 -tags purego -trimpath` |
| 호스트 | Linux aarch64 (생성은 arm64 네이티브. x86-64 하드웨어 없음) |
| ELF | sha256 `c6403c02a110ffd6fe6d31a3c89cd395ac457b5d62e60e2e611b8ab9a8dd911e`, 23486009 바이트. 커밋하지 않는다(`go1.26.10/MANIFEST.md`) |
| 재현성 | 빈 GOCACHE로 두 번째 빌드: sha256 `c6403c02a110ffd6fe6d31a3c89cd395ac457b5d62e60e2e611b8ab9a8dd911e` |
| Kraken / EthLib / Lean | `6064eec` / `8621856` / `nightly-2026-09-21` |

Go 1.26.10은 새 실험 기준선이다. Go 1.26.3 ELF `9c850c97…c501`의 정리 55개는 이 기계어에 옮겨지지 않는다.

## 3. 방법

1. `gen/prysm-gen.sh`가 임시 Prysm 트리에서 생성기를 돌린다. 플래그는 Prysm `build/gen/ssz.go`와 같다.
2. 같은 스크립트가 `gen/invtool`로 생성기 자체의 앞단(`config`, `TypeDefs`, `ParseTypeDef`, 위임 인터페이스 집합)의 IR을 JSON으로 뽑는다.
3. `gen/inventory.py reduce`가 위임 필드 아래를 잘라 `ir/ir-{mainnet,minimal}.json`을 만든다.
4. `gen/inventory.py build`가 집합, 종류, 깊이, 범위를 `inventory.json`에 쓴다.
5. `gen/prysm-elf.sh`가 ELF를 두 번 빌드하고 objdump·nm을 뽑는다. `gen/keepalive.py`가 `main`을 만든다.
6. `gen/mnemonics.py`가 함수마다 명령어 수, 니모닉, 호출 종류를 센다(`go1.26.10/functions.json`).
7. `link/conv.py --norm`(읽기만 함)으로 `.S`를 만들고 `gen/kparse/KParse.lean`이 Kraken 런타임 파서를 돌린다(`go1.26.10/kparse.json`).

- `fork_configs`: ['proto/prysm/v1alpha1/phase0.yaml', 'proto/prysm/v1alpha1/altair.yaml', 'proto/prysm/v1alpha1/bellatrix.yaml', 'proto/prysm/v1alpha1/capella.yaml', 'proto/prysm/v1alpha1/deneb.yaml', 'proto/prysm/v1alpha1/electra.yaml', 'proto/prysm/v1alpha1/fulu.yaml']
- `set_A`: every type configured in a fork config (phase0..fulu)
- `set_B`: named types reached from the fulu.yaml roots through fields; a delegated field is followed into its type's own IR
- `set_I`: inventory set: generated types in the closure of A (A is closed under fields only through I; B is a subset because the fulu.yaml roots are in A)
- `fulu_reachable`: strict sense: B. The classification covers I and marks in_B per type
- `hand_written_delegate`: a named type in the field closure of A with SSZ methods that no config generates (its methods are hand-written Go)
- `inline_depth`: list/vector levels the type's own code walks; bytesN and delegated fields count 0
- `scope_in`: not progressive, no union, inline depth <= 1, every field one of: uint8..64, bool, bytesN, bitvector, bitlist (ValidateBitlist contract), vector/list of a basic, bytesN or delegated container, list[byte], list[uint64], delegated container or delegated hand-written type
- `preset`: mainnet is primary; minimal differences are listed separately

"Kraken이 받는가"의 결정:

- 니모닉 수준: 고정 Kraken의 `Kraken/X64/Parser/Basic.lean` `parseInstr` 분기 문자열 186개와 `j`/`set`/`cmov` + `parseCondCode?` 조건 코드 30개. `conv.py` NORM 형식 10개는 `nop`으로 센다.
- 실제 파서 수준: `include_x64_rt`가 쓰는 `Kraken.X64.Parser.parse`를 파일마다 실행했다(로그 사본 `go1.26.10/kparse-log.txt`). 이것이 판정 기준이다.
- 의미론 수준(`kstep`·정리)은 보지 않았다. 이 표는 분류이고 증명이 아니다.

## 4. 수치

| 항목 | 값 |
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

파서 ERR 목록:

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

`%riz`는 GNU objdump가 색인 없는 SIB 바이트를 적는 철자다(`%r12`가 기준 레지스터일 때). 주소는 `(%r12)`와 같다.
생성기 결함이 아니다. 변환기 또는 Kraken 파서의 빈틈이다(`GENERATOR-FINDINGS.md` 4절).

생성 함수의 니모닉 빈도(I만):

`add` 4054, `and` 267, `callq` 8540, `cmovne` 1, `cmp` 3268, `cmpb` 1, `cmpl` 1624, `cmpq` 914, `data16 nop` 599, `imul` 195, `inc` 306, `ja` 149, `jae` 1032, `jb` 724, `jbe` 388, `je` 2103, `jg` 211, `jge` 426, `jl` 41, `jle` 66, `jmp` 1432, `jmpq` 1282, `jne` 3355, `lea` 10288, `mov` 54433, `movb` 4, `movl` 89, `movq` 2502, `movups` 1420, `movzbl` 17, `mul` 76, `neg` 252, `nop` 3014, `nopl` 1446, `nopw` 270, `or` 1, `pop` 2239, `push` 339, `retq` 2305, `sar` 267, `shl` 379, `shr` 139, `sub` 796, `test` 2145, `xor` 3490

## 5. 집합의 차이

- B 중 생성 타입이지만 A에 없는 것 7개: `proto/engine/v1.ConsolidationRequest`, `proto/engine/v1.DepositRequest`, `proto/engine/v1.ExecutionPayloadDeneb`, `proto/engine/v1.ExecutionPayloadHeaderDeneb`, `proto/engine/v1.ExecutionRequests`, `proto/engine/v1.Withdrawal`, `proto/engine/v1.WithdrawalRequest`.
- I 중 A에 없는 것 11개: `proto/engine/v1.ConsolidationRequest`, `proto/engine/v1.DepositRequest`, `proto/engine/v1.ExecutionPayload`, `proto/engine/v1.ExecutionPayloadCapella`, `proto/engine/v1.ExecutionPayloadDeneb`, `proto/engine/v1.ExecutionPayloadHeader`, `proto/engine/v1.ExecutionPayloadHeaderCapella`, `proto/engine/v1.ExecutionPayloadHeaderDeneb`, `proto/engine/v1.ExecutionRequests`, `proto/engine/v1.Withdrawal`, `proto/engine/v1.WithdrawalRequest`.
- A 중 B에 없는 것 86개. 이름은 `inventory.json` `sets.A_minus_B`에 있다.

Fulu가 아닌 설정:

| 설정 | 타입 수 | 이유 |
| --- | --- | --- |
| `proto/prysm/v1alpha1/gloas.yaml` | 41 | later fork (after Fulu) |
| `proto/prysm/v1alpha1/heze.yaml` | 9 | later fork (after Fulu) |
| `proto/prysm/v1alpha1/non-core.yaml` | 13 | not a fork config and no type reached from the Fulu roots |
| `proto/eth/v1/gateway.yaml` | 20 | not a fork config and no type reached from the Fulu roots |
| `proto/ssz_query/response.yaml` | 3 | not a fork config and no type reached from the Fulu roots |
| `proto/ssz_query/testing/test_containers.yaml` | 5 | not a fork config and no type reached from the Fulu roots |

손 작성 위임 대상(생성기가 만들지 않는 SSZ 메서드):

| 타입 | 부르는 타입 수 |
| --- | --- |
| `consensus-types/primitives.CommitteeIndex` | 2 |
| `consensus-types/primitives.Epoch` | 10 |
| `consensus-types/primitives.Gwei` | 2 |
| `consensus-types/primitives.Slot` | 38 |
| `consensus-types/primitives.ValidatorIndex` | 28 |

minimal에서 IR이 다른 타입은 `inventory.json` `minimal_differences`에 있다. 범위 분류가 바뀐 것은 위 수치와 같다.

## 6. 타입 표

열: 설정, B(Fulu 도달), 종류, 필드 수, 깊이, 범위(이유), 위임 호출(생성/손), 명령어 수 M/S/U(MarshalSSZTo/SizeSSZ/UnmarshalSSZ), 니모닉 종류 수, Kraken 미지원 니모닉, 파서(M/S/U), 런타임 호출(세 함수 합집합).
호출 약어: VBl=ValidateBitlist, VBv=ValidateBitvector, cT64=convT64, fmt=fmt, gen=generated method, grow=growslice, hand=hand-written primitives method, mks=makeslice, mm=memmove, stk=morestack_noctxt, new=newobject, pan=panic*, wb=write barrier, mvS=moveSlice* (stack-backed result to heap), rt?=runtime other, oth?=other, ind=indirect.

| 타입 | 설정 | B | 종류 | 필드 | 깊이 | 범위 | 위임 | M/S/U | 니모닉 | 미지원 | 파서 | 호출 |
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

필드 모양 빈도(I 전체): bitlist 6, bitvector 10, bool 1, bytesN 195, delegated container (fixed) 120, delegated container (variable) 78, delegated overlay CommitteeIndex 2, delegated overlay Epoch 15, delegated overlay Gwei 6, delegated overlay Slot 39, delegated overlay ValidatorIndex 29, list[byte] 18, list[bytesN] 31, list[container] 89, list[list[byte]] 3, list[uint64] 16, uint64 65, vector[ValidatorIndex] 1, vector[bytesN] 46, vector[uint64] 7.
