# SELECTION: list/vector 손 증명 대상 (LV 스트림)

이 파일은 증명을 시작하기 전에 커밋한다.
대상과 경로는 이 커밋 뒤에 바꾸지 않는다.
정리 문장 초안은 `STATEMENTS.md`와 `lean/E2eList/Stmt*.lean`에 따로 커밋한다.

## 1. 기준

| 항목 | 값 |
| --- | --- |
| 기준 커밋 | `6a78c591e8bcd698b7b9313b1c09cb25f3986911` (`syjn99/ssz-fv-reuse-milestone`의 원격 머리) |
| 브랜치 | `claude/ssz-fv-list-vector-20261112` |
| 대상 ELF sha256 | `c6403c02a110ffd6fe6d31a3c89cd395ac457b5d62e60e2e611b8ab9a8dd911e` |
| ELF 재빌드 | 이 장비에서 다시 만들었다. sha256, build ID, objdump sha256, nm sha256이 `build-ids.txt`와 같다 |
| 선정 작성 모델 | `claude-fable-5-2` (계획 담당) |

## 2. 근거 파일

- `prysm/TYPES.md`: 종류, 필드 수, 명령어 수, 호출 집합.
- `prysm/SCOPE-P6.json`: 첫 실패 종류, 새 패턴 종류, 없는 계약.
- `prysm/_generated/mainnet/*.ssz.go`: 생성된 Go 소스.
- 다시 만든 ELF의 `conv.py --norm` 출력: `UnmarshalSSZ`의 줄 수와 `callq` 대상.

## 3. 후보 표 (`UnmarshalSSZ`만)

줄 수는 정규화한 `.S`의 줄 수다.
"계약"은 `CONTRACTS.md`에 꼴이 있는 피호출자만 부르는지를 뜻한다.

| 타입 | list/vector 꼴 | `.S` 줄 | 피호출자 | 계약 | 판정 |
| --- | --- | --- | --- | --- | --- |
| `SyncAggregate` | bitvector 512 (64바이트), bytes96 | 106 | makeslice 2, memmove 2 | 있음 | **선정 T1** |
| `SyncCommittee` | vector[512] of bytes48 (`[][]byte`), bytes48 | 137 | makeslice 3, memmove 2, panicBounds 1 | 있음 | **선정 T2** |
| `IndexedAttestation` | list[uint64] 최대 2048, 위임 `AttestationData`, bytes96 | 279 | fmt.errorf 3, AttestationData.UnmarshalSSZ 1, convT64 2, makeslice 2, memmove 1, newobject 4, panicBounds 3 | 수용 경로는 있음. fmt 경로는 형식별로 확인한다 | **선정 T3 (시간이 남을 때)** |
| `HistoricalBatch` | vector[8192] of bytes32 둘 | 182 | makeslice 4, memmove 2, panicBounds 4 | 있음 | 제외: T2와 같은 꼴이고 더 크다 |
| `Deposit` | vector[33] of bytes32, 위임 `Deposit_Data` | 156 | fmt.errorf 1, Deposit_Data.UnmarshalSSZ 1, 그 밖 | `Deposit_Data` 디코더 명세가 레포에 없다 | 제외 |
| `Attestation` | bitlist, 위임, bytes96 | 218 | ValidateBitlist 1, growslice 1, fmt.errorf 2, 그 밖 | 계약은 Go 1.26.3 기준이다 | 제외: T1–T3 뒤로 미룬다 |
| `PendingAttestation` | bitlist, 손 작성 Slot·ValidatorIndex | 256 | 위와 같고 더 많다 | 위와 같다 | 제외 |

제외 대상 확인(작업 지시 2절):

- T1–T3는 `gen/scal/*`를 쓰지 않는다.
- T1–T3는 `AttestationData.MarshalSSZTo`를 대상으로 하지 않는다. T3는 이미 증명된 `AttestationData.UnmarshalSSZ` 명세만 쓴다.
- T1–T3는 보류 평가(H6) 대상군이 아니다. T1의 64바이트 bitvector와 T2의 `[][]byte`는 그 군의 필드 꼴이 아니다.
- H6 대상군의 `.S`, IR, 증명은 열지 않았다.

`SCOPE-P6`은 `SyncAggregate`와 `SyncCommittee`를 "계약 부재(moveSlice*)"로 분류한다.
`UnmarshalSSZ`의 `.S`에는 `moveSlice*` 호출이 없다.
그 분류는 타입의 세 함수 전체에 대한 것이다. 인코더는 이 작업의 범위 밖이다.

## 4. 대상과 경로

| 대상 | 함수 | 경로 | 순서 |
| --- | --- | --- | --- |
| T1 `SyncAggregate` | `UnmarshalSSZ` | 크기 거부(`len ≠ 160`), 수용, EthLib 명세 대응, 증인 | 1 |
| T2 `SyncCommittee` | `UnmarshalSSZ` | 크기 거부(`len ≠ 24624`), 수용(512회 루프 불변식), EthLib 명세 대응, 증인 | 2 |
| T3 `IndexedAttestation` | `UnmarshalSSZ` | 크기 거부(`len < 228`), 오프셋 거부(`≠ 228`), 수용(원소 루프), 정렬·초과 거부는 계약이 맞을 때만 | 3 |

범위 밖: 세 타입의 `MarshalSSZTo`, `SizeSSZ`, `HashTreeRoot`, morestack 경로, 쓰기 장벽이 켜진 경로.
범위 밖 경로는 "미증명(N)"으로 보고한다.

## 5. 한계

- 이 표는 선정이다. 증명 가능성을 말하지 않는다.
- 호스트는 darwin/arm64다. x86-64 기계어를 실행하지 않았다.
- 계약은 Go 1.26.3 런타임 소스를 읽은 결과다. Go 1.26.10 런타임에 대해서는 `e2e/RUNTIME-1.26.10.md`의 범위만 확인돼 있다.
