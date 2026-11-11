# REPORT: LV (list/vector 손 증명)

**판정: 조건부.**

조건:

1. 런타임 호출은 계약 가설이다(`MakesliceC`, `MemmoveC`). Go 런타임 기계어의 정교화 증명은 없다.
2. 전제 `writeBarrier = 0`과 `guard < rsp`가 경로를 고정한다. 쓰기 장벽 경로와 morestack 경로는 증명하지 않았다.
3. T3 `IndexedAttestation`은 증명하지 않았다. 링크가 LV-1로 막혔다.
4. Go 차분 시험과 x86-64 실행 대조는 하지 않았다.
5. 독립 리뷰 결과는 9절에 적는다.

## 1. 환경과 핀

| 항목 | 값 |
| --- | --- |
| 저장소 원격 | `syjn99/methodical-ssz`는 이 작업 트리에서 원격 이름 `my`다. `origin`은 `OffchainLabs/methodical-ssz`다. 원격에 쓰지 않았다 |
| 기준 커밋 | `6a78c591e8bcd698b7b9313b1c09cb25f3986911` (`syjn99/ssz-fv-reuse-milestone`의 원격 머리) |
| 브랜치 | `claude/ssz-fv-list-vector-20261112` |
| ELF sha256 | `c6403c02a110ffd6fe6d31a3c89cd395ac457b5d62e60e2e611b8ab9a8dd911e` |
| ELF 재빌드 | linux/arm64 컨테이너, Go 1.26.10(공식 tarball sha256 `3f4227ce…9797`), Prysm `ab15ff70`, 생성기 `698c202`, `.git` 없음. sha256, build ID, objdump sha256, nm sha256이 `build-ids.txt`와 같다 |
| Kraken | `6064eecbb730a1152aa6ed891a155d3a92a4f298` |
| EthLib | `862185680cf23ccf54d44eb25b63b26c5020597b` |
| Lean | `4.36.0-nightly-2026-09-21`, Lake 5.0.0. `lean-toolchain`과 같다 |
| 호스트 | darwin/arm64, 18코어, RAM 48 GiB, Apple LLVM 21.0.0(`xcrun`) |
| `.lake` | 시작할 때 없었다. `lake build E2e E2eAd E2eScal` 첫 빌드: exit 0, 982 jobs, 1215 s, 표본 RSS 최대 19.2 GiB(상한 추정) |
| 무거운 작업 | 저장소 밖의 `heavy.py`(이전 ARM 작업의 도구), 상한 40960 MB. `gen/tools/memcap.py`는 `/proc`가 필요해서 macOS에서 돌지 않는다 |
| 모델 | 계획·선정 `claude-fable-5-2`, 증명 `claude-opus-5-5` |
| 기한 | 캠페인 기한(새 증명 2026-11-13T12:00Z)을 따른다고 가정했다. 사용자 확인은 받지 않았다 |

선정 표와 이유는 `SELECTION.md`에 있다.

## 2. 커버리지 (K 커널 검사, X 실행만, N 미증명)

| 타입 | 경로 | 종류 | 정리 |
| --- | --- | --- | --- |
| T1 SyncAggregate | 크기 거부 | K | `sa_e2e_reject_size_main` |
| T1 | 수용 | K | `sa_e2e_accept_main` |
| T1 | 수용, 명세 | K | `sa_e2e_accept_spec_k` |
| T1 | 크기 거부, 명세 | K | `sa_e2e_reject_size_spec` |
| T1 | 거부 완전성 | K | `sa_e2e_reject_complete` |
| T1 | 손 `Desc` = 생산자 `Desc` | K | `prysmSaDesc_deserialize_checker` |
| T1 | 증인 | K | `WitSaA.sa_accept_runs` |
| T2 SyncCommittee | 크기 거부 | K | `sc_e2e_reject_size_main` |
| T2 | 한 바퀴(경계 검사 안 갈림) | K | `sc_iter` |
| T2 | 512회 루프 | K | `sc_loop`, `sc_exit` |
| T2 | 수용 | K | `sc_e2e_accept_main` |
| T2 | 수용, 명세 | K | `sc_e2e_accept_spec_k` |
| T2 | 크기 거부, 명세 | K | `sc_e2e_reject_size_spec` |
| T2 | 거부 완전성 | K | `sc_e2e_reject_complete` |
| T2 | 손 `Desc` = 생산자 `Desc` | K | `prysmScDesc_deserialize_checker` |
| T2 | 증인 | K | `WitScA.sc_accept_runs`, `bump_makeslice_t24`, `bump_makeslice_t1` |
| T1, T2 | 링크 검사 | X | `lv/link/RESULT` |
| T1, T2 | 부정 시험 | X | `lv/negative-lv.json` |
| T3 | 모든 경로 | N | LV-1, 시작하지 않음 |
| T1–T3 | MarshalSSZTo, SizeSSZ, HashTreeRoot | N | 범위 밖 |
| T1, T2 | morestack, 쓰기 장벽 | N | 전제가 막는다 |

모든 주 정리는 `dfc8b93`의 고정 문장 def를 형으로 가진다.
공리는 게이트 결과 `lv/axioms-gate-lv.json`에 있다.

## 3. 막힌 의무

| 의무 | 원인 분류 | 사실 |
| --- | --- | --- |
| T3 링크와 증명 | 도구 빈틈 | `lea 0xffffff1c(%rdi),%rdx`. Kraken은 +4294967068로 읽는다. 기계는 −228이다. 계획 담당 판정으로 시작하지 않았다 |

T1과 T2에서 시도 한도에 닿은 의무는 없다(`ATTEMPTS.md`).
한 증명 전략 안의 컴파일 반복은 시도 한 번으로 셌다. 이것은 구현 담당의 해석이다.

## 4. 시간과 메모리

방법: `heavy.py` 기록, 한 번(n = 1), 표본 RSS는 그룹 합(상한 추정).

| 모듈 | 모듈 시간 | 벽시계 | RSS |
| --- | --- | --- | --- |
| SaReject | 4.3 s | 6.3 s | 1.93 GiB |
| Seg | 3.6 s | 6.3 s | 2.17 GiB |
| SaAccept | 4.7 s | 7.3 s | 2.15 GiB |
| SaSpec / SaSpecK / SaDescEq | 3.2 s 각각 | 5.2–8.3 s | 0.86 GiB 이하 |
| WitSaA | 12 s | 15.7 s | 2.04 GiB |
| ScReject | 3.8 s | 6.3 s | 1.98 GiB |
| ScLemmas | 3.4 s | 5.2 s | 0.86 GiB |
| ScLoop | 6.3 s | 8.3 s | 2.22 GiB |
| ScAccept | 6.6 s | 9.4 s | 2.12 GiB |
| ScSpec / ScSpecK / ScDescEq | 3.2–3.5 s | 5.2–8.4 s | 1.93 GiB 이하 |
| BumpT | 1.7 s | 4.2 s | 1.97 GiB |
| WitScA | 16 s | 18.8 s | 2.07 GiB |

`maxHeartbeats`는 증인 둘에만 16000000이다.
원인: `simp` AC 정렬(로그 27, 7.03 s + 2.08 s).
설정이 없으면 `whnf` 시간 초과다(로그 26, 65).

## 5. 재사용과 새것

재사용: `dechead_seg`, `decepi_seg`, `bytesdec_tail_seg`, `bytesdec_seg`(48), `bump_makeslice1`, `rt_memmove`, `Fv1.deserialize_enc`, `accepted_is_enc`, EthLib `packBits_unpackBits`, `unpackBits_packBits`, `headOf_inline`, `bodiesOf_inline`, `concatParts_size`, `concat_fixed_slices`.

새 Lean(줄): Code 22, Include 85, Data 23, Desc 31, Defs 59, StmtSa 207, StmtSc 229, SaReject 94, ScReject 94, Seg 370, SaAccept 181, ScLemmas 122, ScLoop 313, ScAccept 270, SaSpec 96, ScSpec 173, SaSpecK 41, ScSpecK 46, Sa/ScSpecChecker 13 각각, Sa/ScDescEq 54 각각, BumpT 148(+ `.S` 16), WitSaA 126, WitScA 134.

새 스크립트: `lvlink.py`, `lvcheck_include.py`, `lvdescterm.py`, `lvaxioms_gate.py`, `AxiomsLv.lean`, `lvnegative.py`.
기존 스크립트는 바꾸지 않았다.

## 6. 더한 신뢰 항목

- `MakesliceC … lvSliceType_addr 24 S`는 기존 꼴의 인스턴스로 썼다(계획 담당 판정). 계약은 형식 기술자를 읽지 않는다.
- 이 원소 형식은 포인터를 가진다. 그래서 "호출 중 GC 없음"이 여기서 더 중요하다.
- 신뢰 읽개 `lv_data_include`를 더했다. `E2e/Include.lean`과 같은 글이다(SAME 4개).
- `BumpAllocT`는 비공허성 모델이다. 형식 단어를 비교해 24·cnt 또는 cnt를 뗀다. Go `makeslice`는 `et.Size_`를 읽는다.
- `BumpAllocT.S`는 Lake `input_dir`가 아니다. 그 파일이 바뀌어도 Lake는 다시 빌드하지 않는다.
- 손 `Desc`와 consensus-specs의 같음은 판단이다. 생산자 `Desc`와의 같음은 K다.
- 기준 쪽 drift 덤프는 복제한 `.lake`를 썼다. 독립된 기준 빌드가 아니다.

## 7. 검증

명령, 종료 코드, 로그는 `STEPS.tsv`에 있다.

| 검사 | 결과 |
| --- | --- |
| `lake build E2eList` | exit 0 |
| `--no-build E2e E2eAd E2eScal E2eList` | exit 0, 1035 jobs |
| 공리 게이트 | PASS, 5632 선언, 비표준 0, sorryAx 0 (`axioms-gate-lv.json`) |
| 게이트 대조군(심은 `sorry`) | FAIL(기대대로) (`axioms-gate-lv-plant.json`) |
| 선언 drift (기준 `6a78c591`, 뿌리 E2e/E2eAd/E2eScal) | 0 (`decl-drift-lv.txt`) |
| drift 대조군 | CHANGED(기대대로), 되돌림 |
| 링크 T1, T2 | PASS all |
| 부정 시험 | 18개 중 17개 통과. `lv-sa-bitslen63`은 outside다(오류가 `sa_bits_seg`에 있다). 기록을 남겼다 |
| stale 검사 | flagged 0 |
| Go 차분 시험 | 실행하지 않음 |
| 하드웨어 대조 | 실행하지 않음. 호스트는 arm64다 |

## 8. codec 전체 검증을 위해 배운 것

- 크기가 새로운 고정 바이트 필드마다 구간 보조정리의 증명 글을 한 번 더 복사했다(`Seg.lean` 370줄). `SegN`의 `hn`은 증명 방식의 한계다.
- 512회 루프는 한 바퀴 정리와 귀납으로 닫혔다. `ScLoop` 빌드는 6.3 s다. 루프를 펼치지 않았다.
- 불변식 꼴: 배열 = 앞 i개 헤더 ++ 0, 원소 = 포인터와 입력 조각의 쌍, 힙 = avail − 48·i, 수신자 len 칸.
- 경계 검사는 매 바퀴 수신자에서 len을 읽는다. 그래서 불변식에 그 칸이 있어야 `panicBounds`를 막았다.
- Vector[Bytes48, 512] 명세는 목록 일반 보조정리와 EthLib 정리로 닫았다. `decide`로는 닫히지 않는다.
- 같은 런타임 함수를 다른 esz로 부르면 한 Host 증인에 형식으로 갈리는 모델이 필요했다.
- 도구 빈틈: `kaddr`의 `Width.bits`(기존 T-4), `pks[i]` 증명 항 차이로 `ecancel` 실패(`generalize`로 피함), LV-1.
- 문장 def 형식은 `negative.py`와 맞지 않았다. 문장 모듈을 펼치는 실행기가 필요했다.
- 자동화 후보: 머리·꼬리·필드 구간, 한 바퀴 증명의 단계 열. 이번 두 타입에서 본 것이다. 다른 타입은 시험하지 않았다.
- 손이 필요했던 것: 불변식의 메모리 꼴과 조각 나누기·합치기(`scA_split`, `scA_join`, `scIn_split`).
- 다음 후보: 같은 꼴은 `HistoricalBatch`다. 이번 증명이 옮겨지는지는 시험하지 않았다. 음수 변위가 있는 함수는 LV-1을 먼저 풀어야 한다.

## 9. 발견 후보와 리뷰

- LV-1(열림, X, 도구 빈틈). `FINDINGS-CANDIDATES.md`를 본다.
- 새 production 결함 후보는 없다.
- 독립 리뷰: 이 커밋 시점에는 실행하지 않았다. 결과는 `REVIEW-*.md`에 따로 적는다.
