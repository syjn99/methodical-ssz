# REPORT: LV (list/vector 손 증명)

**판정: 조건부.**

조건:

1. 런타임 호출은 계약 가설이다(`MakesliceC`, `MemmoveC`). Go 런타임 기계어의 정교화 증명은 없다.
2. 전제 `writeBarrier = 0`과 `guard < rsp`가 경로를 고정한다. 쓰기 장벽 경로와 morestack 경로는 증명하지 않았다.
3. T3 `IndexedAttestation` 디코더와 `conv.py` 수정(`93b3f2a`)은 독립 리뷰를 받지 않았다.
4. T3의 P4, P5 거부는 고정 문장으로는 증명되지 않는다. 전제 `e0 ≠ 0`을 더한 `_nz` 문장만 K다.
5. Go 차분 시험과 x86-64 실행 대조는 하지 않았다.
6. 독립 리뷰 결과는 9절에 적는다.

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
| T3 IndexedAttestation | P1 크기 거부 | K | `ia_e2e_reject_size_main`, `ia_e2e_reject_size_spec` |
| T3 | P2 오프셋 거부 | K | `ia_e2e_reject_offset_main`, `ia_e2e_reject_offset_spec` |
| T3 | P3 수용, 모든 n ≤ 2048 | K | `ia_iter`, `ia_exit`, `ia_loop`, `ia_e2e_accept_main` |
| T3 | P3 수용, 명세 | K | `ia_e2e_accept_spec` |
| T3 | P4 정렬 거부, 고정 문장 | N | `ia_reject_misaligned_stmt`와 명세 짝. 쓰인 대로는 증명할 수 없다 |
| T3 | P4 정렬 거부, `e0 ≠ 0` | K | `ia_e2e_reject_misaligned_nz`, `ia_e2e_reject_misaligned_spec_nz` |
| T3 | P5 길이 초과 거부, 고정 문장 | N | `ia_reject_toobig_stmt`와 명세 짝. 같은 이유다 |
| T3 | P5 길이 초과 거부, `e0 ≠ 0` | K | `ia_e2e_reject_toobig_nz`, `ia_e2e_reject_toobig_spec_nz` |
| T3 | P6 | N | 도달할 수 없는 경로로 기록했다. 별도 정리는 없다 |
| T3 | EthLib 거부 사례 | K | `ia_e2e_reject_cases` (기계 정리가 아니다) |
| T3 | 손 `Desc` = 생산자 `Desc` | K | `prysmIaDesc_deserialize_checker` |
| T3 | 증인 | K | `WitIaA.ia_accept_runs`(모든 n ≤ 2048, 예 0, 1, 2048), `WitIaR.ia_misaligned_runs`, `WitIaR.ia_toobig_runs` |
| T3 | 링크 검사 | X | `lv/link-t3/RESULT` |
| T3 | 부정 시험 | X | `lv/negative-lv-t3.json` |
| T1–T3 | MarshalSSZTo, SizeSSZ, HashTreeRoot | N | 범위 밖 |
| T1, T2 | morestack, 쓰기 장벽 | N | 전제가 막는다 |

T1, T2의 주 정리는 `dfc8b93`의 고정 문장 def를 형으로 가진다.
T3의 주 정리는 `e13053a`(`StmtIa.lean`)와 `714989f`(`StmtIaNz.lean`)의 고정 문장 def를 형으로 가진다.
T3의 P4, P5는 오류 값에 대해 `rax ≠ 0`만 말한다.
T3의 행은 리뷰 전이다.
공리는 게이트 결과 `lv/axioms-gate-lv.json`과 `lv/axioms-gate-lv-t3.json`에 있다.

## 3. 막힌 의무

| 의무 | 원인 분류 | 사실 |
| --- | --- | --- |
| T3 P4, P5 고정 문장 | 문장 결함 | errorString itab 레이블 `e0`가 0이면 `test %rcx,%rcx; je`가 형식 단어 읽기를 건너뛴다. 문장에 `e0 ≠ 0`이 없다. 계획 담당이 승인할 때 놓쳤다. 사용자가 `_nz` 문장을 승인했다 |
| T3 증인, 전략 1과 2 | 증명 크기 | WitScA의 글을 그대로 쓰면 64000000 heartbeat에서 `whnf` 시간 초과다(로그 192, 1471 s). 전략 3(`ib`를 먼저 떼는 다시 쓰기)이 닫았다 |

LV-1은 `conv.py` 수정으로 풀렸다(`FINDINGS-CANDIDATES.md`).

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
| WitSaA | 12 s | 17.7 s | 2.04 GiB |
| ScReject | 3.8 s | 6.3 s | 1.98 GiB |
| ScLemmas | 3.4 s | 5.2 s | 0.86 GiB |
| ScLoop | 6.3 s | 8.3 s | 2.22 GiB |
| ScAccept | 6.6 s | 9.4 s | 2.12 GiB |
| ScSpec / ScSpecK / ScDescEq | 3.2–3.5 s | 5.2–8.4 s | 1.93 GiB 이하 |
| BumpT | 1.7 s | 4.2 s | 1.97 GiB |
| WitScA | 16 s | 18.8 s | 2.06 GiB |

`maxHeartbeats`는 증인 둘에만 있다: `WitSaA.sa_accept_runs` 2000000, `WitScA.sc_accept_runs` 4000000.
원인: `simp` AC 정렬(로그 27, 7.03 s + 2.08 s).
설정이 없으면 `whnf` 시간 초과다(로그 26, 65).
리뷰어 r2의 측정: 400000은 둘 다 실패한다. WitSaA는 1000000에서 통과한다. WitScA는 1000000에서 실패하고 2000000에서 통과한다.
`E2eList`에는 `maxRecDepth` 설정이 없다(리뷰 r2 M1, `69f1a70`).
`WitScA.lean`의 `example` 둘은 `by simp` 대신 항 증명(`List.length_replicate`, `List.eq_of_mem_replicate`)을 쓴다.
위 표의 WitSaA, WitScA 값은 그 수정 뒤의 값이다(로그 96, 97).
로그는 로컬에만 있다. 발췌는 `ATTEMPTS.md`에 있다.

T3의 옵션(원인과 문턱은 옵션 옆에 있다. 구현 담당의 측정이다):

- `maxRecDepth 1024`: `ia_iter`, `ia_exit`, `ia_e2e_accept_main`, `_nz` 증명 둘. 없으면 첫 `kat`가 멈춘다(로그 136, 139, 184, 233).
- `maxHeartbeats 1600000`: `ia_e2e_accept_main`. 400000은 실패하고 800000은 통과한다(로그 185).
- `WitIaA`: 파일 수준 `maxRecDepth 2048`(기본값과 1024는 실패한다, 로그 212). `ia_accept_runs`에 `maxHeartbeats 10000000`(4000000은 실패하고 5000000은 통과한다, 로그 211).
- `WitIaR`: 파일 수준 `maxRecDepth 1024`(기본값은 실패한다, 로그 245).
- `lake build E2eList`: 765 jobs, 100 s, 표본 RSS 7.71 GiB(로그 252).

## 5. 재사용과 새것

재사용: `dechead_seg`, `decepi_seg`, `bytesdec_tail_seg`, `bytesdec_seg`(48), `bump_makeslice1`, `rt_memmove`, `Fv1.deserialize_enc`, `accepted_is_enc`, EthLib `packBits_unpackBits`, `unpackBits_packBits`, `headOf_inline`, `bodiesOf_inline`, `concatParts_size`, `concat_fixed_slices`.

새 Lean(줄): Code 22, Include 85, Data 23, Desc 31, Defs 59, StmtSa 207, StmtSc 229, SaReject 94, ScReject 94, Seg 370, SaAccept 181, ScLemmas 122, ScLoop 313, ScAccept 270, SaSpec 96, ScSpec 173, SaSpecK 41, ScSpecK 46, Sa/ScSpecChecker 13 각각, Sa/ScDescEq 54 각각, BumpT 148(+ `.S` 16), WitSaA 126, WitScA 136(`69f1a70` 기준).

새 스크립트: `lvlink.py`, `lvcheck_include.py`, `lvdescterm.py`, `lvaxioms_gate.py`, `AxiomsLv.lean`, `lvnegative.py`.
기존 스크립트는 바꾸지 않았다.

## 6. 더한 신뢰 항목

- `MakesliceC … lvSliceType_addr 24 S`는 기존 꼴의 인스턴스로 썼다(계획 담당 판정). 계약은 형식 기술자를 읽지 않는다.
- 이 원소 형식은 포인터를 가진다. 그래서 "호출 중 GC 없음"이 여기서 더 중요하다.
- 신뢰 읽개 `lv_data_include`를 더했다. `E2e/Include.lean`과 같은 글이다(SAME 4개).
- `BumpAllocT`는 비공허성 모델이다. 형식 단어를 비교해 24·cnt 또는 cnt를 뗀다. Go `makeslice`는 `et.Size_`를 읽는다.
- `BumpAllocT.S`는 리뷰 r1 뒤 Lake `input_dir`(`lv_lean_S`)로 등록했다.
- 손 `Desc`와 consensus-specs의 같음은 판단이다. 생산자 `Desc`와의 같음은 K다.
- 작성자의 기준 쪽 drift 덤프는 복제한 `.lake`를 썼다. 리뷰어 r2는 기준 트리를 따로 빌드했다. 그 덤프는 작성자의 덤프와 바이트 단위로 같다.

- T3: `ia_accept_stmt`는 `len ≤ cap`과 `cap < 2^63`을 전제로 쓴다. `cap < 2^63`이 없으면 결론이 거짓이다(`DESIGN-T3.md`).
- T3: 기계 쪽 거부 완전성은 P4, P5에서 `e0 ≠ 0` 아래에서만 선다. 증인은 `e0 = 0x1012b`를 쓴다.
- T3: 증인 전용 런타임 모델 `BumpAllocT3`(makeslice, esz 8 또는 1), `BumpNewT3`(newobject, 96 또는 72)을 더했다.
- T3: Lake `input_dir` 둘(`lv_t3_norm_S`, `lv_t3_data`)을 lakefile에 덧붙였다(`e13053a`).
- `link/conv.py`를 바꿨다(`93b3f2a`, 사용자 승인). `check.py`는 `conv.py`의 해시를 RESULT 묶음에 넣지 않는다.

## 7. 검증

명령, 종료 코드, 로그는 `STEPS.tsv`에 있다.

| 검사 | 결과 |
| --- | --- |
| `lake build E2eList` | exit 0 (리뷰 r2 수정 뒤 683 jobs, 로그 98) |
| `--no-build E2e E2eAd E2eScal E2eList` | exit 0, 1036 jobs (로그 99) |
| 공리 게이트 | PASS, 5632 선언, 비표준 0, sorryAx 0 (`axioms-gate-lv.json`; 리뷰 r1 뒤 `axioms-gate-lv-r1.json`. 리뷰 r2 수정 뒤 `axioms-gate-lv-r2.json`, 로그 100) |
| 게이트 대조군(심은 `sorry`) | FAIL(기대대로) (`axioms-gate-lv-plant.json`) |
| 선언 drift (기준 `6a78c591`, 뿌리 E2e/E2eAd/E2eScal) | 0 (`decl-drift-lv.txt`. 리뷰 r2 수정 뒤 다시 0, 로그 102) |
| drift 대조군 | CHANGED(기대대로), 되돌림 |
| 링크 T1, T2 | PASS all |
| 부정 시험 | 26개 중 25개 통과(control_pass 7, inside 18). `lv-sa-bitslen63`은 outside다(오류가 `sa_bits_seg`에 있다). 같은 변이를 `sa_bits_seg`에 겨눈 경우는 inside다. `Desc` 변이와 T2 크기 거부 변이를 포함한다(로그 94). `Desc` 변이 파일은 대상에서 잘린다. `prysmS*Desc_fixedSize`나 `ps*_toValue_fits`까지만 간다. `*_spec_k`를 시험하는 `Desc` 변이는 없다. 작성자는 리뷰 r2 수정 뒤 다시 돌리지 않았다. 리뷰어 r3가 다시 돌렸고 사례별 결과는 같다 |
| stale 검사 | flagged 0 |
| T3 `lake build E2eList` | exit 0, 765 jobs (로그 252) |
| T3 `--no-build` 네 라이브러리 | exit 0, 1080 jobs (로그 254) |
| T3 공리 게이트 | PASS, 6402 선언, 정리 5341, 비표준 0, sorryAx 0 (`axioms-gate-lv-t3.json`, 로그 255) |
| T3 선언 drift | 0, 5007 = 5007 (`decl-drift-lv-t3.txt`, 로그 250) |
| T3 링크 | PASS all (`lv/link-t3/RESULT`). U8에서 다시 돌리지 않았다 |
| T3 부정 시험 | 8개 모두 통과: 대조군 2, inside 6 (`negative-lv-t3.json`, 로그 253) |
| T3 게이트 대조군, drift 대조군, stale 검사 | 실행하지 않음 |
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
- T3: 커널 함정 둘을 만났다. `c + -228`에 `simp [BitVec.toNat_add]; omega`를 쓰면 커널이 235–309 s 뒤 "deep recursion"으로 멈춘다(16–20 GiB). 64비트 `sshiftRight`의 `decide`도 같다. 명시적 보조정리로 피했다.
- T3: 증인의 메모리 목표는 `ecancel`로 닫히지 않았다(내부 PANIC 56개, 로그 204–208). AC `simp`로 닫았다.
- T3: 고정 문장은 분기마다 읽는 레이블의 0 여부를 전제로 가져야 한다. P4, P5가 그 사례다.
- 정정: `SELECTION.md`의 "`Deposit_Data` 디코더 명세가 레포에 없다"는 틀리다. `dd_e2e_accept_spec_k`가 있다. `SELECTION.md`는 고정 파일이라서 여기에 적는다.
- 다음 후보: 같은 꼴은 `HistoricalBatch`다. 이번 증명이 옮겨지는지는 시험하지 않았다. 음수 변위가 있는 함수는 LV-1을 먼저 풀어야 한다.

## 9. 발견 후보와 리뷰

- LV-1(수정됨 `93b3f2a`, 리뷰 전, X, 도구 빈틈). `FINDINGS-CANDIDATES.md`를 본다.
- 새 production 결함 후보는 없다.
- 독립 리뷰 r1(`fbf729a`): REQUEST_CHANGES, 필수 수정 1개(M1). `REVIEW-R1.md`를 본다. 수정은 `463ec97`, `3bb6cc1`, `4a18079`, `ec75cd5`다.
- 독립 리뷰 r2(`d169e4b`): REQUEST_CHANGES, 필수 수정 2개(M1, M2). `REVIEW-R2.md`를 본다. 수정은 `1ba8b41`, `69f1a70`, `252380f`와 이 파일의 커밋이다.
- 독립 리뷰 r3(`650b1f5`): APPROVE, 필수 수정 없음. `REVIEW-R3.md`를 본다. 그 뒤의 문서 커밋(N1, N2, `REVIEW-R3.md`)은 리뷰받지 않았다.
- 사용자 확인이 필요한 것:
  - esz 24 `MakesliceC` 인스턴스(리뷰 r1 S7).
  - 기한.
  - Go 차분 시험.
  - `3bb6cc1`의 lakefile 변경(`input_dir` 추가). 루트 `AGENTS.md`는 lakefile 변경에 승인을 요구한다.
  - LV-1의 남은 길(`check.py` 범위 검사, Kraken 요청). `conv.py` 수정은 사용자가 승인했다.
  - `e13053a`의 lakefile 변경(`input_dir` 둘 추가).
  - 시도 횟수 해석(3절).
  - 원격 이름. `origin`은 OffchainLabs다.
