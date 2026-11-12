# REPORT-HB: `HistoricalBatch.UnmarshalSSZ` 손 증명과 T2 재사용 측정

**판정: 조건부.**

조건:

1. 런타임 호출은 계약 가설이다(`MakesliceC` 둘, `MemmoveC`). Go 런타임 기계어의 정교화 증명은 없다.
2. 전제 `writeBarrier = 0`과 `guard < rsp`가 경로를 고정한다. 쓰기 장벽 경로와 morestack 경로는 증명하지 않았다.
3. Go 차분 시험과 x86-64 실행 대조는 하지 않았다.
4. 아래의 K는 작성자 빌드의 커널 검사 결과다. 독립 리뷰 r5는 빌드와 검사를 재현했고 기록과 증인 하나를 고치라고 했다(REQUEST_CHANGES). 그 수정 뒤의 상태를 적는다. 수정은 다시 리뷰받지 않았다.

## 1. 핀

| 항목 | 값 |
| --- | --- |
| 브랜치 | `syjn99/ssz-fv-hb` (기점 `1b5f524`, `claude/ssz-fv-list-vector-20261112`의 머리) |
| ELF sha256 | `c6403c02a110ffd6fe6d31a3c89cd395ac457b5d62e60e2e611b8ab9a8dd911e` (T2와 같다) |
| objdump sha256 | `580b0da9…` (`build-ids.txt`와 같다). 새로 만들지 않고 LV 작업 디렉터리의 파일을 썼다 |
| 링크 묶음 | `lv/link-hb/RESULT`: `PASS all`, BUNDLE `66e6154a…` |
| Kraken, EthLib, Lean | LV `REPORT.md` 1절과 같다. `lake update`를 하지 않았다 |
| `.lake` | 부모 작업 트리에서 APFS 복제. 첫 `lake build E2eList`: exit 0, 749 jobs, 51 s |
| 무거운 작업 | 저장소 밖 `heavy.py`, 상한 40960 MB, 한 번에 하나 |
| 모델 | 구현 `claude-opus-5-5` |

## 2. 커버리지 (K 커널 검사, X 실행만, N 미증명)

| 경로 | 종류 | 정리 | 파일 |
| --- | --- | --- | --- |
| 링크 (a)–(f) | X | `lv/link-hb/RESULT` | `gen/e2e/hblink.py` |
| 크기 거부 | K | `hb_e2e_reject_size_main : hb_reject_size_stmt` | `E2eHb/HbReject.lean` |
| 루프 1 한 바퀴(경계 검사 둘 안 갈림) | K | `hb_iter1` | `E2eHb/HbLoop1.lean` |
| 루프 1 8192회 | K | `hb_loop1`, `hb_exit1` | `E2eHb/HbLoop1.lean` |
| 루프 2 한 바퀴 | K | `hb_iter2` | `E2eHb/HbLoop2.lean` |
| 루프 2 8192회 | K | `hb_loop2`, `hb_exit2` | `E2eHb/HbLoop2.lean` |
| 수용 | K | `hb_e2e_accept_main : hb_accept_stmt` | `E2eHb/HbAccept.lean` |
| 명세 다리 | K | `phb_serialize`, `phb_roundtrip`, `phb_accepted_is_enc`, `phb_spec_accepts_iff` | `E2eHb/HbSpec.lean` |
| 수용, 명세 | K | `hb_e2e_accept_spec_k : hb_accept_spec_stmt` | `E2eHb/HbSpecK.lean` |
| 크기 거부, 명세 | K | `hb_e2e_reject_size_spec : hb_reject_size_spec_stmt` | `E2eHb/HbSpecK.lean` |
| 거부 완전성 | K | `hb_e2e_reject_complete : hb_reject_complete_stmt` | `E2eHb/HbSpecK.lean` |
| 손 `Desc` = 생산자 `Desc` | K | `prysmHbDesc_deserialize_checker` | `E2eHb/HbDescEq.lean` |
| 수용 증인 | K | `WitHbA.hb_accept_runs` 와 구체 입력 셋(0, 대표, 0xff) | `E2eHb/WitHbA.lean` |
| 크기 거부 증인 | K | `WitHbR.hb_reject_runs` (길이 524287, 524289, 0; 리뷰 r5 M3) | `E2eHb/WitHbR.lean` |
| 공리 게이트 | X | PASS, 비표준 0, sorryAx 0 | `lv/axioms-gate-hb.json` |
| 게이트 대조군(심은 `sorry`) | X | FAIL(기대대로) | `lv/axioms-gate-hb-plant.json` |
| MarshalSSZTo, SizeSSZ, HashTreeRoot | N | 범위 밖 | |
| morestack, 쓰기 장벽 켜짐 | N | 전제가 막는다 | |
| 부정 시험(변이) | X | `negcases-hb.json` 10/10 (대조 3, 변이 7). 명세 짝과 거부 완전성의 변이는 `negcases-spec.json` | `CHECKS-HB.md` 2절, `negative-hb.json`, `negative-spec.json` |
| 선언 drift 검사 | X | 기준 `6a78c591`, 뿌리 E2e·E2eAd·E2eScal: drift 0, 심은 대조군 drift 1 | `decl-drift-hb.txt`, `decl-drift-seg.txt` |

고정 문장은 `b3cb1ca`에서 커밋했다. 그 뒤로 바꾸지 않았다. N으로 바꾼 문장은 없다.
`hb_iter2`, `hb_loop2`는 고정 문장이 아니다. 작성 중에 반환 칸 값을 결론에 더했다(5절).

## 3. 재사용 측정

### 3.1 방법

`gen/e2e/hbreuse.py`가 HB 파일의 빈 줄이 아닌 줄을 셋으로 나눈다.
"verbatim"은 T2 원본에 같은 줄이 있는 경우다.
"mechanical"은 이름 바꾸기와 숫자 바꾸기 뒤에 T2 줄과 같은 경우다.
"new"는 둘 다 아닌 경우다. 주석과 문서 줄은 따로 센다.
줄 단위 비교이고 순서를 보지 않는다. `kunfold` 같은 짧은 줄은 쉽게 verbatim이 된다.
그래서 이 수는 옮긴 글의 양이다. 증명 구조가 같다는 증거가 아니다.

### 3.2 결과 (로그 37)

| HB 파일 | T2 원본 | verbatim | mechanical | new | 주석 |
| --- | --- | --- | --- | --- | --- |
| `E2eHb/Code.lean` | `E2eList/Code.lean` | 2 | 2 | 1 | 7 |
| `E2eHb/Defs.lean` | `E2eList/Defs.lean`, `Desc.lean` | 1 | 4 | 10 | 18 |
| `E2eHb/StmtHb.lean` | `E2eList/StmtSc.lean` | 92 | 49 | 26 | 43 |
| `E2eHb/HbReject.lean` | `E2eList/ScReject.lean` | 56 | 23 | 1 | 8 |
| `E2eHb/HbLemmas.lean` | `E2eList/ScLemmas.lean` | 29 | 19 | 9 | 7 |
| `E2eHb/HbLoop1.lean` | `E2eList/ScLoop.lean` | 155 | 84 | 63 | 25 |
| `E2eHb/HbLoop2.lean` | `E2eList/ScLoop.lean` | 148 | 93 | 67 | 18 |
| `E2eHb/HbAccept.lean` | `E2eList/ScAccept.lean` | 118 | 94 | 34 | 22 |
| `E2eHb/HbSpec.lean` | `E2eList/ScSpec.lean` | 32 | 47 | 46 | 15 |
| `E2eHb/HbSpecK.lean` | `E2eList/ScSpecK.lean` | 8 | 12 | 11 | 5 |
| `E2eHb/HbSpecChecker.lean` | `E2eList/ScSpecChecker.lean` | 4 | 0 | 1 | 4 |
| `E2eHb/HbDescEq.lean` | `E2eList/ScDescEq.lean` | 6 | 25 | 4 | 9 |
| `E2eHb/WitHbA.lean` | `E2eList/WitScA.lean` | 40 | 22 | 31 | 28 |
| `gen/e2e/hblink.py` | `gen/e2e/lvlink.py` | 36 | 0 | 27 | 17 |
| `gen/e2e/hbaxioms_gate.py` | `gen/e2e/lvaxioms_gate.py` | 24 | 0 | 2 | 11 |
| `gen/e2e/AxiomsHb.lean` | `gen/e2e/AxiomsLv.lean` | 0 | 6 | 13 | 1 |
| 합계 | | 751 | 480 | 346 | 238 |
| `E2eHb/HbLoop2.lean` | `E2eHb/HbLoop1.lean` (합계 밖) | 207 | 62 | 39 | 18 |

증명 코드 줄(주석 제외) 1577줄 중 78%가 verbatim 또는 mechanical이다.
22%(346줄)가 새 글이다.

### 3.3 복사하지 않고 가져온 것

| 가져온 것 | T2 줄 | 쓰는 곳 |
| --- | --- | --- |
| `lvHdrs`, `lvElems` (`Defs.lean`) | 5 | 문장, 루프, 수용 |
| `zz`, `lvElems_snoc`, `lvHdrs_length`, `lvHdrs_snoc`, `lv_flatten_split`, `jge_false512` (`ScLemmas.lean`) | 40 | `HbLemmas`, 루프 |
| `laddr` 매크로 (`ScLoop.lean`) | 6 | 루프, 수용 |
| `headWidth_inline`, `bodyWidth_inline`, `assemble_inline_ok` (`ScSpec.lean`) | 16 | `HbSpec` |
| `BumpAllocT`, `bump_makeslice_t1`, `bump_makeslice_t24` (`BumpT.lean`, `BumpAllocT.S`) | 164 | 증인 |
| `E2eList.Data.lvSliceType_addr` | 데이터 1 | 계약 인스턴스 |

합계 약 231줄이다. 계약 인스턴스와 증인 모델은 하나도 새로 쓰지 않았다.
`E2eList.WitScA.u8_ne_slice`(3줄)는 가져오지 못하고 복사했다. 그 모듈이 자기 `Host` 인스턴스를 선언한다.

### 3.4 새로 쓴 부분과 이유

| 파일 | 새 부분 | 이유 |
| --- | --- | --- |
| `Defs` | `PHb`, `prysmHbDesc` | 새 타입이다 |
| `StmtHb` | 지역 칸 하나, 둘째 헤더, 둘째 입력, 둘째 배열과 원소, 상수 | 필드가 둘이고 틀 칸이 넷이다 |
| `HbReject` | 틀 크기 식 한 줄 | `sub $0x38` |
| `HbLemmas` | 32/8192 판 정리 셋 | T2 정리가 48/512를 문장에 고정한다 |
| `HbLoop1` | `shl $5` 두 번, `jb` 넘침 검사 안 갈림, 넷째 지역 칸, 저장 순서, `shl5` 표기 | 컴파일러가 다른 색인 계산을 냈다 |
| `HbLoop1` | `shl5` 표기 | `kshl64`가 낸 항의 폭이 `Width.W64.bits`다. `x <<< 5`와 문법이 달라 `ecancel`이 맞추지 못했다 |
| `HbLoop2` | 지시어 번호, `nop` 자리, 수신자 오프셋, `lea 0x40000`, 반환 칸 값 | 둘째 루프의 단계 열이 첫째와 다르다 |
| `HbLoop2` | 반환 칸 값 `k + 133`을 결론에 둠 | 마지막 호출이 루프 안이다. T2는 꼬리 필드가 그 칸을 다시 썼다 |
| `HbAccept` | 가운데 86–103 | 둘째 배열의 makeslice. 머리 단계의 사본이다 |
| `HbSpec` | 32바이트 판 보조정리, `v32_serialize`, `v32_of_bytes`, 두 벡터 필드의 container 정리 | T2 보조정리가 48을 고정한다. 필드 꼴이 다르다 |
| `HbSpecK` | 두 필드의 길이 보조정리 | 필드가 둘이다 |
| `WitHbA` | 메모리 배치, 주소, 두 입력 | 수신자·틀·힙 크기가 다르다 |
| `hblink.py` | 함수 이름, 형식 단어 단언 | 새 함수다 |

### 3.5 생성기가 낼 수 있는 부분

판단이다. 생성기를 만들지 않았고 시험하지 않았다.

- 그대로 낼 수 있다: `Code`, `HbSpecChecker`(이미 `lvdescterm.py`가 낸다), `HbDescEq`, `HbSpecK`, `AxiomsHb`, 링크 스크립트.
- IR과 `.S`에서 낼 수 있다: `StmtHb`(필드 오프셋, 틀 크기, 힙 합계), `HbReject`(지시어 번호와 틀 크기만 다르다), `WitHbA`의 메모리 배치.
- 크기 매개변수로 한 번 일반화하면 생성이 필요 없다: `HbLemmas`, `HbSpec`의 32바이트 보조정리.
- 지시어 단위 틀이 있으면 낼 수 있다: 루프 한 바퀴의 `kat` 열과 적재·저장 단계. 지시어 종류별 틀이 필요하다.
- 손이 필요했던 것: `shl5` 항의 정확한 꼴, `jb` 분기 부등식, 반환 칸 값을 결론에 두는 결정, 루프 불변식의 메모리 꼴.

## 4. 시간과 메모리

방법: `heavy.py` 기록, 한 번(n = 1), 표본 RSS는 그룹 합(상한 추정). 모듈 시간은 Lake 출력이다.

| 모듈 | 모듈 시간 | 벽시계 | RSS |
| --- | --- | --- | --- |
| StmtHb | 3.4 s | 9.3 s | 1.96 GiB |
| HbReject, HbLemmas | 4.5 s, 3.0 s | 6.2 s | 3.25 GiB |
| HbLoop1 | 6.8 s | 9.4 s | 2.10 GiB |
| HbLoop2 | 20 s | 22.8 s | 5.76 GiB |
| HbAccept | 7.9 s | 10.4 s | 2.52 GiB |
| HbSpec | 3.3 s | 5.2 s | 0.94 GiB |
| HbSpecK, HbDescEq | 3.5 s, 3.3 s | 8.3 s | 0.91 GiB |
| WitHbA | 15 s | 17.7 s | 2.07 GiB |

HbLoop2는 HbLoop1의 약 3배다. 원인은 상수 262144가 든 주소식 하나의 `laddr`(omega) 증명의 커널 검사다(12.2 s, `CHECKS-HB.md` 3절).
일반 루프로 다시 유도한 `hb_loop2_g`(`E2eSeg/V32Hb.lean`)는 그 상수를 변수로 두어 모듈이 6.2 s다(`REPORT-SEG.md` 1.1절).
T2(ScLoop 6.3 s, WitScA 16 s)와 비교하면 루프 1과 증인은 비슷하다.
8192회 루프도 펼치지 않는다. 귀납 증명이라 반복 수가 시간에 영향을 주지 않았다.

`maxHeartbeats`는 `WitHbA.hb_accept_runs` 하나에만 있다. 값은 2000000이다.
측정: 200000(로그 23)과 400000(로그 26)은 `whnf`에서 실패한다. 1000000(로그 25)과 2000000(로그 24, 28)은 통과한다.
원인(프로파일, 로그 27): `simp` 11.8 s(9.5 s와 2.23 s). 메모리 전제를 닫는 AC 정렬이다. T2와 같은 원인이다.
`maxRecDepth` 설정은 없다.

## 5. 시도 기록

| 의무 | 전략 수 | 사실 |
| --- | --- | --- |
| 링크 | 1 | filter, conv, data, check 모두 exit 0 |
| 문장 | 1 | 첫 빌드 exit 0 |
| 크기 거부, 보조정리 | 1 | 첫 빌드 exit 0 |
| 루프 1 | 1 | 컴파일 3회. `shl` 항의 꼴을 탐침(로그 10)으로 찾았다 |
| 루프 2 | 2 | 전략 1: 루프 1 글의 기계적 사본(로그 14, 15). 전략 2: 반환 칸 값을 결론에 둠(로그 16, 17) |
| 수용 | 1 | 첫 빌드 exit 0 |
| 명세 다리 | 1 | 컴파일 2회. 남은 `rfl` 한 줄을 지웠다 |
| 명세 짝, `Desc` 같음 | 1 | 첫 빌드 exit 0 |
| 증인 | 1 | 문법 오류 한 번(가져올 수 없는 이름), 그 뒤 heartbeat 측정 |

한 전략 안의 컴파일 반복은 시도 한 번으로 셌다. LV와 같은 해석이다.
시도 한도에 닿은 의무는 없다.

## 6. 신뢰 항목과 한계

- 계약 인스턴스는 T2와 같은 셋이다. 새 계약 꼴, 새 인스턴스 값이 없다.
- 손 `Desc`를 쓰기 전에 생산자 `Desc` 파일을 출력했다. T2보다 독립성이 약하다. 생산자 `Desc`와의 같음은 K다.
- objdump는 LV 작업 디렉터리의 파일을 다시 썼다. sha256이 `build-ids.txt`와 같다. `go tool objdump`를 다시 돌리지 않았다.
- 증인은 고정 크기 타입의 정리 하나다. 가변 길이가 없어서 빈 값, 1개, 최대의 구분이 없다.
- 증인의 구체 입력 셋은 `example`이다. 각각 정리를 구체 값에 적용해 타입 검사를 통과한다.
- `lakefile.toml`은 덧붙이기만 했다(`input_dir` 하나, `lean_lib` 하나). 루트 `AGENTS.md`는 lakefile 변경에 승인을 요구한다. 작업 지시가 덧붙이기를 허용했다.
- 게이트 대조군은 `.lake/build`에 `.olean` 하나를 잠시 넣었다. 실행 뒤 지웠다(LV와 같은 방법).
- stale 검사는 실행하지 않았다. 죽거나 상한에 걸린 빌드가 없었다.

## 7. 검증

| 검사 | 명령 | 결과 |
| --- | --- | --- |
| 링크 | `hblink.py filter`, `link/conv.py --norm`, `hblink.py data`, `link/check.py` | exit 0, `PASS all` (로그 02–06) |
| 빌드 | `lake build E2eHb` | exit 0, 642 jobs (로그 29) |
| `--no-build` | `lake build --no-build E2e E2eAd E2eScal E2eList E2eHb` | exit 0, `All targets up-to-date (1094 jobs)` (로그 30) |
| 공리 게이트 | `python3 -I -B ../gen/e2e/hbaxioms_gate.py run …` | exit 0, PASS, 선언 6364, 손 목록 476, 비표준 0, sorryAx 0 (로그 31) |
| 게이트 대조군 | 같은 명령, 심은 `E2eHb.Planted` | exit 1, FAIL, sorryAx `E2eHb.Planted.planted_sorry` (로그 35) |
| 금지 낱말 | `grep -rnE "sorry|admit|axiom |native_decide|bv_decide|maxRecDepth|maxHeartbeats" lean/E2eHb gen/e2e/hb* gen/e2e/AxiomsHb.lean` | `WitHbA.lean`의 측정된 `maxHeartbeats` 한 줄과 주석 한 줄만 |
| 홈 경로 | `grep -rnE "Users/|/home/|lv-work"` (새 파일) | 0 |
| 재사용 측정 | `python3 -I -B gen/e2e/hbreuse.py` | exit 0 (로그 37) |
| 부정 시험 | `lvnegative.py ../prysm/go1.26.10/e2e/lv/negcases-hb.json …` | exit 0, 10/10 (`CHECKS-HB.md` 2절). 명세 쪽은 `negcases-spec.json` (`REPORT-SEG.md` 5절) |
| 선언 drift | `decl_dump.lean` + `decl_drift.py` | drift 0 (`decl-drift-hb.txt`, `decl-drift-seg.txt`) |
| Go 차분 시험, 하드웨어 대조 | | 실행하지 않음. 호스트는 arm64다 |

명령과 종료 코드의 표는 `STEPS-HB.tsv`에 있다. 로그는 로컬에만 있다.

## 8. 발견 후보

- 새 production 결함 후보는 없다.
- LV-1(감싼 음수 변위)은 HB `.S`에 없다(`0xffff` 무늬 0개).
