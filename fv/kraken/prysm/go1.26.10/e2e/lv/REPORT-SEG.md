# REPORT-SEG: 구간 보조정리 일반화와 Deposit 이식

**판정: 조건부.**

조건:

1. 독립 리뷰를 받지 않았다. 아래의 K는 작성자 빌드의 커널 검사 결과다.
2. 원소 루프의 일반화는 원소 32바이트의 코드 꼴에만 있다. 48바이트 꼴(T2)은 일반화하지 않았다(4절).
3. Deposit은 크기 거부와 수용 기계 정리만 있다. 명세 짝, 증인, 부정 시험은 N이다.
4. 런타임 호출은 계약 가설이다. 새 계약 꼴과 새 인스턴스 꼴은 없다. 새 인스턴스 값은 `NewobjectC … depDataType_addr 120`이다.

먼저 한 일(1부)은 `CHECKS-HB.md`에 있다: 선언 drift 0, 부정 시험 10/10, HbLoop2 시간의 원인.

## 1. 일반화한 것 (K)

| 파일 | 정리 | 변수 | 전제 |
| --- | --- | --- | --- |
| `E2eSeg/ListG.lean` | `flat_len`, `in_split`, `arr_split`, `arr_join` | 원소 폭 w, 개수 n | `w * n ≤ 2^64`, `24 * n ≤ 2^64` |
| `E2eSeg/SegG.lean` | `bytesdec_seg_g`, `bytesdec_seg_z_g`, `bytesdec_seg_nop_g` | 고정 바이트 필드 크기 n | `n < 2^31` |
| `E2eSeg/V32.lean`, `V32Loop.lean` | `v32_iter`, `v32_exit`, `v32_loop` | 개수 n, 스택 칸 다섯, 수신자 오프셋 둘, 레이블, 원천 오프셋, `nop` 자리 넷 | `n < 2^31`, 원소 32바이트 |
| `E2eSeg/RejG.lean` | `rej_size_g` | 틀 크기 F, 크기 sz, 레이블, `nop` 하나 | `F < 2^31`, `sz < 2^31` |

- SegN의 `hn : n = 32 ∨ 48 ∨ 96`은 증명 방식의 한계였다. 리터럴 크기를 계산하는 자리가 셋이었다.
- 그 셋을 보조정리로 바꿨다: makeslice 수, memmove 수(32비트 즉시값), 저장한 len·cap 단어(64비트 즉시값).
- 루프 몸은 블록 여섯과 틈으로 나눴다. `Glue`는 틈이 비었거나 `nop` 하나임을 말한다. `GlueSrc`는 비었거나 `lea src(%rbx),%rbx`임을 말한다.
- 블록 틀은 `lv/link-hb` 지시어 36–77의 Kraken 항이다. 변하는 피연산자만 매개변수로 바꿨다.
- 일반 파일들은 `maxHeartbeats` 설정 없이 빌드된다. SegN은 16000000이 필요했다.

### 1.1 고정 인스턴스를 다시 유도함 (K)

| 손 보조정리(바꾸지 않음) | 새 이름 | 증명 |
| --- | --- | --- |
| `E2eScal.bytesdec_seg`, `bytesdec_seg_z` (n ∈ {32, 48, 96}) | `bytesdec_seg_inst`, `bytesdec_seg_z_inst` | 한 줄 (`type_of%`) |
| `E2eList.bytesdec_seg_z64`, `bytes96dec_seg_nop` | `bytesdec_seg_z64_inst`, `bytes96dec_seg_nop_inst` | 한 줄 |
| `E2eScal.H4.bytes32dec_seg_nop` | `bytes32dec_seg_nop_inst` | 한 줄 |
| `E2eList.scIn_split`, `scA_split`, `scA_join` | `scIn_split'`, `scA_split'`, `scA_join'` | 한 줄, 그리고 `rfl`로 같은 문장임을 확인 |
| `E2eHb.hbIn_split`, `hbA_split`, `hbA_join` | `hbIn_split'`, `hbA_split'`, `hbA_join'` | 한 줄, `rfl` 확인 |
| `E2eHb.hb_loop1` | `hb_loop1_g` | 약 70줄: 블록·틈 사실 읽기, 레이블, 출구 레이블 한 단계 |
| `E2eHb.hb_loop2` | `hb_loop2_g` | 약 65줄 |
| 고정 문장 `sc_reject_size_stmt` (T2) | `sc_reject_size_g` | `rej_size_g` 한 번 적용 |
| 고정 문장 `hb_reject_size_stmt` | `hb_reject_size_g` | `rej_size_g` 한 번 적용 |

- 루프 인스턴스가 한 줄이 아닌 이유: 블록 여섯과 틈 다섯의 위치를 실제 프로그램에서 읽어야 한다.
- 그 사실들은 `infix_sub`와 `simp`로 닫는다. 지시어 수에 따라 줄이 늘지 않는다.
- `hb_loop2_g` 모듈은 6.2 s다. 손 `HbLoop2`는 22.8 s였다(`CHECKS-HB.md` 3절의 상수 262144 문제가 없다).

## 2. 생성한 것 (b): 없음

- 생성기 `gen/e2e/lvseggen.py`는 만들지 않았다. 범위 안의 반복은 모두 일반화로 닫혔다.
- 일반화하지 않은 것과 이유(시도하지 않았다, 실패 로그 없음):
  - 원소 48바이트 루프(T2 `ScLoop`). 컴파일러가 다른 명령어 열을 낸다(`lea (x,x,2)`, `shl $4`). 매개변수가 아니라 다른 꼴이다.
  - 원소 크기를 shift 수로 매개화하는 것. `kshl64`는 리터럴 shift 수를 요구한다. 이 가족의 원소는 모두 32바이트다(4절).
- 다른 꼴이 필요하면 같은 방법(블록 틀과 틈)으로 그 꼴의 일반 정리를 한 번 쓰면 된다. 판단이다.

## 3. 증명 사용: Deposit (c)

선정: `HistoricalBatch`와 같은 가족(`[][]byte`로 된 `Vector[Bytes32, N]` 필드)이다.
금지 타입이 아니고 기존 증명이 없다.
포인터 필드가 없는 같은 가족은 HistoricalBatch와 SyncCommittee뿐이다.
Deposit의 포인터 필드(Deposit_Data)는 디코더 증명(`E2eScal.H4.dd_e2e_accept_main`)이 이미 있다.

| 의무 | 종류 | 정리 또는 파일 |
| --- | --- | --- |
| 링크 (a)–(f) | X | `lv/link-dep/RESULT` PASS all, 묶음 `bd37b3f9…` (`gen/e2e/deplink.py`) |
| 고정 문장 | 커밋 `57316a9` | `E2eDep/Stmt.lean`: `dep_reject_size_stmt`, `dep_accept_stmt` |
| 크기 거부 | K | `dep_e2e_reject_size_main`, `rej_size_g` 한 번 적용, 첫 빌드 통과 |
| 수용 | K | `dep_e2e_accept_main`: 루프는 `v32_loop`(n = 33), Deposit_Data는 `dd_e2e_accept_main` |
| 명세 다리, 명세 짝, Desc 같음 | N | 하지 않음 |
| 수용 증인 | N | 하지 않음 |
| 부정 시험 | N | 하지 않음 |

수용 정리의 `maxHeartbeats`는 800000이다. 200000은 실패, 400000과 800000은 통과(로그 95–97).
원인(로그 98): 한 선언의 길이다. 전술 실행 3.37 s, `simp` 1.11 s, 커널 검사 1.58 s다.

### 3.1 줄 수 (`gen/e2e/segreuse.py`, 로그 103)

| Deposit 파일 | 원본 | verbatim | mechanical | new | 주석 |
| --- | --- | --- | --- | --- | --- |
| `E2eDep/Code.lean` | `E2eHb/Code.lean` | 2 | 2 | 4 | 11 |
| `E2eDep/Stmt.lean` | `E2eHb/StmtHb.lean` | 42 | 14 | 53 | 34 |
| `E2eDep/Reject.lean` | `E2eHb/HbReject.lean` | 2 | 4 | 16 | 2 |
| `E2eDep/Accept.lean` | `E2eHb/HbAccept.lean`, `E2eSeg/V32Hb.lean` | 141 | 86 | 154 | 25 |
| `gen/e2e/deplink.py` | `gen/e2e/hblink.py` | 54 | 4 | 9 | 18 |
| 합계 | | 241 | 110 | 236 | 90 |

- HB의 새 줄은 346이었다(`REPORT-HB.md` 3.2). Deposit은 236이다.
- 루프 증명을 위해 새로 쓴 줄은 0이다. 루프 사용은 `v32_loop` 적용과 블록·틈 사실 약 45줄이다.
- HB에서 루프 둘은 손으로 610줄(HbLoop1 302, HbLoop2 308)이었다.
- 크기 거부는 16줄이다(HB 80줄의 손 증명).
- 새 줄의 대부분은 이 가족 밖의 일이다: `new(Deposit_Data)`, 위임 호출, 피호출자 틀을 우리 scratch로 나누기(약 120줄), 문장의 피호출자 필드.

### 3.2 HB에서 없어질 줄

일반 정리를 쓰면 다음 손 파일의 코드 줄이 필요 없다(`segreuse.py` 2부).

| 손 파일 | 코드 줄 | 대신 |
| --- | --- | --- |
| `E2eHb/HbLemmas.lean` | 57 | `ListG` 적용, 0줄 |
| `E2eHb/HbLoop1.lean` | 302 | `hb_loop1_g` 형식의 적용, 약 70줄 |
| `E2eHb/HbLoop2.lean` | 308 | `hb_loop2_g` 형식의 적용, 약 65줄 |
| `E2eHb/HbReject.lean` | 80 | `rej_size_g` 적용, 약 15줄 |
| 합계 | 747 | 약 150 |

일반 파일 자체는 1097 코드 줄이다(ListG 65, SegG 494, V32 87, V32Loop 327, RejG 124). 한 번만 쓴다.

## 4. 손으로 남은 것과 이유

- 함수 머리(크기 확인 뒤 배열 makeslice, 헤더 저장)와 꼬리. 필드 수와 수신자 배치에 따라 명령어 열이 다르다. 다음 후보는 `rejHead` 같은 머리 틀이다(하지 않음).
- 위임 호출과 피호출자 틀의 배치(Deposit 약 120줄). T3와 같은 일이다. 일반화하지 않았다.
- 문장(`Stmt`). 수신자와 틀의 칸 목록은 타입마다 다르다. IR과 `.S`에서 낼 수 있다고 본다(판단).
- 명세 쪽(`HbSpec` 꼴). `ListG`처럼 폭으로 매개화할 수 있다고 본다. 하지 않았다.
- 원소 48바이트 루프(2절).

## 5. 검증

| 검사 | 결과 |
| --- | --- |
| `lake build E2eHb E2eSeg E2eDep` | exit 0, 730 jobs (로그 100) |
| `lake build --no-build E2e E2eAd E2eScal E2eList E2eHb E2eSeg E2eDep` | exit 0, `All targets up-to-date (1124 jobs)` (로그 101) |
| 공리 게이트 `gen/e2e/segaxioms_gate.py` | exit 0, PASS, 선언 6627, 손 목록 502, 비표준 0, sorryAx 0 (로그 102, `axioms-gate-seg.json`) |
| 게이트 대조군 | 이 스크립트로는 다시 돌리지 않았다. 같은 게이트 코드의 대조군은 `axioms-gate-hb-plant.json`(FAIL, 기대대로) |
| 금지 낱말 | `E2eDep/Accept.lean`의 측정된 `maxHeartbeats` 한 줄만 |
| 홈 경로 | 새 파일에 0 |
| 선언 drift(1부) | 기준 `6a78c591`, drift 0 (`decl-drift-hb.txt`). 그 뒤 커밋은 E2e·E2eAd·E2eScal을 바꾸지 않았다 |
| Go 차분 시험, 하드웨어 대조 | 실행하지 않음 |

명령과 종료 코드는 `STEPS-SEG.tsv`에 있다. 로그는 로컬에만 있다.

## 6. 신뢰 항목과 한계

- `depDataType_addr`는 손으로 쓴 정의다. 값은 `link-dep/data/depDataType.data`의 `at` 줄이고 형식은 LV 읽개의 형식이다. 읽개의 도움 함수가 모듈 밖에 보이지 않아서다. 그 데이터 파일은 `check.py` (f)가 ELF와 대조했다.
- 블록 틀이 실제 코드와 같음은 각 인스턴스에서 `infix_sub`로 검사된다. 틀 자체는 신뢰 대상이 아니다.
- `lakefile.toml`은 덧붙이기만 했다(`lean_lib` E2eSeg, `input_dir` 둘, `lean_lib` E2eDep).
- 줄 분류는 줄 단위이고 순서를 보지 않는다(`hbreuse.py`의 한계).
