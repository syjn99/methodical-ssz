# REPORT-SEG: 구간 보조정리 일반화와 Deposit 이식

**판정: 조건부.**

조건:

1. 독립 리뷰를 받지 않았다. 아래의 K는 작성자 빌드의 커널 검사 결과다.
2. 원소 루프는 두 코드 꼴이다: 32바이트 꼴(`v32_*`)과 `3·2^k` 꼴(`vtri_*`, w ∈ {24, 48, 96}). 다른 꼴은 일반화하지 않았다(4절).
3. `vtri_*`의 w = 24, 96 인스턴스는 틀에 대해서만 증명했다. 이 ELF에 그 크기의 실제 코드가 없어 틀과 실제 코드의 같음은 확인하지 못했다.
4. 런타임 호출은 계약 가설이다. 새 계약 꼴과 새 인스턴스 꼴은 없다. 새 인스턴스 값은 `NewobjectC … depDataType_addr 120`이다.

먼저 한 일(1부)은 `CHECKS-HB.md`에 있다: 선언 drift 0, 부정 시험 10/10, HbLoop2 시간의 원인.
2차 작업(Deposit 마감, T2 루프 일반화, 원소 크기 매개변수)은 3절, 1절, 2절, 7절에 반영했다.

## 1. 일반화한 것 (K)

| 파일 | 정리 | 변수 | 전제 |
| --- | --- | --- | --- |
| `E2eSeg/ListG.lean` | `flat_len`, `in_split`, `arr_split`, `arr_join` | 원소 폭 w, 개수 n | `w * n ≤ 2^64`, `24 * n ≤ 2^64` |
| `E2eSeg/SegG.lean` | `bytesdec_seg_g`, `bytesdec_seg_z_g`, `bytesdec_seg_nop_g` | 고정 바이트 필드 크기 n | `n < 2^31` |
| `E2eSeg/V32.lean`, `V32Loop.lean` | `v32_iter`, `v32_exit`, `v32_loop` | 개수 n, 스택 칸 다섯, 수신자 오프셋 둘, 레이블, 원천 오프셋, `nop` 자리 넷 | `n < 2^31`, 원소 32바이트 |
| `E2eSeg/RejG.lean` | `rej_size_g` | 틀 크기 F, 크기 sz, 레이블, `nop` 하나 | `F < 2^31`, `sz < 2^31` |
| `E2eSeg/VTri.lean`, `VTriLoop.lean` | `vtri_iter`, `vtri_exit`, `vtri_loop` | 개수 n, 스택 칸 다섯, 수신자 오프셋 둘, 레이블, 원천 오프셋, 틈, 원소 크기 (k, w) | `n < 2^31`, `TriSize k w`(w = 3·2^k, k ∈ {3, 4, 5}) |
| `E2eSeg/SpecG.lean` | `vN_flatten_length`, `vN_serialize`, `vN_of_bytes` | `Vector[Bytes32, n]`의 n | `32 * n < 2^32` |

- SegN의 `hn : n = 32 ∨ 48 ∨ 96`은 증명 방식의 한계였다. 리터럴 크기를 계산하는 자리가 셋이었다.
- 그 셋을 보조정리로 바꿨다: makeslice 수, memmove 수(32비트 즉시값), 저장한 len·cap 단어(64비트 즉시값).
- 루프 몸은 블록 여섯과 틈으로 나눴다. `Glue`는 틈이 비었거나 `nop` 하나임을 말한다. `GlueSrc`는 비었거나 `lea src(%rbx),%rbx`임을 말한다.
- 블록 틀은 `lv/link-hb` 지시어 36–77의 Kraken 항이다. 변하는 피연산자만 매개변수로 바꿨다.
- `ListG`, `SegG`, `V32`, `V32Loop`, `RejG`, `SpecG`는 설정 없이 빌드된다. SegN은 `maxHeartbeats` 16000000이 필요했다.
- `VTriLoop`의 `vtri_iter`에는 `maxHeartbeats` 800000이 있다(옵션 목록은 5.1절).

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
| `E2eList.sc_loop` (T2) | `sc_loop_g` | `vtri_loop`(k = 4, w = 48) 적용, 약 80줄, 첫 빌드 통과 |
| `E2eHb.v32_serialize`, `v32_flatten_length`, `v32_of_bytes` | `example` 셋 | 한 줄 (`SpecG`) |
| 고정 문장 `hb_reject_size_stmt` | `hb_reject_size_g` | `rej_size_g` 한 번 적용 |

- 루프 인스턴스가 한 줄이 아닌 이유: 블록 여섯과 틈 다섯의 위치를 실제 프로그램에서 읽어야 한다.
- 그 사실들은 `infix_sub`와 `simp`로 닫는다. 지시어 수에 따라 줄이 늘지 않는다.
- `hb_loop2_g` 모듈은 6.2 s다. 손 `HbLoop2`는 22.8 s였다(`CHECKS-HB.md` 3절의 상수 262144 문제가 없다).

## 2. 생성한 것 (b)와 원소 크기

생성기는 만들지 않았다. 남은 반복은 모두 일반화와 리터럴 가족으로 닫혔다.

T2의 48바이트 루프: 두 명령어 열을 한 문장으로 덮지 않았다.
32바이트 꼴은 넘침 검사(`jb`)와 지역 칸 넷이 있다. `3·2^k` 꼴은 넘침 검사가 없고 `3i`를 저장한 뒤 `shl $k`한다.
블록의 길이와 레지스터가 달라서 틀 하나로 쓸 수 없다. 그래서 두 번째 일반 루프(`vtri_*`)를 썼다.
그 루프로 `sc_loop`를 다시 유도했다(`sc_loop_g`, K).

원소 크기를 매개변수로 두는 일: `kshl64`가 요구하는 것은 다음 둘이다.

- shift 수가 숫자 리터럴이어야 한다. `count == 0` 분기를 `decide`로 정한다.
- `(BitVec.extractLsb' 0 8 (k : BitVec 64)).toNat &&& 63 = k`를 `decide`로 다시 쓴다.

또 크기 w가 단계 안에 숫자로 들어간다: makeslice·memmove 수(`by rfl`), len·cap 저장 값(`decide`), 원천 주소 `buf + w·i`(`omega`).
변수 k, w로 하면 `i * 2^k` 꼴의 비선형 식이 생겨 `omega`가 닫지 못한다. 시도하지 않았다(판단).
그래서 `3·2^k` 꼴은 리터럴 가족 `TriSize`(w ∈ {24, 48, 96})로 문장 하나, 증명 글 하나(`vtri_iter_body`)를 쓴다.
32바이트 꼴은 w = 32 하나다. 이 ELF의 같은 가족 타입은 모두 32바이트다.

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
| 손 Desc, 고정 명세 문장 | 커밋 `bf2ebe7` | `E2eDep/SpecStmt.lean`: `prysmDepDesc`(생산자 Desc 출력 전에 작성), `dep_accept_spec_stmt`, `dep_reject_size_spec_stmt`, `dep_reject_complete_stmt` |
| 명세 다리 | K | `dep_serialize`, `dep_roundtrip`, `dep_accepted_is_enc`, `dep_spec_accepts_iff` (`E2eDep/Spec.lean`) |
| 명세 짝 | K | `dep_e2e_accept_spec_k`, `dep_e2e_reject_size_spec`, `dep_e2e_reject_complete` |
| 손 Desc와 생산자 Desc의 codec 같음 | K | `prysmDepDesc_deserialize_checker`: 모든 bs, v에 대해 `deserialize prysmDepDesc bs = .ok v ↔ deserialize depCheckerDesc bs = .ok v`. 두 Desc는 필드 이름만 다르다(중첩 container 포함). 생산자 파일 sha256 `cd4b71f0…` = 검사기 기록 |
| 증인 | K | `WitR.dep_reject_runs`(길이 1239, 1241, 0), `WitA.dep_accept_runs`(0, 대표, 0xff). 새 증인 모델 `BumpNew120` |
| 부정 시험 | X | `negcases-dep.json` 9/9: 대조 2, 변이 7(문장·코드 크기, 루프 상한, 원소 크기, Data 오프셋·길이, 힙 양) |
| `depDataType_addr` 검사 | X | `gen/e2e/depcheck_data.py`: SAME. 자체 시험(심은 오프셋)은 기대대로 다름 |

`WitA`의 설정: `maxRecDepth` 2000(512 실패, 1000 통과), `maxHeartbeats` 4000000(1000000 실패, 2000000 통과). 원인은 `simp` 정렬 20.1 s다(로그 115–122).
루프·원소 크기 변이는 블록 사실(`infix_sub`의 `decide`)에서 실패한다. 루프 증명은 일반 정리라서 변이 대상이 아니다.

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

범위: 위 표는 Deposit 파일 다섯을 HB 원본과 비교했다(이름 바꾸기 HB → Deposit, `segreuse.py` 1부).
`REPORT-HB.md` 3.2의 346은 다른 범위다: HB 파일 16개를 T2 원본과 비교했다(이름 바꾸기 T2 → HB).
같은 범위(같은 파일 종류)로 맞춘 수는 다음과 같다(`segreuse.py` 3부, 로그 151).

| 범위 | HB new (참조 T2) | Deposit new (참조 HB) |
| --- | --- | --- |
| 코드 포함 | 1 | 4 |
| 기계 문장 | 26 | 53 |
| 크기 거부 | 1 | 16 |
| 루프 1 | 63 | 0 (일반 정리, 파일 없음) |
| 루프 2 | 67 | 0 (일반 정리, 파일 없음) |
| 수용 | 34 | 154 |
| 링크 스크립트 | 27 | 9 |
| 합계 | 219 | 236 |

- 참조와 이름 바꾸기 표가 다르다. 두 수는 "앞 타입에서 옮겨지지 않은 줄"만 말한다.
- 루프의 새 줄은 0이 되었다. HB는 루프 둘에 130줄이었다. Deposit의 루프 사용(블록 사실과 적용, 약 60줄)은 수용 154줄 안에 있다.
- 크기 거부는 HB 1줄(80줄 사본의 이름 바꾸기)에서 Deposit 16줄(일반 정리 한 번 적용)이 되었다. 거부 증명 전체는 80줄에서 22줄이 되었다.
- 같은 범위의 새 줄 합계는 줄지 않았다(219 → 236). 늘어난 곳은 수용(위임 호출, 약 120줄)과 문장(피호출자 필드)이다. 둘 다 HB에 없던 일이다.

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
- 명세 쪽의 container 조립(`dep_serialize`, `dep_toValue_surjective`). 필드 꼴이 타입마다 다르다. 벡터 필드 부분은 `SpecG`로 일반화했다.
- 32바이트 꼴의 다른 원소 크기, 그리고 두 꼴 밖의 루프 꼴(2절).

## 5. 검증

| 검사 | 결과 |
| --- | --- |
| `lake build E2eHb E2eSeg E2eDep` | exit 0, 730 jobs (로그 100) |
| `lake build --no-build E2e E2eAd E2eScal E2eList E2eHb E2eSeg E2eDep` | exit 0, `All targets up-to-date (1124 jobs)` (로그 101) |
| 공리 게이트 `gen/e2e/segaxioms_gate.py` | exit 0, PASS, 선언 6627, 손 목록 502, 비표준 0, sorryAx 0 (로그 102, `axioms-gate-seg.json`). 이 json은 `axioms-gate-seg2.json`과 리뷰 r5 뒤의 `axioms-gate-seg2-r5.json`이 대체한다. 옛 파일은 고치지 않았다 |
| 게이트 대조군 | 이 스크립트로는 다시 돌리지 않았다. 같은 게이트 코드의 대조군은 `axioms-gate-hb-plant.json`(FAIL, 기대대로) |
| 금지 낱말 | `sorry`, `admit`, 새 `axiom`, `native_decide`, `bv_decide`: 0. 측정된 옵션 넷만 있다(5.1절) |
| 홈 경로 | 새 파일에 0 |
| 선언 drift(1부) | 기준 `6a78c591`, drift 0 (`decl-drift-hb.txt`). 그 뒤 커밋은 E2e·E2eAd·E2eScal을 바꾸지 않았다 |
| 2차: `--no-build` 8개 라이브러리(E2eDepW 포함) | exit 0, 1150 jobs (로그 135) |
| 2차: 공리 게이트 `gen/e2e/seg2axioms_gate.py` | PASS, 선언 6851, 손 목록 517, 비표준 0, sorryAx 0 (로그 136, `axioms-gate-seg2.json`) |
| 2차: 게이트 대조군(심은 `E2eDep.Planted`) | FAIL(기대대로), sorryAx `E2eDep.Planted.planted_sorry` (로그 138, `axioms-gate-seg2-plant.json`) |
| 2차: 선언 drift (기준 `6a78c591`, 뿌리 E2e·E2eAd·E2eScal) | drift 0. 대조군(덤프 사본의 해시 하나) drift 1 (로그 139–141, `decl-drift-seg.txt`) |
| Go 차분 시험, 하드웨어 대조 | 실행하지 않음 |

명령과 종료 코드는 `STEPS-SEG.tsv`에 있다. 로그는 로컬에만 있다.

### 5.1 측정된 옵션 (전부)

| 위치 | 옵션 | 값 | 측정(실패 / 통과) | 원인 |
| --- | --- | --- | --- | --- |
| `E2eDep/Accept.lean`, `dep_e2e_accept_main` | `maxHeartbeats` | 800000 | 200000 실패 / 400000, 800000 통과 (로그 95–97) | 한 선언의 길이: 전술 3.37 s, `simp` 1.11 s, 커널 1.58 s (로그 98) |
| `E2eSeg/VTriLoop.lean`, `vtri_iter` | `maxHeartbeats` | 800000 | 200000 실패(셋째 경우) / 400000, 800000 통과 (로그 130–132) | 경우 나누기가 증명 글을 크기마다 한 번, 모두 세 번 돈다 |
| `E2eDepW/WitA.lean`, `dep_accept_runs` | `maxHeartbeats` | 4000000 | 200000, 1000000 실패 / 2000000, 4000000 통과 (로그 115, 120, 121) | `simp` AC 정렬 20.1 s (로그 122) |
| `E2eDepW/WitA.lean`, `P_len`, `hk308`, `hk324`, `hk330` | `maxRecDepth` | 2000 | 512(기본) 실패 / 1000, 2000, 5000, 20000 통과 (로그 115, 117–119, 파일 전체 설정으로 잼) | 356 지시어 Host 위의 목록 계산. 리뷰 r5 S2 뒤 선언마다 둔다(로그 145) |
| `E2eHb/WitHbA.lean`, `hb_accept_runs` (HB 작업) | `maxHeartbeats` | 2000000 | 200000, 400000 실패 / 1000000 통과 | `REPORT-HB.md` 4절 |

### 5.2 시도 기록 (리뷰 r5 S5)

| 단위 | 빌드(실패 / 통과) | 전략 수 | 사실 |
| --- | --- | --- | --- |
| `SegG` + `ListG` | 3 / 2 (로그 48, 52–55) | 1 | `omega`의 비선형 항, 남은 `rfl`, `type_of%` 인스턴스 바인더 |
| `V32` | 2 / 1 (로그 56–58) | 1 | `Directive` 형 이름, `nop` 단계의 `whnf` |
| `V32Loop` | 1 / 2 (로그 59–61) | 1 | 출구의 플래그 식 |
| `V32Hb` | 3 / 2 (로그 62–66) | 2 | 전략 1: 루프 1. 전략 2: 루프 2(`lea` 틈 읽기, 반환 칸 값) |
| `RejG` | 4 / 1 (로그 68–72) | 1 | `open` 오류, 주소식의 `OfNat` 원자, 마지막 rsp 식 |
| `E2eDep.Accept` | 11 / 1 (로그 83–94; 93은 탐침) | 1 | 단계별로 증명을 늘렸다. 실패는 탐침(`done`), 이름 충돌, 인수 수, 주소 식이다 |
| `VTriLoop` | 3 / 1 (로그 128–130, 133) + 옵션 측정 (131, 132) | 1 | 저장 값의 `OfNat` 꼴, `maxHeartbeats` |

- 탐침 빌드 둘(로그 93, 129)은 목표의 꼴을 보려고 파일을 잠시 바꿨다. 로그 129의 탐침은 두 경우를 `sorry`로 두었다. 그 상태는 커밋하지 않았고 어떤 주장의 근거도 아니다. 빌드 뒤 바로 되돌렸다.
- 한 전략 안의 컴파일 반복은 시도 한 번으로 셌다. LV와 HB와 같은 해석이다.
- 이 해석에서 3전략 한도에 닿은 단위는 없다. 빌드 횟수로 세면 `RejG`와 `E2eDep.Accept`가 3을 넘는다.

### 5.3 기록만 (리뷰 r5 S3)

- Lake `input_dir` `lv_dep_data`는 선언했지만 그것을 읽는 Lean 파일이 없다. `depDataType_addr`는 손 정의다(6절).
- 객체 크기 120은 데이터 파일(`Size_ = 0x78`)을 읽어서 정했다. Lean 정리는 이 값을 데이터 파일에 묶지 않는다. `NewobjectC … 120`은 문장의 가설이다.

## 6. 신뢰 항목과 한계

- `depDataType_addr`는 손으로 쓴 정의다. 값은 `link-dep/data/depDataType.data`의 `at` 줄이고 형식은 LV 읽개의 형식이다. 읽개의 도움 함수가 모듈 밖에 보이지 않아서다. `gen/e2e/depcheck_data.py`가 둘의 같음을 검사한다(SAME). 그 데이터 파일은 `check.py` (f)가 ELF와 대조했다.
- 블록 틀이 실제 코드와 같음은 각 인스턴스에서 `infix_sub`로 검사된다. 틀 자체는 신뢰 대상이 아니다.
- `lakefile.toml`은 덧붙이기만 했다(`lean_lib` E2eSeg, `input_dir` 둘, `lean_lib` E2eDep).
- 줄 분류는 줄 단위이고 순서를 보지 않는다(`hbreuse.py`의 한계).

## 7. 같은 가족의 다음 타입에 드는 손 줄

Deposit에서 쓴 손 코드 줄을 부분별로 쟀다(`gen/e2e/segcost.py`, 로그 142). 주석과 빈 줄은 뺐다. 측정은 한 타입이다.

| 부분 | 코드 줄 |
| --- | --- |
| 문장(기계) | 109 |
| 문장(명세) + 손 Desc | 113 |
| 크기 거부 증명 | 22 |
| 수용: 보조(scratch·객체 나누기) | 42 |
| 수용: 머리 단계(지시어 0–40) | 113 |
| 수용: 루프 사용(블록 사실, `v32_loop` 적용) | 60 |
| 수용: Data 객체, 위임 호출, 끝 | 166 |
| 명세 다리 + 짝 + Desc 같음 | 150 |
| 증인(거부, 수용) + newobject 모델 | 201 |
| 코드 포함 | 8 |
| 링크 스크립트 | 85 |
| 합계 | 1069 |

- 루프 증명과 거부 증명에 드는 줄은 각각 약 60, 22다. 일반 정리 이전에는 루프 하나가 약 300줄이었다.
- 위임 호출(166)과 증인(201)이 가장 크다. 둘 다 타입마다 다른 틀 배치와 메모리 배치를 손으로 적는다.
- 문장(222)은 IR과 `.S`에서 낼 수 있다고 본다(판단, 시험하지 않음).
- 링크 스크립트는 앞 스크립트의 사본이다(85줄 중 새 줄 9, 3.1절).

## 8. 사용자를 위한 것

- `lakefile.toml`에 덧붙였다: `lean_lib` 넷(E2eHb, E2eSeg, E2eDep, E2eDepW), `input_dir` 넷(`lv_hb_norm_S`, `lv_dep_norm_S`, `lv_dep_data`, `lv_dep_lean_S`). 루트 `AGENTS.md`는 lakefile 변경에 승인을 요구한다.
- 새 인스턴스 값: `NewobjectC Heap depDataType_addr 120`(기존 꼴). 증인 모델 `BumpNew120`(`E2eDepW/BumpNew120.S`)을 더했다.
- 이 브랜치의 기점 `1b5f524`는 LV 브랜치의 리뷰 r4 수정보다 앞선다. 합치기 전에 병합이 필요하다.
- 같은 가족의 다음 타입 비용은 7절의 1069줄(한 타입 측정)이다.

