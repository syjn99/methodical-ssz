# REVIEW R5: 두 대상

리뷰어 모델은 `claude-fable-5-2`다.
리뷰어는 증명을 쓰지 않은 새 세션이다. r1–r4 리뷰어가 아니다.
리뷰어는 `git archive`의 scratch 사본 둘에서 확인했다.
이 파일은 리뷰어의 보고를 계획 담당이 옮겨 적은 것이다. 리뷰 로그는 로컬에만 있다.
이 파일의 커밋은 리뷰 뒤의 문서 변경이다.

## 대상 2: 이 브랜치, `9e2272b..4d42634` (리뷰 r4 권장 수정)

**판정: APPROVE.** 필수 수정은 없다.

- 수정 S1–S9는 실제로 반영됐다. 다른 변경은 없다(파일 13개).
- 커널 검사(리뷰어의 빌드): `lake build E2e E2eAd E2eScal E2eList` exit 0, 1082 jobs. `WitIaR2`, `WitIaR`, `WitIaA`, `WitSaA`, `WitScA`는 소스에서 빌드했다. 나머지는 재생했다.
- 실행 검사: 공리 게이트 PASS, 선언 6451, 비표준 0, `sorryAx` 0. `axioms-gate-lv-t3-r4.json`과 바이트 단위로 같다.
- r4 리뷰어의 덤프 대비: ADDED 49, CHANGED 0, REMOVED 0.
- 부정 시험 14개 모두 통과(대조군 5, inside 9).

권장 수정:

| ID | 내용 |
| --- | --- |
| T2-S1 | 사례 `lv-ia-nz-mis-no-he0nz`는 `intro`에서 실패한다. 어떤 바인더를 빼도 실패한다. `e0 ≠ 0`이 필요함을 시험하지 않는다 |
| T2-S2 | P2 기계 정리 `ia_e2e_reject_offset_main`을 직접 겨눈 변이가 없다 |
| T2-S3 | `REPORT.md` 2절은 게이트 결과로 `axioms-gate-lv-t3.json`을 든다. 현재 것은 `axioms-gate-lv-t3-r4.json`이다 |

실행하지 않은 것: 기준 대비 drift, 링크 검사, 게이트·drift 대조군, `stale_olean.py`, 옮긴 옵션의 문턱, Go 차분 시험, 하드웨어 대조.

## 대상 1: 브랜치 `syjn99/ssz-fv-hb`, `1b5f524..a1c5191` (HB, 일반화 보조정리, Deposit)

**판정: REQUEST_CHANGES.** 증명 결함은 찾지 못했다. 필수 수정은 3개다.
그 브랜치는 이 브랜치에 병합되지 않았다. 그 보고서는 그 브랜치에 있다.

| ID | 내용 |
| --- | --- |
| M1 | `REPORT-SEG.md`의 두 기록이 틀리다. 일반 파일에 `maxHeartbeats`가 없다고 쓰지만 `VTriLoop.lean:214`에 800000이 있다. 5절은 옵션을 하나만 든다 |
| M2 | `REPORT-SEG.md` 3.1절은 범위가 다른 두 수를 비교한다(HB 346은 파일 16개, Deposit 236은 파일 5개). 같은 범위의 HB 값은 219다 |
| M3 | `hb_e2e_reject_size_main`에 증인이 없고 `REPORT-HB.md`가 그것을 적지 않는다 |

리뷰어가 다시 확인한 것(요약):

- 커널 검사: 라이브러리 8개 빌드 exit 0, 1150 jobs. 새 모듈 38개는 소스에서 빌드했다.
- 실행 검사: 공리 게이트 둘, drift 0(대조군 1), 부정 시험 HB 10/10과 Deposit 9/9, 링크 묶음 둘의 `check.py`, 재사용·비용 스크립트. 모두 커밋된 결과와 같다.
- 읽기 판단: 주 정리 10개는 고정 def를 형으로 가진다. 일반화는 실제 일반화다. `type_of%` 재유도는 건전하다. 계약은 기존 꼴뿐이다.

권장 수정 10개와 사용자 항목은 워커에게 보냈다.
사용자 항목: lakefile 덧붙임(`lean_lib` 4, `input_dir` 4), 새 인스턴스 값 `NewobjectC … 120`, 두 브랜치의 병합.
