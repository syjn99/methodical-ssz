# REVIEW R3: LV (`650b1f5`, 변경분 `d169e4b..650b1f5`, 기준 `6a78c59`)

**판정: APPROVE.**
필수 수정은 없다. 권장 수정은 2개다.
리뷰어 모델은 `claude-fable-5-2`다.
리뷰어는 증명을 쓰지 않은 새 세션이다. r1, r2 리뷰어가 아니다.
리뷰어는 `git archive 650b1f5`의 scratch 사본에서 확인했다.
`.lake/packages`는 작업 트리에서 복사했다. `.lake/build`는 r2 리뷰어의 소스 빌드(`d169e4b`)에서 복사했다.
이 파일은 리뷰어의 보고를 계획 담당이 옮겨 적은 것이다. 리뷰 로그는 로컬에만 있다.
이 파일의 커밋과 N1, N2 수정은 리뷰 뒤의 문서 변경이다. 그 변경은 리뷰받지 않았다.

## 1. r2 항목의 상태

M1, M2, S1, S2, S3, S4, S5: 모두 닫혔다.

## 2. 권장 수정

| ID | 내용 |
| --- | --- |
| N1 | `REPORT.md` 4절은 WitSaA, WitScA 행이 수정 뒤의 값이라고 쓴다. 두 칸이 로그와 다르다. WitSaA 벽시계 15.7 s는 로그 96에서 17.7 s다. WitScA RSS 2.07 GiB는 로그 97에서 2.06 GiB다 |
| N2 | `negative-lv.json`은 r2 수정 뒤 새로 만들지 않았다. 받아들일 수 있다. 부정 사례는 Wit 모듈을 쓰지 않는다. 리뷰어가 다시 돌렸고 결과는 같다 |

## 3. 리뷰어가 다시 확인한 것

커널 검사(리뷰어의 빌드):

- `lake build E2e E2eAd E2eScal E2eList`: exit 0, 1036 jobs, 24.0 s. Built 2(`WitSaA` 14 s, `WitScA` 17 s), Replayed 284.
- `--no-build`: exit 0, 1036 jobs.
- `WitSaA`는 `maxHeartbeats 2000000`으로, `WitScA`는 4000000으로 컴파일된다. `maxRecDepth` 설정은 없다.
- 한계: 다른 모듈은 r2 리뷰어의 빌드에서 재생했다. 그 소스는 r2의 트리와 바이트 단위로 같다.

실행 검사(리뷰어의 실행):

- 공리 게이트: PASS, 선언 5632, 정리 4684, 손 목록 462, 비표준 0, `sorryAx` 0. 커밋된 `axioms-gate-lv-r2.json`과 같다.
- 선언 덤프는 작성자의 덤프와 바이트 단위로 같다. drift 0 (5007 = 5007).
- 부정 시험 26개: 25개 통과(대조군 7, inside 18), outside 1개(`lv-sa-bitslen63`). 사례별로 초 칸 말고 모든 칸이 커밋된 `negative-lv.json`과 같다.
- `git diff d169e4b 650b1f5 -- fv/kraken/lean`은 `WitSaA.lean`과 `WitScA.lean`뿐이다. 정리 문장과 def는 바뀌지 않았다.
- `git diff dfc8b93 650b1f5`는 `StmtSa`, `StmtSc`, `Defs`, `Desc`, `Code`, `Data`, `Include`, `lv/link/`에 대해 비어 있다.
- 변경분의 Lean에 금지 토큰이 없다.
- 이력: `d169e4b`는 `650b1f5`의 조상이다. 새 커밋 4개뿐이다.
- 커밋된 파일에 홈 경로, 실행 디렉터리, 세션 id가 없다.
- objdump 개수: TEXT 함수 641(UnmarshalSSZ 211, MarshalSSZTo 211, SizeSSZ 211, MarshalSSZ 6, ValidateBitvector 1, ValidateBitlist 1). 좁은 무늬 153개, 넓은 무늬 161개, 함수 104개(67 + 37). 커밋된 `.S` 222개에는 두 무늬가 없다.
- `STEPS.tsv` 96–102행은 `heavy.py` 기록, 로그와 맞다.

읽기 판단:

- 고쳐 쓴 `example` 둘은 실제 검사다. 형은 `sc_accept_runs`를 같은 인수에 적용한 형이다. 전제는 증명한다. 가정하지 않는다.
- `example`은 선언을 만들지 않는다. 같은 덤프는 `example`에 대한 증거가 아니다. 증거는 위의 빌드다.
- `maxHeartbeats` 값은 리뷰어 r2가 잰 통과 값의 두 배다. 원인과 문턱이 옵션 옆에 적혀 있다. 문턱은 리뷰어 측정으로 표시돼 있다.
- `REPORT.md` 9절의 결정 목록은 r2의 다섯 항목과 앞의 세 항목을 담는다.

실행하지 않은 것: `650b1f5`의 소스 전체 재빌드, 기준 트리 빌드, drift 대조군, 게이트 대조군, `maxHeartbeats` 문턱 측정, 링크 검사(`lv/link`는 `dfc8b93` 뒤 바뀌지 않았다), `stale_olean.py`, 스크립트 자체 시험, Go 차분 시험, 하드웨어 대조, T3.
