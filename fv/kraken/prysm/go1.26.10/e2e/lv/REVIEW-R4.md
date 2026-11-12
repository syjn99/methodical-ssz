# REVIEW R4: LV (`9e2272b`, 변경분 `29683a8..9e2272b`, 기준 `6a78c59`)

**판정: APPROVE.**
필수 수정은 없다. 권장 수정은 9개다.
범위는 `link/conv.py` 수정(`93b3f2a`)과 T3 `IndexedAttestation` 디코더다.
리뷰어 모델은 `claude-fable-5-2`다.
리뷰어는 증명을 쓰지 않은 새 세션이다. r1, r2, r3 리뷰어가 아니다.
리뷰어는 `git archive 9e2272b`의 scratch 사본에서 확인했다.
이 파일은 리뷰어의 보고를 계획 담당이 옮겨 적은 것이다. 리뷰 로그는 로컬에만 있다.
이 파일의 커밋과 권장 수정의 반영은 리뷰 뒤의 변경이다. 그 변경은 리뷰받지 않았다.

## 1. 권장 수정

| ID | 내용 |
| --- | --- |
| S1 | P1, P2 주 정리(`ia_e2e_reject_size_main`, `ia_e2e_reject_offset_main`)에 증인이 없다. `fv/AGENTS.md`는 주 정리마다 증인을 요구한다. T1, T2의 크기 거부도 증인이 없고 r1–r3는 받아들였다 |
| S2 | `REPORT.md` 4절의 `maxRecDepth 1024` 목록에 P1, P2 정리가 빠졌다(`IaReject.lean:28`, `:98`, 로그 123, 124) |
| S3 | `WitIaR.lean:30`과 `WitIaA.lean:33`은 파일 전체에 `maxRecDepth`를 건다. WitIaR에서 옵션이 필요한 곳은 `P_len`과 `hk284`뿐이다 |
| S4 | `negative-lv-t3.json`에 `prechecks` 항목이 둘이다. 첫째는 실패한 실행(로그 251)의 것이다. 사례 8행은 맞다 |
| S5 | `STEPS.tsv` 105, 107, 108행의 시각이 틀리다. 로그 mtime은 22:48:35Z, 22:49:32Z, 22:50:02Z다 |
| S6 | "쓰인 대로는 증명할 수 없다"는 과하다. 반례 모형은 없다. 확인된 것: itab 레이블이 0이면 `je`를 반박할 수 없고 증명 방법이 거기서 실패한다 |
| S7 | `REPORT.md` 조건 1은 `MakesliceC`, `MemmoveC`만 든다. T3는 `NewobjectC`, `ConvT64C`, `FmtErrorfDWC`도 쓴다 |
| S8 | `_nz` 정리, P2, 명세 정리를 겨눈 부정 사례가 없다 |
| S9 | `conv.py`는 베이스 없는 SIB 꼴과 베이스 없는 세그먼트 꼴의 감싼 변위를 그대로 둔다. 이 objdump에는 둘 다 0개다. 감싼 꼴이 남아도 `conv.py`는 실패하지 않는다 |

## 2. `conv.py` (`93b3f2a`)

실행 검사(리뷰어의 실행, python만):

- 옛 `conv.py`와 새 `conv.py`의 `--norm` 출력: 함수 파일 641개, 바뀐 파일 104개, 바뀐 줄 161개. 바뀐 줄마다 리뷰어의 2의 보수 다시 쓰기와 같다. 다른 차이 0.
- objdump의 피연산자 꼴: 베이스 있는 감싼 disp32 161개, 베이스 없는 것 0, `%rip` 0, 세그먼트 꼴 0.
- 만든 입력: 즉시값, `%rip`, movabs, 양수 `0x7fffffff`, 7자리와 9자리 수는 그대로다. 베이스+인덱스, `*disp(%reg)`, `%fs:disp(%reg)`, AVX 꼴은 맞게 바뀐다.
- 다시 만들기, 바이트 단위로 같음: 묶음 7개와 `lv/link-t3` 41/41, `link/out` 30/30, `link/norm` 136/136.
- selftest 통과.
- `check.py`: exit 0, PASS (a)–(f). RESULT는 커밋된 `lv/link-t3/RESULT`와 바이트 단위로 같다.

읽기 판단: 64비트 모드에서 베이스 있는 disp32는 항상 부호 확장된다. 그래서 이 다시 쓰기는 맞는 피연산자를 바꿀 수 없다.

## 3. T3

커널 검사(리뷰어의 빌드):

- `lake build E2e E2eAd E2eScal E2eList`: exit 0, 1080 jobs, 127.3 s, 표본 RSS 7.72 GiB. E2eList 모듈 45개는 소스에서 빌드했다. 270 jobs는 재생했다.
- 한계: E2e, E2eAd, E2eScal과 패키지는 작업 트리의 `.lake`에서 재생했다. 그 소스는 기준과 같다.
- `--no-build`: exit 0, 1080 jobs.

실행 검사(리뷰어의 실행):

- 공리 게이트: PASS, 선언 6402, 정리 5341, 손 목록 485, 비표준 0, `sorryAx` 0. 커밋된 `axioms-gate-lv-t3.json`과 바이트 단위로 같다.
- 선언 덤프는 작성자의 덤프와 바이트 단위로 같다. drift 0 (5007 = 5007).
- r3의 게이트 덤프(5632행) 대비: ADDED 770, CHANGED 0, REMOVED 0. T1, T2 선언은 r3 뒤 바뀌지 않았다.
- T3 부정 시험 8개 모두 통과(대조군 2, inside 6). 초 칸 말고 커밋된 파일과 같다.
- 문턱 표본: `IaReject`는 `maxRecDepth` 없이 실패한다. `IaAccept`는 `maxHeartbeats 400000`에서 실패한다.
- `StmtIa.lean` 등 고정 파일은 `e13053a` 뒤 차이가 없다. `StmtIaNz.lean`은 `714989f` 뒤 차이가 없다. `_nz` def는 고정 def에 `(he0nz : e0 ≠ 0)`과 이름만 더한 것이다.
- 주 정리 11개 모두 고정 def를 형으로 가진다.
- 변경분에 금지 토큰, 홈 경로, 세션 id, hold-out 타입 이름이 없다. 커밋 18개는 선형이고 `29683a8`은 조상이다.

읽기 판단:

- 문장은 뜻이 있다. 수용 문장은 입력, 수신자, `R`, 프레임, rsp + 8, rbp, r14, 힙 `avail − (8n + 432)`를 남긴다. `⋆ True` 꼬리는 없다.
- `ia_accept_spec_stmt`의 전제는 비어 있지 않다(`pia_roundtrip`).
- 증인은 모든 전제를 증명한다. 계약 가설 9개는 모델에서 온다. `WitIaR`의 프레임은 `fun _ => True`다(선례 `WitLuMa`와 같다).
- 결함 설명은 사실이다. 지시어 103–106과 66–69는 `mov global,%rcx; test; je; mov 0x8(%rcx),%rcx`다.
- `e0 ≠ 0`은 공정하다. RESULT (b)는 `go_itab._errors.errorString_error = 0xd28520`을 묶는다.
- P6 도달 불가: 187의 호출은 항상 rcx = 0x80을 받는다. P1–P5의 전제가 모든 입력을 덮는다.
- 계약은 기존 꼴뿐이다. `Fk/Contracts.lean`은 바뀌지 않았다.
- `len ≤ cap`과 `cap < 2^63`은 기록돼 있고 필요하다.

실행하지 않은 것: 기준 트리 빌드, E2e/E2eAd/E2eScal과 패키지의 소스 재빌드, 게이트 대조군, drift 대조군, `stale_olean.py`, WitIaA 문턱 측정, Kraken 탐침, `opt-r1/link`, ELF 재빌드, Go 차분 시험, 하드웨어 대조.

## 4. 사용자가 정할 것 (리뷰어 목록)

- 고정 뒤의 `_nz` 정정. 리뷰어는 기록된 사용자 승인을 확인할 수 없다.
- `conv.py` 변경. 같은 말이다.
- `e13053a`의 lakefile 변경.
- 증인 없는 P1, P2(S1).
- WitIaA의 시도 횟수 세기.
