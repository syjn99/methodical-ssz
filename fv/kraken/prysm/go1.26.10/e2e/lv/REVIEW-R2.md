# REVIEW R2: LV (`d169e4b`, 변경분 `fbf729a..d169e4b`, 기준 `6a78c59`)

**판정: REQUEST_CHANGES.**
리뷰어 모델은 `claude-fable-5-2`다.
리뷰어는 증명을 쓰지 않은 새 세션이다. r1 리뷰어가 아니다.
리뷰어는 `git archive d169e4b`의 scratch 사본에서 확인했다.
`.lake/packages`는 작업 트리에서 복사했다. `.lake/build`는 복사하지 않았다.
이 파일은 리뷰어의 보고를 계획 담당이 옮겨 적은 것이다. 리뷰 로그는 로컬에만 있다.

## 1. 필수 수정

| ID | 내용 |
| --- | --- |
| M1 | `E2eList/WitScA.lean`의 `set_option maxRecDepth 100000 in` 둘(126행, 134행)이 필요한 값보다 넓다. 1024는 실패하고 2048은 통과한다. 측정한 문턱이 기록에 없다. `(by simp) (by simp)`를 항 증명(`List.length_replicate`, `List.eq_of_mem_replicate`)으로 바꾸면 옵션 없이 컴파일된다. 기록의 행 번호 127은 126이 맞다 |
| M2 | `FINDINGS-CANDIDATES.md`의 "이 objdump 파일의 함수는 모두 SSZ 메서드다(… HashTreeRoot)"가 틀리다. TEXT 함수는 641개다: UnmarshalSSZ 211, MarshalSSZTo 211, SizeSSZ 211, MarshalSSZ 6, `ssz.ValidateBitvector` 1, `ssz.ValidateBitlist` 1. HashTreeRoot는 0개다. 153과 104는 맞다. 104개는 UnmarshalSSZ 67개와 MarshalSSZTo 37개다 |

r1 M1의 닫힌 부분: 범위는 `example` 둘뿐이다. 원인은 기록돼 있다. `WitSaA.lean`에는 `maxRecDepth`가 없다.

## 2. 권장 수정

| ID | 내용 |
| --- | --- |
| S1 | `maxHeartbeats 16000000`(`WitSaA.lean:90`, `WitScA.lean:95`)은 필요하다. 기본값과 400000은 `whnf`에서 실패한다. WitSaA는 1000000에서 통과한다. WitScA는 1000000에서 실패하고 2000000에서 통과한다. 문턱이 기록에 없다 |
| S2 | `REPORT.md` 5절의 줄 수 "WitSaA 126, WitScA 134"가 낡았다. `d169e4b`에서는 125와 139다 |
| S3 | LV-1 개수: 넓은 무늬 `0x[89a-f][0-9a-f]{7}\(%`는 161개를 준다. 더해진 8개는 `0xffd6xxxx(%r..)` 꼴의 `lea`다. 161개 모두 같은 함수 104개에 있다. 커밋된 `.S` 222개에는 두 꼴이 없다 |
| S4 | `REPORT.md` 7절은 부정 시험이 Desc 변이를 포함한다고 쓴다. Desc 변이 파일은 대상에서 잘린다. `prysmS*Desc_fixedSize`나 `ps*_toValue_fits`까지만 간다. `*_spec_k`를 시험하는 Desc 변이는 없다 |
| S5 | `WitSaA.lean:25-26`과 `WitScA.lean:26-27`에 빈 줄이 둘씩 있다 |

## 3. 사용자가 정할 것 (리뷰어 목록)

- esz 24 `MakesliceC` 인스턴스(r1 S7), 기한, Go 차분 시험.
- `3bb6cc1`의 lakefile 변경. 루트 `AGENTS.md`는 lakefile 변경에 사용자 승인을 요구한다. 작업 지시는 새 라이브러리 추가를 허용한다. `input_dir` 추가는 거기에 이름이 없다.
- LV-1의 처리 길(`conv.py` 부호 있는 변위, `check.py` 범위 검사, Kraken 요청).
- 시도 횟수 읽기("한 전략 안의 컴파일 반복은 한 번의 시도다", `REPORT.md` 3절).
- 원격 이름: `origin`은 OffchainLabs다. 사용자가 이 상태를 받아들였다는 기록은 `REVIEW-R1.md`에만 있다. 리뷰어는 확인할 수 없다.

## 4. 리뷰어가 다시 확인한 것

커널 검사(리뷰어의 재빌드):

- `lake build E2e E2eAd E2eScal E2eList`: exit 0, 1036 jobs, 1176 s, 표본 RSS 최대 24.4 GiB. `--no-build`: exit 0.
- 공리 게이트: PASS, 선언 5632, 정리 4684, 손 목록 462, 비표준 0, `sorryAx` 0. 커밋된 `axioms-gate-lv-r1.json`과 모든 칸이 같다.
- 리뷰어의 덤프는 작성자의 r1 덤프, 수정 전 덤프와 바이트 단위로 같다. `fbf729a..d169e4b`에서 선언 형, def 값, 공리 집합은 바뀌지 않았다.
- 기준 트리(`6a78c59`)의 별도 빌드: 982 jobs, exit 0, 1153 s. 덤프는 작성자의 기준 덤프와 바이트 단위로 같다. drift 0 (5007 = 5007).

실행 검사(리뷰어의 실행):

- drift 대조군: 기준 사본의 `E2eScal.WitBhU.s0`에 `112 + 0`을 심었다. exit 1, `CHANGED`. 되돌렸다.
- 부정 시험 26개 전부: 25개 통과(대조군 7, inside 18), 1개 outside(`lv-sa-bitslen63`). 초 칸 말고 모든 칸이 커밋된 `negative-lv.json`과 같다.
- 새 사례 8개: 변이 파일은 `E2eList.Desc`, `E2eList.Defs`를 import하지 않는다. 정리는 변이된 Desc를 본다.
- Lake 입력: `E2eList/BumpAllocT.S`에 주석 한 줄을 더하면 `--no-build E2eList`가 exit 3이다. 되돌리면 exit 0이다.
- 개수: 새 선언 625, 지워진 것 0, `E2eList.` 시작 434, `E2eList` 포함 623.
- `lv/`, `E2eList/`, 새 스크립트 6개에 홈 경로, 실행 디렉터리, 세션 id가 없다.
- `ATTEMPTS.md`의 로그 발췌(08, 26, 27, 65, 66)와 로그 86–95의 설명은 로컬 로그와 맞다.

읽기 판단:

- `git diff dfc8b93 d169e4b`는 `StmtSa`, `StmtSc`, `Defs`, `Desc`, `Code`, `Data`, `Include`, `lv/link/`에 대해 비어 있다. 주 정리 10개의 형은 고정 문장 def다.
- lakefile은 기준 대비 덧붙임뿐이다. `fbf729a` 대비로는 `E2eList` 항목의 `needs`만 바뀌었다.
- 추가된 파일에 금지 토큰이 없다.
- `lvnegative.py`의 inline 방식이 공허하게 통과하는 길은 찾지 못했다.
- `DESIGN.md` 6a절은 `Defs.lean`, `StmtSc.lean`과 맞다.
- `REPORT.md`는 K, X, N을 따로 둔다.

실행하지 않은 것: 링크 검사(`lv/link`는 r1 뒤 바뀌지 않았다), 게이트 대조군, `stale_olean.py`, 스크립트 자체 시험, Go 차분 시험, 하드웨어 대조, T3.

리뷰어가 밝힌 실수: 덤프 명령이 작성자의 로컬 scratch 파일 하나를 덮어썼다(작업 트리 밖).
새 내용의 sha256과 크기는 기준 덤프, r1 리뷰어의 머리 덤프 사본과 같다. 내용이 바뀌었을 가능성은 낮다.
