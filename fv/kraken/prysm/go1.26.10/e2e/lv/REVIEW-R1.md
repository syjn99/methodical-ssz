# REVIEW R1: LV (`fbf729a`, 기준 `6a78c59`)

**판정: REQUEST_CHANGES.**
리뷰어 모델은 `claude-fable-5-2`다.
리뷰어는 증명을 쓰지 않은 새 세션이다.
리뷰어는 `git archive fbf729a`의 scratch 사본에서 확인했다.
`.lake/packages`는 작업 트리에서 복사했다. `.lake/build`는 복사하지 않았다.
이 파일은 리뷰어의 보고를 계획 담당이 옮겨 적은 것이다. 리뷰 로그는 로컬에만 있다.

## 1. 필수 수정

| ID | 내용 |
| --- | --- |
| M1 | `E2eList/WitSaA.lean:26`과 `E2eList/WitScA.lean:27`의 `set_option maxRecDepth 100000`에 기록된 원인이 없다. 이 줄이 없어도 `WitSaA`는 오류 0으로 컴파일된다. `WitScA`는 첫째와 셋째 `example`만 실패한다(`List.replicate 512`의 `simp`, 재귀 깊이). `sc_accept_runs`는 이 줄이 필요 없다 |

## 2. 권장 수정

| ID | 내용 |
| --- | --- |
| S1 | `STEPS.tsv` 73, 76행에 실행 디렉터리 경로가 있다 |
| S2 | 보고서가 인용하는 로그 26, 27, 65, 66, 08은 커밋되지 않았다. 내용은 보고서와 맞다 |
| S3 | `ATTEMPTS.md`의 "`E2eList.` 이름 622개"가 틀리다. 새 행 625개, `E2eList.`로 시작 434개, `E2eList` 포함 623개다 |
| S4 | 부정 시험에 명세(`Desc`) 변이와 T2 크기 거부 사례가 없다. 리뷰어가 돌린 두 종류는 설계대로였다 |
| S5 | `E2eList/BumpAllocT.S`는 Lake 입력이 아니다 |
| S6 | `lvElems`는 두 목록의 길이가 다르면 `emp`다. 지금 문장은 모두 길이 512를 고정한다. 가변 길이 목록에는 길이 조건이 있는 새 정의가 필요하다 |
| S7 | esz 24 `MakesliceC` 인스턴스는 `CONTRACTS.md`와 `RUNTIME-1.26.10.md`에 없다. 리뷰어는 기존 꼴의 인스턴스라는 판단에 동의한다. 원소 형식이 포인터를 가지므로 사용자의 확인이 필요하다 |
| S8 | LV-1: 전체 ELF objdump에는 감긴 변위 꼴의 피연산자가 153개 있다 |
| S9 | 사용자에게 올릴 것: 원격 이름, 기한 미확인, Go 차분 시험 미실행 |

S9의 원격에 대한 계획 담당의 확인: 이 작업 트리의 원격은 `kasey`, `my`(syjn99), `origin`(OffchainLabs), `upstream`(OffchainLabs)이다.
사용자는 시작할 때 이 상태를 듣고 실행을 골랐다.

## 3. 리뷰어가 다시 확인한 것

커널 검사(리뷰어의 재빌드):

- `lake build E2e E2eAd E2eScal E2eList`: exit 0, 1035 jobs, 1147 s. `--no-build`: exit 0.
- 공리 게이트: PASS, 선언 5632, 정리 4684, 손 목록 462, 비표준 0, `sorryAx` 0. 커밋된 `axioms-gate-lv.json`과 모든 칸이 같다.
- 주 정리 10개의 형은 `dfc8b93`의 고정 문장 def다. 그 뒤 `StmtSa`, `StmtSc`, `Defs`, `Desc`, `Code`, `Data`, `Include`, `lv/link/`는 바뀌지 않았다.
- T2의 `panicBounds` 분기는 `sc_iter`가 안 갈림을 증명한다. 전제가 아니다.
- 증인 둘은 고정 문장의 전제 전체를 만족한다. T2는 한 `runtime.makeslice`에서 `MakesliceC` 인스턴스 둘을 얻는다.

실행 검사(리뷰어의 실행):

- 선언 drift 0 (5007 = 5007). 리뷰어의 소스 빌드 덤프가 작성자의 기준 덤프, 머리 덤프와 바이트 단위로 같다. 기준 트리의 별도 빌드는 하지 않았다.
- 링크 검사 PASS all, 같은 BUNDLE `5c166606…`. 명령어 96 + 124개, 446 + 568바이트가 ELF 바이트와 같다. ELF, objdump, nm의 sha256이 `build-ids.txt`와 같다.
- `lvSliceType`: ELF 바이트로 Size_ 24, PtrBytes 8, kind 23, 원소 형식은 uint8이다.
- 부정 시험: 커밋된 사례 8개와 리뷰어의 사례 8개, 16/16이 설계대로다. 명세 변이 3개는 명세 보조정리를 깬다.
- 게이트 대조군: 심은 `axiom`은 FAIL, 손 목록에서 뺀 행은 FAIL, 바꾼 해시는 drift 1이다.
- LV-1 재현: Kraken은 `lea 0xffffff1c(%rdi),%rdx`를 `disp := ↑4294967068`로 읽는다. ELF 바이트의 disp32는 −228이다. 커밋된 `.S`에 감긴 변위는 없다.
- 금지 토큰 없음. 기준 대비 추가가 아닌 변경은 `lakefile.toml`의 덧붙임뿐이다.

읽기 판단:

- 문장의 강도는 `E2eScal.H4.dd_accept_stmt` 계열과 같다. `⋆ True`가 없다. 목표를 비우는 전제가 없다.
- 손 `Desc`는 consensus-specs altair mainnet과 맞다.
- 새 계약 꼴은 없다.
- 증인 값: 주소는 8 정렬이 아니고 `guard = 0`, `ra = 0`이다(`WitDdA`와 같다).

실행하지 않은 것: 기준 트리의 별도 빌드, `stale_olean.py`, 커밋된 나머지 부정 사례 10개, Go 차분 시험, 하드웨어 대조, T3.
