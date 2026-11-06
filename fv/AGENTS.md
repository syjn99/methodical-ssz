# AGENTS.md

`fv/` 아래를 바꾸는 모든 에이전트와 사람에게 적용되는 규칙이다.
방향과 신뢰 기반 결정은 `fv/<project>/DIRECTION.md`, 현재 상태는 `REPORT.md`, 이력은 `HISTORY.md`에 있다.

## 기본 규칙

[EthLib의 AGENTS.md](https://github.com/ethereum/EthLib/blob/8621856/AGENTS.md)를 기본 규칙으로 채택한다.
이 파일은 다른 점과 더하는 점만 적는다. 두 문서가 충돌하면 이 파일이 우선한다.

## 출처 셋

정리 하나에 출처가 셋이다. 하나라도 바뀌면 정리를 다시 검사한다.

| 출처 | 무엇을 적는가 | 어디에 |
| --- | --- | --- |
| 명세 | EthLib 커밋, 모듈, 정의 이름 | 정리 파일 머리와 `SPEC.md` |
| 대상 | Go 소스 경로, 생성기 커밋, Go 버전, 빌드 플래그, ELF sha256 | `link/out/build-ids.txt`와 `TOOLS.md` |
| 의미론 | Kraken 커밋. PR 브랜치면 PR 번호와 "main에 없음" | `lake-manifest.json`과 `TOOLS.md` |

다른 클라이언트의 동작과 Go 컴파일러의 출력은 근거가 아니다.

## 레이아웃

`fv/<project>/`에 `target/`(대상 Go), `link/`(빌드·변환·링크 검사), `lean/`(정리), `negative/`(부정 시험), `review/`(리뷰 본문과 Lean 회귀 파일)을 둔다.
문서는 `DIRECTION.md`, `REPORT.md`, `HISTORY.md`, `CONTRACTS.md`, `SPEC.md`, `TOOLS.md`다.
한 프로젝트의 커밋은 그 디렉터리 밖을 건드리지 않는다.
외부 클론(`upstream/`, `vcgen-src/`)과 생성물은 `.gitignore`에 넣는다.

## 증명

- `sorry`, `admit`, 새 `axiom`, `native_decide`, `bv_decide`를 쓰지 않는다. 공리는 `propext`, `Classical.choice`, `Quot.sound`뿐이다.
- 계약 가설은 크기 범위, 런타임 소유 메모리, 프레임, 스택 창을 명시한다. "모든 크기, 모든 프레임"에 양화하지 않는다.
- 주 정리마다 전제 전체를 만족하는 구체 상태의 증인을 둔다. 가변 길이는 빈 값, 1개, 최대. 증인이 없으면 완료가 아니다.
- 사후조건은 입력, 접두사, 프레임, 반환 후 rsp, 보존 레지스터를 남긴다. `⋆ True`로 끝내지 않는다.
- 레이블 신선성과 전역 주소는 정리의 전제다. 실제 ELF에서 성립함은 `link/` 검사가 확인한다.

## 검사

PR 전에 `REPORT.md` 재현 절의 명령을 모두 실행하고 결과를 적는다.
실행하지 않은 검사는 실행하지 않았다고 적는다.
하드웨어 대조를 돌리지 못했으면 `REPORT.md` 신뢰 항목에 적는다.

## 알려진 답

기대값은 consensus-specs 테스트 벡터나 EthLib에서 가져온다. 검사 대상 코드로 기대값을 만들지 않는다.
ELF 해시 하나로 변환 결과, `Code.lean`, `AXIOMS.txt`, 검사 로그를 묶는다. 해시는 마지막 PASS 줄 뒤에 찍는다.

## 도구 경계

- Kraken, gohashtree, `sszgen/`, `ssz/`, `fv/<project>/upstream/`을 고치지 않는다.
- 없는 명령어는 `REPORT.md` "Kraken 요청 목록"에, 생성기 버그는 "발견" 절에 적는다.
- 상류 PR은 사용자가 만든다. 열린 PR 브랜치는 시험에만 쓰고 출처를 적는다.
- 해시 함수는 `gohashtree` 프로젝트가 증명하기 전까지 계약이다.

## 문서

- 한국어 문서는 ASD-STE100 스타일이다. 한 문장은 20단어 이내, 한 줄에 한 문장. 추측을 사실로 쓰지 않는다.
- `REPORT.md`는 판정(`가능`, `조건부`, `불가`)으로 시작한다. 조건부면 조건 목록이 바로 따른다.
- `REPORT.md`는 현재 상태만 적는다. 세션 이력과 철회는 `HISTORY.md`에 한 단락으로 적는다.
- 지운 것은 git 이력이 보관한다. "역사 자료"라는 이유로 파일을 남기지 않는다.

## 커밋과 PR

- 제목은 영어 Conventional Commits `<type>(<scope>): <summary>`. type은 EthLib 목록 + `proof`. scope는 `kraken`, `gohashtree`, `link`, `spec`, `contracts`, `negative`.
- 본문 끝에 작성 모델을 밝힌다: `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`.
- PR 본문: 문제, 아이디어, 예시 하나, 리뷰어가 알아야 할 것. AI 에이전트면 밝힌다.

## 세션 운영

- 무거운 Lean 빌드는 한 번에 하나다. `pgrep -fl "lean|lake"`로 확인하고 기다린다.
- 명령에 홈 디렉터리 절대 경로를 쓰지 않는다. `~` 또는 `$HOME`을 쓴다.
- 디렉터리는 `rm` 대신 `trash`로 지운다.
- 작업 단위마다 커밋한다. 진행은 `orca worktree set --worktree active --comment "..."`로 갱신한다.
- 끝나면 `orca worktree set --worktree active --workspace-status in-review --unread`를 실행한다.
- 막히면 그 항목을 미수행으로 표시하고 다음으로 간다. 전체가 막힐 때만 멈춘다.
