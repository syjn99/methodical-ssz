# AGENTS.md

`fv/` 아래를 바꾸는 모든 에이전트, 사람과 AI, 에게 적용되는 규칙이다.

이 디렉터리는 methodical-ssz가 생성한 Go 코드와 그 런타임 패키지가 x86-64 기계어 수준에서 EthLib SSZ 명세를 만족한다는 기계 검사 증명을 담는다.
기계어 정리는 Kraken의 x64 의미론 위에 있다.
여기서 틀린 정리는 "증명됐다"는 말을 거짓으로 만든다.
그래서 모든 정리는 출처가 있고, 전제가 만족 가능하며, 실제 바이너리와 연결돼야 한다.

## 기본 규칙

[EthLib의 AGENTS.md](https://github.com/ethereum/EthLib/blob/8621856/AGENTS.md)를 기본 규칙으로 채택한다.
기준, 출처, Lean 코드와 증명, 알려진 답, 문서, 커밋과 PR 절이 그대로 적용된다.
이 파일은 그 규칙과 다른 점과 더하는 점만 적는다.
두 문서가 충돌하면 이 파일이 우선한다.

## 출처 셋

EthLib은 명세 하나를 구현하므로 출처가 하나다.
여기서는 정리 하나에 출처가 셋이다.

| 출처 | 무엇을 적는가 | 어디에 |
| --- | --- | --- |
| 명세 | EthLib 커밋, 모듈, 정의 이름. 예: `EthLib 8621856`, `Ssz.Codec.serialize` | 정리 파일 머리와 `SPEC.md` |
| 대상 | Go 소스 경로, 생성기 커밋, Go 버전, `GOOS`/`GOARCH`/`GOAMD64`/빌드 플래그, ELF sha256 | `link/out/build-ids.txt`와 `TOOLS.md` |
| 의미론 | Kraken 커밋. PR 브랜치를 썼으면 PR 번호, 커밋, "main에 없음" 표시 | `lake-manifest.json`과 `TOOLS.md` |

세 출처 중 하나라도 바뀌면 정리를 다시 검사한다.
다른 클라이언트의 동작은 테스트이지 근거가 아니다.
Go 컴파일러의 출력은 대상이지 근거가 아니다.

## 레이아웃

```text
fv/AGENTS.md                      이 파일
fv/<project>/target/              대상 Go 타입과 드라이버
fv/<project>/link/                빌드, 디스어셈블, 변환, 링크 검사 스크립트와 산출물
fv/<project>/lean/Fv1/            EthLib 위의 명세 복사본과 전이 정리
fv/<project>/lean/Fk/             Kraken 위의 기계어 정리
fv/<project>/lean/scripts/        공리와 선언 검사
fv/<project>/negative/            부정 사례
fv/<project>/review/              검토 결과와 반례
fv/<project>/CONTRACTS.md         외부 함수 계약표
fv/<project>/SPEC.md              Desc, 추상화, 오류 대응표
fv/<project>/REPORT.md            판정, 조건, 이견
fv/<project>/COST.md              항목별 시간
fv/<project>/TOOLS.md             버전, 시간, 메모리, 막힌 오류
```

`<project>`는 지금 `kraken`(SSZ 코덱)과 `gohashtree`(SHA-256)다.
한 프로젝트의 커밋은 그 디렉터리 밖을 건드리지 않는다.
`upstream/`과 `vcgen-src/` 같은 외부 클론은 `.gitignore`에 넣는다.

## 증명

EthLib의 증명 규칙이 그대로 적용된다.
`sorry`, `admit`, 새 `axiom`, `native_decide`, `bv_decide`를 쓰지 않는다.
공리는 `propext`, `Classical.choice`, `Quot.sound`뿐이다.

기계어 정리에는 규칙 넷을 더한다.

- 계약 가설은 양화 범위를 제한한다.
  외부 함수의 계약은 크기 범위, 런타임이 소유한 메모리 조각, 프레임, 스택 창을 명시한다.
  "모든 크기, 모든 프레임"에 양화된 계약은 만족 불가능할 수 있다.
  그런 계약을 전제로 한 정리는 참이지만 아무것도 말하지 않는다.
- 전제 만족 증인을 둔다.
  주 정리마다 전제 전부를 만족하는 구체 상태를 만드는 정리를 하나 이상 둔다.
  가변 길이 타입은 빈 값, 1개, 최대 길이 셋을 둔다.
  증인이 없는 정리는 완료로 표시하지 않는다.
- 사후조건은 조합 가능해야 한다.
  입력, 접두사, 프레임, 반환 후 스택 포인터, 보존 레지스터를 결론에 남긴다.
  `⋆ True`로 끝나는 사후조건은 다음 함수를 부를 때 쓸 수 없다.
- 레이블과 주소는 링크 검사로 연결한다.
  레이블 신선성과 전역 주소는 정리의 전제다.
  그 전제가 실제 ELF에서 성립함은 `link/` 검사가 확인한다.

## 검사

PR을 열기 전에 다음을 실행하고 결과를 적는다.
실행하지 않은 검사는 실행하지 않았다고 적는다.

```bash
cd fv/<project>/lean && lake build        # 기본 대상에 명세 복사본 전부를 포함한다
lake env lean scripts/Axioms.lean         # Fv1과 Fk의 모든 정리를 전수 조회한다
lake env lean scripts/Decls.lean          # partial, opaque, unsafe, extern, implemented_by, bv_decide, native_decide
fv/<project>/link/check.sh                # ELF ↔ objdump ↔ 변환 결과 ↔ Host 레이블과 전역 주소
fv/<project>/negative/run.sh              # 변이가 지정한 정리에서 실패한다
```

`scripts/decls_baseline.txt`는 지금 있는 위반을 적는다.
위반을 없애는 PR은 그 줄을 지운다.
새 위반은 고치지 목록에 더하지 않는다.

하드웨어 대조는 x86-64 Linux에서만 돈다.
돌리지 못했으면 `REPORT.md` 신뢰 기반 문구에 그렇게 적는다.

## 알려진 답

EthLib 규칙이 그대로 적용된다.
기대값은 consensus-specs 테스트 벡터나 EthLib에서 가져온다.
검사 대상 코드로 기대값을 만들어 검사라고 부르지 않는다.
ELF 해시 하나로 변환 결과, `Code.lean`, `AXIOMS.txt`, 검사 로그를 묶는다.
해시는 마지막 PASS 줄까지 쓴 뒤에 찍는다.

## 도구 경계

- Kraken 소스를 고치지 않는다.
  없는 명령어와 기능은 `REPORT.md` "Kraken 요청 목록"에 적는다.
  열린 상류 PR 브랜치는 시험에만 쓰고 출처를 적는다.
- 상류 PR은 사용자가 만든다.
  에이전트는 만들지 않는다.
- `sszgen/`, `ssz/`, `fv/<project>/upstream/`을 고치지 않는다.
  생성기 버그는 `REPORT.md` 발견 절에 적는다.
- 해시 함수는 계약이다.
  `gohashtree` 프로젝트가 그 계약을 증명으로 바꾸기 전까지 그렇다.

## 문서

EthLib의 문서 규칙에 더해 한국어 문서는 ASD-STE100 스타일로 쓴다.
한 문장은 20단어 이내다.
한 줄에 한 문장을 쓴다.
추측을 사실로 쓰지 않는다.

세션 보고서 `REPORT.md`는 판정으로 시작한다.
판정 단어는 `가능`, `조건부`, `불가` 셋 중 하나다.
조건부면 조건 목록이 바로 따른다.
브리프와 다르게 한 것은 "이견" 절에 적는다.

## 커밋과 PR

EthLib의 Conventional Commits 규칙을 따른다.
제목은 영어다.

```text
<type>(<scope>): <summary>
```

type은 EthLib의 목록에 `proof`를 포함한 그대로다.
scope는 프로젝트나 모듈이다: `kraken`, `gohashtree`, `link`, `spec`, `contracts`, `negative`.

```text
proof(kraken): prove ListU64.UnmarshalSSZ accept path with a heap-resource makeslice contract
feat(link): reject converter input lines without a byte comment
docs(kraken): record the vacuity finding and its fix in REPORT.md
```

커밋 본문 끝에 작성 모델을 밝힌다.

```text
Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
```

PR 본문은 EthLib 순서를 따른다: 문제, 아이디어, 예시 하나, 리뷰어가 알아야 할 것.
AI 에이전트면 PR에 밝힌다.

## 세션 운영

- 무거운 Lean 빌드는 한 번에 하나만 돌린다.
  다른 세션이 돌고 있으면 `pgrep -fl "lean|lake"`로 확인하고 기다린다.
- 명령에 홈 디렉터리 절대 경로를 쓰지 않는다.
  `~` 또는 `$HOME`을 쓴다.
- 디렉터리는 `rm` 대신 `trash`로 지운다.
- 작업 단위마다 커밋한다.
- 진행 상황을 `orca worktree set --worktree active --comment "..."`로 갱신한다.
- 끝나면 `orca worktree set --worktree active --workspace-status in-review --unread`를 실행한다.
- 막히면 그 항목을 미수행으로 표시하고 다음으로 간다.
  전체가 막힐 때만 멈춘다.
