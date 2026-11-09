조건부

1. 사용자 머신의 전체 저메모리 재현 전에 발견 1의 절차를 수정한다.
2. OrbStack 측정 결과와 Colima 직접 검증을 구분한다.
3. 전체 빌드 여유 2.28 GiB를 사용자 머신의 보장값으로 사용하지 않는다.

증명 변경은 수용할 수 있다.
공개 assertion, 즉 정리가 주장하는 명제의 약화를 발견하지 못했다.
재컴파일한 원본과 수정본의 선언 290개를 직접 대조했다.
타입과 정의 값이 같고, 추가된 공리는 허용된 두 공리뿐이다.
사용자 머신의 전체 빌드 재현 절차에는 필수 수정이 필요하다.

## 검토 대상과 작업 상태

| 항목 | 값 |
| --- | --- |
| 브랜치 | `syjn99/ssz-fv-memopt` |
| 기준 | `86fd060349257c133e981e420120f63c61f582e1` |
| 검토 HEAD | `e8f95e3bf1578497b9eff720674d8e23ffbc402d` |
| 워크트리 | `~/orca/workspaces/methodical-ssz/ssz-fv-memopt` |
| 시작 `git status --short` | 출력 없음 |
| 종료 `git status --short` | 출력 없음 |
| 보고서 위치 | 사용자 지정 `E/REVIEW-gpt6-astra.md` |

`E`는 이 보고서가 있는 `scratchpad/memopt/review` 디렉터리다.
`E/target.txt`, `E/status-start.txt`, `E/status-end.txt`에 대상과 상태를 기록했다.
워크트리의 소스, 생성물, 의존성을 수정하지 않았다.
검사용 소스와 산출물은 모두 `E/`에 썼다.
push, PR 생성, 의존성 변경, Docker 설정 변경은 하지 않았다.

## 발견

### 1. P1: 주 재현 절차는 캐시가 남은 전체 빌드를 저메모리 재현으로 오인하게 할 수 있다

`memopt/REPORT.md:217`은 프로젝트 산출물을 제거하지 않고 `lake build`를 실행한다.
사용자 머신은 이전 실패 전에 여러 모듈을 이미 빌드한 상태다.
이 상태에서 수정본을 가져오면 Lake는 유효한 기존 산출물을 재사용할 수 있다.
따라서 성공 메시지만으로 전체 프로젝트 재빌드의 메모리 한계를 확인할 수 없다.

근거:

- `memopt/REPORT.md:211`의 명령 블록에는 `.lake/build` 제거 단계가 없다.
- `memopt/REPORT.md:226`은 전체 빌드 뒤에 단일 증인의 산출물만 제거한다.
- `memopt/logs/m3-orig-noop.out.txt`는 `Built` 없이 `Replayed` 45개와 `Build completed successfully (643 jobs)`를 출력한다.
- 따라서 성공 메시지의 jobs 수는 실제 재컴파일 수가 아니다.
- 실제 M4 전체 측정은 `.lake/build`를 제거했다.
- `memopt/logs/lm-full.out.txt:7001`에는 `Built Fk.WitLcM4x16`이 있고, 프로젝트 모듈 159개의 `Built` 기록이 있다.

이 발견은 기존 M4 성공 로그를 부정하지 않는다.
문제는 사용자 머신에 제시한 주 재현 절차다.

수정 제안: 별도 검증 복사본에서 `.lake/build`를 제거하고 전체 빌드의 시간, 최고 메모리, 종료 상태를 기록한다.
의존성 산출물 유지 여부도 명시한다.

### 2. P2: 저메모리 실행 스크립트는 수정본 빌드와 공리 검사 실패를 종료 코드 0으로 바꾼다

`memopt/lowmem/run.sh:63`부터 65까지의 `|| true`가 수정본 검증 실패를 숨긴다.
이 스크립트의 종료 상태를 사용하는 호출자는 실패를 성공으로 처리할 수 있다.

근거:

- 측정 명령만 종료 코드 23을 반환하는 가짜 `docker` 명령으로 실행했다.
- `new-1`, `full`, `axioms` 단계는 각각 종료 코드 0을 반환했다.
- 결과는 `E/wrapper-exit-test.txt`에 있다.
- 실제 Docker 컨테이너는 실행하지 않았다.
- 기존 로그의 성공 여부는 각 `summary.txt`와 실제 빌드 출력을 별도로 확인했다.

수정 제안: 수정본 단계 세 곳에서 `|| true`를 제거한다.
원본의 예상 실패는 별도로 처리한다.

### 3. P2: M2 진단 생성기는 최종 HEAD에서 잘못된 비교 파일을 만든다

`memopt/scratch/gen.py:8`은 현재 수정본을 읽지만, 30행은 원본의 `:= by decide`를 가정한다.
현재 HEAD에서 실행하면 일부 파일은 비교 대상을 바꾸고, 일부 파일은 문법 오류를 만든다.

근거:

- `memopt/M2-CAUSE.md` 재현 절은 현재 파일에서 이 생성기를 실행하도록 안내한다.
- 임시 복사본에서 실행한 생성기는 종료 코드 0을 반환했다.
- 생성된 `A1`과 `C0`는 원본 `decide` 대신 수정본 `simp`를 사용한다.
- 생성된 `C1`, `C3`, `C9`에는 한 선언에 할당 기호 `:=`가 두 번 들어간다.
- 생성된 `C1.lean`의 Lean 실행은 종료 코드 1을 반환했다.
- 오류는 `unexpected token ':='; expected command`다.
- 결과는 `E/diagnostic-repro.txt`, `E/diagnostic-C1.txt`에 있다.

수정 제안: 생성기가 `git show 86fd060:fv/kraken/lean/Fk/WitLcM4x16.lean`으로 고정 원본을 읽게 한다.

## Assertion과 정의의 독립 검증

### 소스 차이

`git diff 86fd060 HEAD -- fv/kraken/lean`을 전체 확인했다.
Lean 소스 변경은 세 증인 파일의 `u64v` 증명 일곱 줄뿐이다.
생성기 변경도 그 증명을 출력하는 한 줄뿐이다.

각 수정본에서 새 증명 문자열을 원본 증명 문자열로 되돌린 뒤 파일 전체를 비교했다.
여섯 증인 모두 기준 커밋과 바이트 단위로 같았다.
그 결과는 `E/static-checks.txt`에 있다.

따라서 다음 항목의 소스 변경은 없다.

- 정리 이름, 선언 종류, universe, 인자, 타입, 전제, 결론.
- 원소 네 개, 각 길이 16, 값 1부터 16까지의 입력.
- `block`, `objs`, `mem`, `s0`와 반환 길이 548.
- `u64Bytes`, `uintBytes`, `lcElem`, `lc_marshal_main`의 정의.
- `Fk.lean`의 import 목록과 빌드 대상.

### 기존 Inspector의 검사 범위

`.olean`은 Lean의 컴파일된 모듈 파일이다.
`Inspect.lean:48`의 `importModules`는 실제 `.olean`을 읽는다.
`Inspect.lean:51`은 해당 모듈이 소유한 선언 목록을 읽는다.
소스 문자열을 다시 분석하는 검사는 아니다.

하지만 이 검사기는 모든 선언 내용을 완전히 비교하지 않는다.

| 범위 | 실제 검사 |
| --- | --- |
| 일반 선언 | 이름, 소유 모듈, 종류, universe, 전체 표시 타입, 타입 해시 |
| 일반 정의 | 정의 값의 해시와 사용 상수 이름 |
| 정리 증명 값 | 값과 사용 상수 비교를 생략한다 |
| 내부 선언 | 이름과 종류만 출력한다 |
| 공리 | 일반 선언의 전이적 의존 공리를 수집한다 |
| 외부 정의 | 검사 대상 모듈 밖의 정의 값을 재귀 비교하지 않는다 |

`Inspect.lean:52`, 60행부터 63행, 74행부터 76행이 이 범위를 정한다.
`pp.all`은 타입을 상세히 표시하지만, 내부 선언의 내용이나 외부 정의의 의미를 검증하지 않는다.
정의 값은 표시하지 않고 해시만 출력한다.
따라서 타입 문자열과 해시 일치만으로 일반적인 의미 보존을 보장할 수 없다.

이번 변경에서는 전체 소스 차이가 증명 본문에 한정된다는 별도 근거가 있다.
기존 Inspector의 수정본 출력을 다시 생성했고, 기록된 출력과 정확히 일치했다.
결과는 `E/inspect-current.txt`, `E/inspect-current-match.txt`에 있다.

### 별도 컴파일과 직접 대조

원본 여섯 파일은 기준 커밋에서 추출했다.
수정본 여섯 파일은 현재 워크트리에서 복사했다.
각 파일을 `E/orig/Fk`와 `E/new/Fk`에 별도로 컴파일했다.
열두 번 모두 성공했다.
이 빌드는 기존 대상 증인의 `.olean`을 재사용하지 않았다.
변하지 않은 의존 모듈은 같은 현재 `.olean`을 사용했다.

`E/Compare.lean`은 원본과 수정본을 서로 다른 Lean 환경으로 읽는다.
출력은 실제로 읽은 대상 `.olean` 경로를 포함한다.
타입과 정의 값은 `Expr.equal`로 비교한다.
이 함수는 바인더 이름과 속성을 포함한 식 구조를 비교한다.
해시 일치만으로 판정하지 않는다.

최종 결과는 `E/compare-final.txt`에 있다.

```text
PASS: 290 owned declarations, including internal declarations
PASS: 5 external declarations
PASS: 57 definition values structurally equal
PASS: names, owners, kinds, universes and full type expressions equal
```

외부 선언 다섯 개는 `Fv1.u64Bytes`, `EthLib.Serialization.Ssz.uintBytes`, `lcElem`, `lc_marshal_main`, `Int.toBytes`다.
내부 선언도 이름만 비교하지 않고 타입과 정의 값을 비교했다.
정리의 증명 값은 비교하지 않았다.
증명 값 변경 자체가 이번 최적화다.
두 환경 사이의 동등성 정리를 커널로 증명한 검사는 아니다.
각 대상 파일의 컴파일 성공과 식 구조 일치를 결합한 검사다.

### 공리

새 증명은 `propext`와 `Quot.sound`만 추가한다.
두 공리는 `fv/AGENTS.md`가 허용한다.
일곱 `u64v`의 공리만 바뀌었다.
`lc_marshal_runs`와 `s_mem`은 이전부터 세 허용 공리에 의존했고, 이 목록은 같다.

직접 실행한 출력:

```text
'Fk.WitLcM4x16.lc_marshal_runs' depends on axioms: [propext, Classical.choice, Quot.sound]
'Fk.WitLcM4x16.u64v0' depends on axioms: [propext, Quot.sound]
TOTAL 1571 NONSTANDARD 0
ALL-DECLARATIONS TOTAL 7975 NONSTANDARD 0
```

`E/recheck.txt`, `E/axioms.txt`, `E/axioms-all.txt`에 전체 출력을 보관했다.
공리 두 범위 출력은 워크트리의 공리 보고서와 정확히 같다.
새 비표준 공리나 검증 우회를 발견하지 못했다.
진단 파일의 `debug.skipKernelTC`는 생산 빌드에 포함되지 않는다.

## 캐시와 보호 파일

### macOS

M1은 형제 워크트리의 `.lake/packages`를 복사했다.
이 사실과 복사 범위는 `ENV.md`에 공개되어 있다.
프로젝트 `.lake/build`를 복사했다는 근거는 없다.
M1과 M4 전체 로그는 모두 프로젝트 모듈 159개를 `Built`로 기록한다.
세 변경 증인도 두 로그에서 실제 빌드했다.

M3의 원본 확인 실행은 `Replayed`만 출력했다.
수정 후에는 세 변경 증인을 `Built`로 출력했다.
나머지 증인과 의존 모듈의 재사용은 변경 범위와 일치한다.

보존된 원본·수정본 `.olean` 열두 개의 SHA256을 직접 확인했다.
모두 `artifacts/olean.sha256`과 일치했다.
현재 Inspector 출력도 기록된 수정본 출력과 일치했다.
이 증거와 별도 재컴파일에서 대상 증인의 오래된 산출물 혼입을 발견하지 못했다.

의존성 전체를 원본과 수정본마다 처음부터 다시 빌드하지는 않았다.
과거 의존성 산출물 각각의 생성 과정을 독립적으로 확인하지 못했다.
현재 패키지 15개의 HEAD는 manifest와 같고, 추적 파일 변경은 없다.

### Linux 컨테이너

`lowmem/run.sh:48`의 rsync 제외 규칙은 각 패키지의 최상위 `.lake`를 제외한다.
작은 합성 디렉터리에서도 같은 규칙이 `.lake/build/Test.olean`을 제외했다.
결과는 `E/rsync-exclusion-test.txt`에 있다.
두 복사본은 `/work/pkgs`를 공유하므로 의존 산출물 경로가 같다.

`lm-prebuild-new`와 `lm-prebuild-orig`는 Linux 의존성 선빌드 기록을 남긴다.
단독 단계는 `WitLcM4x16.*` 산출물을 제거한다.
전체 단계는 프로젝트 `.lake/build`를 제거한다.
실제 로그의 `Built` 기록도 이 절차와 일치한다.
macOS 산출물을 그대로 Linux 성공으로 보고했다는 증거는 없다.

다만 setup의 `.lake` 개수 출력은 로그 파일에 보존되지 않았다.
실제 컨테이너의 삭제 후 파일 목록을 독립적으로 다시 확인하지 못했다.
스크립트와 빌드 로그를 근거로 판정했다.

### 보호 대상

`sszgen/`, `ssz/`, 대상 Go, 명세 모듈, 계약과 helper의 소스 차이는 없다.
manifest, toolchain, lakefile, 정규화된 명령어와 `build-ids.txt`도 같다.
ELF, 즉 검증 대상 실행 파일의 SHA256은 다음과 같다.

```text
9c850c97066b9d33d6e4c5ef0a385dcbe2c984ae774a527cdedd18d2b72ac501
```

이 값은 기준값과 같다.
`link/out/RESULT`의 변경은 공리 보고서 해시와 묶음 해시 두 줄뿐이다.
`E/static-checks.txt`, `E/code.diff`, `E/artifact-hash-check.txt`가 근거다.

## 측정 조건과 해석

RSS는 프로세스의 상주 메모리 크기다.
GiB는 2의 30제곱 바이트다.
cgroup은 Linux가 자원을 제한하고 사용량을 집계하는 프로세스 그룹이다.
OOM kill은 메모리 부족으로 프로세스를 종료한 사건이다.

| 비교 | 독립 판정 |
| --- | --- |
| M1 대 M3 단독 | 같은 macOS, 명령, 도구와 의존 산출물 조건의 비교다. 원본 13.01~13.27 GiB, 수정본 약 1.42 GiB를 원시 로그에서 확인했다. |
| M1 대 M4 전체 | 프로젝트 산출물 제거 조건이 같다. 최대 단일 RSS는 13.19 GiB에서 4.46 GiB로 줄었다. |
| macOS 대 Linux | 운영체제와 메모리 집계 방식이 다르다. 절대값을 같은 지표로 합치면 안 된다. |
| Linux 단독 | 원본은 두 번 OOM kill이었다. 수정본은 두 번 실제 재빌드에 성공했다. |
| Linux 전체 | 수정본은 프로젝트 재빌드에 성공했다. 최고 cgroup 사용량은 7.41 GiB였다. |

macOS의 자손 RSS 합계는 0.5초 간격 표본이다.
이 표본은 정확한 전체 메모리 최고치와 같다고 보장하지 못한다.
최대 단일 프로세스 RSS로 전체 빌드의 여유를 계산해서도 안 된다.

Linux 로그는 `memory.max=10403971072`, `memory.swap.max=0`을 기록한다.
VM 자체에는 swap 17061 MB가 있지만, 측정 cgroup의 swap 한도는 0이다.
따라서 보고서의 swap 0은 컨테이너 범위로 읽어야 한다.
VM 전체에 swap이 없었다는 뜻은 아니다.

수정본 단독의 cgroup 최고치는 0.44 GiB와 1.46 GiB다.
각 실행의 최대 RSS는 1.80 GiB와 1.77 GiB다.
이 차이는 두 지표가 같지 않다는 직접 근거다.
page cache, 즉 파일 내용의 메모리 캐시가 어느 그룹에 청구됐는지는 확인하지 못했다.
보고서는 그 원인을 추정으로 표시했고, 이 처리는 적절하다.

전체 빌드의 2.28 GiB는 관측한 cgroup 한도와 최고치의 차이다.
해당 실행은 CPU 18개와 기본 병렬도를 사용했다.
기존 의존 산출물과 여러 선행 실행 뒤의 캐시 상태도 포함한다.
이를 Colima의 운영체제 비용과 다른 CPU 수까지 포함한 여유로 해석할 수 없다.
전체 빌드는 한 번 측정했으므로 변동 범위도 확인하지 못했다.

M2의 A0, A1, A2와 C6, C7은 비용이 `u64v`의 elaboration, 즉 증명 구문을 처리하는 단계에 집중됨을 뒷받침한다.
다만 최고치 차이는 각 선언이 단독으로 할당한 정확한 바이트 수가 아니다.
whnf 내부 비용이나 성장 차수 전체를 직접 측정한 결과도 아니다.
보고서의 내부 원인 추정과 최대 프로세스 추정은 이 범위로 제한해야 한다.

## 완료 기준 10개

| # | 완료 기준 | 판정 | 독립 근거 |
| --- | --- | --- | --- |
| 1 | 원본 정상 baseline과 로그 | 충족 | M1 단독 세 번과 전체 빌드의 종료 상태, 시간, RSS 로그를 교차 확인했다. |
| 2 | 급증 지점과 원인 실측 | 충족 | 선언 제거 실험과 커널 생략 실험이 `u64v` 처리 비용을 분리한다. 내부 구현 원인은 제한된 추론이다. |
| 3 | 동일 조건 전후 측정 | 충족 | macOS 단독과 프로젝트 재빌드의 명령, 도구, 의존 산출물 조건이 일치한다. |
| 4 | 공개 assertion과 정의 보존 | 충족 | 별도 컴파일 뒤 선언 290개와 정의 값 57개의 식 구조가 같았다. |
| 5 | 신뢰 가정과 공리 범위 | 충족 | 허용 공리만 추가됐고, 두 범위를 직접 실행하여 `NONSTANDARD 0`을 확인했다. |
| 6 | 보호 코드·ELF·의존성 불변 | 충족 | 소스 diff, ELF 해시, 패키지 revision과 추적 파일 상태를 확인했다. |
| 7 | 회귀 성공 또는 미수행 분리 | 충족 | M4는 전체 빌드, 링크 24개, 부정 시험 16개, Go 시험과 Lean 회귀 결과를 기록했다. |
| 8 | 저메모리 단독·전체 결과 | 충족 | OrbStack의 제한된 cgroup에서 실제 재빌드 성공 기록이 있다. 사용자 Colima 직접 검증은 아니다. |
| 9 | 생성기 재현 가능 | 충족 | 임시 디렉터리에서 여섯 조합을 재생성했고, 모두 커밋된 파일과 같았다. |
| 10 | 독립 리뷰의 세 위험 확인 | 충족 | assertion, 캐시 혼입, 측정 조건 차이를 이 보고서에서 확인했다. 재현 절차의 결함도 분리했다. |

표의 충족은 각 항목에 적힌 범위에만 적용한다.
전체 프로젝트의 기존 게이트 1 통과를 뜻하지 않는다.
`DIRECTION.md`와 프로젝트 `REPORT.md`의 기존 신뢰 제약은 그대로다.

## 사용자 머신 재현 절차의 실행 가능성

`memopt/REPORT.md` 8.2절은 그대로 붙여 넣어 실행할 수 있는 완성된 명령 목록은 아니다.

- `<remote>`와 `<보고서 커밋 SHA>`는 실제 값으로 바꿔야 한다.
- 검토한 최종 SHA는 이 보고서의 대상 표에 적었다.
- 해당 커밋의 사용자 머신 전달이나 원격 브랜치 존재는 확인하지 못했다.
- A는 Linux 작업 컨테이너의 저장소 루트에서 시작해야 한다.
- B는 Docker를 사용하는 호스트의 저장소 루트에서 시작해야 한다.
- A를 마친 현재 디렉터리는 `fv/kraken/lean`이므로 B 전에 실행 위치를 다시 지정해야 한다.
- `docker --context colima`를 사용하면 전역 Docker 컨텍스트 변경 없이 대상을 지정할 수 있다.
- B의 setup에는 호스트 `.lake/packages`가 필요하며, 보고서는 이 전제를 명시한다.
- A의 전체 재빌드 조건은 발견 1처럼 수정해야 한다.

OrbStack의 0.44~1.46 GiB, 7.41 GiB와 원본 OOM 발생은 사용자 머신의 고정 기대값이 아니다.
성공 기준은 새 대상 재빌드의 종료 상태와 실제 적용된 메모리 제한이다.
전체 빌드는 기존 프로젝트 산출물이 없는 상태에서 별도로 확인해야 한다.

## 생성기와 길이 범위

다음 여섯 인자를 임시 디렉터리에서 실행했다.

```text
0
1
4
1 1x1
16,16,16,16 4x16
0,1,16 Mix
```

출력은 모두 현재 커밋 파일과 바이트 단위로 같았다.
여섯 원본과 여섯 수정본의 Lean 컴파일도 모두 성공했다.
길이 0은 `u64v`를 생성하지 않고 기존 `u64nil`을 사용한다.
길이 1과 16의 새 `simp` 증명은 1x1, 4x16, Mix에서 직접 확인했다.
손 패치가 필요하다는 근거는 없다.

다른 생성기의 최적화는 범위 밖이다.
`wlca.py`의 큰 길이 계산과 `lcTl_parts`의 `rfl`은 별도 조사 후보다.
이번 작업에서 그 비용의 원인을 확인하지 못했다.

## 실행 명령과 결과 파일

다음 명령은 검토 과정에서 실행했다.
긴 경로는 `E`와 저장소 루트 `R`로 표기한다.
실제 Lean 명령 인수는 JSON 결과 파일에도 저장했다.

| 명령 또는 검사 | 결과 파일 |
| --- | --- |
| `git status --short`, `git branch --show-current`, `git log -1 --format=fuller` | `E/status-start.txt`, `E/status-end.txt`, `E/target.txt` |
| `git diff 86fd060 HEAD --stat` | `E/diff-stat.txt` |
| `git diff 86fd060 HEAD -- fv/kraken/lean fv/kraken/AXIOMS.txt fv/kraken/link/out/RESULT` | `E/code.diff` |
| 보호 경로 diff, 증명 문자열 제외 전체 파일 비교, 패키지 revision 확인, ELF 해시 계산 | `E/static-checks.txt` |
| `python3 tools/wit/wlcm.py tools/wit <인자>`에 해당하는 절대 경로 명령 여섯 개 | `E/regen/lean/Fk/*.lean`, `E/static-checks.txt` |
| `pgrep -fl 'bin/lean\|lake'` | 각 Lean 실행 묶음 전에 일치 프로세스 없음 확인 |
| `python3 E/run-lean.py` | `E/lean-commands.json`, `E/orig-WitLcM*.txt`, `E/new-WitLcM*.txt` |
| 위 스크립트의 `lake env lean -R E/<stage> -o E/<stage>/Fk/<module>.olean E/<stage>/Fk/<module>.lean` | 원본·수정본 각 여섯 개의 `.olean`, `E/rebuilt-olean.sha256` |
| `lake env lean E/Recheck.lean` | `E/recheck.txt` |
| `REVIEW_DIR=E lake env lean E/Compare.lean` | `E/compare-final.txt`, `E/final-check-commands.json` |
| `lake env lean tools/Axioms.lean` | `E/axioms.txt` |
| `lake env lean tools/AxiomsAll.lean` | `E/axioms-all.txt` |
| `INSPECT_MOD=Fk.WitLcM4x16 lake env lean ../memopt/Inspect.lean` | `E/inspect-current.txt`, `E/inspect-current-match.txt` |
| 기록된 원시 시간·RSS와 요약 비교, Inspector 출력 diff | `E/evidence-crosscheck.txt` |
| 빌드 로그의 `Built`, `Replayed`, 종료 상태 분석 | `E/log-audit.txt` |
| 보존된 `.olean` SHA256 대조 | `E/artifact-hash-check.txt` |
| `python3 E/diagnostic-repro/gen.py`와 생성된 `C1.lean` 검사 | `E/diagnostic-repro.txt`, `E/diagnostic-C1.txt` |
| 가짜 Docker 명령으로 `sh fv/kraken/memopt/lowmem/run.sh <stage>` 실행 | `E/stub-bin/docker`, `E/wrapper-exit-test.txt` |
| 합성 디렉터리의 `rsync -a --delete --exclude='/*/.lake'` 검사 | `E/rsync-exclusion-test.txt` |

초기 `/usr/bin/time -l` 실행은 샌드박스의 `sysctl kern.clockrate` 제한으로 종료 상태 1을 반환했다.
따라서 그 실행을 성능 측정으로 사용하지 않았다.
측정 도구를 제거하고 열두 대상 파일을 다시 컴파일했다.
기록은 `E/time-sandbox-failure.txt`에 있다.

검토용 Lean 파일의 초기 시도에는 이름 해석과 검사 코드 오류가 있었다.
오류를 수정했고, 최종 검사들은 종료 상태 0을 반환했다.
초기 오류 기록도 `E/`에 보존했다.
발견 3의 생성된 진단 파일 오류는 검토용 파일 오류와 별개다.

전체 프로젝트 빌드, Docker 저메모리 실행, 링크 검사, 부정 시험과 Go 시험은 다시 실행하지 않았다.
그 항목은 기존 M4 로그를 검토했다.
의존성 전체의 별도 초기 빌드와 사용자 Colima 직접 재현은 확인하지 못했다.
한국어 문장은 ASD-STE100의 구조 원칙을 적용했으며, 공식 영문 사전 준수를 인증하지 않는다.

## 필수 수정 목록

1. 발견 1을 수정한다. 사용자 머신의 전체 저메모리 재현에서 기존 프로젝트 산출물 재사용을 막고 측정값을 남긴다.
