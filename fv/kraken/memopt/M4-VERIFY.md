# M4: 전체 회귀와 9.69 GiB 컨테이너 검증

판정: macOS 회귀는 모두 성공이다. 단, `link/out/RESULT`에 생성물 diff가 있다(A.2절).
저메모리(9.69 GiB, swap 0): 원본 단독은 OOM kill, 수정본 단독과 수정본 전체는 성공이다.

| 저메모리 항목 | exit | `memory.peak` (GiB) | `oom_kill` |
| --- | --- | --- | --- |
| 원본 단독 (2회) | 1, 1 (lean 137) | 9.69, 9.69 (상한) | 1, 1 |
| 수정본 단독 (2회) | 0, 0 | 0.44, 1.46 | 0, 0 |
| 수정본 전체 (1회) | 0 | 7.41 | 0 |

- 모델: Claude Opus 5.5 (`claude-opus-5-5`, 시스템 프롬프트 기준).
- Orca 터미널: `ORCA_TERMINAL_HANDLE=term_ed352d24-0977-4ec0-a4ef-c526be7399f4`.
- Claude Code 세션 ID: `f13b3406-f217-439a-877c-6d970585c7e8` (scratchpad 경로에서 읽었다).
- 기준: 브랜치 `syjn99/ssz-fv-memopt`, HEAD `e5fb3d3`. 소스는 바꾸지 않았다.
- Lean 빌드는 한 번에 하나만 돌렸다. A를 끝낸 뒤 B를 시작했다.

## A. macOS 회귀 (48 GiB, arm64, swap 0)

명령과 cwd는 `REPORT.md` 8절을 따랐다. 로그는 `memopt/logs/`에 있다.

| # | 명령 | cwd | exit | 핵심 출력 | 로그 |
| --- | --- | --- | --- | --- | --- |
| 1 | `trash .lake/build && ../memopt/measure.sh m4-full lake build` | `fv/kraken/lean` | 0 | `Build completed successfully (856 jobs)`, 153.56 s | `m4-full.*` |
| 2 | `sh tools/axioms.sh` | `fv/kraken/lean` | 0 | `TOTAL 1571 NONSTANDARD 0`, `ALL-DECLARATIONS TOTAL 7975 NONSTANDARD 0`, AXIOMS diff 없음 | `m4-axioms.txt` |
| 3 | `lake env lean tools/RegressFix2.lean` | `fv/kraken/lean` | 0 | 오류 없음 | `m4-regressfix2.txt` |
| 4a | `lake env lean ../review/<f>.lean` (10개) | `fv/kraken/lean` | 모두 0 | 오류 없음 | `m4-review.txt` |
| 4b | `lake build Kraken.FunSpec`, `lake env lean ../review/Review1bFixB0.lean` | `fv/kraken/vcgen` | 0, 0 | `[propext, Classical.choice, Quot.sound]` | `m4-review-b0.txt` |
| 5a | `go run fv/kraken/lean/tools/wit/layout.go > …/layout.json` | 저장소 루트 | 0 | `git diff --stat` 출력 없음 | `m4-goval.txt` |
| 5b | `python3 tools/wit/goval.py` | `fv/kraken/lean` | 0 | `79 witness files, 0 with a violation, 2 with a value not checked` | `m4-goval.txt` |
| 6a | `python3 fv/kraken/link/check.py fv/kraken/link/out` | 저장소 루트 | 0 | `PASS all`, `BUNDLE sha256 215df515…9829` | `m4-link.txt` |
| 6b | `python3 fv/kraken/link/check.py --selftest fv/kraken/link/out` | 저장소 루트 | 0 | 24 cases, 모두 expected | `m4-link.txt` |
| 7 | `fv/kraken/negative/run.sh SCRATCH/memopt/negative-out` | 저장소 루트 | 0 | 16 cases 모두 `ok`, 624 s, `negative/RESULT` diff 없음 | `m4-negative.txt` |
| 8 | `GOROOT=$(go env GOROOT) go test ./fv/kraken/semtest/` | 저장소 루트 | 0 | `TestF1BitvectorPadding`, `TestF2BitlistByteLimit` PASS | `m4-semtest.txt` |
| 9 | `shasum -a 256 fv/kraken/link/out/p1bin-amd64`, `git status --short` | 저장소 루트 | 0 | `9c850c97…c501` 기준과 같음 | `m4-protect.txt` |

### A.1 실행 메모

- 4a: `ReviewReproveFix`, `ReviewReproveFix2` 출력에 문자열 `error`가 있다. 그 줄은 레이블 `go_itab._errors.errorString_error`다. 오류 메시지가 아니다.
- 4b: `vcgen/`에는 `.lake`가 없었다. 첫 `lake env lean`은 의존성을 fetch한 뒤 `unknown module prefix 'Kraken'`으로 exit 1이었다.
  - `lake env lean`은 import를 빌드하지 않는다. 그래서 `lake build Kraken.FunSpec`(53 jobs, 15 s)을 먼저 실행했다. 다시 실행한 결과는 exit 0이다.
  - `vcgen/.lake`는 git이 무시한다. 두 시도 모두 로그에 있다.
- 5b: 브리프의 cwd(저장소 루트)에서 `goval.py`는 `0 witness files`를 낸다. HANDOFF.md의 올바른 cwd `fv/kraken/lean`에서 다시 실행했다. 두 출력 모두 로그에 있다.
- 7: 결과 디렉터리는 `SCRATCH/memopt/negative-out`이다. 워크트리 밖이다.

### A.2 생성물 diff: `link/out/RESULT`

- `check.py`가 `link/out/RESULT`를 다시 쓴다. 두 줄이 바뀐다.
  - `file sha256 … AXIOMS.txt`: `8e4632f2…a488`에서 `dde4d7bb…d2b2`로.
  - `BUNDLE sha256`: `f28fa78c…621c`에서 `215df515…9829`로.
- 원인: M3(`df6d7bd`)가 `AXIOMS.txt`의 `u64v` 정리 7줄을 바꾸었다. 그 커밋은 `RESULT`를 갱신하지 않았다.
- 브리프 D에 따라 이 diff는 커밋하지 않았다. 전체 diff는 `logs/m4-link.txt` 끝에 있다.
- 작업 트리의 `RESULT`는 커밋본으로 되돌렸다(`git checkout -- fv/kraken/link/out/RESULT`). 6a를 다시 실행하면 같은 diff가 생긴다.
- 갱신 여부는 오케스트레이터가 정한다.

### A.3 전체 빌드 메모리 (M1 원본과 비교)

| 항목 | M1 `full-r1` (원본 `86fd060`) | M4 `m4-full` (수정본 `e5fb3d3`) |
| --- | --- | --- |
| exit, jobs | 0, 856 | 0, 856 |
| wall | 173.11 s | 153.56 s |
| 최대 단일 프로세스 RSS (`/usr/bin/time -l`) | 13.19 GiB | 4.46 GiB |
| 자손 RSS 합계 최대 (0.5 s 표본) | 19.08 GiB | 16.96 GiB |
| 8 GiB를 넘는 프로세스 | 있음 (경과 154–169 s) | 없음 (표본 0개) |
| `WitLcM4x16` 빌드 시간 | 22 s | 6.3 s |
| `WitLcM4x16.olean` | 841528 바이트 | 1056528 바이트 |

- 최대 단일 프로세스 표본은 4.45 GiB(4668992 KiB)다. 경과 132–140 s에서 3.9 GiB를 넘는다.
- 그 프로세스는 `Fk.WitLcA4x16`일 것으로 추정한다. 표본은 모듈 이름을 적지 않으므로 확인하지 않았다.
  - 근거 1: M1의 `WitLcA4x16` 단독 peak가 4.44 GiB다.
  - 근거 2: `WitLcA4x16`의 빌드 시간은 16 s다. 출력에서 `[836/856]`으로 끝난다. 이는 끝 부분 순서와 맞는다.
- 모듈 빌드 시간 상위: `Fk.LcLoop` 39 s, `Fk.AdMarshal` 32 s, `Fk.AdAccept` 27 s, `Fk.NeMarshal` 18 s.
- 조건은 M1과 같다. `.lake/build`만 지웠고 `.lake/packages`는 유지했다. `LEAN_NUM_THREADS`는 설정하지 않았다.

## B. 저메모리 검증 (OrbStack 컨테이너)

### B.1 환경

| 항목 | 값 |
| --- | --- |
| 실행 | `docker run --memory=9922m --memory-swap=9922m`, 단계마다 새 컨테이너(새 cgroup) |
| `memory.max` | `10403971072` (9922 MiB = 9.69 GiB) |
| `memory.swap.max` | `0` |
| `--cpus` | 지정 안 함(기본). 사용자 환경의 CPU 수를 모른다 |
| `nproc` | 18 |
| `uname -m`, 커널 | `aarch64`, `7.2.12-orbstack-00394-gbecdd6130068` |
| `free -m` (VM 전체) | Mem total 16037, Swap total 17061 |
| `lean --version` | `4.36.0-nightly-2026-09-21, aarch64-unknown-linux-gnu, commit ca39d2bc730f…` |
| 이미지 | `memopt-lowmem` (ubuntu:24.04, elan, toolchain `leanprover/lean4:nightly-2026-09-21`) |
| 소스 | 워크트리 `git clone`. `/work/new` = `e5fb3d3`, `/work/orig` = `86fd060` |
| 의존성 | macOS `.lake/packages`의 소스만 `rsync`로 복사(`--exclude='/*/.lake'`). 네트워크 fetch 없음 |
| 의존성 공유 | 두 clone의 `.lake/packages`는 같은 `/work/pkgs`로의 심볼릭 링크다 |

- VM에는 swap 17061 MB가 있다. 그러나 cgroup의 `memory.swap.max`가 0이다. 그래서 컨테이너는 swap을 쓸 수 없다.
- macOS `.olean`은 컨테이너에 넣지 않았다. 다른 플랫폼에서 빌드한 산출물을 섞으면 그 빌드를 Linux 결과로 볼 수 없다.
  - 복사 뒤 `/work/pkgs` 안의 `.lake` 디렉터리 수는 0이었다. 이 값은 `setup` 단계의 터미널 출력이다. 로그 파일에는 없다.
- 의존성 `.olean`은 컨테이너 안에서 빌드했다. 원본과 수정본은 같은 의존성 `.olean`을 썼다.
- 스크립트: `memopt/lowmem/run.sh`, `cmeasure.sh`, `Dockerfile`. 저장소 루트에서 단계 이름을 인수로 준다.

### B.2 측정 방법

- `cmeasure.sh`는 컨테이너 안에서 명령을 GNU `/usr/bin/time -v`로 돌린다.
- 0.5 s마다 `memory.current`, `memory.peak`, lean 프로세스 수를 적는다. 끝에 `memory.events`를 적는다.
- `memory.peak`는 그 컨테이너 cgroup의 최댓값이다. 컨테이너 시작부터 센다.
- `oom_kill`은 명령 전후 `memory.events` 값의 차이다.
- 단독 빌드 전에 `WitLcM4x16.*` 산출물을 지웠다. 그래서 lake가 그 모듈을 다시 빌드한다.

### B.3 결과

| 단계 | 명령 | exit | `memory.peak` (GiB) | max RSS (GiB) | wall (s) | `oom_kill` | 로그 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 의존성 선빌드 (수정본) | `lake build Fk.LcMarshal Fk.RtCopy Fk.WHost` | 0 (631 jobs) | 4.85 | 3.58 | 107 | 0 | `lm-prebuild-new.*` |
| 의존성 선빌드 (원본) | 같음 | 0 | 2.77 | 3.59 | 78 | 0 | `lm-prebuild-orig.*` |
| 원본 단독 1 | `lake build Fk.WitLcM4x16` | 1 (lean 137) | 9.69 (상한) | 11.16 | 4 | 1 | `lm-orig-1.*` |
| 원본 단독 2 | 같음 | 1 (lean 137) | 9.69 (상한) | 11.18 | 5 | 1 | `lm-orig-2.*` |
| 수정본 단독 1 | `lake build Fk.WitLcM4x16` | 0 (633 jobs) | 0.44 | 1.80 | 3 | 0 | `lm-new-1.*` |
| 수정본 단독 2 | 같음 | 0 (633 jobs) | 1.46 | 1.77 | 3 | 0 | `lm-new-2.*` |
| 수정본 전체 | `.lake/build` 삭제 뒤 `lake build` | 0 (856 jobs) | 7.41 | 4.78 | 96 | 0 | `lm-full.*` |
| 공리 | `sh tools/axioms.sh` | 0 | 0.25 | 1.79 | 13 | 0 | `lm-axioms.*` |

- 의존성 선빌드는 9.69 GiB 안에서 끝났다. 제한 없는 컨테이너는 쓰지 않았다.
- 원본 단독: lake 출력은 `error: Lean exited with code 137`이다. `memory.events`는 `oom 6`, `oom_kill 1`이다. 기대와 같다. 2회에서 멈췄다.
- 수정본 단독: 출력은 `Built Fk.WitLcM4x16 (2.4s)`, `(2.7s)`다.
- 수정본 전체: `Built Fk.WitLcM4x16 (2.7s)`, `Build completed successfully (856 jobs)`. 동시 lean 프로세스는 최대 18개다. peak는 경과 85 s에 생겼다.
- 전체 빌드가 기본 병렬도로 성공했다. 그래서 낮은 병렬도 재시도는 하지 않았다.
  - 참고: 이 Lake에는 `-j` 옵션이 없다(`error: unknown short option '-j'`). 브리프의 `lake build -j4`는 그대로 실행할 수 없다.
- 공리: `TOTAL 1571 NONSTANDARD 0`, `ALL-DECLARATIONS TOTAL 7975 NONSTANDARD 0`.
  - 실행 뒤 컨테이너 clone 두 개의 `git status --short`는 비어 있었다. Linux에서 쓴 `AXIOMS.txt`도 커밋본과 같다.

### B.4 수치 해석의 한계

- max RSS가 `memory.peak`보다 클 수 있다. 원본은 11.16 GiB로 상한 9.69 GiB보다 크다.
  - RSS는 mmap한 `.olean` 같은 파일 페이지를 센다. cgroup은 그 페이지를 먼저 읽은 cgroup에 청구할 수 있다. 이것은 추정이다. 확인하지 않았다.
- `memory.peak`는 그 cgroup에 청구된 page cache를 포함한다. 순수 프로세스 메모리보다 클 수 있다.
- 수정본 단독 1, 2의 `memory.peak` 차이(0.44, 1.46)의 원인은 확인하지 않았다. page cache 청구 차이일 수 있다.
- 그래서 여유는 cgroup 기준과 RSS 기준을 같이 적는다.

## C. 48 GiB 성공과 저메모리 성공 (HANDOFF.md 5절 구분)

| 구분 | 결과 |
| --- | --- |
| 48 GiB 머신 (macOS arm64, swap 0) | 전체 빌드 856 jobs 성공, 회귀 A 전부 exit 0. 예외는 A.2 생성물 diff |
| 저메모리 9.69 GiB (Linux aarch64 컨테이너, swap 0) 단독 | 원본 실패(OOM kill), 수정본 성공 2/2 |
| 저메모리 9.69 GiB 전체 | 수정본 성공 1/1, 공리 검사 성공 |
| swap | 두 환경 모두 0. swap 조건 결과는 없다 |

### C.1 여유

| 항목 | peak (GiB) | 9.69 GiB와의 차이 (GiB) |
| --- | --- | --- |
| 수정본 단독, `memory.peak` | 0.44, 1.46 | 9.25, 8.23 |
| 수정본 단독, max RSS | 1.80, 1.77 | 7.89, 7.92 |
| 수정본 전체, `memory.peak` | 7.41 | 2.28 |
| 수정본 전체, max RSS (단일 프로세스) | 4.78 | 4.91 |

- 전체 빌드의 여유는 2.28 GiB(cgroup 기준)다. 병렬 프로세스 합이 peak를 정한다.
- 사용자 환경은 Colima VM이다. 이 측정은 OrbStack VM 안의 cgroup 제한이다. 두 환경의 커널과 CPU 수가 다를 수 있다.
- 사용자 머신에서 직접 재현하지 않았다.

## D. 미실행·제약

- 사용자 머신(Colima, 16 GiB macOS)에서의 재현은 하지 않았다.
- `-j4` 재시도는 필요하지 않았다. 또 이 Lake에서 `-j`는 없다.
- `link/out/RESULT` 갱신은 하지 않았다(A.2).
- 컨테이너는 단계마다 `--rm`으로 지웠다. 볼륨 `memopt-lowmem-work`도 지웠다. 이미지 `memopt-lowmem`(3.67 GB)은 남겼다.
- 호스트 설정(OrbStack 메모리 등)은 바꾸지 않았다.

## E. 재현

macOS 회귀는 `REPORT.md` 8절이다. 4b와 5b는 A.1절의 cwd를 쓴다.

저메모리(저장소 루트, docker 컨텍스트 `orbstack`):

```sh
fv/kraken/memopt/lowmem/run.sh image setup env prebuild-new prebuild-orig
fv/kraken/memopt/lowmem/run.sh orig-1 orig-2 new-1 new-2 full axioms
fv/kraken/memopt/lowmem/run.sh clean
```
