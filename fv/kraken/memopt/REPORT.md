# REPORT: WitLcM4x16 메모리 최적화 (memopt)

## 0. 판정

**조건부.** 9.69 GiB 컨테이너에서 원본 단독 빌드는 OOM kill로 실패한다. 수정본 단독과 전체 빌드는 성공한다.

조건:

1. 사용자 머신(macOS 16 GiB, Colima 10 GiB Linux aarch64)에서 재현하지 않았다. 저메모리 결과는 OrbStack 컨테이너의 모사다. 재현 절차는 8.2절이다.
2. 전체 빌드의 여유 2.28 GiB는 보장값이 아니다. 이 값은 OrbStack, CPU 18개, 기본 병렬도, 1회 측정의 관측값이다. Colima에서는 재지 않았다.

독립 리뷰(gpt-6-astra)는 끝났다. 판정은 조건부, 필수 수정 1건, 권고 2건이다. 세 건 모두 반영했다(11절).

## 1. 기준과 최종

| 항목 | 값 |
| --- | --- |
| 기준 | 브랜치 `syjn99/ssz-fv-cleanup`, SHA `86fd060349257c133e981e420120f63c61f582e1` |
| 작업 브랜치 | `syjn99/ssz-fv-memopt` |
| 최종 | 브랜치 `syjn99/ssz-fv-memopt` 끝 커밋. `git log -1`로 확인한다 |
| Lean 소스 | `e5fb3d3` 뒤 `fv/kraken/lean` diff는 없다. 저메모리 측정(`e5fb3d3`)은 최종 Lean 소스와 같다 |
| 보호 ELF | `fv/kraken/link/out/p1bin-amd64` sha256 `9c850c97066b9d33d6e4c5ef0a385dcbe2c984ae774a527cdedd18d2b72ac501`. 기준과 같다 |

커밋(`86fd060..`브랜치 끝):

| 커밋 | 내용 |
| --- | --- |
| `daa9dbc` | M1: 원본 baseline |
| `1bd8c02` | M2: 원인 분리 |
| `df6d7bd` | M3: 생성기 1줄 변경과 재생성 |
| `e5fb3d3` | M3: 변경 기록과 inspector 결과 |
| `54ac82e` | M4: 전체 회귀와 9.69 GiB 컨테이너 검증 |
| `509faff` | M5: `link/out/RESULT` 갱신 |
| `e8f95e3` | M5: 이 보고서와 `HISTORY.md` 단락 |
| `253a84a` | M6: 독립 리뷰 본문과 증거(`memopt/review/`) |
| 끝 커밋 | M6: 리뷰 반영(8.2절 재현 절차, `run.sh` 종료 코드, `gen.py` 원본) |

## 2. 변경 파일

`git diff --stat 86fd060 509faff -- . ':!fv/kraken/memopt'`는 6개 파일, 17줄 추가, 17줄 삭제다.

| 파일 | 변경 | 이유 |
| --- | --- | --- |
| `lean/tools/wit/wlcm.py` | 1줄. `u64v{i}`의 증명 `by decide`를 `by simp [u64Bytes, EthLib.Serialization.Ssz.uintBytes]`로 바꾼다 | `decide`의 elaboration이 peak를 정한다(M2 3.1, 3.2) |
| `lean/Fk/WitLcM1x1.lean` | 재생성. 증명 줄 1개 | 같은 생성기의 출력 |
| `lean/Fk/WitLcM4x16.lean` | 재생성. 증명 줄 4개 | 같은 생성기의 출력 |
| `lean/Fk/WitLcMMix.lean` | 재생성. 증명 줄 2개 | 같은 생성기의 출력 |
| `AXIOMS.txt` | 7줄. 위 `u64v` 정리의 공리가 `[]`에서 `[Quot.sound, propext]`로 바뀐다 | `simp` 증명은 `propext`, `Quot.sound`를 쓴다. 둘 다 허용 공리다 |
| `link/out/RESULT` | 2줄. `AXIOMS.txt` sha256과 BUNDLE sha256 | `fv/AGENTS.md` "알려진 답": ELF 해시가 `AXIOMS.txt`를 묶는다 |

`memopt/` 아래(`509faff`에서 추적 파일 319개):

| 경로 | 내용 |
| --- | --- |
| `ENV.md`, `M1-BASELINE.md`, `M2-CAUSE.md`, `M3-CHANGE.md`, `M4-VERIFY.md` | 단계별 보고서 |
| `measure.sh` | macOS 측정 도구(`/usr/bin/time -l`과 0.5 s RSS 표본) |
| `Inspect.lean` | `.olean` inspector |
| `lowmem/run.sh`, `cmeasure.sh`, `Dockerfile` | 9.69 GiB 컨테이너 검증 |
| `scratch/*.lean`, `scratch/gen.py` | M2 진단 파일 26개. 증명으로 쓰지 않는다 |
| `artifacts/` | inspector 출력, `inspect.diff`, `olean.sha256`. `.olean`, `.ilean`은 git이 무시한다 |
| `logs/` | 측정 로그 268개. M5가 `m5-link.txt`를, M6가 `m6-*.txt` 2개를 더한다 |
| `review/` | 독립 리뷰 본문과 증거. `review/README.md`가 파일 역할을 적는다 |

## 3. 모델과 세션

| 역할 | 모델 | Claude Code 세션 ID | Orca 터미널 |
| --- | --- | --- | --- |
| 오케스트레이터 | Claude Fable 5.1 (`claude-fable-5-1`) | `1ed5ce76-4249-4990-9a56-ff7e3bf4dcd8` | 기록 없음 |
| M1 실행자 | Claude Opus 5.5 (`claude-opus-5-5`) | `8f59b152-2fb0-46d1-bc3b-720512a2031a` | `term_7808bd2a-4b86-4a40-98fe-7ce8b429a43d` |
| M2 실행자 | Claude Opus 5.5 (`claude-opus-5-5`) | `86e99ddd-2f6f-44bb-ab17-3e2f399311d8` | `term_5525b821-81d4-44d5-8522-8a65fedc6917` |
| M3 실행자 | Claude Opus 5.5 (`claude-opus-5-5`) | `41c39677-b5cd-41f2-a673-11963168d812` | `term_fa8167b6-ff38-4ec6-8bb3-fcb2d627f932` |
| M4 실행자 | Claude Opus 5.5 (`claude-opus-5-5`) | `f13b3406-f217-439a-877c-6d970585c7e8` | `term_ed352d24-0977-4ec0-a4ef-c526be7399f4` |
| M5 실행자 | Claude Opus 5.5 (`claude-opus-5-5`) | `806ed31a-c07d-4c52-8861-bc66c87b9fe3` | `term_3689a4eb-7ded-4038-8eb6-7ad372243dd2` |

- 실행자 모델명은 각 세션의 시스템 프롬프트에서 읽었다. 세션 ID는 scratchpad 경로에서 읽었다.
- `orca status --json`에는 `caller` 필드가 없다(M1). 그래서 Orca 터미널 핸들을 적는다.

## 4. Benchmark

### 4.1 환경

| 환경 | 값 |
| --- | --- |
| macOS (M1–M4 A) | Apple M5 Pro, 48 GiB, 18코어, swap 0, macOS 26.7.2. `lean` 4.36.0-nightly-2026-09-21 (`ca39d2bc…`). 상세는 `ENV.md` |
| 저메모리 (M4 B) | OrbStack 컨테이너, Linux aarch64, `memory.max` 9922 MiB(9.69 GiB), `memory.swap.max` 0, `nproc` 18. 상세는 `M4-VERIFY.md` B.1 |
| 의존성 | Kraken `6064eec`, EthLib `8621856` (`lake-manifest.json`). 원본과 수정본은 같은 의존 `.olean`을 쓴다 |
| 병렬도 | Lake 기본값. `LEAN_NUM_THREADS`는 설정하지 않았다 |

macOS 측정 명령은 `fv/kraken/lean`에서 `../memopt/measure.sh <label> <cmd>`다.
macOS peak RSS는 `/usr/bin/time -l`의 최대 단일 프로세스 값이다.
저메모리 측정 명령은 저장소 루트에서 `fv/kraken/memopt/lowmem/run.sh <stage>`다.
저메모리 peak는 cgroup `memory.peak`와 GNU `/usr/bin/time -v` max RSS다.

### 4.2 단독 빌드 (macOS)

| 명령 | 상태 | exit | peak RSS (GiB) | wall (s) | 로그 |
| --- | --- | --- | --- | --- | --- |
| `lake env lean Fk/WitLcM4x16.lean` | 원본 (M1, 3회) | 0, 0, 0 | 13.01, 13.26, 13.27 | 18.00, 17.71, 18.48 | `logs/m4x16-r{1,2,3}.*` |
| `lake env lean Fk/WitLcM4x16.lean` | 수정 (M3, 3회) | 0, 0, 0 | 1.42, 1.42, 1.42 | 3.78, 3.62, 3.55 | `logs/m3-m4x16-r{1,2,3}.*` |

### 4.3 전체 빌드 (macOS, `.lake/build` 삭제 뒤)

| 명령 | 상태 | exit, jobs | 최대 단일 RSS (GiB) | 자손 RSS 합계 최대 (GiB) | wall (s) | 로그 |
| --- | --- | --- | --- | --- | --- | --- |
| `lake build` | 원본 (M1) | 0, 856 | 13.19 | 19.08 | 173.11 | `logs/full-r1.*` |
| `lake build` | 수정 (M4) | 0, 856 | 4.46 | 16.96 | 153.56 | `logs/m4-full.*` |

수정본의 최대 단일 프로세스는 `Fk.WitLcA4x16`으로 추정한다. 확인하지 않았다(`M4-VERIFY.md` A.3).

### 4.4 저메모리 (9.69 GiB, swap 0, M4 B.3)

| 단계 | 명령 | exit | `memory.peak` (GiB) | max RSS (GiB) | wall (s) | `oom_kill` | 로그 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 원본 단독 1 | `lake build Fk.WitLcM4x16` | 1 (lean 137) | 9.69 (상한) | 11.16 | 4 | 1 | `logs/lm-orig-1.*` |
| 원본 단독 2 | 같음 | 1 (lean 137) | 9.69 (상한) | 11.18 | 5 | 1 | `logs/lm-orig-2.*` |
| 수정본 단독 1 | 같음 | 0 | 0.44 | 1.80 | 3 | 0 | `logs/lm-new-1.*` |
| 수정본 단독 2 | 같음 | 0 | 1.46 | 1.77 | 3 | 0 | `logs/lm-new-2.*` |
| 수정본 전체 | `.lake/build` 삭제 뒤 `lake build` | 0 (856 jobs) | 7.41 | 4.78 | 96 | 0 | `logs/lm-full.*` |
| 수정본 공리 | `sh tools/axioms.sh` | 0 | 0.25 | 1.79 | 13 | 0 | `logs/lm-axioms.*` |

- max RSS가 `memory.peak`보다 클 수 있다. RSS는 mmap 파일 페이지를 센다. 이 설명은 추정이다(M4 B.4).
- 원본 전체 빌드는 저메모리에서 실행하지 않았다. 단독 빌드가 이미 OOM kill로 실패한다.

## 5. Assertion과 공리 검증

### 5.1 원인 (M2)

- `u64v0`–`u64v3`의 `by decide`가 elaboration에서 `u64Bytes`의 `Array ++` 사슬을 계산한다.
- 하나는 기준선보다 2.95 GiB를 더 쓴다. `Elab.async`가 넷을 동시에 elaborate한다. 그래서 peak가 약 13 GiB다.
- kernel을 생략해도 peak는 같다(C6, C7). 같은 명제를 `simp`로 증명하면 전체 파일이 1.42 GiB다(C10).

### 5.2 Inspector (M3 3절)

- 소스: `fv/kraken/memopt/Inspect.lean`. `Lean`만 import한다. `importModules`로 실제 `.olean`을 읽는다.
- 대상 모듈의 모든 상수를 출력한다: 이름, 소유 모듈, 종류, level params, `pp.all` 타입, 타입 `Expr.hash`.
- 정의는 값 `Expr.hash`와 사용 상수도 출력한다. 모든 상수에 `collectAxioms`를 출력한다.
- 대상: `WitLcM0`, `WitLcM1`, `WitLcM1x1`, `WitLcM4`, `WitLcM4x16`, `WitLcMMix`.
- 결과: `diff`는 7줄이다. 모두 `u64v`의 공리 줄이다(`#[]`에서 `#[propext, Quot.sound]`로). 출력은 `artifacts/inspect.diff`다.
- 그 밖의 줄은 같다. 상수 수, 이름, 소유 모듈, 종류, 타입, 타입 hash, 정의 값 hash, 내부 상수 목록을 포함한다.
- 외부 정의(`u64Bytes`, `uintBytes`, `lcElem`, `lc_marshal_main` 등): `git diff 86fd060 -- fv/kraken/lean/Fv fv/kraken/lean/Fv1 fv/kraken/lean/Fk`는 위 witness 셋만 보인다. manifest, toolchain, lakefile의 diff는 없다.

한계:

- 이 inspector는 두 `.olean`을 한 환경에 적재하지 않았다. `Expr.hash`는 충돌할 수 있다. `pp.all` 텍스트 일치가 그 보완이다.
- 독립 리뷰가 이 한계를 보완했다. 원본과 수정본을 별도로 컴파일하고 두 환경으로 읽었다. 선언 290개의 타입과 정의 값 57개가 `Expr.equal`로 같다(`review/compare-final.txt`).
- 두 환경의 동등성을 kernel 정리로 증명하지는 않았다. 정리의 증명 값은 비교하지 않았다. 증명 값의 변경이 이 최적화다.
- 원본과 수정본을 별도 artifact 디렉터리에서 각각 cold 빌드하지 않았다. 원본 `.olean`은 빌드 뒤 복사로 보존했다.

### 5.3 공리

| 범위 | 기준 (`86fd060`) | 최종 |
| --- | --- | --- |
| 정리 (`AXIOMS.txt`) | `TOTAL 1571 NONSTANDARD 0` | `TOTAL 1571 NONSTANDARD 0` |
| 모든 선언 (`AXIOMS-ALL.txt`) | `TOTAL 7975 NONSTANDARD 0` | `TOTAL 7975 NONSTANDARD 0` |

- macOS(M3, M4)와 Linux 컨테이너(M4 B) 모두 같은 결과다. Linux에서 쓴 `AXIOMS.txt`는 커밋본과 같았다.
- 새 `sorry`, `axiom`, `native_decide`, `bv_decide`는 없다.

## 6. 회귀 (M4 A, macOS)

| # | 검사 | 결과 | 로그 (`memopt/logs/`) |
| --- | --- | --- | --- |
| 1 | `lake build` (cold 프로젝트) | 856 jobs 성공 | `m4-full.*` |
| 2 | `sh tools/axioms.sh` | 두 범위 `NONSTANDARD 0` | `m4-axioms.txt` |
| 3 | `lake env lean tools/RegressFix2.lean` | 오류 없음 | `m4-regressfix2.txt` |
| 4 | review Lean 파일 11개 | 오류 없음 | `m4-review.txt`, `m4-review-b0.txt` |
| 5 | `layout.go`, `goval.py` | layout diff 없음. 79 파일, 위반 0, 미검사 2 | `m4-goval.txt` |
| 6 | `check.py`, `--selftest` | `PASS all`. 24 cases 기대대로 | `m4-link.txt`, `m5-link.txt` |
| 7 | `negative/run.sh` (워크트리 밖) | 16 cases `ok`. `negative/RESULT` diff 없음 | `m4-negative.txt` |
| 8 | `go test ./fv/kraken/semtest/` | F1, F2 PASS | `m4-semtest.txt` |
| 9 | 보호 파일 | ELF sha256 기준과 같다 | `m4-protect.txt` |

- M4에서 `check.py`는 `link/out/RESULT`의 두 줄을 바꾸었다. M5가 그 diff를 확인하고 `509faff`로 커밋했다.
- M5 확인: diff는 `AXIOMS.txt` sha256 줄과 BUNDLE 줄뿐이다. ELF, `norm/*.S`, `build-ids.txt`의 diff는 없다.
- `check.py`는 Lean을 실행하지 않는다. 외부 명령은 `go`, `clang`, `llvm-objdump`뿐이다.

`REPORT.md`(프로젝트) 8절 확인:

- 명령은 그대로 유효하다. 단, 두 줄은 cwd 주의가 필요하다(M4 A.1).
- `goval.py` 줄은 저장소 루트에서 실행하면 `0 witness files`를 낸다. `fv/kraken/lean`에서 실행해야 한다.
- `Review1bFixB0.lean`은 `vcgen/`에서 실행한다. `vcgen/.lake`가 없으면 먼저 `lake build Kraken.FunSpec`을 실행해야 한다.
- 이 브리프는 8절을 고치지 않게 한다. 그래서 고치지 않았다.

## 7. 재생성

`fv/kraken/lean`에서 실행한다. 모두 exit 0이다(M3 1.1).

```sh
python3 tools/wit/wlcm.py tools/wit 0
python3 tools/wit/wlcm.py tools/wit 1
python3 tools/wit/wlcm.py tools/wit 4
python3 tools/wit/wlcm.py tools/wit 1 1x1
python3 tools/wit/wlcm.py tools/wit 16,16,16,16 4x16
python3 tools/wit/wlcm.py tools/wit 0,1,16 Mix
```

- `WitLcM0`, `WitLcM1`, `WitLcM4`는 diff가 없다. 이 셋에는 `u64v`가 없다.
- 나머지 셋의 diff는 7줄이다. 각 줄의 ` := ` 왼쪽(명제)은 바이트 단위로 같다. 오른쪽(증명)만 바뀌었다.
- 커밋된 witness 파일은 생성기 출력과 같다. 손 패치는 없다.

## 8. 남은 제약과 사용자 머신 재현

### 8.1 제약

- 저메모리 결과는 OrbStack VM 안의 cgroup 상한이다. Colima VM과 커널, CPU 수가 다를 수 있다.
- 전체 빌드 peak 7.41 GiB는 동시 lean 프로세스 18개에서 쟀다. 병렬 프로세스 합이 peak를 정한다.
- 이 Lake에는 `-j` 옵션이 없다. 병렬도를 낮추는 재시도 방법은 확인하지 않았다.
- 다른 witness는 바꾸지 않았다. `WitLcA4x16`은 macOS 단독 4.44 GiB다(10절).

### 8.2 재현 명령 (사용자 머신)

사용자 환경: macOS 16 GiB, Colima 10 GiB, Linux aarch64 작업 컨테이너(약 9.69 GiB, swap 0).

성공 기준은 실제 재빌드(로그에 `Built` 기록)의 exit 0과 적용된 `memory.max`다.
OrbStack 수치(아래 표)는 고정 기대값이 아니다.

A. 작업 컨테이너 안에서 직접 빌드한다(주 방법). 저장소 루트에서 시작한다.

`<remote>`는 사용자의 fork remote다. 대상은 `syjn99/ssz-fv-memopt` 끝 커밋이다. `git log -1`로 확인한다.

```sh
git fetch <remote> syjn99/ssz-fv-memopt
git checkout --detach FETCH_HEAD
git log -1                                 # syjn99/ssz-fv-memopt 끝 커밋인지 확인한다
cd fv/kraken/lean
```

A(a). 증분 빌드(참고용). 기존 산출물을 재사용한다.

```sh
cat /sys/fs/cgroup/memory.events           # oom_kill 값을 적는다
lake build
cat /sys/fs/cgroup/memory.events
```

- 이 결과는 저메모리 검증이 아니다. Lake는 유효한 기존 산출물을 `Replayed`로 재사용한다.
- 성공 메시지의 jobs 수(856)는 재컴파일한 모듈 수가 아니다.

A(b). 검증용 전체 재빌드. 프로젝트 산출물 `.lake/build`를 지운다.
의존성 산출물 `.lake/packages`(Kraken, EthLib 등)는 지우지 않는다.
컨테이너에 `trash`가 없을 수 있다. 그래서 Linux의 재귀 삭제 명령을 쓴다.

```sh
cat /sys/fs/cgroup/memory.max              # 적용된 상한을 적는다
cat /sys/fs/cgroup/memory.events           # 시작 oom_kill 값을 적는다
rm -rf .lake/build                         # 프로젝트 산출물만. .lake/packages는 유지한다
/usr/bin/time -v -o /tmp/memopt-full.time.txt lake build > /tmp/memopt-full.out.txt 2>&1; echo "exit $?"
cat /sys/fs/cgroup/memory.events           # 종료 oom_kill 값을 적는다
cat /sys/fs/cgroup/memory.peak             # 파일이 있으면 적는다
grep -E 'Exit status|Elapsed|Maximum resident' /tmp/memopt-full.time.txt
grep -c ' Built ' /tmp/memopt-full.out.txt # OrbStack: 159
grep 'Built Fk.WitLcM4x16' /tmp/memopt-full.out.txt
tail -1 /tmp/memopt-full.out.txt           # Build completed successfully (856 jobs).
sh tools/axioms.sh                         # TOTAL 1571 NONSTANDARD 0, ALL-DECLARATIONS TOTAL 7975 NONSTANDARD 0
git status --short                         # 출력 없음
```

- 기록할 값: 시작과 종료의 `oom_kill`, `/usr/bin/time -v`의 exit·wall·max RSS, `memory.peak`(있으면), `memory.max`, `Built` 줄 수.
- `memory.peak` 파일이 없는 커널도 있다. 그러면 `memory.peak`는 적지 않는다.

A(c). 단독 빌드. A(b) 뒤에 한다. 이 모듈의 산출물을 지워 lake가 다시 빌드하게 한다.

```sh
find .lake/build -name 'WitLcM4x16.*' -delete
/usr/bin/time -v lake build Fk.WitLcM4x16  # exit 0. OrbStack max RSS 약 1.8 GiB
```

- `/usr/bin/time`이 없으면 `time` 패키지를 설치하거나 `memory.peak`만 본다.
- 처음 빌드는 의존성(Kraken, EthLib)을 받는다. Mathlib cache는 쓰지 않는다. toolchain과 manifest를 바꾸지 않는다.

A와 B는 다른 셸이다. B 전에 저장소 루트로 돌아간다.

```sh
cd "$(git rev-parse --show-toplevel)"
```

B. `memopt/lowmem/run.sh`로 원본과 수정본을 같이 잰다(선택). Docker 호스트의 저장소 루트에서 실행한다.

`run.sh`는 `docker`를 직접 부른다. 그래서 컨텍스트는 환경 변수 `DOCKER_CONTEXT`로 정한다. 전역 컨텍스트는 바꾸지 않는다.

```sh
export DOCKER_CONTEXT=colima
NEW=$(git rev-parse HEAD) fv/kraken/memopt/lowmem/run.sh image setup env prebuild-new prebuild-orig
NEW=$(git rev-parse HEAD) fv/kraken/memopt/lowmem/run.sh orig-1 new-1 new-2 full axioms
fv/kraken/memopt/lowmem/run.sh clean
unset DOCKER_CONTEXT
```

주의:

- 스크립트는 OrbStack에서 만들었다. `DOCKER_CONTEXT`가 없으면 지금 docker 컨텍스트를 쓴다.
- `orig-*` 단계는 실패(OOM)를 기대한다. 그 exit는 스크립트를 멈추지 않는다.
- `new-*`, `full`, `axioms` 단계가 실패하면 스크립트는 그 exit로 멈춘다. 뒤 단계는 실행하지 않는다.
- `full` 단계는 컨테이너 안 수정본의 `.lake/build`를 지운 뒤 빌드한다. 의존성 산출물(`/work/pkgs`)은 유지한다.
- `--memory=9922m`은 Colima VM 전체 RAM(약 9.69 GiB)과 거의 같다. VM의 OOM이 cgroup OOM보다 먼저 올 수 있다. 그러면 `oom_kill` 값이 아니라 컨테이너 종료로 보인다.
- `setup`은 호스트의 `fv/kraken/lean/.lake/packages` 소스를 복사한다. 호스트에 그 디렉터리가 없으면 `setup`은 실패한다.
- `image`는 elan과 toolchain을 네트워크로 받는다.
- 이미지 크기는 3.67 GB다. 끝나면 `docker --context colima image rm memopt-lowmem`으로 지울 수 있다.

OrbStack 관측값(고정 기대값이 아니다. 사용자 머신에서는 다를 수 있다):

| 항목 | OrbStack 관측값 |
| --- | --- |
| 원본 단독 | exit 1, `Lean exited with code 137`, `oom_kill` 1 |
| 수정본 단독 | exit 0, `memory.peak` 0.44–1.46 GiB, max RSS 약 1.8 GiB |
| 수정본 전체 | exit 0, `Built` 159줄, 856 jobs, `memory.peak` 7.41 GiB, `oom_kill` 0 |
| 공리 | 두 범위 `NONSTANDARD 0` |

수정본 단독·전체의 exit가 0이 아니거나 `oom_kill`이 늘면 바꾸지 말고 보고한다.
보고에 명령, exit, `memory.max`, `memory.events`, `nproc`, 로그를 넣는다.

## 9. 완료 기준 (HANDOFF.md)

- [x] 원본의 정상 실행 baseline과 측정 로그가 있다. — M1: 단독 3회 13.01–13.27 GiB, 전체 856 jobs, `logs/m4x16-r*`, `logs/full-r1.*`.
- [x] 메모리 급증 지점과 원인에 대한 실측 근거가 있다. — M2: 제거 실험 A0–A4, kernel 생략 C6·C7, 대체 증명 C3·C10, 크기 E1–E16.
- [x] 최적화 전후 동일 조건의 peak RSS와 wall time이 기록돼 있다. — 단독 M1 대 M3, 전체 M1 대 M4. 같은 머신, 같은 `.lake/packages`.
- [x] 공개 assertion 및 참조 정의의 의미가 보존됐다. — inspector diff는 공리 7줄뿐이다. 한계는 5.2절이다(kernel 직접 비교 없음).
- [x] 새 신뢰 가정이 없고 공리 두 범위 `NONSTANDARD 0`이다. — 1571/7975 그대로. 새 공리는 허용 공리 `propext`, `Quot.sound`뿐이다.
- [x] 보호된 코드·ELF·의존성은 변하지 않았다. — ELF sha256 같음. `sszgen`, `ssz`, `target`, manifest, toolchain diff 없음. `link/out` diff는 `RESULT` 2줄뿐이다.
- [x] 전체 baseline 회귀가 성공했거나, 미실행·실패 항목이 명확히 분리됐다. — M4 A 9개 모두 exit 0. `RESULT` diff는 `509faff`로 해결했다.
- [x] 저메모리 환경의 단독/전체 빌드 결과가 있다. — OrbStack 9.69 GiB 컨테이너에서 원본 OOM, 수정본 단독 2/2와 전체 1/1 성공. 사용자 머신 결과는 아니다.
- [x] 생성기에서 재현 가능한 변경이다. — `wlcm.py` 1줄, 재생성 명령 6개, diff 7줄, 손 패치 없음.
- [x] 독립 리뷰가 assertion 약화, cache 혼입, 측정 조건 차이를 확인했다. — gpt-6-astra, `review/REVIEW-gpt6-astra.md`. 별도 컴파일한 원본·수정본의 선언 290개를 `Expr.equal`로 대조했다(`review/compare-final.txt`). 판정과 반영은 11절이다.

추가 항목:

- [ ] 사용자 머신(Colima)에서 직접 재현했다. — 하지 않았다. 8.2절 명령으로 한다.

## 10. 권고 (실행하지 않음)

`grep -n "by decide" lean/tools/wit/*.py` 결과(`fv/kraken`에서):

- 생성기 23개에 `by decide`가 있다: `wadm`, `wbl`, `wblm`, `wblr`, `wblri`, `wbv`, `wbvr`, `wcomp`, `wcompsc`, `wgen`, `wlca`, `wlcm`, `wlcs`, `wlcz`, `wlur`, `wmar`, `wmrej`, `wne`, `wnes`, `wnem`, `wrej`, `wvbvr`, `wsize`.
- 대부분은 작은 수 범위, 레이블 신선성, 길이 같은 부수 조건이다. 이 비용은 측정하지 않았다.
- `u64Bytes`를 `decide`로 계산하는 줄은 `wlcm.py`의 `u64nil`뿐이다. 그 리스트는 비어 있다.
- `wlca.py`의 `lcTl_t0`, `lcTl_t1`은 544바이트 리스트의 길이를 `decide`로 증명한다.
- `wlca.py`의 `lcTl_parts`는 `u64Bytes`를 포함하는 등식을 `rfl`로 닫는다. M2 C2는 같은 크기에서 `rfl`도 `decide`만큼 비싸다고 보였다.

`WitLcA4x16`(macOS 단독 4.44 GiB)에는 `u64v` decide가 없다. 그래서 원인은 이 작업의 원인과 다르다.
그 원인은 조사하지 않았다. 위 `lcTl_*` 증명은 후보일 뿐이다.
다른 witness로 확대할지는 오케스트레이터와 사용자가 정한다.

## 11. 독립 리뷰

| 항목 | 값 |
| --- | --- |
| 리뷰어 | gpt-6-astra |
| 대상 | `e8f95e3` |
| 판정 | 조건부. 증명 변경은 수용할 수 있다. 공개 assertion의 약화는 없다 |
| 근거 | `review/REVIEW-gpt6-astra.md`. 파일 역할은 `review/README.md`다 |

| # | 등급 | 발견 | 반영 | 확인 |
| --- | --- | --- | --- | --- |
| 1 | P1 | 8.2절 A의 `lake build`가 기존 프로젝트 산출물을 재사용할 수 있다. 성공 메시지만으로 저메모리 재빌드를 확인할 수 없다 | 8.2절 A를 증분 빌드(참고용)와 검증용 전체 재빌드로 나눈다. 재빌드는 `.lake/build`를 지우고 `.lake/packages`를 유지한다. `memory.events`, `/usr/bin/time -v`, `memory.peak`, `Built` 줄 수를 기록한다. B의 컨텍스트는 `DOCKER_CONTEXT=colima`로 정한다 | 문서 변경. 사용자 머신 실행은 하지 않았다 |
| 2 | P2 | `lowmem/run.sh`의 `new-[12]`, `full`, `axioms`가 실패를 exit 0으로 바꾼다 | 세 곳의 `\|\| true`를 지운다. `orig-[123]`은 기대 실패라서 남긴다 | 가짜 `docker`(exit 23): `new-1`, `new-2`, `full`, `axioms`는 exit 23, `orig-1`은 exit 0(`logs/m6-wrapper-exit-test.txt`) |
| 3 | P2 | `scratch/gen.py`가 현재 수정본을 읽어서 잘못된 진단 파일을 만든다 | `git show 86fd060:fv/kraken/lean/Fk/WitLcM4x16.lean`에서 원본을 읽는다 | 임시 사본 실행: `A4.lean`이 원본과 바이트 단위로 같다. 생성 파일 23개가 커밋된 `scratch/*.lean`과 같다. `C10.lean`은 HEAD의 `Fk/WitLcM4x16.lean`과 같다. `lake env lean ../memopt/scratch/C1.lean` exit 0(`logs/m6-gen-check.txt`) |

- 반영 커밋: 리뷰 증거 `253a84a`, 수정은 브랜치 끝 커밋 `fix(kraken): apply the memopt review fixes ...`다.
- `scratch/N1.lean`, `N2.lean`은 `gen.py`의 출력이 아니다. M3의 손 진단 파일이다(`M3-CHANGE.md`).
- `C10.lean`이 HEAD의 증인과 같은 이유: C10은 원본의 `u64v` 증명을 M3의 `simp` 증명으로 바꾼 파일이다. M3는 같은 바꿈을 생성기에 넣었다.
