# M1: WitLcM4x16 메모리 baseline

판정: baseline 확보. 원본 WitLcM4x16 단독 peak RSS는 13.01–13.27 GiB다. 전체 빌드는 856 jobs 성공이다.

- 모델: Claude Opus 5.5 (`claude-opus-5-5`, 시스템 프롬프트 기준).
- 세션: `orca status --json`에 `caller` 필드가 없다. 최상위 키는 `target`, `app`, `runtime`, `graph`뿐이다.
  - 대신 Orca 터미널 `ORCA_TERMINAL_HANDLE=term_7808bd2a-4b86-4a40-98fe-7ce8b429a43d`를 적는다.
  - Claude Code 세션 ID는 `8f59b152-2fb0-46d1-bc3b-720512a2031a`다(scratchpad 경로에서 읽었다).
- 기준: `86fd060`, 브랜치 `syjn99/ssz-fv-memopt`. 환경은 `ENV.md`에 있다.
- 머신: Apple M5 Pro, 48 GiB, 18코어, swap 0. 소스 파일은 바꾸지 않았다.

## 1. 측정 표

모든 명령은 `fv/kraken/lean`에서 `../memopt/measure.sh <label> <cmd>`로 실행했다.
peak RSS는 `/usr/bin/time -l`의 max RSS다. 최대 단일 프로세스 값이다.
"표본 합계"는 0.5초 표본에서 모든 자손 프로세스 RSS 합의 최댓값이다. `lake` 프로세스(약 0.65 GiB)를 포함한다.

| 명령 | exit | peak RSS (GiB) | 표본 합계 (GiB) | wall (s) | 반복 | 로그 |
| --- | --- | --- | --- | --- | --- | --- |
| `lake env lean Fk/WitLcM4x16.lean` | 0, 0, 0 | 13.01, 13.26, 13.27 | 13.62–13.92 | 18.00, 17.71, 18.48 | 3 | `logs/m4x16-r{1,2,3}.*` |
| `lake env lean Fk/WitLcM1x1.lean` | 0 | 1.36 | 1.78 | 3.19 | 1 | `logs/m1x1-r1.*` |
| `lake env lean Fk/WitLcM4.lean` | 0 | 1.37 | 2.01 | 3.54 | 1 | `logs/m4-r1.*` |
| `lake env lean Fk/WitLcA4x16.lean` | 0 | 4.44 | 5.09 | 16.13 | 1 | `logs/a4x16-r1.*` |
| `lake build` (cold 프로젝트, 기본 병렬도) | 0 | 13.19 | 19.08 | 173.11 | 1 | `logs/full-r1.*` |
| `lake env lean --memory=9000 Fk/WitLcM4x16.lean` | 1 | 13.27 | 13.92 | 7.71 | 1 | `logs/m4x16-mem9000.*` |
| `sh tools/axioms.sh` | 0 | 미측정 | 미측정 | 12.11 | 1 | `logs/axioms.out.txt` |

범위 요약: WitLcM4x16 단독 peak 13.01–13.27 GiB, wall 17.71–18.48 s.

## 2. 전체 빌드

- 결과: `Build completed successfully (856 jobs)`. exit 0. wall 173.11 s.
- 조건: `LEAN_NUM_THREADS` 미설정. 빌드 전에 `.lake/build`를 지웠다. `.lake/packages`는 유지했다.
- 최대 단일 프로세스: 13.19 GiB (`/usr/bin/time`). 표본 최대는 13.12 GiB(13756752 KiB), 경과 160 s.
- 모든 자손 RSS 합계 최대: 19.08 GiB, 경과 160 s. 그때 프로세스 4개가 있었다.
- 동시 프로세스 수 최대: 19.
- 8 GiB를 넘는 단일 프로세스는 경과 154–169 s에만 있다.
- 표본은 파일 이름을 적지 않는다. 그 프로세스를 WitLcM4x16으로 보는 것은 추정이다.
  - 근거: 크기가 단독 peak와 같다. WitLcM4x16 빌드 시간은 22 s다.
- `.lake/build/lib/lean/Fk/WitLcM4x16.olean`: 841528 바이트.
- 모듈 빌드 시간 상위: Fk.LcLoop 40 s, Fk.AdMarshal 34 s, Fk.AdAccept 31 s, Fk.WitLcM4x16 22 s, Fk.NeMarshal 19 s.

## 3. 공리

`sh tools/axioms.sh` 결과:

```
TOTAL 1571 NONSTANDARD 0
ALL-DECLARATIONS TOTAL 7975 NONSTANDARD 0
```

`AXIOMS.txt`, `AXIOMS-ALL.txt`는 다시 썼지만 git diff가 없다.

## 4. 관찰: 선언별 시간

`lake env lean --profile` 출력은 `logs/m4x16.profile.txt`에 있다. 100 ms를 넘는 항목은 다음과 같다.

| 순위 | 항목 | 시간 |
| --- | --- | --- |
| 1 | tactic execution of `decide` | 4.04 s |
| 2 | tactic execution of `decide` | 4.04 s |
| 3 | tactic execution of `decide` | 4.02 s |
| 4 | tactic execution of `decide` | 4.00 s |
| 5 | type checking | 2.73 s |
| 6 | type checking | 2.54 s |
| 7 | type checking | 2.48 s |
| 8 | type checking | 2.47 s |
| 9 | import | 1.2 s |
| 10 | type checking | 115 ms |

누적: tactic execution 16.3 s, type checking 10.5 s, simp 333 ms, elaboration 157 ms.
누적 합은 wall 18 s보다 크다. 증명은 병렬로 elaborate된다(`Elab.async`).

`--profile`은 선언 이름을 적지 않는다.
그래서 `-Dtrace.profiler=true -Dtrace.profiler.threshold=100`으로 한 번 더 실행했다.
요약은 `logs/m4x16.trace-profiler.summary.txt`에 있다. 원본 로그는 6.5 GB라서 지웠다.
trace 실행의 시간은 trace 비용을 포함한다. 상대 크기만 쓴다.

| 선언 | elaboration (trace) | kernel 검사 (trace) |
| --- | --- | --- |
| `u64v0` | 14.24 s | 2.49 s |
| `u64v1` | 14.37 s | 2.30 s |
| `u64v2` | 14.38 s | 2.53 s |
| `u64v3` | 14.35 s | 2.43 s |
| `s_mem` | 0.65 s | 0.12 s |
| `block` | 0.18 s | 100 ms 미만 |
| `lc_marshal_runs` | 0.14 s | 100 ms 미만 |

- 시간의 대부분은 `u64v0`–`u64v3`의 `by decide`다. 네 선언은 같은 명제다.
- `s_mem`과 `lc_marshal_runs`는 1 s 미만이다.
- WitLcM4(u64v 없음)와 WitLcM1x1(1원소 u64v 하나)는 1.37 GiB 이하다.
- WitLcA4x16은 같은 크기의 accept 증인이다. `u64v` decide가 없고 peak는 4.44 GiB다.
- 이 표는 시간의 근거다. 메모리가 어느 선언에서 커지는지는 M1에서 측정하지 않았다.

## 5. 관찰: RSS 시계열

`logs/m4x16-r1.rss.txt`: lean RSS는 경과 4 s에 5.0 GiB, 9 s에 12.4 GiB, 11 s에 13.0 GiB다.
그 뒤 끝(18 s)까지 약 13.0 GiB를 유지한다.
`logs/m4x16-mem9000.rss.txt`: 경과 6 s에 12.9 GiB, 8 s에 13.3 GiB다. wall은 7.71 s다.

## 6. `--memory=9000` 시험 (참고 자료)

1회만 실행했다. 이것은 cgroup OOM 재현이 아니다.
exit 1이다. 오류는 다음과 같다.

```
Fk/WitLcM4x16.lean:45:8: error: (kernel) excessive memory consumption detected   (u64v0)
Fk/WitLcM4x16.lean:48:8: ...   (u64v1)
Fk/WitLcM4x16.lean:51:8: ...   (u64v2)
Fk/WitLcM4x16.lean:54:8: ...   (u64v3)
Fk/WitLcM4x16.lean:56:4: ...   (block)
Fk/WitLcM4x16.lean:59:4: error: failed to compile definition, compiler IR check failed at `Fk.WitLcM4x16.mem._closed_1` ...
PANIC at ... Lean.Compiler.LCNF.ExplicitBoxing ...
```

- 상한을 두어도 max RSS는 13.27 GiB였다. 상한은 RSS를 막지 않았다.
- 오류 위치는 상한을 넘은 시점에 실행 중이던 선언을 가리킬 수 있다. 원인 선언의 증거로 쓰지 않는다.
- `mem`의 IR 오류와 PANIC은 앞의 오류에 따른 것으로 보인다. 확인하지 않았다.

## 7. 저메모리 환경과의 관계

- HANDOFF.md의 저메모리 환경은 약 9.69 GiB다.
- 이 머신의 WitLcM4x16 단독 peak 13.01–13.27 GiB는 그 값보다 크다.
- 측정 환경이 다르다(macOS arm64 대 Linux aarch64 컨테이너). 수치를 그대로 옮기지 않는다.

## 8. 미실행 항목

- 원인 분리(어느 선언이 메모리를 쓰는지)는 M2 범위라서 실행하지 않았다.
- `LEAN_NUM_THREADS=1` 측정은 브리프에 없어서 실행하지 않았다.
- `goval`, 링크 검사, 부정 시험, semtest, review 파일, `RegressFix2`는 M1 범위가 아니라서 실행하지 않았다.
- 비교 파일 3개와 전체 빌드는 각 1회만 측정했다.

## 9. 재현

```sh
cd fv/kraken/lean
lake build Fk.LcMarshal Fk.RtCopy Fk.WHost Fk.LcAccept Fk.BumpMore
for r in 1 2 3; do ../memopt/measure.sh m4x16-r$r lake env lean Fk/WitLcM4x16.lean; done
lake env lean --profile Fk/WitLcM4x16.lean > ../memopt/logs/m4x16.profile.txt 2>&1
for f in M1x1 M4 A4x16; do ../memopt/measure.sh $f-r1 lake env lean Fk/WitLc$f.lean; done
trash .lake/build && ../memopt/measure.sh full-r1 lake build
sh tools/axioms.sh
../memopt/measure.sh m4x16-mem9000 lake env lean --memory=9000 Fk/WitLcM4x16.lean
```
