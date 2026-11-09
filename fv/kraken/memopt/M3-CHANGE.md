# M3: `u64v` 증명 변경과 의미 보존 검사

판정: 변경을 적용했다. `WitLcM4x16` 단독 peak RSS는 13.01–13.27 GiB에서 1.42 GiB로 줄었다. 공개 선언의 타입과 정의 값은 같다. 두 공리 범위는 `NONSTANDARD 0`이다.

- 모델: Claude Opus 5.5 (`claude-opus-5-5`, 시스템 프롬프트 기준).
- Orca 터미널: `ORCA_TERMINAL_HANDLE=term_fa8167b6-ff38-4ec6-8bb3-fcb2d627f932`.
- Claude Code 세션 ID: `41c39677-b5cd-41f2-a673-11963168d812` (scratchpad 경로에서 읽었다).
- 기준: 브랜치 `syjn99/ssz-fv-memopt`, HEAD `1bd8c02`. 환경은 `ENV.md`와 같다.
- 측정 중 다른 Lean 프로세스는 없었다(`pgrep -fl "bin/lean|lake"` 출력 없음).

## 1. 변경

| 파일 | 변경 | 이유 |
| --- | --- | --- |
| `lean/tools/wit/wlcm.py` | `u64v{i}`의 증명 `by decide`를 `by simp [u64Bytes, EthLib.Serialization.Ssz.uintBytes]`로 바꾼다 | M2 후보 1. `decide`의 elaboration 비용이 peak를 정한다(M2 3.1, 3.2) |
| `lean/Fk/WitLcM1x1.lean` | 재생성. `u64v0` 증명 줄 1개 | 같은 생성기의 출력 |
| `lean/Fk/WitLcM4x16.lean` | 재생성. `u64v0`–`u64v3` 증명 줄 4개 | 같은 생성기의 출력 |
| `lean/Fk/WitLcMMix.lean` | 재생성. `u64v1`, `u64v2` 증명 줄 2개 | 같은 생성기의 출력 |
| `AXIOMS.txt` | 위 7개 정리의 공리 줄 | 1.5절 |

- 브리프의 증명 텍스트는 `simp [u64Bytes, uintBytes]`다. M2 C3, C10은 `uintBytes`를 전체 이름으로 썼다. 그래서 측정된 C3, C10의 텍스트를 그대로 쓴다.
- `set_option maxHeartbeats 4000000 in` 줄과 파일 단위 `set_option maxRecDepth 100000`은 그대로다.
- 정리 이름, 명제, 다른 선언은 바꾸지 않았다. 손 패치는 없다.
- 후보 2(`u64Bytes_toList` 보조정리)는 쓰지 않았다. `simp`가 길이 1, 16에서 모두 닫혔다.

### 1.1 재생성

`fv/kraken/lean`에서 실행했다. 모두 exit 0이다.

```sh
python3 tools/wit/wlcm.py tools/wit 0
python3 tools/wit/wlcm.py tools/wit 1
python3 tools/wit/wlcm.py tools/wit 4
python3 tools/wit/wlcm.py tools/wit 1 1x1
python3 tools/wit/wlcm.py tools/wit 16,16,16,16 4x16
python3 tools/wit/wlcm.py tools/wit 0,1,16 Mix
```

- `WitLcM0`, `WitLcM1`, `WitLcM4`는 diff가 없다. 이 셋의 원소는 모두 길이 0이라서 `u64v`가 없다.
- 나머지 셋의 diff는 7줄이다. 스크립트로 각 줄을 ` := `에서 나누어 비교했다. 왼쪽(명제)은 바이트 단위로 같다. 오른쪽만 `by decide`에서 `by simp [...]`로 바뀌었다.

### 1.2 옵션 없이 닫히는가

| 진단 파일 | 내용 | exit | peak RSS (GiB) | wall (s) |
| --- | --- | --- | --- | --- |
| `scratch/N1.lean` | 새 `WitLcM4x16`에서 `u64v` 앞 `maxHeartbeats ... in` 4줄 삭제. 파일 단위 `maxRecDepth`는 남는다 | 0 | 1.42 | 3.48 |
| `scratch/N2.lean` | import, `open`, 길이 16 `u64v0` 하나. `set_option` 없음 | 0 | 1.31 | 2.79 |

새 증명은 두 옵션 없이 닫힌다. 이 결과는 기록만 한다. 옵션 줄은 지우지 않았다.

## 2. 측정

명령은 `fv/kraken/lean`에서 `../memopt/measure.sh <label> <cmd>`다. peak RSS는 `/usr/bin/time -l`의 최대 단일 프로세스 값이다.

| 명령 | 상태 | exit | peak RSS (GiB) | 표본 합계 (GiB) | wall (s) | 로그 |
| --- | --- | --- | --- | --- | --- | --- |
| `lake env lean Fk/WitLcM4x16.lean` | 원본 (M1) | 0, 0, 0 | 13.01, 13.26, 13.27 | 13.62–13.92 | 18.00, 17.71, 18.48 | `logs/m4x16-r{1,2,3}.*` |
| `lake env lean Fk/WitLcM4x16.lean` | 수정 | 0, 0, 0 | 1.42, 1.42, 1.42 | 2.02–2.03 | 3.78, 3.62, 3.55 | `logs/m3-m4x16-r{1,2,3}.*` |
| `lake build Fk.WitLcM0 Fk.WitLcM1 Fk.WitLcM1x1 Fk.WitLcM4 Fk.WitLcM4x16 Fk.WitLcMMix` | 수정 | 0 | 1.43 | 4.66 | 6.63 | `logs/m3-build6.*` |
| `sh tools/axioms.sh` | 수정 | 0 | 1.36 | 2.02 | 11.29 | `logs/m3-axioms.*` |

- 원본 대비 `WitLcM4x16` 단독: peak −11.6 GiB 이상, wall 약 4.8배 감소다.
- `lake build` 6개 모듈 출력은 `Built`가 `WitLcM1x1`, `WitLcMMix`, `WitLcM4x16`이다. 나머지 셋은 `Replayed`다. 그래서 바뀐 모듈만 다시 빌드했다.
- 표본 합계 4.66 GiB는 `lean` 프로세스 셋이 병렬로 돈 합이다.
- 변경 전 같은 명령은 `Replayed`만 냈다(`logs/m3-orig-noop.out.txt`). 그래서 보존한 원본 `.olean`은 원본 소스에서 나온 것이다. 그때 `git status`는 깨끗했다.
- 경고 줄은 원본(M1 `m4x16-r1`)과 같다(`Fk...warning` 줄 10개, `diff` 출력 없음).

### 2.1 `.olean` 크기와 sha256

| 모듈 | 원본 바이트 | 수정 바이트 | 원본 sha256 | 수정 sha256 |
| --- | --- | --- | --- | --- |
| WitLcM0 | 295224 | 295224 | `31ab1c23…` | 같다 |
| WitLcM1 | 392328 | 392328 | `eebea441…` | 같다 |
| WitLcM1x1 | 415184 | 436776 | `88a0f10c…` | `5b7e854d…` |
| WitLcM4 | 550328 | 550328 | `1bcb4d23…` | 같다 |
| WitLcM4x16 | 841528 | 1056528 | `b3a5e22d…` | `d2aacbbc…` |
| WitLcMMix | 751320 | 973080 | `18393ff5…` | `b7a0cef4…` |

- `simp` 증명 항이 `decide` 증명 항보다 크다. 그래서 바뀐 셋의 `.olean`이 21–29% 커졌다.
- 전체 sha256은 `artifacts/olean.sha256`에 있다. `.olean`, `.ilean`은 커밋하지 않는다(`artifacts/.gitignore`).

## 3. 의미 보존 검사

### 3.1 방법

- `Inspect.lean`은 `Lean`만 import한다. `#eval`에서 `importModules`로 `INSPECT_MOD`의 `.olean` 폐포를 읽는다.
- 대상은 그 모듈 `.olean`이 가진 모든 상수(`ModuleData.constNames`)다. 이름 순서로 출력한다.
- 비내부 상수마다 출력한다: 이름, 소유 모듈, 종류(theorem/def/reducible/instance), level params, `pp.all true` 타입.
- 같이 출력한다: 타입 `Expr.hash`, 정의의 값 `Expr.hash`, 사용 상수(타입, 정의면 값 포함), `collectAxioms`.
- theorem의 증명 값은 hash와 사용 상수에 넣지 않는다. 증명이 바뀌었기 때문이다.
- 내부 상수(`_proof_N`, `match_N`, `eq_1` 등)는 이름과 종류만 따로 출력한다.
- 실행: `INSPECT_MOD=Fk.<M> lake env lean ../memopt/Inspect.lean > artifacts/<orig|new>/Fk.<M>.inspect.txt`.
- 원본 출력은 변경 전 `.lake/build`에서, 수정 출력은 재빌드 뒤 `.lake/build`에서 만들었다.
- 같은 원본에서 두 번 실행한 출력은 `cmp`로 같았다(`WitLcM4x16`).
- `.olean`을 읽는다는 근거: 수정 셋의 sha256이 다르다. 그 셋에서만 `u64v`의 `axioms` 줄이 바뀌었다.

### 3.2 결과

`diff -r artifacts/orig artifacts/new`(`.inspect.txt`만)의 차이는 7줄이다. 모두 `u64v`의 `axioms` 줄이다. 전체 출력은 `artifacts/inspect.diff`다.

| 모듈 | 선언 | 원본 | 수정 |
| --- | --- | --- | --- |
| WitLcM1x1 | `u64v0` | `#[]` | `#[propext, Quot.sound]` |
| WitLcM4x16 | `u64v0`–`u64v3` | `#[]` | `#[propext, Quot.sound]` |
| WitLcMMix | `u64v1`, `u64v2` | `#[]` | `#[propext, Quot.sound]` |

- 원인: `decide` 증명은 공리를 쓰지 않는다. `simp` 증명은 `propext`, `Quot.sound`를 쓴다. 둘 다 허용 공리다(`fv/AGENTS.md`).
- 이 차이는 증명에서 나온다. 명제는 바뀌지 않았다. 그래서 진행했다.
- 그 밖의 줄은 같다: 상수 수, 이름, 소유 모듈, 종류, level params, `pp.all` 타입, 타입 hash.
- 정의(`P`, `dataLabels`, `block`, `mem`, `s0`, `objs`, `z`, `host`)의 값 hash와 사용 상수도 같다.
- 내부 상수 목록도 같다. `simp`가 새 내부 상수를 남기지 않았다.
- `lc_marshal_runs`, `s_mem`의 공리는 원본에서 이미 `propext, Classical.choice, Quot.sound`다. 이 값은 바뀌지 않았다.

### 3.3 외부 정의

- 타입이 참조하는 외부 정의(`u64Bytes`, `uintBytes`, `lcElem`, `Int.toBytes`, `lc_marshal_main`)는 `Fv`, `Fv1`, `Fk`, EthLib, Kraken에 있다.
- `git diff 86fd060 -- fv/kraken/lean/Fv fv/kraken/lean/Fv1 fv/kraken/lean/Fk`(변경 전)는 출력이 없었다.
- 변경 뒤 같은 명령은 위 세 witness 파일만 보인다. `lake-manifest.json`, `lean-toolchain`, lakefile의 diff도 없다. 그래서 EthLib, Kraken revision은 같다.
- 정의의 값 hash 비교는 이 모듈이 정의한 상수만 다룬다. 외부 정의는 소스 diff로 본다.

### 3.4 방법의 한계

- 원본과 수정본 `.olean`을 한 환경에 동시에 적재하지 않았다. 두 환경을 차례로 열고 출력 텍스트를 비교했다.
- 그래서 kernel이 두 타입의 정의상 같음을 직접 검사하지 않았다. 근거는 같은 toolchain, 같은 의존 `.olean`에서의 `pp.all` 텍스트와 `Expr.hash` 일치다.
- `Expr.hash`는 충돌할 수 있다. `pp.all` 텍스트 일치가 그 보완이다.
- 비교는 같은 머신, 같은 `.lake` 디렉터리에서 했다. 별도 artifact 디렉터리에서 각각 빌드하지 않았다. 원본 `.olean`은 빌드 뒤 복사로 보존했다.
- 의존 모듈의 `.olean`은 변경 전후 다시 빌드되지 않았다(`Replayed`). 그래서 두 환경의 의존 부분은 같은 파일이다.

## 4. 공리

`sh tools/axioms.sh`(`fv/kraken/lean`):

```text
TOTAL 1571 NONSTANDARD 0
ALL-DECLARATIONS TOTAL 7975 NONSTANDARD 0
```

- 정리 수 1571, 전체 선언 수 7975는 M1과 같다.
- `AXIOMS.txt`의 diff는 3.2절의 7개 정리 줄이다. 각각 `[]`에서 `[Quot.sound, propext]`로 바뀌었다.
- `AXIOMS-ALL.txt`의 diff는 없다. 이 파일은 비표준 공리를 쓰는 선언과 합계만 적는다.

## 5. 보호 파일

- `shasum -a 256 fv/kraken/link/out/p1bin-amd64`: `9c850c97066b9d33d6e4c5ef0a385dcbe2c984ae774a527cdedd18d2b72ac501`. 기준과 같다.
- `git diff 86fd060 --stat -- sszgen ssz fv/kraken/target fv/kraken/link/out`: 출력 없음.

## 6. 미실행 항목

- 전체 `lake build`, `goval.py`, link check, `--selftest`, negative tests, Go semtest, review Lean 파일, `RegressFix2`. M4 범위다.
- 저메모리(약 9.69 GiB) 환경의 단독·전체 빌드. M4 범위다.
- 원본과 수정본을 별도 artifact 디렉터리에서 각각 cold 빌드하는 비교. 3.4절을 본다.
- 두 `.olean`을 한 환경에서 kernel로 비교하는 검사.
- 다른 생성기(`wlca.py` 등)의 같은 패턴. 범위 밖이다.

## 7. 재현

```sh
cd fv/kraken/lean
for a in "0" "1" "4" "1 1x1" "16,16,16,16 4x16" "0,1,16 Mix"; do
  python3 tools/wit/wlcm.py tools/wit ${=a}   # zsh. sh/bash: $a
done
git diff --stat
for r in 1 2 3; do ../memopt/measure.sh m3-m4x16-r$r lake env lean Fk/WitLcM4x16.lean; done
../memopt/measure.sh m3-build6 lake build Fk.WitLcM0 Fk.WitLcM1 Fk.WitLcM1x1 Fk.WitLcM4 Fk.WitLcM4x16 Fk.WitLcMMix
for m in WitLcM0 WitLcM1 WitLcM1x1 WitLcM4 WitLcM4x16 WitLcMMix; do
  INSPECT_MOD=Fk.$m lake env lean ../memopt/Inspect.lean > ../memopt/artifacts/new/Fk.$m.inspect.txt
done
diff -r -x '*.olean' -x '*.ilean' ../memopt/artifacts/orig ../memopt/artifacts/new
../memopt/measure.sh m3-axioms sh tools/axioms.sh
```
