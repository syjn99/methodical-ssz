# ENV: memopt M1 측정 환경

이 문서는 M1 baseline을 측정한 환경을 기록한다.
명령은 모두 `fv/kraken/lean`에서 실행했다(ELF 해시만 예외, 경로를 적는다).

## 저장소와 toolchain

| 항목 | 값 |
| --- | --- |
| `git rev-parse HEAD` | `86fd060349257c133e981e420120f63c61f582e1` |
| 브랜치 | `syjn99/ssz-fv-memopt` |
| `cat lean-toolchain` | `leanprover/lean4:nightly-2026-09-21` |
| elan 해석 | `leanprover/lean4-nightly:nightly-2026-09-21` (`lean-toolchain`으로 override) |
| `lake --version` | `Lake version 5.0.0-src (Lean version 4.36.0-nightly-2026-09-21)` |
| `lean --version` | `Lean (version 4.36.0-nightly-2026-09-21, arm64-apple-darwin24.6.0, commit ca39d2bc730f0382e4897ce314b93a4f168ff15e, Release)` |
| `lean`, `lake` 경로 | `/opt/homebrew/bin/lean`, `/opt/homebrew/bin/lake` (elan proxy) |
| Kraken (manifest) | `6064eecbb730a1152aa6ed891a155d3a92a4f298` |
| EthLib (manifest) | `862185680cf23ccf54d44eb25b63b26c5020597b` |
| mathlib (manifest, inherited) | `56a005855ea17e0b0958f73ec801ae140b0a1679` (`v4.35.0`) |

## 머신

| 항목 | 값 |
| --- | --- |
| `uname -m` | `arm64` |
| CPU | Apple M5 Pro |
| OS | macOS 26.7.2 (25G332) |
| `hw.memsize` | `51539607552` (48 GiB) |
| `hw.ncpu` | `18` |
| `vm.swapusage` | `total = 0.00M  used = 0.00M  free = 0.00M  (encrypted)` |
| `env \| grep -i lean` | `PWD=…/fv/kraken/lean`만 나온다. `LEAN_*` 변수는 없다 |
| 병렬도 | Lake 기본값. `LEAN_NUM_THREADS`는 설정하지 않았다 |

## 보호 파일

`shasum -a 256 fv/kraken/link/out/p1bin-amd64`:
`9c850c97066b9d33d6e4c5ef0a385dcbe2c984ae774a527cdedd18d2b72ac501`.
기대값 `9c850c97…c501`과 같다.

## 의존성 캐시

`.lake/packages`를 형제 워크트리에서 복사했다.
원본: `$HOME/orca/workspaces/methodical-ssz/ssz-fv-cleanup/fv/kraken/lean/.lake/packages` (그 워크트리 HEAD `86fd060`).
명령: `cp -Rc <원본> .lake/packages` (APFS clone, 501 MB).
`.lake/build`(프로젝트 모듈)는 복사하지 않았다. 이 워크트리에는 복사 전에 `.lake`가 없었다.
원본에서 빌드 산출물이 있는 패키지는 EthLib(`.olean` 129개)와 Kraken(`.olean` 25개)뿐이다.
mathlib 등 나머지 패키지는 소스만 있다. 프로젝트는 이들의 모듈을 import하지 않는다.
복사 뒤 EthLib HEAD는 `8621856…`, Kraken HEAD는 `6064eec…`다.

`diff`로 두 워크트리의 `lake-manifest.json`, `lean-toolchain`, `lakefile.toml`을 비교했다. 차이는 없다.

복사 뒤 첫 `lake build`에서 Lake는 의존성을 다시 받지 않았다.
로그 `logs/prebuild.out.txt`에 clone, fetch, download, updating 줄이 없다. Kraken 모듈은 "Replayed"로 나온다.

## 빌드 순서

1. `lake build Fk.LcMarshal Fk.RtCopy Fk.WHost`: 631 jobs, 128.3 s (`logs/prebuild.out.txt`). 측정 대상이 아니다.
2. `lake build Fk.LcAccept Fk.BumpMore`: 601 jobs, 6.8 s (`logs/prebuild2.out.txt`). WitLcA4x16의 import다.
3. 단독 측정(`lake env lean <file>`)은 `.olean`을 쓰지 않는다.
4. 전체 빌드 전에 `trash .lake/build`를 실행했다. 프로젝트 모듈은 모두 처음부터 빌드했다. `.lake/packages`는 유지했다.

## 측정 도구

- `/usr/bin/time -l` (macOS): exit status, wall(`real`), max RSS(바이트).
  max RSS는 기다린 자식 프로세스 중 최대 단일 프로세스 값이다.
- `ps -A -o pid=,ppid=,rss=,comm=`: 0.5초 간격 표본. `/usr/bin/time`의 모든 자손을 찾는다.
  표본마다 RSS 합계와 최대 단일 프로세스 RSS를 적는다.
- 두 도구를 `memopt/measure.sh`가 묶는다. 사용법은 그 파일 머리에 있다.
- 표본 간격 0.5초보다 짧은 peak는 표본에서 빠질 수 있다. `/usr/bin/time`의 값은 이 한계가 없다.
- `lake env lean --profile`: 선언별 elaboration·type checking 시간.
