# TOOLS: 고정 버전과 명령

## 고정 버전

| 항목 | 값 | 어디서 고정하는가 |
| --- | --- | --- |
| 생성기 | 소스(`sszgen/`, `ssz/`) = `syjn99/ssz-gen-fixes` `698c202`. 병합 기준 `2d0150b` | `git rev-parse HEAD:ssz`, `link/out/build-ids.txt` |
| Go | 1.26.3, `GOOS=linux GOARCH=amd64 GOAMD64=v1 CGO_ENABLED=0 -tags purego -trimpath`, 표준 런타임 | `link/build.sh`, `link/out/build-ids.txt` |
| ELF | sha256 `9c850c97…c501` | `link/out/build-ids.txt` |
| Kraken | `6064eecbb730a1152aa6ed891a155d3a92a4f298` (AeneasVerif/kraken main) | `lean/lakefile.toml` `rev`, `lean/lake-manifest.json` |
| Lean | `leanprover/lean4:nightly-2026-09-21` | `lean/lean-toolchain` |
| EthLib | `862185680cf23ccf54d44eb25b63b26c5020597b` | `lean/lakefile.toml` `rev` |
| Prysm 축약 타입의 출처 | v7.1.8 `51b5a75ebbadf05af22bd2601b5baf7a9e99b66d`, Checkpoint·AttestationData 스키마 | `target/prysm/types.go` |
| gohashtree, go-bitfield | `v0.0.5-beta`, `v0.0.0-20260504143531-5cbb6d0f5f2e` | `go.mod` |
| objdump, LLVM, clang | `go tool objdump -gnu`, `llvm-objdump`(독립 디코딩), `clang --target=x86_64-linux-gnu`(재조립) | `link/check.py`의 `tool()` |
| vcgen 평가(채택 안 함) | sgraf812/kraken `a4cce2ec6d840376e4dbbf4a11a777ebdf42a3cb`, `nightly-2026-10-29` | `vcgen/` |

## 대상 생성

저장소 루트에서 실행한다.

```sh
P=github.com/OffchainLabs/methodical-ssz/fv/kraken/target
go run ./cmd/ssz gen --package $P --output=fv/kraken/target/types.ssz.go --type-names=Scalars,FixedVec,ListU64
go run ./cmd/ssz gen --package $P --output=fv/kraken/target/types1b.ssz.go --type-names=BitVec,Nested,ListC,BitL
go run ./cmd/ssz gen --package $P/prysm --output=fv/kraken/target/prysm/types.ssz.go --type-names=Checkpoint,AttestationData
fv/kraken/link/build.sh          # ELF, objdump, nm, norm/*.S, SHash.lean, build-ids.txt
```

## 도구

| 도구 | 역할 | 실행 |
| --- | --- | --- |
| `link/check.py` | ELF ↔ objdump ↔ `.S` ↔ Host 레이블·전역 주소, (a)–(h), `link/out/RESULT` | `python3 fv/kraken/link/check.py fv/kraken/link/out [--selftest]` |
| `link/golits.go` | Go 소스의 `fmt.Errorf` 첫 인수 리터럴(링크 검사 (g)) | `go run fv/kraken/link/golits.go -- <file.go> ...` |
| `lean/tools/axioms.sh` | `AXIOMS.txt`(정리), `AXIOMS-ALL.txt`(모든 선언) | `cd fv/kraken/lean && sh tools/axioms.sh` |
| `lean/tools/wit/layout.go` | gc amd64 배치를 `layout.json`에 | `go run fv/kraken/lean/tools/wit/layout.go > fv/kraken/lean/tools/wit/layout.json` |
| `lean/tools/wit/goval.py` | 증인의 Go 값 검사 | `python3 fv/kraken/lean/tools/wit/goval.py` |
| `lean/tools/wit/` 생성기 | `Fk/Wit*.lean` 생성 | `lean/tools/wit/README.md` |
| `lean/tools/RegressFix2.lean` | 현재 계약의 회귀 검사 | `cd fv/kraken/lean && lake env lean tools/RegressFix2.lean` |
| `negative/run.sh` | 부정 시험 16개, `negative/RESULT` | `fv/kraken/negative/run.sh <워크트리 밖 scratch 디렉터리>` |
| `semtest/` | F1·F2 Go 회귀 시험, x86-64 하드웨어 대조 스크립트 | `GOROOT=$(go env GOROOT) go test ./fv/kraken/semtest/` |

`go run`과 `go test`는 `GOROOT=$(go env GOROOT)`로 돌린다.
