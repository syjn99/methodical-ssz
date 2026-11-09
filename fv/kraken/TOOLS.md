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
fv/kraken/link/build.sh          # ELF, objdump, nm, norm/*.S, data/*.data, build-ids.txt
```

## 도구

| 도구 | 역할 | 실행 |
| --- | --- | --- |
| `link/check.py` | ELF ↔ objdump ↔ `.S` ↔ Host 레이블·전역 주소 (a)–(e), 데이터 파일 = ELF (f), `link/out/RESULT` | `python3 -B fv/kraken/link/check.py fv/kraken/link/out [--selftest]` |
| `link/data.py` | ELF 데이터 항목을 `link/out/data/<id>.data`로 | `python3 -B fv/kraken/link/data.py fv/kraken/link/out` |
| `lean/tools/axioms.sh` | `AXIOMS.txt`(정리), `AXIOMS-ALL.txt`(모든 선언) | `cd fv/kraken/lean && sh tools/axioms.sh` |
| `lean/tools/wit/layout.go` | gc amd64 배치를 `layout.json`에 | `go run fv/kraken/lean/tools/wit/layout.go > fv/kraken/lean/tools/wit/layout.json` |
| `lean/tools/wit/goval.py` | 증인의 Go 값 검사 | `python3 fv/kraken/lean/tools/wit/goval.py` |
| `lean/tools/wit/` 생성기 | `Fk/Wit*.lean` 생성 | `lean/tools/wit/README.md` |
| `lean/tools/RegressFix2.lean` | 현재 계약의 회귀 검사 | `cd fv/kraken/lean && lake env lean tools/RegressFix2.lean` |
| `negative/run.sh` | 부정 시험 16개, `negative/RESULT` | `fv/kraken/negative/run.sh <워크트리 밖 scratch 디렉터리>` |
| `semtest/` | F1·F2 Go 회귀 시험, x86-64 하드웨어 대조 스크립트 | `GOROOT=$(go env GOROOT) go test ./fv/kraken/semtest/` |

`go run`과 `go test`는 `GOROOT=$(go env GOROOT)`로 돌린다.

## ELF 데이터 include (수정 3, 인터페이스 v1)

정리가 읽는 rodata·런타임 자료는 손 상수가 아니라 ELF 바이트를 include한 정의다.
코드 include(`Fk/Code.lean`, `include_x64_rt`)와 같은 구조다.

- 추출기: `link/data.py`. ELF와 `p1bin-amd64.nm`에서 항목 표(id, 레이블, 오프셋, 길이)의 바이트를 읽는다.
- 데이터 파일: `link/out/data/<id>.data`. 항목 하나에 파일 하나. 텍스트다.
- Lean: `Fk/Include.lean`의 명령 `data_include <id>`가 `../link/out/data/<id>.data`를 읽는다. `Fk/Data.lean`이 항목마다 한 줄로 부른다.
- 정의: `Fk.Data.<id> : List UInt8`(바이트), `Fk.Data.<id>_addr : BitVec 64`(= `(label "<레이블>" + <오프셋>).toBitVec`). 주소만 있는 항목은 `_addr`만 있다.
- 포인터 워드가 있는 항목(itab, 타입 기술자)의 바이트는 `[Host]`에 의존한다. 워드는 `Int.toBytes 8 (label "<s>" + <o>).toBitVec.toInt`이다.
- 정리의 전제 모양은 그대로 `Eq (bytes.At addr)`다. Kraken 데이터 메모리는 코드와 분리되어 있다(con-agua DESIGN `ldc`).

데이터 파일 문법(한 줄에 지시어 하나, `#`로 시작하면 주석):

| 지시어 | 뜻 |
| --- | --- |
| `at <레이블> <오프셋>` | 첫 지시어. 항목의 주소 = 레이블 + 오프셋. 레이블은 `conv.py`가 정리한 이름이다 |
| `bytes <hex> ...` | 원시 바이트(두 자리 16진수, 공백 구분) |
| `word <레이블> <오프셋>` | 8바이트 리틀엔디언 절대 주소 = 레이블 + 오프셋(재배치 워드) |

검사: `link/check.py`가 모든 데이터 파일을 ELF와 비교한다. `python3 -B link/data.py --check link/out`은 재생성 결과가 추적 파일과 같은지 본다(다르면 종료 1).
줄 규칙(두 읽기기 공통): 줄은 `\n`으로 나눈다. 다른 문자는 모두 출력 가능한 ASCII다. `\r`·탭·제어 문자가 있으면 `check.py` (f)와 `data_include`가 모두 거부한다.
`bytes`는 그 구간의 파일 바이트와, `word`는 그 위치의 8바이트 값 = 심볼 주소 + 오프셋과 같아야 한다. 파일의 sha256은 (a)와 같은 해시 묶음에 들어간다.
재빌드: `lean/lakefile.toml`의 `Fk` 라이브러리 `needs`에 `link/out/norm`, `link/out/data`, `lean/Fk/*.S`를 입력으로 등록한다.

항목 표(v1). 오프셋은 이 ELF(`9c850c97…c501`)의 값이다.

| id | 레이블 + 오프셋 | 길이 | 종류 | 바꾸는 것 |
| --- | --- | --- | --- | --- |
| `blFmtB` | `go_string._` + 526 | 5 | rodata 문자열 `B: %w` | `BlMarshal.lean blFmtB` |
| `bvFmtJ` | `go_string._` + 511 | 5 | rodata 문자열 `J: %w` | `BvSpec.lean bvFmtJ` |
| `vbvFmt` | `go_string._` + 27706 | 35 | rodata 문자열(ValidateBitvector) | `Vbv.lean vbvFmt`, `bvRO` |
| `lcFmtZero` | `go_string._` + 39370 | 53 | rodata 문자열 | `LcReject.lean lcFmtZero` |
| `lcFmtShort` | `go_string._` + 42000 | 63 | rodata 문자열 | `LcReject.lean lcFmtShort` |
| `lcFmtOrder` | `go_string._` + 42579 | 67 | rodata 문자열 `offset %d is not greater …` | 새 항목(X5) |
| `vblMsgE` | `go_string._` + 33605 | 42 | rodata 문자열(ValidateBitlist) | `Vbl.lean vblMsgE`, `vblRO` |
| `vblMsgZ` | `go_string._` + 13272 | 21 | rodata 문자열 | `Vbl.lean vblMsgZ` |
| `vblMsgB` | `go_string._` + 5743 | 13 | rodata 문자열 | `Vbl.lean vblMsgB` |
| `luFmtTooBig` | `go_string._` + 40290 | 56 | rodata 문자열 | `LuRejectCall.lean luFmtTooBig` |
| `luFmtMis` | `go_string._` + 42646 | 68 | rodata 문자열 | `LuRejectCall.lean luFmtMis` |
| `errorStringItab` | `go_itab._errors.errorString_error` + 0 | 32 | itab 전체(워드 3: inter, Type, Fun[0]) | 옛 (h)의 itab 검사 |
| `errorStringPtrType` | `type__` + 68096 | 56 | `*errors.errorString`의 abi.PtrType(abi.Type 48 + Elem) | 옛 (h)의 포인터 종류 검사, 증인의 0 기술자 |
| `intType` | `type__` + 49184 | 48 | `int`의 abi.Type | `LuRejectCall.lean luTW`, 옛 (h) |
| `uint64Type` | `type__` + 49120 | 48 | `uint64`의 abi.Type | 새 항목(X5, `%d` uint64 인수) |
| `staticuint64s` | `runtime.staticuint64s` + 0 | 2048 | uint64 0..255 표 | `Contracts.lean StaticBox`, 옛 (h) |
| `ErrSize` 외 오류 전역 6개 | `ssz.Err*` + 0 | 0 | 주소만(값은 런타임 초기화) | 증인의 전역 초기화 전제(X3) |

신뢰 한계(수정 3 리뷰 M3):
- 검사 도구는 Lean 소스를 읽지 않는다. 정리가 이 정의를 쓰는지는 정리 문장으로 읽는다. 어떤 도구도 확인하지 않는다.
- 항목 id ↔ 주소의 결합은 증명이 한다. 검사 (f)는 "파일 = 그 주소의 ELF 바이트"만 본다.
- 형식 문자열의 내용과 동사 모양이 계약(`FmtErrorfWC`·`DWC`·`DDC`)과 맞는지는 계약 가설이다. Lean은 길이와 `%` 없음만 묶는다.

오류 전역 id: `ErrSize`, `ErrInvalidSerialization`, `ErrInvalidVariableOffset`, `ErrListTooBig`, `ErrBytesLength`, `ErrIncorrectListSize`.
정리는 지금처럼 `label "ssz.Err*"`를 직접 쓴다. 이것은 심볼이고 손 숫자가 아니다.
