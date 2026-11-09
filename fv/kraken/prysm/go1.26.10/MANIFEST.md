# MANIFEST: phase1c 실험 기준선 Go 1.26.10

이 디렉터리는 phase1c(1c)의 대상 바이너리 기록이다. 별도 이름공간이다.
Go 1.26.3 ELF(`9c850c97…c501`)와 그 정리·표·데이터 파일과 섞지 않는다.

## 1. 결정 (사용자 결정 2026-11-09, run `fvpar-20261109T150658Z-f1d44da4` DECISIONS D1)

- Prysm 소스는 `ab15ff70c72a568c870b2de662474685a95de294`이다. 배치는 slice + `ssz-size`다.
- 이 소스는 옛 고정 배열 핀 `5ac1d028f5`(핀 브랜치 `45394e5`)과 같다고 주장하지 않는다. 옛 핀은 대체된 이력이다(그 커밋은 `syjn99/prysm`에서 얻을 수 없다).
- 1c 컴파일러는 Go 1.26.10(`/workspace/tooling/go1.26.10`)이다. 새 실험 기준선이다.
- 옛 1c 컴파일러 값 Go 1.26.3은 1c에서만 대체됐다. fix3는 Go 1.26.3 ELF를 그대로 쓴다.
- Prysm `go` 지시자를 낮추지 않았다. 타입 추출 우회를 만들지 않았다.
- 생성기·런타임은 `698c2025a73a296b55b95744a8408f3b03b2546b`이다. 생성기를 고치지 않았다.
- **Go 1.26.3 기계어의 정리 55개는 이 ELF에 옮겨지지 않는다.** 새 기계어는 새 표와 새 증명 대응이 필요하다. 컴파일 성공은 아무것도 증명하지 않는다.

## 2. 대상

| 항목 | 값 |
| --- | --- |
| 호스트 | linux/arm64, `go version go1.26.10 linux/arm64`. x86-64 하드웨어 없음 |
| 생성 | 호스트 네이티브(arm64). 생성기 바이너리 sha256 `e962d9b6b863a20f958bbb10f42867fc278c67274ce174db29887fb49bdf87d4`(Go 1.26.10, `-trimpath`, 698c202 트리에서 빌드) |
| 대상 | 교차 컴파일 `GOOS=linux GOARCH=amd64 GOAMD64=v1 CGO_ENABLED=0 go build -p 2 -tags purego -trimpath` |
| 패키지 | `github.com/OffchainLabs/prysm/v7/fvphase1c/p1cbin`(임시 트리의 스크래치 `main`, 사본 `p1cbin-main.go.txt`) |
| ELF sha256 | `c6403c02a110ffd6fe6d31a3c89cd395ac457b5d62e60e2e611b8ab9a8dd911e` |
| ELF 크기 | 23486009 바이트. 5 MB를 넘어서 커밋하지 않는다. 사본: run 디렉터리 `streams/phase1c/artifacts/elf/p1cbin-amd64` |
| Go build ID | `vvezRAx2XfNAzHGIedKc/LVz05eLSmRibjKM02M9g/vTUc8QDCGkwQyqjmLKtu/siAyhYgBvYBhMpoLOoxx` |
| 재현성 | 두 번째 빌드는 빈 GOCACHE로 했다. sha256과 build ID가 같다(`build-ids.txt`) |
| objdump / nm | sha256 `580b0da9…4a47` / `88ee8b9a…40ac`(`build-ids.txt`). 커밋하지 않는다(17 MB / 2 MB) |

## 3. 소스 고정

| 항목 | 값 |
| --- | --- |
| Prysm 트리 | `/workspace/worktrees/prysm/fv-phase1c`, HEAD `ab15ff70…`, 커밋 0개 |
| `replace` | `replace github.com/OffchainLabs/methodical-ssz => /workspace/worktrees/methodical-ssz/fv-pin-smoke-generator`(`prysm-go.mod.diff`) |
| 생성기 트리 | `/workspace/worktrees/methodical-ssz/fv-pin-smoke-generator`, `698c202`, 읽기 전용, `git status --porcelain --ignored` 0줄 |
| 트리 상태 | `prysm-tree-status.txt`: `go.mod`, 생성 파일 16개, 스크래치 `fvphase1c/` 두 파일 |
| 생성 파일 | `../_generated/`(sha256 `../_generated/SHA256SUMS`). 임시 트리의 같은 이름 파일을 이것으로 덮어썼다 |
| 모듈 | Go 프록시만(`GOPROXY=https://proxy.golang.org`, `GOTOOLCHAIN=local`) |

## 4. 재빌드

run 디렉터리 `$S`(= `/workspace/agent-runs/methodical-fv-parallel/streams/phase1c`)의 환경 파일을 쓴다. 모든 단계는 gate 안에서 돈다.

```sh
. $S/env-go12610.sh
# 1. 깨끗한 ab15ff70 트리에 replace 한 줄을 붙인다(prysm-go.mod.diff).
# 2. 생성과 IR
sh fv/kraken/gen/prysm-gen.sh <prysm-tree> <ssz-698c202 바이너리> <out>
# 3. 생성 파일을 트리에 놓는다(<out>/gen/{mainnet,minimal}/* -> proto/prysm/v1alpha1, proto/engine/v1)
python3 -I fv/kraken/gen/inventory.py reduce <out>/ir-mainnet.json fv/kraken/prysm/ir/ir-mainnet.json   # minimal도 같다
python3 -I fv/kraken/gen/inventory.py build fv/kraken/prysm
python3 -I fv/kraken/gen/keepalive.py fv/kraken/prysm/inventory.json <prysm-tree>/fvphase1c/p1cbin/main.go
sh fv/kraken/gen/prysm-elf.sh <prysm-tree> <elf-out> <빈 GOCACHE 디렉터리>
python3 -I fv/kraken/gen/mnemonics.py <elf-out>/p1cbin-amd64.objdump fv/kraken/lean/.lake/packages/Kraken/Kraken/X64/Parser/Basic.lean fv/kraken/link/conv.py fv/kraken/prysm/inventory.json fv/kraken/prysm/go1.26.10/functions.json
python3 -I fv/kraken/link/conv.py <elf-out>/p1cbin-amd64.objdump <elf-out>/p1cbin-amd64.nm <norm-out> --norm
(. $S/env-lean.sh; cd fv/kraken/lean && KPARSE_LIST=<.S 목록> lake env lean ../gen/kparse/KParse.lean)
python3 -I fv/kraken/gen/kparse/summ.py <kparse 로그> fv/kraken/prysm/go1.26.10/functions.json fv/kraken/prysm/go1.26.10/kparse.json
python3 -I fv/kraken/gen/types_md.py fv/kraken/prysm
```

이 세션의 실행 로그: `$S/logs/01`(생성기 빌드), `02`(go list), `03`(생성), `04`(IR), `05`(ELF ×2, objdump), `06`·`07`(파서), `08`(`%riz` 진단).

## 5. 신뢰 한계

- x86-64 하드웨어에서 실행하지 않았다. Kraken = 실제 CPU 대조가 없다.
- `layout`과 Go 배치는 `go/types`의 gc amd64 규칙이다(`ir/*.json` `go_fields`). amd64 실행으로 확인하지 않았다.
- 이 ELF에 대한 정리는 아직 없다. 표는 분류다.
