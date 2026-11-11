# MANIFEST: OPT-R1 새 ELF (Checkpoint 인코더 용량 예약)

이 디렉터리는 최적화 시험 OPT-R1의 대상 바이너리 기록이다. 별도 이름공간이다.
기준 ELF `c6403c02…911e`와 그 정리·표·기록은 바뀌지 않는다.
옛 정리는 옛 ELF에 대한 것이다. 새 ELF로 옮겨지지 않는다.

## 1. 바뀐 것

- 생성기: 브랜치 `claude/ssz-gen-opt-r1`, 커밋 `ca191bb`(부모 `698c202`).
- 새 선택 플래그 `--reserve-marshal=<타입>`. 기본값은 끔이다.
- 끔: 생성 파일 16개가 `698c202` 출력(`../../_generated/`)과 바이트 단위로 같다.
- 켬(`phase0.yaml` 실행에만 `Checkpoint`): 함수 본문 하나만 다르다. mainnet과 minimal의 `Checkpoint.MarshalSSZTo`다(`generated.diff`).
- 넣은 문장은 하나다. `cap(dst)-len(dst) < 40`이면 40바이트를 한 번 덧붙이고 길이를 되돌린다.
- `gen-wrap.sh`가 `phase0.yaml` 실행에만 플래그를 붙인다. `fv/kraken/gen/prysm-gen.sh`는 그대로다.
- `ssz/` 런타임은 바뀌지 않았다. Prysm `replace`는 `698c202` 트리를 가리킨다.

## 2. 대상

| 항목 | 값 |
| --- | --- |
| 빌드 | `GOOS=linux GOARCH=amd64 GOAMD64=v1 CGO_ENABLED=0 go build -p 2 -tags purego -trimpath`, Go 1.26.10 linux/arm64 호스트 |
| 패키지 | `fvphase1c/p1cbin`(기준과 같은 `main.go`, `../p1cbin-main.go.txt`) |
| ELF sha256 | `3ef7ac890ba1a797fb90877b84ad1a6ffe0ac283f77c10b09ffb2c8cd7b7f602`, 23486305 바이트. 커밋하지 않는다 |
| 재현성 | 두 번째 빌드는 빈 GOCACHE로 했다. sha256과 build ID가 같다(`build-ids.txt`) |
| 대조 빌드 | 같은 트리에서 끔 출력으로 빌드하면 기준 ELF `c6403c02…911e`가 나온다 |
| 링크 검사 | `link/RESULT`: PASS all. 기존 도구(`gen/e2e/e2elink.py`, `link/conv.py`, `link/check.py`)를 고치지 않고 썼다 |

## 3. 새 함수의 기계어 (`link/norm/…Checkpoint.MarshalSSZTo.S`)

- 126 명령어, 574 바이트(기준 85, 341).
- 프레임 `sub $0x90,%rsp`(기준 `$0x68`). 스택 검사는 `lea -0x18(%rsp),%r12` 형식이다.
- 런타임 호출: `growslice` 세 곳, `memmove` 두 곳, `panicBounds` 한 곳, `morestack_noctxt` 한 곳.
- `panicBounds`는 `[:len(dst)]` 경계 검사다. 계약이 없다. 정리는 그 분기가 안 갈림을 증명해야 한다.
- 영 배열은 `movups %xmm15`로 채운다. 정리는 X15 = 0을 가정하지 않는다.
- 나머지 함수 6개의 `.S`와 데이터 10개는 기준 `../e2e/link/`와 sha256이 같다.

## 4. 재빌드

1. 생성기 `ca191bb`를 Go 1.26.10, `-trimpath`로 빌드한다.
2. `OPTR1_GEN=<생성기> sh fv/kraken/gen/prysm-gen.sh <prysm-tree> fv/kraken/prysm/go1.26.10/opt-r1/gen-wrap.sh <out> gen`.
3. `<out>/gen/*/phase0*.ssz.go`를 기준 임시 트리(`../MANIFEST.md` §3)의 사본에 놓는다.
4. 위 플래그로 `./fvphase1c/p1cbin`을 빌드한다. 객체 덤프는 `fv/kraken/gen/prysm-elf.sh`의 정규식과 같다.
5. `python3 -I -B fv/kraken/gen/e2e/e2elink.py filter <link-out> <objdump> <elf> <nm>`, `conv.py --norm`, `e2elink.py data`, `link/check.py`.

모든 단계는 무거운 작업 게이트 안에서 하나씩 돌았다.
