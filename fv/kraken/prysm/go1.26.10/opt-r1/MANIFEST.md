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

## 5. 정리와 검사 (Lean 모듈 `fv/kraken/lean/E2e/OptR1/`)

정리는 새 ELF의 기계어에 대한 것이다. 옛 정리는 바뀌지 않았다.

| 정리 | 범위 | 결론 |
| --- | --- | --- |
| `E2e.OptR1.cpo_marshal_main` | `len + 40 ≤ cap < 2^63` | `(dst.ptr, len + 40, cap, nil)`. `dst[len..len+40]`만 쓴다. 힙을 쓰지 않는다 |
| `E2e.OptR1.cpo_marshal_reject_main` | 같은 범위, Root 길이 ≠ 32 | `(nil, ErrBytesLength)`. `dst[len..len+8]`만 쓴다(C-1) |
| `E2e.OptR1.cpo_marshal_grow_main` | `len ≤ cap < len + 40` | 새 블록 하나. 호출자 배열 `pre ++ spare`는 그대로다 |
| `E2e.OptR1.cpo_marshal_reject_grow_main` | 같은 범위, Root 길이 ≠ 32 | `(nil, ErrBytesLength)`. 새 블록 하나. 호출자 배열은 그대로다 |
| `E2e.OptR1.cpo_marshal_spec_k` | 빠른 경로 | 기준 `cp_e2e_marshal_spec_k`와 같은 결론. 전제는 새 프레임이다 |
| `E2e.OptR1.cpo_marshal_cover` | 모든 `len ≤ cap` | `pre ++ serialize`를 돌려준다. 두 번째 growslice 분기가 없다 |
| `E2e.OptR1.cpo_marshal_reject_cover` | 모든 `len ≤ cap` | `(nil, ErrBytesLength)` |

- 계약 가설: `GrowsliceC`, `MemmoveC`(기존 형식). `panicBounds`와 `morestack`은 분기가 안 갈림을 증명한다.
- 새 전제 형식은 없다. 스택 검사 전제는 `guard + 24 < rsp`다(`E2eScal.lea_cmp_be_false` 형식).
- reject 정리 둘은 `cap < 2^63`을 전제로 더 가진다. 기준 reject 정리에는 없다. 부호 있는 비교 때문이다.
- reject 경로의 계약 의존이 바뀌었다(리뷰 opt-r1-r1 S1).
- `8 ≤ spare < 40`에서 reject 증명은 `GrowsliceC`, `MemmoveC`, 힙 예산에 의존한다.
- 기준 reject 정리(`spare ≥ 8`)는 계약 없이 증명된다.
- `cpo_marshal_reject_cover`는 기준 reject 덮개에 없던 `MemmoveC`를 전제로 가진다.
- 덮개는 틀이 없다. 두 덮개는 `⋆ True`로 끝난다(S2).
- 기준에는 틀이 있는 덮개가 있다(`E2e/CpWCoverF.lean`). 이 집합에는 없다.
- 주 정리 넷은 범위마다 정확하다. 넷이 함께 모든 `len ≤ cap`을 덮는다.
- 증인: `WitO`(빠른 경로), `WitOW`·`WitOWR`(덮개, spare 0, 7, 8, 39, 40, 41과 nil dst). 수신자 Go 값 검사가 있다.
- 직접 증인이 있는 정리는 `cpo_marshal_main`, `cpo_marshal_cover`, `cpo_marshal_reject_cover`뿐이다(S4).
- `cpo_marshal_spec_k`, `cpo_marshal_grow_main`, `cpo_marshal_reject_main`, `cpo_marshal_reject_grow_main`은 덮개 증인을 거쳐서만 도달한다.
- 부정 시험: `negcases.json`, 결과 `negative.json`. 23개 중 21개 통과. 저장 변이 둘은 시간 초과다. 통과로 세지 않는다.
- 저장 변이 둘을 사례 제한 900초로 한 번씩 다시 돌렸다(S3, 통합 INT3). 세 번째 실행은 없다.
- `o-tail-fit-store`: 분류 `outside`, 통과가 아니다. 484초에 끝났다.
- 첫 오류는 정리 안 125행이다. 한 칸 밀린 저장 주소에서 `ecancel`이 실패한다.
- 나중에 217행과 38행에 heartbeat 시간 초과가 있다. 38행은 정리 앞 `set_option … in` 줄이다. 범위 밖이다.
- `o-tail-fit-val`: 분류 `timeout_heartbeat`, 통과가 아니다. 488초에 끝났다.
- 첫 오류는 217행의 heartbeat 시간 초과다. 벽시계 시간 초과는 둘 다 없었다.
- 따라서 `tail_fit`의 epoch 저장 민감도는 통과한 부정 시험으로 보이지 않았다.
- `negative.json`은 300초 실행의 기록이다. 다시 돌린 결과는 `RESULT.json` `negatives.s3_rerun_int3`에 있다.
- 공리 관문: `axioms-gate.json` PASS, 선언 3860. 선언 차이: `decl-drift.txt`, ADDED 377개, 모두 `E2e.OptR1`.
- `axioms-gate.json`은 시험 브랜치 트리(`5821b19`)의 기록이다.
- 통합 트리의 기록은 `../e2e/axioms-gate.json`이다. PASS, 선언 4519 = 4142 + 377.
- Go 차분(arm64, Go 의미론만): `diff/`. 벤치마크(arm64만): `bench/`.
- 새 `.S`는 Lake 입력이 아니다. `.S`가 바뀌면 `E2e.OptR1`을 깨끗이 다시 빌드한다.

## 6. 오류 경로 효과와 벤치마크 (리뷰 opt-r1-r1 S5, S6)

- 오류 경로 효과가 바뀌었다(계약 항목 6).
- Root가 무효이고 `8 ≤ spare < 40`이면 새 코드는 블록 하나를 할당한다. 옛 코드는 할당하지 않는다.
- 같은 경우 새 코드는 호출자의 spare를 쓰지 않는다. 옛 코드는 C-1 쓰기를 한다.
- 돌려주는 값은 같다. `(nil, ErrBytesLength)`다.
- 벤치마크는 linux/arm64에서만 돌았다. x86-64 결과는 없다. 수치는 `bench/bench-summary.json`에 있다.
- B2(nil dst): 할당 2 → 1, 56 → 48 B. ns는 더 빠르다. 크기는 실행마다 다르다.
- B3(cap 8): 기대한 2 → 1 할당이 성립하지 않았다. 둘 다 2다.
- 이유: 옛 코드는 cap 8에서 epoch가 맞으므로 한 번만 늘린다. 탈출하는 `make`가 양쪽에 할당 하나를 더한다.
- B5(빠른 경로 재사용): 새 코드가 느리다. 1.92 → 2.19 ns, +14 %.
- B8(1000번 덧붙이기): 할당 18 → 17. ns는 나아지지 않았다. +3.4 %.
- B9(무효 Root, spare 16): 할당 0 → 1, 0 → 48 B. ns도 나빠졌다.
- `MarshalSSZ()`(B1)와 중첩 AttestationData(B7)는 바뀌지 않았다.
- 리뷰어의 부분 재실행(B2, B5, B8, B9만, 전체 절차가 아니다)은 다음을 보였다.
- B5 +12.6 %가 재현되었다(1.90 → 2.14 ns, 범위가 겹치지 않는다).
- 할당 수와 B/op가 재현되었다.
- 할당하는 경우의 ns는 회차 사이에 약 35 %까지 달라졌다. B2-new 24.96과 16.94 ns, B9-new 24.02와 15.92 ns.
- B2-old는 26.4 ns였다(작업자 실행 38.6 ns). 그래서 B2의 고정 백분율을 적지 않는다.
- 결론: 정확성을 지키는 재검증은 보였다. 속도 향상은 일반적으로 보이지 않았다. 결과가 섞여 있다.

## 덧붙임 (2026-11-12, 통합 INT7; 리뷰 int6-r1 S1)

- 위 "통합 트리의 기록"의 4519는 통합 INT3 때의 값이다. 그 줄은 고치지 않는다.
- 지금 통합 트리의 기록도 `../e2e/axioms-gate.json`이다. INT7 뒤 PASS, 선언 9758이다.
- `E2e.OptR1` 선언은 그 수에 들어 있다. 이 디렉터리의 `axioms-gate.json`(3860)은 시범 브랜치 트리의 기록 그대로다.
