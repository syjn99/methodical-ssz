# REPORT-1b-fix: 1b 리뷰 결함 수정 (Kraken x64)

기준: 브랜치 `syjn99/ssz-fv-phase1b-fix`, 시작 `32c0bdc`(1b `9ff7c73` + fv/AGENTS.md 2커밋).
Kraken `6064eec`(main), Lean `nightly-2026-09-21`, EthLib `8621856`, Go 1.26.3, `GOAMD64=v1`.
작성 2026-11-05.
시각은 `date`로 잰 IST 에이전트 시간이다.

## 0. 판정

(작성 중)

## 1. 완료 단위의 정의

완료 단위는 다섯 가지를 모두 가진다.

1. 계약 또는 정리의 수정.
2. 구체 Host에서 전제 전체의 증인. 가변 길이는 빈 값, 1개, 최대.
3. 기계어 정리.
4. 링크 검사 PASS.
5. 부정 시험: 변이가 지정 정리 안에서 실패하고 대조군이 통과한다.

코드가 빌드되는 것은 완료가 아니다.

## 2. X0. 준비

- 1b `.lake`를 복사해 캐시를 덥혔다. `lake build` 678 jobs 성공.
- `review/Review1b.lean`이 현재(수정 전) 코드에서 False 4개를 증명했다. 표준 공리 3개만 쓴다.
- `pgrep -fl "lean|lake"`: 다른 세션의 언어 서버만 있었다. 빌드는 없었다.

## 3. X1. GrowsliceC 재정의 (astra 발견 1, P0)

시간: 14:42–15:07, 25분(X0 포함). 측정값이다. 추정이 아니다.

### 3.1 새 계약

`Fk/Contracts.lean`의 `GrowsliceC Heap ty esz S`.
Go 1.26.3 `runtime/slice.go`의 `growslice`와 `nextslicecap`을 읽고 만들었다.

| 항목 | 전제 | 근거 |
| --- | --- | --- |
| 원소 크기 | `0 < esz` | Go는 `esz = 0`이면 `zerobase`와 cap = newLen을 돌려준다. 성장 정책과 다르다 |
| 서명 있는 길이 범위 | `newLen ≤ 2^48`(예산에서 유도) | `newLen < 0`이면 Go가 패닉한다 |
| oldCap | `oldLen = newLen − num ≤ oldCap < newLen` | 컴파일러는 `newLen > oldCap`일 때만 부른다 |
| 성장 정책 | 결과 `nc ≤ newCap`, `nc = nextSliceCap newLen oldCap` | `nextslicecap`을 Lean으로 옮겼다(`growLoop`, 연료 = newLen으로 충분함을 증명) |
| 할당 한도 | `2·esz·nc + 8192 ≤ avail ≤ maxAlloc = 2^48` | `roundupsize(n) ≤ 2n + 8192`. Go 크기 등급 표 전수 검사로 확인(작은 객체 최악 +6, 큰 객체는 페이지 반올림) |
| 소유 자원 | `Heap avail`, 옛 블록, scratch `S`, spill 40바이트 | Go ABIInternal에서 피호출자는 레지스터 인수 5개의 spill 칸을 쓴다 |
| 결과 | rsp + 8, rbp·r14 보존, rbx = newLen, `esz·newCap ≤ 2·esz·nc + 8192`, `avail' + esz·newCap ≤ avail` | 힙이 줄어든다는 관계를 결론에 둔다 |

1b 형식은 `newLen = 2^63`에서 결론이 `2^63 ≤ newCap < 2^63`이 되어 모순이었다.
`review1b_input_excluded`가 그 입력이 새 예산 전제를 만족하지 못함을 증명한다.

### 3.2 계약 모델과 증인

| 정리 | 내용 |
| --- | --- |
| `rt_memmove` | `Fk/RtCopy.S`의 바이트 복사 루프가 모든 `S`에서 `MemmoveC S`를 만족한다 |
| `rt_growslice` | 범프 할당기(`Fk/Bump.lean`의 `bumpHeap`)와 같은 복사 루프가 모든 `ty`, `S`에서 `GrowsliceC bumpHeap ty 1 S`를 만족한다. newCap = 2·newLen + 192 |
| `growslice_call_runs` | `witnessHost`(ListU64 수용 증인 Host에 `RtCopy`를 붙임)에서 `old.length ≤ oc < n ≤ 1000`인 구체 상태가 계약 전제를 모두 만족하고 호출이 돌아온다 |
| 예제 3개 | BitL 형태 n = 1(빈 old)과 n = 257(BitL 최대), ListU64 형태(old 3바이트, cap 3, newLen 7) |
| `review1b_input_excluded` | `newLen = 2^63`은 모든 esz, oldCap, avail에서 예산 전제를 어긴다 |

### 3.3 다시 증명한 정리

| 정리 | 바뀐 전제 |
| --- | --- |
| `bl_accept_main` | spill 40바이트(rsp − 120), `2·n + 8192 ≤ avail`, `avail ≤ maxAlloc` |
| `bl_unmarshal_accept_spec_k` | spill, `8706 ≤ avail`(EthLib가 받는 입력은 n ≤ 257), `avail ≤ maxAlloc` |
| `lum_grow_site` | spill(rsp), `len ≤ cap < len + 4`, `2·nextSliceCap(len + 4, cap) + 8192 ≤ avail ≤ maxAlloc` |

### 3.4 검사

- `lake build` 680 jobs 성공. `tools/axioms.sh`: `TOTAL 620 NONSTANDARD 0`.
- `review/Review1b.lean`은 새 계약에서 정교화되지 않는다(`review/review1b-regression.log`, 오류 5개). 회귀 자료로 그대로 둔다.
- 링크 검사 PASS(대상 바이트는 바뀌지 않았다).
- 부정 시험 `gsnum`: BitL의 `mov %rbx,%rdi`(num = n)를 `mov %rcx,%rdi`(num = 0)로 바꾸면 `bl_accept_main`의 growslice 호출 지점(`BlAccept.lean:254`)에서 실패한다. 대조군은 통과한다.

### 3.5 완료 단위 판정

- `GrowsliceC`: 완료. 계약 수정, 모델, 구체 호출 증인, 부정 시험이 있다.
- `lum_grow_site`: 증인 부분. 계약은 만족 가능하다. ListU64 마샬 Host의 전체 증인은 없다.
- `bl_accept_main`, `bl_unmarshal_accept_spec_k`: 증인 없음. 같은 Host에서 `ValidateBitlistC`의 모델이 필요하다(X4).

## 4. X2. fmt.errorf 계약 (astra 발견 2, P1)

시간: 15:07–15:22, 15분.

### 4.1 Go 1.26.3의 두 함수

- 공개 `fmt.Errorf`는 내부 `fmt.errorf`를 부른다. 결과가 nil이면 `errors.New(format)`을 돌려준다.
- 내부 `errorf`는 `len(a) = 0`이고 형식에 `%`가 없으면 nil을 돌려준다. 그 외에는 항상 nil이 아닌 오류를 돌려준다.
- 생성 코드는 `errors.New`를 인라인한다: `runtime.newobject`로 16바이트 `errors.errorString`을 만든다.

### 4.2 계약을 인수 조건으로 나눔

| 계약 | 전제 | 결과 |
| --- | --- | --- |
| `FmtErrorfNilC S` | rdi = 0, 형식 바이트 `fs`에 0x25 없음, spill 40 | rax = 0, 할당 없음, r14 보존 |
| `FmtErrorfC Heap S` | `1 ≤ len(a) = cap(a)`, `fs`, 인수 배열(16·len 바이트), spill 40 | rax ≠ 0, `fs`·인수 보존, `avail' ≤ avail`, r14 보존 |
| `ConvT64C Heap S` | `8 ≤ avail`, spill 8 | rax ≠ 0, `avail' ≤ avail ≤ avail' + 8`, r14 보존 |

`FmtErrorfC`에 남는 신뢰: fmt는 인터페이스 값을 읽고 `%w` 인수의 `Error()`를 부른다. 계약은 그것이 끝나고 `F`에 쓰지 않는다고 가정한다.

### 4.3 다시 증명한 정리

- ListC `lc_reject_zero_main`, `lc_reject_past_main`, `lc_reject_tail_main`: nil 반환 → `test; jne` 안 감 → `newobject`(16바이트) → 문자열 헤더 저장 → itab 반환. 새 전제: spill 40(rsp − 224), Go 소스의 형식 바이트(`lcFmtZero` 53바이트, `lcFmtShort` 63바이트) 조각, `16 ≤ avail`, `NewobjectC`, itab 주소 ≠ 0.
- 세 `*_spec` 감싸개(`Fk/LcSpec.lean`)도 같은 전제로 바꿨다.
- ListU64 `lu_reject_toobig_main`, `lu_reject_misaligned_main`: 좁힌 `FmtErrorfC`(인수 2개)와 새 `ConvT64C`로 다시 증명했다. 인수 배열 32바이트를 한 조각으로 넘긴다(`join4`). 새 전제: spill 40(rsp − 136), 형식 바이트 조각(56, 68바이트), `8 ≤ avail`.

### 4.4 모델과 검사

- `Fk/RtErr.lean`: `rt_errorf_nil`, `rt_errorf`, `rt_convT64`. 한 `fmt.errorf` 코드가 두 계약을 함께 만족한다.
- `lake build` 682 jobs. `TOTAL 629 NONSTANDARD 0`.
- 부정 시험 `nilerr`: ListC zero 경로의 `jne`를 `je`로 바꾸면 `lc_reject_zero_main` 안(`LcReject.lean:434`)에서 실패한다.

### 4.5 완료 단위 판정

- 세 계약: 계약 모델이 있다. 호출 지점의 구체 Host 증인은 없다.
- ListC 거부 3정리, ListU64 거부 2정리: 실제 분기를 증명한다. 정리별 증인 없음.
- 형식 바이트와 ELF의 대조는 X6에서 링크 검사에 넣는다.
