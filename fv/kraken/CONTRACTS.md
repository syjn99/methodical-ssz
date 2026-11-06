# CONTRACTS: 피호출자와 전역의 처리 (Kraken 가설 형식)

대상: 1a 9개 함수(Scalars, FixedVec, ListU64의 SizeSSZ, MarshalSSZTo, UnmarshalSSZ)와 1b 18개 함수(BitVec, Nested, ListC, BitL, Checkpoint, AttestationData), 재증명에서 더한 `ssz.ValidateBitvector`. 정의는 `lean/Fk/Contracts.lean`, `lean/Fk/FunSpecs.lean`, `lean/Fk/Vbl.lean`(ValidateBitlist), `lean/Fk/Vbv.lean`(ValidateBitvector 명세). 작성 2026-11-05, 재증명 갱신 2026-11-06, 재증명 수정(X5, X6) 갱신 2026-11-06, 재증명 수정 2(X4, X5) 갱신 2026-11-06. 재증명 수정 2의 변경은 1e절에 모았다. 1–1d절의 해당 행은 1e절이 대신한다.

분류:
- **(a) 증명 대상**: 기계어를 Kraken 의미론으로 실행해서 증명한다.
- **(b) 계약**: 정리의 가설이다. 모든 기계 상태, 반환 주소, 프레임 `F`에 대해 양화한다.
- **(c) 사전조건 아래 제외**: 정리의 전제가 그 경로를 막는다. 막는다는 사실은 증명한다.

## 1. 피호출자

| 피호출자 | 호출하는 함수(경로) | 분류 | Kraken 형식 | 비공허성 |
| --- | --- | --- | --- | --- |
| `runtime.makeslice` | ListU64.UnmarshalSSZ(수용), FixedVec.UnmarshalSSZ(수용) | (b) | `MakesliceC Heap ty esz S`: 사전조건에 런타임 힙 조각 `Heap avail`, 타입 인수 `rax = ty`, `len ≤ cap = cnt`, `esz·cnt ≤ avail`. 사후조건: 반환 주소로 복귀, rsp + 8, 0으로 채운 `esz·cnt` 바이트 블록을 `Heap`에서 떼어냄, `Heap (avail − esz·cnt)`, `F` 보존 | **있음.** `bump_makeslice`(범프 할당기가 계약을 만족, Kraken 의미론 위 증명). `lu_accept_runs`(구체 Host에서 `lu_accept_main`의 모든 전제를 증명, n ≤ 16) |
| `runtime.memmove` | FixedVec.UnmarshalSSZ(수용), FixedVec.MarshalSSZTo(빠른 경로, 거부) | (b) | `MemmoveC S`: 서로소인 원천·목적 조각(n 바이트), 복귀 후 목적 = 원천, 원천과 `F` 보존. 겹치는 범위는 계약 밖(호출자의 `⋆`가 배제) | **모델 있음(1b-fix).** `rt_memmove`: 바이트 복사 루프(`Fk/RtCopy.S`)가 모든 `S`에서 계약을 만족한다. 호출 지점 증인: 아래 1b 표의 memmove 행 |
| `runtime.growslice` | 모든 MarshalSSZTo(용량 부족 경로) | (b) | `GrowsliceC Heap ty esz S`(1b-fix). 전제: `0 < esz`, `rsi = ty`, `num ≤ newLen`, `oldLen = newLen − num ≤ oldCap < newLen`, `nc = nextSliceCap newLen oldCap`(Go 1.26.3 `nextslicecap`)에 대해 `2·esz·nc + 8192 ≤ avail ≤ maxAlloc = 2^48`, 옛 원소 `old`(esz·oldLen 바이트), scratch `S`, 반환 슬롯 위 spill 40바이트. 사후조건: rsp + 8, rbp·r14 보존, rbx = newLen, `nc ≤ newCap`, `esz·newCap ≤ 2·esz·nc + 8192`, 새 블록 = `old ++ tail`, `avail' + esz·newCap ≤ avail`, 옛 블록과 `F` 보존 | **모델 있음.** `rt_growslice`(범프 할당기 + 복사 루프, esz = 1). `growslice_call_runs`(구체 Host, 빈 값·1·257·ListU64 형태). 1b 형식은 모순이었다(`review/Review1b.lean`) |
| `runtime.convT64` | ListU64.UnmarshalSSZ(거부 3, 4) | (b) | `ConvT64C Heap S`(1b-fix): 전제 `8 ≤ avail`, spill 8바이트. 사후조건: rsp + 8, r14 보존, **rax ≠ 0**, `avail' ≤ avail ≤ avail' + 8`, `F` 보존. 상자 내용은 말하지 않는다(fmt 계약이 읽지 않는다) | 모델 있음(`rt_convT64`) |
| `fmt.errorf`(내부 함수, 공개 `fmt.Errorf`가 아님) | ListU64.UnmarshalSSZ(거부 3, 4) | (b) | 재증명 수정 X5부터 `FmtErrorfWC Heap S`(아래 표). 1b-fix의 `FmtErrorfC`(인수 ≥ 1, 인수 형태 제한 없음)는 지웠다. 인수 2개: `convT64` 상자(`%d`)와 전역 `ssz.ErrListTooBig`·`ssz.ErrIncorrectListSize`(`%w`). 전제: 전역의 첫 워드 e0 = errorString itab, 데이터 e1의 `ErrStr e1 sp msg`, 예산 `msg + 8268 ≤ avail`(convT64 8바이트 + fmt). 결론 rax ≠ 0 | 모델 있음(`rt_errorf_w`). 증인: `WitLuTb`, `WitLuMa`(전역 오류 객체와 메시지 "err"를 블록에 둔다) |
| `runtime.newobject` | ListU64.UnmarshalSSZ(거부 3, 4, `fmt.errorf`가 nil을 돌려준 경우) | (c) | 인수 2개라 Go의 `errorf`는 nil을 돌려주지 않는다. `FmtErrorfWC`의 rax ≠ 0이 이 경로를 막는다 | 해당 없음 |
| `runtime.gcWriteBarrier2` | FixedVec·ListU64 UnmarshalSSZ(수용) | (c) | 전제: `runtime.writeBarrier` 4바이트 = 0. 코드가 플래그를 읽고 `je`로 건너뜀을 증명한다 | 해당 없음 |
| `runtime.morestack_noctxt.abi0` | 프레임이 있는 모든 함수 | (c) | 전제: `g.stackguard0`(r14 + 16) < rsp(또는 rsp − 8). `jbe`가 안 갈림을 증명한다 | 해당 없음 |
| `runtime.panicBounds` | FixedVec·ListU64 UnmarshalSSZ 루프 | (a) | 경계 검사 분기가 안 갈림을 루프 한 바퀴마다 증명한다(`lu_iter`, `fv_iter`) | 해당 없음 |

### 1b에서 더한 것

| 피호출자 | 호출하는 함수(경로) | 분류 | Kraken 형식 | 비공허성 |
| --- | --- | --- | --- | --- |
| `runtime.newobject` | Nested.UnmarshalSSZ(S, L 할당), AttestationData.UnmarshalSSZ(Source, Target), ListC.UnmarshalSSZ(원소마다, 오류 객체 3경로), ssz.ValidateBitvector(오류 객체) | (b) | `NewobjectC Heap ty sz S`: 사전조건 `rax = ty`, `sz ≤ avail`. 사후조건: 복귀, rsp + 8, r14 보존, 0으로 채운 `sz`바이트 블록을 `Heap`에서 떼어냄, `F` 보존 | **모델 있음.** `bump_newobject16`(재증명, errorString), `bump_newobject24`, `bump_newobject32`(1b-fix). 증인: `WitNe0/1/16`(24), `WitLcA1/4`(24, ListC 원소, 재증명 수정 X8), `WitAd`(32), `WitLcZ/P/T`(16), `WitBvR`(16, ValidateBitvector 안) |
| `runtime.makeslice`(byte, 0, 32), (*ListU64, n, n) | Checkpoint·AttestationData UnmarshalSSZ, ListC.UnmarshalSSZ(원소 포인터 배열) | (b) | `MakesliceC`(len ≤ cap로 넓힘, c0f3396) | `bump_makeslice1`, `bump_makeslice`. 증인: `WitCp`, `WitAd`, ListC 포인터 배열 호출 지점 `WitLcA1/4`(재증명 수정 X8) |
| `runtime.memmove` | Checkpoint·AttestationData·BitL의 Unmarshal·Marshal | (b) | `MemmoveC S` | `rt_memmove`. 증인: `WitCp`, `WitAd`, `WitCpM`, `WitAdM`, `WitBl1/257`, `WitBlM1/257`, `WitFvM`, `WitFvMR`, `WitCpMR` |
| `runtime.growslice` | BitL.UnmarshalSSZ(`append([]byte{}, buf[4:]...)`) | (b) | `GrowsliceC`, 옛 원소 `[]`(빈 슬라이스, 주소 `runtime.noptrbss`), oldCap = 0, newLen = num = n. `nextSliceCap n 0 = n`이라 예산은 `2n + 8192` | 계약 모델 있음(`rt_growslice`). `bl_accept_main` 공동 증인: `WitBl1`, `WitBl257`(ValidateBitlist·growslice·memmove 한 힙). ListU64 마샬 호출 지점: `WitLuG`(재증명 수정 X8) |
| `fmt.errorf` | ListC.UnmarshalSSZ(오프셋 오류 3경로: zero, past, tail) | (b) | `FmtErrorfNilC S`(1b-fix): 인수 0개(rdi = 0), 형식 바이트에 `%`(0x25) 없음 → **rax = 0**, 할당 없음. 그 뒤 코드가 `runtime.newobject`(`NewobjectC`, 16바이트)로 `errors.errorString`을 만든다. 정리가 이 분기를 증명한다. 형식 바이트는 Go 소스의 문자열(`lcFmtZero`, `lcFmtShort`)이고 ELF 대조는 `link/check.py`가 한다(X6) | 모델 있음(`rt_errorf_nil`) |
| `ssz.ValidateBitlist` | BitL.UnmarshalSSZ, BitL.MarshalSSZTo(재증명, F2 수정) | (b) | 재증명 수정 X5에서 입력으로 나눴다. `ValidateBitlistC S`(유효 입력): 전제 `blValid buf`(EthLib `unpackDelimited (some 2048)`이 받음), 결론 rax = 0, 할당 없음, `F`와 바이트 보존. `ValidateBitlistErrC Heap S`(무효 입력): 전제 `¬ blValid buf`, 예산 `8192 ≤ avail`, 결론 rax = errorString itab, rbx = e, `ErrStr e sp msg`(16바이트 객체 + 문자열, msg ≤ 128)를 힙에서 받음(`avail' + 16 + msg ≤ avail ≤ avail' + 8192`). 이 함수는 `bsr`이 있어 Kraken이 파싱하지 못한다. **bitlist의 핵심 검사가 이 계약 뒤에 있다** | **모델 있음.** `rt_validate_bitlist`, `rt_validate_bitlist_err`(`Fk/RtVbl.S`, bsr 없이 `blArith` 계산, 무효면 bump 힙 16바이트 = 빈 메시지 errorString). 증인: `WitBl1/257`, `WitBlM1/257`(유효), `WitBlR`(무효) |
| `target.Scalars.UnmarshalSSZ` | Nested.UnmarshalSSZ | (a) 함수 명세 | `ScUAccC`: 우리 쪽 정리 `sc_accept_main`에서 유도(`sc_uacc_holds`) | 증명됨(가설이 아니라 정리에서 나온다) |
| `target.ListU64.UnmarshalSSZ` | Nested.UnmarshalSSZ, ListC.UnmarshalSSZ(원소마다) | (a) 함수 명세 | `LuUAccC Heap S`: `lu_accept_main`에서 유도(`lu_uacc_holds`, `MakesliceC` 필요) | 증명됨 |
| `runtime.gcWriteBarrier1/2` | 1b 디코더 전부 | (c) | 쓰기 장벽 0 전제. 플래그를 읽고 건너뜀을 증명한다(AttestationData는 6번) | 해당 없음 |
| `runtime.convT64` | ListC.UnmarshalSSZ(정렬 오류, 원소 수 초과) | (b) | `ConvT64C` | 모델 있음(`rt_convT64`). ListC의 그 두 경로는 증명하지 않았다 |

### 재증명에서 더한 것 (생성기 수정 F1·F2)

| 피호출자 | 호출하는 함수(경로) | 분류 | Kraken 형식 | 비공허성 |
| --- | --- | --- | --- | --- |
| `ssz.ValidateBitvector` | BitVec.UnmarshalSSZ, BitVec.MarshalSSZTo | (a) 함수 명세 | `VbvAccC`(수용), `VbvPadC Heap S`(패딩 거부). `vbv_accept_main`, `vbv_reject_pad_main`에서 유도한다(가정이 아니다). 패딩 거부 경로 안의 `fmt.errorf`(인수 0개)와 `newobject`(16바이트)는 `FmtErrorfNilC`, `NewobjectC` 계약이다 | 증명됨. `WitBv`, `WitBvM`가 실제 코드로 수용 명세를 쓴다 |
| `ssz.ValidateBitlist` | BitL.MarshalSSZTo | (b) | `ValidateBitlistC S`, `ValidateBitlistErrC Heap S`(위 표) | `rt_validate_bitlist`, `rt_validate_bitlist_err` |
| `fmt.errorf`(인수 1개, `%w`) | BitVec 디코더의 `"J: %w"`, BitL 인코더의 `"B: %w"` | (b) | `FmtErrorfWC Heap S`(재증명 수정 X5): 인수는 `%w` 하나이고 그 값은 errorString 오류다. 인터페이스 타입 워드 = itab + 8의 워드, 데이터 워드 e, `ErrStr e sp msg`가 발자국에 있고 보존된다. 예산 `fs + msg + 8192 ≤ avail`. 형식 바이트는 `link/check.py` (g)가 ELF·Go 소스와 대조한다(`bvFmtJ`, `blFmtB` 포함, 오프셋 목록 대조) | `rt_errorf_w`. 증인: `WitBvR`(BitVec, 실제 ValidateBitvector가 만든 오류), `WitBlR`(BitL, `rt_validate_bitlist_err`가 만든 오류) |

## 1c. 계약별 조건 (1b-fix X3)

모든 계약은 Go 1.26.3 ABIInternal(amd64)의 호출을 가정한다.
반환 주소는 rsp에 있다.
`S`는 반환 슬롯 아래의 scratch 바이트 수다.
spill은 반환 슬롯 바로 위의 레지스터 인수 칸이다. 피호출자가 쓸 수 있다.

| 계약 | 인수 조건 | 자원 예산 | 스택 창 | 보존 | 모델 |
| --- | --- | --- | --- | --- | --- |
| `MakesliceC Heap ty esz S` | rax = ty, `len ≤ cap = cnt`, `cnt < 2^63` | `esz·cnt ≤ avail`, `esz·cnt ≤ maxAlloc` | scratch S, spill 24 | rsp + 8, r14, rbp, `F` | `bump_makeslice`(esz = 8) |
| `MemmoveC S` | rcx = n, 원천·목적 n바이트, 서로소 | 없음 | scratch S(Go 함수는 쓰지 않는다), spill 없음(asm, `$0-24`) | rsp + 8, r14, rbp, 원천, `F` | `rt_memmove` |
| `GrowsliceC Heap ty esz S` | `0 < esz`, rsi = ty, `num ≤ newLen`, `oldLen ≤ oldCap < newLen` | `2·esz·nc + 8192 ≤ avail ≤ maxAlloc` | scratch S, spill 40 | rsp + 8, r14, rbp, rbx, 옛 블록, `F` | `rt_growslice`(esz = 1) |
| `NewobjectC Heap ty sz S` | rax = ty | `sz ≤ avail` | scratch S, spill 8 | rsp + 8, r14, rbp, `F` | `bump_newobject16/24/32` |
| `ConvT64C Heap S` (수정 2) | 없음(모든 값). 사전조건에 `StaticBox v`(v < 256이면 `staticuint64s + 8v`의 8바이트, 읽기 전용) | `8 ≤ avail`. 결론 `avail' + hb.length ≤ avail ≤ avail' + 8` | scratch S, spill 8 | rsp + 8, r14, `StaticBox v`, `F`. 결론 `BoxIn rax v hb`(정적 표 또는 힙 8바이트 = v)와 `Eq (hb.At rax)` | `rt_convT64`(bump 힙에 v 저장, `ConvT64C bumpHeap S`) |
| `FmtErrorfNilC S` | rdi = 0, 형식에 `%` 없음, 형식 바이트 조각 | 없음(할당 없음) | scratch S, spill 40 | rsp + 8, r14, 형식, `F` | `rt_errorf_nil` |
| `ValidateBitlistC S` | rbx = len(buf), rdi = 2048, buf 조각, `blValid buf` | 할당 없음 | scratch S, spill 32 | rsp + 8, r14, rbp, buf, `F` | `rt_validate_bitlist`(`RtVbl`) |
| `ValidateBitlistErrC Heap S` (수정 2) | 위와 같음, `¬ blValid buf`. 사전조건에 rodata 메시지 셋 `vblRO` | `8192 ≤ avail`. 결론 `avail' + 16 + hm.length ≤ avail ≤ avail' + 8192` | scratch S, spill 32 | rsp + 8, r14, rbp, buf, `vblRO`, `F`. 새 `ErrObj rbx sp msg`(16바이트)와 `Eq (hm.At sp)`, `VblMsg sp msg hm`(rodata 셋 중 하나이고 hm = [], 또는 `%d` 힙 메시지 hm = msg ≤ 128) | `rt_validate_bitlist_err`(힙 경우, 빈 메시지) |
| `FmtErrorfWC Heap fs RO MsgIn S` (수정 2) | 형식 `fs` 고정(정리가 상수 `bvFmtJ`·`blFmtB`로 정한다), rdi = rsi = 1, 인수 배열 `ity ++ e`, `ErrObj e sp msg`, `Eq (hm.At sp)`, 읽기 전용 `RO`, `MsgIn sp msg hm` | `fs + msg + 8192 ≤ avail`, 결론 `avail' ≤ avail` | scratch S, spill 40 | rsp + 8, r14, 형식, 인수, `ity`, 오류 객체, `hm`, `RO`, `F` | `rt_errorf_w`(모든 fs, RO, MsgIn) |
| `FmtErrorfDWC Heap fs tw S` (수정 2) | 형식 `fs` 고정(`luFmtTooBig`·`luFmtMis`), rdi = rsi = 2, 인수 배열 `tw ++ bx ++ ity ++ e`(tw = `type:int`, `luTW`), `BoxIn bx v hb`, `StaticBox v`, `Eq (hb.At bx)`, `ErrStr e sp msg` | `fs + 20 + msg + 8192 ≤ avail` | scratch S, spill 40 | 위와 같음, 상자 자원 포함 | `rt_errorf_dw` |

전역 상태 가정(모든 계약 공통):
- `runtime.writeBarrier`(4바이트)는 호출자 정리의 전제에서 0이다. 그 조각은 계약의 `F`에 있다. 그래서 계약은 "호출 중 쓰기 장벽이 켜지지 않는다"를 가정한다. GC가 할당 중 표시 단계에 들어가면 이 가정은 거짓이다(조건 C19).
- 스택 가드(`g.stackguard0`, r14 + 16)는 호출자 정리의 전제다. 피호출자의 스택 증가(`morestack`)는 계약 밖이다. scratch `S`가 충분하다고 가정한다.
- 타입 기술자(`type__+…`)의 내용은 계약이 읽지 않는다. 모델은 크기를 상수로 둔다. 실제 런타임은 기술자를 읽는다.
- 호출자 프레임에서 spill 칸이 비어 있음은 정리의 전제가 그 자리를 별도 조각으로 받는다는 것으로 확인했다(ListU64 rsp − 136, FixedVec·BitVec rsp − 32, Checkpoint rsp − 40, AttestationData rsp − 48, ListC rsp − 224, Nested rsp − 96, BitL rsp − 120, ListU64 거부 rsp − 136).

## 1d. 추상 모델 증명과 Go 정교화 (재증명 R8)

두 종류의 증명을 구분한다.

- **추상 모델 증명.** `rt_*`, `bump_*` 정리는 Kraken 의미론 위의 작은 어셈블리가 계약을 만족함을 보인다.
  이것은 계약이 모순이 아니고, 여러 계약을 한 Host와 한 힙에서 함께 만족할 수 있음을 보인다.
  계약을 쓰는 주 정리가 공허하지 않다는 근거다.
- **Go 정교화.** Go 1.26.3 런타임의 실제 기계어가 계약을 만족한다는 증명이다.
  이 세션에는 없다. 모든 계약 호출은 실제 Go 실행에 대해서는 신뢰 항목이다.

재증명 수정 X5에서 형식 전제로 옮긴 것(astra 재증명 발견 3):

| 항목 | 이전 | 지금 |
| --- | --- | --- |
| ValidateBitlist 오류의 데이터 포인터 | 규정 없음(rbx 임의) | `ValidateBitlistErrC` 결론: rbx = e, `ErrStr e sp msg` |
| 오류 객체 자원(16바이트 errorString, 문자열 바이트) | 없음 | `ErrStr`: 객체 (sp, len)와 메시지 바이트. 힙에서 받는다 |
| ValidateBitlist의 할당 예산 | 없음(`F` 밖 할당을 가정) | 전제 `8192 ≤ avail`, 결론 `16 + msg ≤ 소비 ≤ 8192` |
| `%w` 인수의 형태 | 임의의 16바이트 | `FmtErrorfWC`: 타입 워드 = errorString itab + 8의 워드, 데이터 = e, `ErrStr e sp msg`가 발자국에 있다 |
| `Error()`가 읽는 것 | 신뢰(주석) | `ErrStr`가 계약의 발자국에 있고 보존된다. `*errorString.Error`는 `e.s`를 돌려줄 뿐이다 |
| fmt의 할당 예산 | `avail' ≤ avail`만 | 전제 `fs + msg + 8192 ≤ avail` |
| ValidateBitvector 오류 객체 | 16바이트 내용 임의 | `VbvPadC` 결론: 객체 = (`go_string._+27706`, 35). 실제 코드에서 증명 |
| 프레임 보존 | 계약 결론 `F` | 그대로(형식). 다만 GC가 없다는 가정에 기댄다(아래) |

ListU64 거부 두 경로(`lu_reject_toobig_main`, `lu_reject_misaligned_main`)도 `FmtErrorfWC`로 옮겼다(재증명 수정 X5).
전제는 전역 오류의 첫 워드 e0 = errorString itab(errors.New의 값), 데이터 e1의 `ErrStr`, 예산이다.
그래서 제한 없는 `FmtErrorfC`를 쓰는 정리가 없어 지웠다(`rt_errorf`도 지웠다).

계약별로 형식 전제로 옮기지 못한 신뢰 항목:

| 계약 | 신뢰 항목(형식 전제 밖) | 옮기지 못한 이유 |
| --- | --- | --- |
| `FmtErrorfWC` | Go의 실제 할당량이 예산(`fs + msg + 8192`) 안이다(printer 객체, 결과 문자열 `len(fs) − 2 + len(msg)`, `*fmt.wrapError` 32바이트). 호출 중 GC가 없다 | fmt의 할당 경로와 sync.Pool을 모델하지 않았다. 예산 값은 코드를 읽은 결과다 |
| `ValidateBitlistErrC` | 메시지가 힙 바이트라고 모델한다. Go 1.26.3에서 인수 없는 세 메시지("bitlist empty…", "trailing byte is zero", "too many bits")는 rodata에 있다. 그래서 실제 Go에 적용하려면 호출자 `F`가 그 rodata 바이트를 갖지 않아야 한다. 가장 긴 메시지는 82바이트(고정 43바이트, int 19자리, uint64 20자리)라 msg ≤ 128이다 | 계약은 모든 `F`에 대해 양화한다. "rodata는 `F` 밖"을 표현할 영역 모델이 없다 |
| `FmtErrorfWC`(`pre`) | ListU64 거부의 첫 인수(`convT64` 상자, `%d`)의 내용과 타입. `%w` 인수(errorString)는 형식 전제다 | `ConvT64C`가 상자 내용을 말하지 않는다(아래 행) |
| `FmtErrorfNilC` | 형식 바이트에 `%`가 없으면 할당 없이 nil을 돌려준다(Go 1.26.3 `fmt/errors.go`의 분기를 읽은 결과) | fmt 내부 코드를 증명하지 않았다 |
| `ConvT64C` | 상자의 내용(값 v)과 그 메모리를 말하지 않는다. `avail' ≤ avail ≤ avail' + 8`만 말한다 | 이 세션의 호출자는 그 포인터를 fmt에 넘기기만 한다. 넣으면 호출자 정리와 모델을 함께 바꿔야 한다(이견) |
| `MakesliceC`, `NewobjectC`, `GrowsliceC` | 타입 기술자를 읽지 않는다. 할당 중 GC가 없다(쓰기 장벽 0이 `F`에 있다). 할당기 실패는 정리 밖이다 | 할당기와 GC 모델이 없다 |
| `MemmoveC` | 겹치지 않는 범위만 다룬다 | 호출자의 `⋆`가 겹침을 배제한다. Go memmove는 겹침도 허용하므로 이것은 좁은 적용이다 |
| `ValidateBitlistC`, `ValidateBitlistErrC` | 수용 집합 = EthLib 규칙(`bsr` 포함 Go 코드는 증명하지 않았다). 무효 입력에서 rax = errorString itab(Go 1.26.3에서 모든 오류가 `%w` 없는 `fmt.Errorf`라 `errors.New`를 거친다) | Kraken이 `bsr`를 파싱하지 못한다 |

계약이 아닌 것(가정이 아니라 정리에서 유도): `VbvAccC`, `VbvPadC`(`vbv_acc_holds`, `vbv_pad_holds`), `ScUAccC`, `LuUAccC`(`sc_uacc_holds`, `lu_uacc_holds`).

## 2. 전역과 런타임 상태

| 항목 | 처리 | 근거 |
| --- | --- | --- |
| `ssz.Err*`(두 단어) | 레이블 주소의 분리 조각 + 값 전제(e0, e1) | C5. 주소는 `link/check.py` (b)가 ELF `.symtab`과 대조 |
| `ssz.ErrX`의 itab + 8 | 거부 3, 4가 `*(e0 + 8)`을 읽는다. 전제: e0 ≠ 0, 그 8바이트 조각 | 패키지 초기화 뒤 사실(전제) |
| `runtime.writeBarrier` | 4바이트 = 0 전제. 계약 호출(`makeslice`) 동안 `F`에 있으므로 바뀌지 않는다고 가정한다 | GC가 할당 중 표시 단계에 들어가면 바뀔 수 있다(astra 지적). 조건 C19의 남은 항목 |
| 스택 가드 | 위 (c) | |
| X15 = 0 (Go ABI) | 거부 경로는 가정하지 않는다. `movups %xmm15` 저장은 임의 값 저장으로 증명한다. ListC 빈 리스트 수용만 전제로 둔다(값이 `c.Items`의 len, cap이 된다) | 거부 3, 4. 전제는 Go ABIInternal(amd64)이 보장한다 |
| 레이블 신선성 | 정리의 전제 `LabelsFresh`. 실제 배치(`all.S`)에서 성립함은 `link/check.py` (c)가 검사한다. 구체 Host 하나에서는 Lean 정리(`Fk.Witness.hf5`, `hf198`) | |

## 3. 1a 발견 7(havoc 색인)의 확인

1a는 계약을 기계 모델 안의 표(`rtOf H`)로 실행했다. 계약 결과는 색인된 havoc 값이었고, 그 값이 경로(분기)를 고르는 문제가 있었다.

Kraken에서는 계약이 정리의 **가설**이고, 모든 상태·반환 주소·프레임에 대해 양화한다. 호출 지점에서 `eventually_trans`로 계약의 사후조건을 받고, 사후조건을 만족하는 **임의의** 상태에서 증명을 이어 간다. 그래서:
- 색인이 없다. 같은 계약을 두 번 부르면 두 번 다 같은 가설을 다른 상태에 적용한다(ListU64 거부 3, 4: `convT64` 뒤 `fmt.errorf`, 같은 반환 슬롯).
- 결과가 경로를 고르는 경우는 사후조건의 사실로 분기를 정한다. `fmt.errorf`의 rax ≠ 0이 `test %rax,%rax; jne`의 방향을 정한다(`lu_reject_toobig_main`, `lu_reject_misaligned_main`의 `split` 단계). 사후조건이 그 사실을 주지 않으면 두 경로를 모두 증명해야 한다.
- **정정(1b-fix X2).** 1b는 ListC의 인수 없는 호출에도 rax ≠ 0을 가정했다. Go 1.26.3의 내부 `errorf`는 그 경우 nil을 돌려준다(astra 발견 2). 그래서 1b의 ListC 거부 3정리는 실제 실행 경로가 아닌 분기를 증명했다. 지금은 계약을 인수 조건으로 나누고 nil 뒤 `newobject` 분기를 증명한다.
- 남는 위험은 계약 자체의 모순이다(이전 `hms`). 이것은 증인으로만 검사한다.
- **철회(1b-fix).** 1b의 이 절은 "힙 조각 형식이면 이전 모순이 생기지 않는다"고 판단했다. 그 판단은 틀렸다. 1b의 `GrowsliceC`는 같은 형식이었지만 입력 범위가 없어 모순이었다(astra 발견 1, `review/Review1b.lean`). 형식에 근거한 판단은 비공허성의 근거가 아니다.
- 지금 계약 모델(구현이 계약을 만족한다는 Lean 정리)이 있는 계약: `makeslice`(`bump_makeslice` esz = 8, `bump_makeslice1` esz = 1), `memmove`(`rt_memmove`), `growslice`(`rt_growslice`, esz = 1), `newobject`(`bump_newobject16/24/32`), `fmt.errorf`(`rt_errorf_nil`, `rt_errorf_w`), `convT64`(`rt_convT64`), `ValidateBitlist`(`rt_validate_bitlist`, `rt_validate_bitlist_err`). 모든 계약에 모델이 있다(재증명, 재증명 수정 X5). `joint_models`는 아홉 계약을 한 Host·한 힙에서 함께 만족한다. 모델은 만족 가능성의 근거다. Go 구현의 정교화가 아니다(1d절).

## 4. 정리의 전제가 실제 Go 호출자에서 성립하는가

| 전제 | Go 호출자 |
| --- | --- |
| 인수 레지스터(rax = 수신자, rbx/rcx/rdi = 슬라이스) | ABIInternal이 보장 |
| 수신자 ≠ nil, 주소 0 아님 | 보장하지 않는다. nil 수신자는 Go에서 패닉(`test %al,(%rax)`). 분리 조각이 있으면 그 주소는 매핑된 것으로 본다(접근 권한은 Kraken `Effects.All`이 검사하지 않음, C19) |
| 입력·수신자·스택·출력의 서로소(`⋆`) | 보통의 Go 값에서 성립. 별칭(수신자 안의 바이트를 입력으로)은 배제한다 |
| 스택 가드, 쓰기 장벽 0 | 빠른 경로 전제. 일반 호출의 보장이 아니다 |
| `bool` 바이트 ∈ {0, 1}, 슬라이스 len ≤ cap < 2^63 | Go 값의 불변식. 주 정리는 이 불변식을 전제로 두지 않을 수 있다(더 넓은 상태를 허용). 증인은 Go 값이어야 한다: `lean/tools/wit/goval.py`가 모든 증인의 인수 슬라이스, 수신자 슬라이스·포인터 필드를 검사한다(len ≤ cap < 2^63, 데이터가 블록 안). 68개 증인 위반 0(재증명 수정 X4) |
| 힙 여유(`avail`) | 런타임 할당기가 실패하면 Go는 정상 복귀하지 않는다. 정리는 성공 경우만 말한다 |

## 1e. 재증명 수정 2의 계약 변경 (astra 재증명 수정 발견 4, 5)

| 계약 | 이전 | 지금 | 모델 | 쓰는 정리 |
| --- | --- | --- | --- | --- |
| `FmtErrorfWC` | 임의 `fs`, 임의 앞 인수 `pre`, `1 ≤ rdi` | 정의 인수 `fs`(정리가 상수로 고정), `RO`, `MsgIn`. 인수 하나(rdi = 1), `pre` 없음. 메시지는 `ErrObj ⋆ Eq (hm.At sp) ⋆ RO`에 있다 | `rt_errorf_w` | `bv_reject_padding_main`(`bvFmtJ`, `bvRO`, `BvMsg`), `bl_marshal_reject_main`·`bl_reject_invalid_main`(`blFmtB`, `vblRO`, `VblMsg`) |
| `FmtErrorfDWC` | 없음(ListU64는 `FmtErrorfWC`의 `pre`) | 새 계약. `%d`(int 상자, `tw` = `type:int`) + `%w`(errorString). 예산 `fs + 20 + msg + 8192` | `rt_errorf_dw` | `lu_reject_toobig_main`(`luFmtTooBig`), `lu_reject_misaligned_main`(`luFmtMis`) |
| `ConvT64C` | rax ≠ 0, 상자 내용 없음 | `BoxIn`(정적 표 `staticuint64s + 8v` 또는 힙 8바이트 = v), `StaticBox v`(읽기 전용) 보존, 힙 소비 `hb.length` | `rt_convT64`: bump 힙 8바이트에 v를 저장(이전 모델은 rax = 1만) | ListU64 거부 둘 |
| `ValidateBitlistErrC` | 메시지를 힙 `ErrStr`로 새로 꺼냄. 모든 `F` | 사전조건에 rodata 메시지 셋 `vblRO`(`go_string._+33605/13272/5743`), 결론에서 보존. 힙에서는 16바이트 `ErrObj`와 `%d` 메시지 `hm`만. `F`는 `⋆`로 `vblRO`와 분리 | `rt_validate_bitlist_err`(힙 경우, `hm = msg = []`) | `bl_marshal_reject_main`, `bl_reject_invalid_main` |

정리 전제의 변화(강화, 보고서 5절):
- ListU64 거부 둘: 전제 `StaticBox v` 조각 추가, 예산 `msg + 8268` → `msg + 8276`(toobig)·`msg + 8288`(misaligned), `fs` 인수 대신 상수.
- BitL 인코더 거부: 전제 `vblRO` 조각 추가.
- BitVec 디코더 거부: 결론·전제 변화 없음(메시지는 이미 전제의 rodata `vbvFmt`였다).

링크 검사로 고정한 상수(`link/check.py`):
- (g) `vblMsgE`·`vblMsgZ`·`vblMsgB`, `luFmtTooBig`·`luFmtMis`(FMTLEN은 비었다).
- (h) `luTW` = `type__+49184`의 abi.Type이 Size_ 8, Kind_ 2(int). itab+8이 가리키는 abi.Type이 Kind_ 22(포인터). `runtime.staticuint64s`가 uint64 0..255의 2048바이트.

여전히 신뢰 항목(형식 전제 밖):
- Go의 실제 할당량이 예산 안이다. 호출 중 GC가 없다.
- `VblMsg`는 어느 입력이 어느 메시지인지 말하지 않는다(셋 중 하나 또는 `%d`).
- 오류 결과 객체(fmt가 만든 `*wrapError` 등)는 결론에 없다(rax ≠ 0만).
- 증인의 전역 오류 값(`ssz.Err*`)은 Go 값 검사(goval) 밖이다.
