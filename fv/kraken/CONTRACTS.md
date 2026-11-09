# CONTRACTS: 피호출자와 전역의 처리 (Kraken 가설 형식)

대상: 9개 타입의 SizeSSZ, MarshalSSZTo, UnmarshalSSZ와 `ssz.ValidateBitvector`.
정의는 `lean/Fk/Contracts.lean`, `lean/Fk/FunSpecs.lean`, `lean/Fk/Vbl.lean`(ValidateBitlist), `lean/Fk/Vbv.lean`(ValidateBitvector 명세)에 있다.
변경 이력은 `HISTORY.md`에 있다.

분류:

- **(a) 증명 대상**: 기계어를 Kraken 의미론으로 실행해서 증명한다.
- **(b) 계약**: 정리의 가설이다. 모든 기계 상태, 반환 주소, 프레임 `F`에 대해 양화한다.
- **(c) 사전조건 아래 제외**: 정리의 전제가 그 경로를 막는다. 막는다는 사실은 증명한다.

## 1. 피호출자

| 피호출자 | 호출하는 함수(경로) | 분류 | 형식 | 모델 | 증인 |
| --- | --- | --- | --- | --- | --- |
| `runtime.makeslice` | FixedVec·ListU64·Checkpoint·AttestationData UnmarshalSSZ, ListC.UnmarshalSSZ(원소 포인터 배열) | (b) | `MakesliceC` | `bump_makeslice`(esz 8), `bump_makeslice1`(esz 1) | `lu_accept_runs`, `WitCp`, `WitAd`, `WitLcA*` |
| `runtime.memmove` | FixedVec·Checkpoint·AttestationData·BitL의 Unmarshal·Marshal | (b) | `MemmoveC` | `rt_memmove` | `WitCp`, `WitAd`, `WitCpM`, `WitAdM`, `WitBl1/257`, `WitBlM1/257`, `WitFvM`, `WitFvMR`, `WitCpMR` |
| `runtime.growslice` | 모든 MarshalSSZTo(용량 부족), BitL.UnmarshalSSZ(`append([]byte{}, buf[4:]...)`) | (b) | `GrowsliceC` | `rt_growslice`(esz 1) | `growslice_call_runs`, `WitBl1/257`, `WitLuG` |
| `runtime.newobject` | Nested·AttestationData·ListC UnmarshalSSZ, ListC 오류 객체 셋, `ssz.ValidateBitvector` 오류 객체 | (b) | `NewobjectC` | `bump_newobject16/24/32` | `WitNe0/1/16`(24), `WitLcA*`(24), `WitAd`(32), `WitLcZ/P/T`(16), `WitBvR`(16) |
| `runtime.convT64` | ListU64.UnmarshalSSZ(정렬, 초과), ListC.UnmarshalSSZ(정렬, 원소 수) | (b) | `ConvT64C` | `rt_convT64` | `WitLuTb`, `WitLuMa`. ListC의 두 경로는 정리가 없다 |
| `fmt.errorf`, 인수 0개 | ListC.UnmarshalSSZ(오프셋 오류 zero, past, tail) | (b) | `FmtErrorfNilC` | `rt_errorf_nil` | `WitLcZ/P/T` |
| `fmt.errorf`, `%w` | BitVec 디코더 `"J: %w"`, BitL 디코더·인코더 `"B: %w"` | (b) | `FmtErrorfWC` | `rt_errorf_w` | `WitBvR`, `WitBlR`, `WitBlRI` |
| `fmt.errorf`, `%d %w` | ListU64.UnmarshalSSZ(정렬, 초과) | (b) | `FmtErrorfDWC` | `rt_errorf_dw` | `WitLuTb`, `WitLuMa` |
| `fmt.errorf`, `%d %d` | ListC.UnmarshalSSZ 원소 오프셋 순서(`lc_reject_offset_order_main`) | (b) | `FmtErrorfDDC` | `rt_errorf_dd` | `WitLcO` |
| `ssz.ValidateBitlist` | BitL.UnmarshalSSZ, BitL.MarshalSSZTo | (b) | `ValidateBitlistC`(유효), `ValidateBitlistErrC`(무효) | `rt_validate_bitlist`, `rt_validate_bitlist_err`(`Fk/RtVbl.S`) | `WitBl1/257`, `WitBlM1/257`, `WitBlR`, `WitBlRI` |
| `ssz.ValidateBitvector` | BitVec 디코더·인코더 | (a) 함수 명세 | `VbvAccC`, `VbvPadC` | 정리에서 유도(`vbv_acc_holds`, `vbv_pad_holds`) | `WitBv`, `WitBvM`, `WitBvR` |
| `target.Scalars.UnmarshalSSZ` | Nested.UnmarshalSSZ | (a) 함수 명세 | `ScUAccC` | `sc_uacc_holds` | `WitNe*` |
| `target.ListU64.UnmarshalSSZ` | Nested.UnmarshalSSZ, ListC.UnmarshalSSZ(원소마다) | (a) 함수 명세 | `LuUAccC` | `lu_uacc_holds`(`MakesliceC` 필요) | `WitNe*`, `WitLcA*` |
| `runtime.newobject` 뒤 nil 분기 | ListU64 거부(`fmt.errorf`가 nil을 돌려준 경우) | (c) | `FmtErrorfDWC`의 rax ≠ 0이 막는다 | | |
| `runtime.gcWriteBarrier1/2` | 모든 디코더 | (c) | 전제 `runtime.writeBarrier` = 0. 플래그를 읽고 건너뜀을 증명한다 | | |
| `runtime.morestack_noctxt.abi0` | 프레임이 있는 모든 함수 | (c) | 전제 `g.stackguard0`(r14 + 16) < rsp. `jbe`가 안 갈림을 증명한다 | | |
| `runtime.panicBounds` | FixedVec·ListU64 UnmarshalSSZ 루프 | (a) | 경계 검사가 안 갈림을 한 바퀴마다 증명한다(`lu_iter`, `fv_iter`) | | |

`joint_models`(`Fk/Regress.lean`)는 계약 11개를 한 Host·한 힙에서 함께 만족한다(수정 3에서 `FmtErrorfDDC` 추가).
`tools/RegressFix2.lean`은 정리가 쓰는 형식·자원 조합으로 그것을 다시 적용한다.

## 2. 계약별 조건

모든 계약은 Go 1.26.3 ABIInternal(amd64) 호출을 가정한다.
반환 주소는 rsp에 있다.
`S`는 반환 슬롯 아래의 scratch 바이트 수다.
spill은 반환 슬롯 바로 위의 레지스터 인수 칸이다. 피호출자가 쓸 수 있다.

| 계약 | 인수 조건 | 자원 예산 | 스택 창 | 보존과 결론 |
| --- | --- | --- | --- | --- |
| `MakesliceC Heap ty esz S` | rax = ty, `len ≤ cap = cnt`, `cnt < 2^63` | `esz·cnt ≤ avail`, `esz·cnt ≤ maxAlloc` | scratch S, spill 24 | rsp + 8, r14, rbp, `F`. 0으로 채운 `esz·cnt` 바이트 블록을 `Heap`에서 떼어 낸다 |
| `MemmoveC S` | rcx = n, 원천·목적 n바이트, 서로소 | 없음 | scratch S, spill 없음(asm `$0-24`) | rsp + 8, r14, rbp, 원천, `F`. 목적 = 원천 |
| `GrowsliceC Heap ty esz S` | `0 < esz`, rsi = ty, `num ≤ newLen`, `oldLen = newLen − num ≤ oldCap < newLen` | `nc = nextSliceCap newLen oldCap`(Go `nextslicecap`), `2·esz·nc + 8192 ≤ avail ≤ maxAlloc = 2^48` | scratch S, spill 40 | rsp + 8, r14, rbp, rbx = newLen, 옛 블록, `F`. `nc ≤ newCap`, 새 블록 = `old ++ tail`, `avail' + esz·newCap ≤ avail` |
| `NewobjectC Heap ty sz S` | rax = ty | `sz ≤ avail` | scratch S, spill 8 | rsp + 8, r14, rbp, `F`. 0으로 채운 `sz`바이트 블록 |
| `ConvT64C Heap S` | 모든 v. 사전조건 `StaticBox v`(v < 256이면 포함된 ELF 표 `Fk.Data.staticuint64s`의 8v부터 8바이트, 읽기 전용; `staticBox_of_lt`로 = v) | `8 ≤ avail`. 결론 `avail' + hb.length ≤ avail ≤ avail' + 8` | scratch S, spill 8 | rsp + 8, r14, `StaticBox v`, `F`. `BoxIn rax v hb`(정적 표 또는 힙 8바이트 = v)와 `Eq (hb.At rax)` |
| `FmtErrorfNilC S` | rdi = 0, 형식에 `%` 없음, 형식 바이트 조각 | 할당 없음 | scratch S, spill 40 | rsp + 8, r14, 형식, `F`. rax = 0 |
| `FmtErrorfWC Heap fs RO MsgIn S` | 형식 `fs` 고정(`bvFmtJ`, `blFmtB`), rdi = rsi = 1, 인수 배열 `ity ++ e`, `ErrObj e sp msg`, `Eq (hm.At sp)`, 읽기 전용 `RO`, `MsgIn sp msg hm` | `fs + msg + 8192 ≤ avail`. 결론 `avail' ≤ avail` | scratch S, spill 40 | rsp + 8, r14, 형식, 인수, `ity`, 오류 객체, `hm`, `RO`, `F`. rax ≠ 0 |
| `FmtErrorfDWC Heap fs tw S` | 형식 `fs` 고정(`luFmtTooBig`, `luFmtMis`), rdi = rsi = 2, 인수 배열 `tw ++ bx ++ ity ++ e`(tw = `Fk.Data.intType_addr`, `type:int`), `BoxIn bx v hb`, `StaticBox v`, `Eq (hb.At bx)`, `ErrStr e sp msg` | `fs + 20 + msg + 8192 ≤ avail` | scratch S, spill 40 | 위와 같다. 상자 자원 포함. rax ≠ 0 |
| `FmtErrorfDDC Heap fs tw S` | 형식 `fs` 고정(`lcFmtOrder`), rdi = rsi = 2, 인수 배열 `tw ++ bx1 ++ tw ++ bx2`(tw = `Fk.Data.uint64Type_addr`), `BoxIn` 둘, `StaticBox v1`, `StaticBox v2`, 상자 바이트 둘 | `fs + 40 + 8192 ≤ avail` | scratch S, spill 40 | 위와 같다. 상자 자원 포함. rax ≠ 0 |
| `ValidateBitlistC S` | rbx = len(buf), rdi = 2048, buf 조각, `blValid buf` | 할당 없음 | scratch S, spill 32 | rsp + 8, r14, rbp, buf, `F`. rax = 0 |
| `ValidateBitlistErrC Heap S` | 위와 같다, `¬ blValid buf`. 사전조건에 rodata 메시지 셋 `vblRO`(`go_string._+33605/13272/5743`) | `8192 ≤ avail`. 결론 `avail' + 16 + hm.length ≤ avail ≤ avail' + 8192` | scratch S, spill 32 | rsp + 8, r14, rbp, buf, `vblRO`, `F`. rax = errorString itab, 새 `ErrObj rbx sp msg`(16바이트)와 `Eq (hm.At sp)`, `VblMsg sp msg hm`(rodata 셋 중 하나이고 hm = [], 또는 `%d` 힙 메시지 hm = msg ≤ 128) |

`blValid`는 EthLib `unpackDelimited (some 2048)`가 받는다는 뜻이다.
ValidateBitlist의 가장 긴 메시지는 82바이트다(고정 43, int 19자리, uint64 20자리). 그래서 msg ≤ 128이다.

링크 검사로 고정한 상수(`link/check.py`):

- (g) `vbvFmt`, `bvFmtJ`, `blFmtB`, `vblMsgE`·`vblMsgZ`·`vblMsgB`, `luFmtTooBig`·`luFmtMis`, `lcFmtZero`, `lcFmtShort`.
- (h) `luTW` = `type__+49184`의 abi.Type이 Size_ 8, Kind_ 2(int). itab+8이 가리키는 abi.Type이 Kind_ 22(포인터). `runtime.staticuint64s`가 uint64 0..255의 2048바이트.

## 3. 추상 모델과 Go 정교화

두 종류의 증명을 구분한다.

- **추상 모델 증명.** `rt_*`, `bump_*` 정리는 Kraken 의미론 위의 작은 어셈블리가 계약을 만족함을 보인다.
  계약이 모순이 아니고 여러 계약을 한 Host·한 힙에서 함께 만족할 수 있다는 근거다.
- **Go 정교화.** Go 1.26.3 런타임의 실제 기계어가 계약을 만족한다는 증명이다. 없다.
  모든 계약 호출은 실제 Go 실행에 대해 신뢰 항목이다.

형식 전제 밖의 신뢰 항목:

| 계약 | 신뢰 항목 | 이유 |
| --- | --- | --- |
| `FmtErrorfWC`, `FmtErrorfDWC`, `FmtErrorfDDC` | Go의 실제 할당량(printer 객체, 결과 문자열, `*fmt.wrapError` 32바이트)이 예산 안이다. 호출 중 GC가 없다. 결과 객체는 결론에 없다(rax ≠ 0만) | fmt의 할당 경로와 sync.Pool을 모델하지 않았다. 예산 값은 코드를 읽은 결과다 |
| `FmtErrorfNilC` | 형식에 `%`가 없으면 할당 없이 nil을 돌려준다(Go 1.26.3 `fmt/errors.go`를 읽은 결과) | fmt 내부 코드를 증명하지 않았다 |
| `ValidateBitlistC`, `ValidateBitlistErrC` | 수용 집합 = EthLib 규칙. 무효 입력에서 rax = errorString itab. `VblMsg`는 어느 입력이 어느 메시지인지 말하지 않는다 | Kraken이 `bsr`를 파싱하지 못한다 |
| `MakesliceC`, `NewobjectC`, `GrowsliceC`, `ConvT64C` | 타입 기술자를 읽지 않는다. 할당 중 GC가 없다. 할당기 실패는 정리 밖이다 | 할당기와 GC 모델이 없다 |
| `MemmoveC` | 겹치지 않는 범위만 다룬다 | 호출자의 `⋆`가 겹침을 배제한다. Go memmove는 겹침도 허용한다 |
| 모든 오류 증인 | 전역 오류 값(`ssz.Err*`)과 타입 기술자 내용은 Go 값 검사 밖이다 | goval이 읽지 않는다 |

## 4. 전역과 런타임 상태

| 항목 | 처리 | 근거 |
| --- | --- | --- |
| `ssz.Err*`(두 단어) | 레이블 주소의 분리 조각 + 값 전제(e0, e1) | 주소는 `link/check.py` (b)가 ELF `.symtab`과 대조 |
| `ssz.ErrX`의 itab + 8 | 거부 경로가 `*(e0 + 8)`을 읽는다. 전제: e0 ≠ 0, 그 8바이트 조각 | 패키지 초기화 뒤 사실(전제) |
| `runtime.writeBarrier` | 4바이트 = 0 전제. 계약 호출 동안 `F`에 있으므로 바뀌지 않는다고 가정한다 | GC가 할당 중 표시 단계에 들어가면 거짓이다 |
| 스택 가드 | 1절 (c). 피호출자의 스택 증가는 계약 밖이다. scratch `S`가 충분하다고 가정한다 | |
| X15 = 0 (Go ABI) | 거부 경로는 가정하지 않는다(`movups %xmm15` 저장은 임의 값 저장으로 증명). ListC 빈 리스트 수용만 전제로 둔다 | Go ABIInternal(amd64)이 보장 |
| 레이블 신선성 | 정리의 전제 `LabelsFresh`. 실제 배치(`all.S`)에서는 `link/check.py` (c)가 검사한다. 구체 Host에서는 Lean 정리(`Fk.Witness.hf5`, `hf198`) | |
| spill 칸 | 정리의 전제가 그 자리를 별도 조각으로 받는다(ListU64 rsp − 136, FixedVec·BitVec rsp − 32, Checkpoint rsp − 40, AttestationData rsp − 48, ListC rsp − 224, Nested rsp − 96, BitL rsp − 120) | |

## 5. 계약을 가설로 두는 방식

계약은 정리의 **가설**이다. 모든 상태·반환 주소·프레임에 대해 양화한다.
호출 지점에서 `eventually_trans`로 계약의 사후조건을 받고, 그것을 만족하는 임의의 상태에서 증명을 잇는다.

- 색인된 havoc 값이 없다(1a 발견 7). 같은 계약을 두 번 부르면 같은 가설을 다른 상태에 적용한다.
- 결과가 경로를 고르면 사후조건의 사실로 분기를 정한다. 예: `FmtErrorfDWC`의 rax ≠ 0이 `test %rax,%rax; jne`의 방향을 정한다. 사후조건이 그 사실을 주지 않으면 두 경로를 모두 증명한다.
- 남는 위험은 계약 자체의 모순이다. 형식은 비공허성의 근거가 아니다. 모델과 증인만이 근거다.

## 6. 정리의 전제가 실제 Go 호출자에서 성립하는가

| 전제 | Go 호출자 |
| --- | --- |
| 인수 레지스터(rax = 수신자, rbx/rcx/rdi = 슬라이스) | ABIInternal이 보장 |
| 수신자 ≠ nil | 보장하지 않는다. nil 수신자는 Go에서 패닉(`test %al,(%rax)`). 분리 조각이 있으면 그 주소는 매핑된 것으로 본다(Kraken `Effects.All`은 접근 권한을 검사하지 않는다) |
| 입력·수신자·스택·출력의 서로소(`⋆`) | 보통의 Go 값에서 성립. 별칭(수신자 안의 바이트를 입력으로)은 배제한다 |
| 스택 가드, 쓰기 장벽 0 | 빠른 경로 전제. 일반 호출의 보장이 아니다 |
| bool 바이트 ∈ {0, 1}, 슬라이스 len ≤ cap < 2^63, 객체 크기·정렬·겹침 | Go 값의 불변식. 주 정리는 더 넓은 상태를 허용할 수 있다. 증인은 Go 값이어야 한다: `lean/tools/wit/goval.py`가 `layout.json`으로 검사한다 |
| 힙 여유(`avail`) | 할당기가 실패하면 Go는 정상 복귀하지 않는다. 정리는 성공 경우만 말한다 |
