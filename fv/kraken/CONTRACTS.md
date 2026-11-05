# CONTRACTS: 피호출자와 전역의 처리 (Kraken 가설 형식)

대상: 1a 9개 함수(Scalars, FixedVec, ListU64의 SizeSSZ, MarshalSSZTo, UnmarshalSSZ)와 1b 18개 함수(BitVec, Nested, ListC, BitL, Checkpoint, AttestationData). 정의는 `lean/Fk/Contracts.lean`, `lean/Fk/FunSpecs.lean`, `lean/Fk/BlAccept.lean`. 작성 2026-11-05.

분류:
- **(a) 증명 대상**: 기계어를 Kraken 의미론으로 실행해서 증명한다.
- **(b) 계약**: 정리의 가설이다. 모든 기계 상태, 반환 주소, 프레임 `F`에 대해 양화한다.
- **(c) 사전조건 아래 제외**: 정리의 전제가 그 경로를 막는다. 막는다는 사실은 증명한다.

## 1. 피호출자

| 피호출자 | 호출하는 함수(경로) | 분류 | Kraken 형식 | 비공허성 |
| --- | --- | --- | --- | --- |
| `runtime.makeslice` | ListU64.UnmarshalSSZ(수용), FixedVec.UnmarshalSSZ(수용) | (b) | `MakesliceC Heap ty esz S`: 사전조건에 런타임 힙 조각 `Heap avail`, 타입 인수 `rax = ty`, `len = cap = cnt`, `esz·cnt ≤ avail`. 사후조건: 반환 주소로 복귀, rsp + 8, 0으로 채운 `esz·cnt` 바이트 블록을 `Heap`에서 떼어냄, `Heap (avail − esz·cnt)`, `F` 보존 | **있음.** `bump_makeslice`(범프 할당기가 계약을 만족, Kraken 의미론 위 증명). `lu_accept_runs`(구체 Host에서 `lu_accept_main`의 모든 전제를 증명, n ≤ 16) |
| `runtime.memmove` | FixedVec.UnmarshalSSZ(수용), FixedVec.MarshalSSZTo(빠른 경로, 거부) | (b) | `MemmoveC S`: 서로소인 원천·목적 조각(n 바이트), 복귀 후 목적 = 원천, 원천과 `F` 보존. 겹치는 범위는 계약 밖(호출자의 `⋆`가 배제) | 없음(남은 일). 바이트 복사 루프 구현으로 같은 방식의 증인을 만들 수 있다 |
| `runtime.growslice` | 모든 MarshalSSZTo(용량 부족 경로) | (b) | `GrowsliceC Heap ty esz S`: `rsi = ty`, `num ≤ newLen`, 옛 원소 `old`(esz·(newLen − num) 바이트). 사후조건: rsp + 8, rbp 보존, rbx = newLen, newLen ≤ newCap < 2^63, 새 블록 = `old ++ tail`(길이 esz·newCap), 옛 블록과 `F` 보존, 힙은 `∃ avail'` | 없음. 한 지점만 증명에 썼다(`lum_grow_site`) |
| `runtime.convT64` | ListU64.UnmarshalSSZ(거부 3, 4) | (b) | `ConvT64C Heap S`: 복귀, rsp + 8, `F` 보존, 힙은 `∃ avail'`. 결과 값은 쓰지 않는다(인수 배열에 넘길 뿐) | 없음 |
| `fmt.errorf` (`fmt.Errorf`) | ListU64.UnmarshalSSZ(거부 3, 4) | (b) | `FmtErrorfC Heap S`: 복귀, rsp + 8, **rax ≠ 0**(nil이 아닌 오류), `F` 보존. 어떤 오류를 감싸는지(`%w`)는 모델하지 않는다 | 없음 |
| `runtime.newobject` | ListU64.UnmarshalSSZ(거부 3, 4, `fmt.errorf`가 nil을 돌려준 경우) | (c) | `FmtErrorfC`의 rax ≠ 0이 이 경로를 막는다(`jne` 분기 정리) | 해당 없음 |
| `runtime.gcWriteBarrier2` | FixedVec·ListU64 UnmarshalSSZ(수용) | (c) | 전제: `runtime.writeBarrier` 4바이트 = 0. 코드가 플래그를 읽고 `je`로 건너뜀을 증명한다 | 해당 없음 |
| `runtime.morestack_noctxt.abi0` | 프레임이 있는 모든 함수 | (c) | 전제: `g.stackguard0`(r14 + 16) < rsp(또는 rsp − 8). `jbe`가 안 갈림을 증명한다 | 해당 없음 |
| `runtime.panicBounds` | FixedVec·ListU64 UnmarshalSSZ 루프 | (a) | 경계 검사 분기가 안 갈림을 루프 한 바퀴마다 증명한다(`lu_iter`, `fv_iter`) | 해당 없음 |

### 1b에서 더한 것

| 피호출자 | 호출하는 함수(경로) | 분류 | Kraken 형식 | 비공허성 |
| --- | --- | --- | --- | --- |
| `runtime.newobject` | Nested.UnmarshalSSZ(S, L 할당), AttestationData.UnmarshalSSZ(Source, Target) | (b) | `NewobjectC Heap ty sz S`: 사전조건 `rax = ty`, `sz ≤ avail`. 사후조건: 복귀, rsp + 8, r14 보존, 0으로 채운 `sz`바이트 블록을 `Heap`에서 떼어냄, `F` 보존 | 없음. `makeslice`와 같은 범프 할당기로 증인을 만들 수 있다(남은 일) |
| `runtime.makeslice`(byte, 0, 32) | Checkpoint·AttestationData UnmarshalSSZ | (b) | `MakesliceC`(len ≤ cap로 넓힘, c0f3396) | 1a와 같다(`bump_makeslice`). 이 호출 지점의 구체 Host 증인은 없다 |
| `runtime.memmove` | Checkpoint·AttestationData·BitL의 Unmarshal·Marshal | (b) | `MemmoveC S` | 없음 |
| `runtime.growslice` | BitL.UnmarshalSSZ(`append([]byte{}, buf[4:]...)`) | (b) | `GrowsliceC`, 옛 원소 `[]`(빈 슬라이스, 주소 `runtime.noptrbss`) | 없음 |
| `fmt.errorf` | ListC.UnmarshalSSZ(오프셋 오류 3경로) | (b) | `FmtErrorfC` | 없음 |
| `ssz.ValidateBitlist` | BitL.UnmarshalSSZ | (b) | `ValidateBitlistC S`: 복귀, rsp + 8, `F`와 바이트 보존, **rax = 0 ⟺ EthLib `unpackDelimited (some 2048)`이 받음**. 이 함수는 `bsr`이 있어 Kraken이 파싱하지 못한다. **bitlist의 핵심 검사가 이 계약 뒤에 있다** | 없음 |
| `target.Scalars.UnmarshalSSZ` | Nested.UnmarshalSSZ | (a) 함수 명세 | `ScUAccC`: 우리 쪽 정리 `sc_accept_main`에서 유도(`sc_uacc_holds`) | 증명됨(가설이 아니라 정리에서 나온다) |
| `target.ListU64.UnmarshalSSZ` | Nested.UnmarshalSSZ | (a) 함수 명세 | `LuUAccC Heap S`: `lu_accept_main`에서 유도(`lu_uacc_holds`, `MakesliceC` 필요) | 증명됨 |
| `runtime.gcWriteBarrier1/2` | 1b 디코더 전부 | (c) | 쓰기 장벽 0 전제. 플래그를 읽고 건너뜀을 증명한다(AttestationData는 6번) | 해당 없음 |
| `runtime.convT64` | ListC.UnmarshalSSZ(정렬 오류, 원소 수 초과) | (b) | `ConvT64C` | 그 두 경로는 증명하지 않았다 |

## 2. 전역과 런타임 상태

| 항목 | 처리 | 근거 |
| --- | --- | --- |
| `ssz.Err*`(두 단어) | 레이블 주소의 분리 조각 + 값 전제(e0, e1) | C5. 주소는 `link/check.py` (b)가 ELF `.symtab`과 대조 |
| `ssz.ErrX`의 itab + 8 | 거부 3, 4가 `*(e0 + 8)`을 읽는다. 전제: e0 ≠ 0, 그 8바이트 조각 | 패키지 초기화 뒤 사실(전제) |
| `runtime.writeBarrier` | 4바이트 = 0 전제. 계약 호출(`makeslice`) 동안 `F`에 있으므로 바뀌지 않는다고 가정한다 | GC가 할당 중 표시 단계에 들어가면 바뀔 수 있다(astra 지적). 조건 C19의 남은 항목 |
| 스택 가드 | 위 (c) | |
| X15 = 0 (Go ABI) | 가정하지 않는다. `movups %xmm15` 저장은 임의 값 저장으로 증명한다 | 거부 3, 4 |
| 레이블 신선성 | 정리의 전제 `LabelsFresh`. 실제 배치(`all.S`)에서 성립함은 `link/check.py` (c)가 검사한다. 구체 Host 하나에서는 Lean 정리(`Fk.Witness.hf5`, `hf198`) | |

## 3. 1a 발견 7(havoc 색인)의 확인

1a는 계약을 기계 모델 안의 표(`rtOf H`)로 실행했다. 계약 결과는 색인된 havoc 값이었고, 그 값이 경로(분기)를 고르는 문제가 있었다.

Kraken에서는 계약이 정리의 **가설**이고, 모든 상태·반환 주소·프레임에 대해 양화한다. 호출 지점에서 `eventually_trans`로 계약의 사후조건을 받고, 사후조건을 만족하는 **임의의** 상태에서 증명을 이어 간다. 그래서:
- 색인이 없다. 같은 계약을 두 번 부르면 두 번 다 같은 가설을 다른 상태에 적용한다(ListU64 거부 3, 4: `convT64` 뒤 `fmt.errorf`, 같은 반환 슬롯).
- 결과가 경로를 고르는 경우는 사후조건의 사실로 분기를 정한다. `fmt.errorf`의 rax ≠ 0이 `test %rax,%rax; jne`의 방향을 정한다(`lu_reject_toobig_main`, `lu_reject_misaligned_main`의 `split` 단계). 사후조건이 그 사실을 주지 않으면 두 경로를 모두 증명해야 한다.
- 남는 위험은 계약 자체의 모순이다(이전 `hms`). 이것은 증인(`bump_makeslice`, `lu_accept_runs`)으로 검사한다. 증인이 없는 계약(memmove, growslice, convT64, fmt.errorf, newobject, ValidateBitlist)은 1절 표에 "없음"으로 적었다. 모두 `makeslice`와 같은 형식(힙 조각, 길이가 명시된 조각, 임의의 `F`)이다. 이전 `hms`의 모순(블록이 모든 주소를 덮음, `F`가 나머지 전부)은 이 형식에서 생기지 않는다. 블록이 `Heap` 조각에서 나오기 때문이다. 증인이 없으므로 "모순이 없다"는 증명이 아니라 형식에 근거한 판단이다(REPORT-1b C18).

## 4. 정리의 전제가 실제 Go 호출자에서 성립하는가

| 전제 | Go 호출자 |
| --- | --- |
| 인수 레지스터(rax = 수신자, rbx/rcx/rdi = 슬라이스) | ABIInternal이 보장 |
| 수신자 ≠ nil, 주소 0 아님 | 보장하지 않는다. nil 수신자는 Go에서 패닉(`test %al,(%rax)`). 분리 조각이 있으면 그 주소는 매핑된 것으로 본다(접근 권한은 Kraken `Effects.All`이 검사하지 않음, C19) |
| 입력·수신자·스택·출력의 서로소(`⋆`) | 보통의 Go 값에서 성립. 별칭(수신자 안의 바이트를 입력으로)은 배제한다 |
| 스택 가드, 쓰기 장벽 0 | 빠른 경로 전제. 일반 호출의 보장이 아니다 |
| `bool` 바이트 ∈ {0, 1}, 슬라이스 len ≤ cap < 2^63 | Go 값의 불변식 |
| 힙 여유(`avail`) | 런타임 할당기가 실패하면 Go는 정상 복귀하지 않는다. 정리는 성공 경우만 말한다 |
