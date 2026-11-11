# DESIGN-T3: `IndexedAttestation.UnmarshalSSZ` 손 증명 설계

이 파일은 증명 전에 커밋한다. 계획이다. 증명 가능성을 주장하지 않는다.
정리 문장은 `lean/E2eList/StmtIa.lean`에 있다. 목록은 `STATEMENTS-T3.md`에 있다.

## 1. 입력

| 항목 | 값 |
| --- | --- |
| Go 소스 | `prysm/_generated/mainnet/phase0.ssz.go` 2819–2864행 |
| `.S`와 데이터 | `lv/link-t3/norm`, `lv/link-t3/data` (`conv.py` LV-1 수정 뒤, `check.py` `PASS all`, 묶음 `393eade6…`) |
| 지시어 수 | 279줄(0부터 센다) |
| 수신자 배치 | `prysm/ir/ir-mainnet.json` `go_fields`: `state` 0, `AttestingIndices` 8 (ptr, len, cap), `Data` 32 (포인터), `Signature` 40 (ptr, len, cap), `unknownFields` 64 (24), `sizeCache` 88 (4), 크기 96 |
| AttestationData 객체 | 크기 96(`lvAdType.data`의 Size_ = 0x60, Kind = 25) |

## 2. 경로

| 경로 | Go 조건 | 반환 | 지시어 | 목표 |
| --- | --- | --- | --- | --- |
| P1 크기 거부 | `len < 228` | `ssz.ErrSize` | 2–10, 137–142 | K 목표 `ia_reject_size_stmt` |
| P2 오프셋 거부 | 첫 오프셋 ≠ 228 | `ssz.ErrInvalidVariableOffset` | 11–17, 131–136 | K 목표 `ia_reject_offset_stmt` |
| P4 정렬 거부 | `(len − 228) % 8 ≠ 0` | `fmt.Errorf("misaligned bytes: … %d … %w", len − 228, ssz.ErrIncorrectListSize)` | 18–26, 94–130 | K 목표 `ia_reject_misaligned_stmt` |
| P5 초과 거부 | `numElem > 2048` | `fmt.Errorf("ssz-max exceeded: … %d … %w", numElem, ssz.ErrListTooBig)` | 27–30, 57–93 | K 목표 `ia_reject_toobig_stmt` |
| P3 수용 | 위가 모두 아니고 위임이 받음 | nil | 31–56, 143–165 루프, 166–189, 217–260 | K 목표 `ia_accept_stmt` |
| P6 위임 오류 | `c.Data.UnmarshalSSZ`가 오류 | `fmt.Errorf("Data: %w", err)` | 190–216 | 도달하지 않음(아래) |
| morestack, 쓰기 장벽 켜짐 | — | — | 268–278, 46–49 등 | N, 범위 밖(전제 `guard < rsp − 48`, `writeBarrier = 0`) |

P4와 P5의 계약 꼴은 있다(3절). 그래서 둘 다 K 목표다. "계약 부재로 막힘"인 경로는 없다.

P6: 위임 호출의 입력은 항상 `buf[4:132]`, 128바이트다(지시어 182–186: rbx = buf + 4, rcx = 0x80).
`E2eAd.ad_e2e_accept_main`은 128바이트 입력 전부에서 rax = 0, rbx = 0을 준다. 내용에 대한 전제가 없다.
그래서 P3의 전제 아래에서 188–189의 `test %rax,%rax; je`는 항상 간다. P6은 도달하지 않는다.
이 사실은 따로 정리로 두지 않는다. `ia_accept_stmt`의 증명이 그 분기를 정하면서 보인다.
EthLib도 128바이트 `data`를 전부 받는다(`E2e.pad_spec_accepts_iff`). 그래서 P6에 해당하는 명세 거부는 없다.

## 3. 피호출자 표

| 지시어 | 대상 | 경로 | 처리 | 꼴 또는 정리 |
| --- | --- | --- | --- | --- |
| 39 | `runtime.makeslice` | P3 | 계약 | `MakesliceC Heap lvU64Type_addr 8 S` (len = cap = numElem ≤ 2048) |
| 47, 177, 231, 250 | `runtime.gcWriteBarrier2` | — | 제외 | 전제 `writeBarrier = 0` |
| 62 | `runtime.convT64` | P5 | 계약 | `ConvT64C Heap S`, v = numElem |
| 79 | `fmt.errorf` | P5 | 계약 | `FmtErrorfDWC Heap lvFmtTooBig e2eIntType_addr S` (형식 73바이트, rdi = rsi = 2) |
| 84 | `runtime.newobject` | P5 | 제외 | errorf가 nil일 때의 `errors.New`. DWC 결론 rax ≠ 0이 막는다 |
| 99 | `runtime.convT64` | P4 | 계약 | `ConvT64C Heap S`, v = len − 228 |
| 116 | `fmt.errorf` | P4 | 계약 | `FmtErrorfDWC Heap lvFmtMis e2eIntType_addr S` (형식 83바이트) |
| 121 | `runtime.newobject` | P4 | 제외 | 84와 같다 |
| 168 | `runtime.newobject` | P3 | 계약 | `NewobjectC Heap lvAdType_addr 96 S` (`c.Data = new(AttestationData)`) |
| 187 | `AttestationData.UnmarshalSSZ` | P3 | 증명된 정리 | `E2eAd.ad_e2e_accept_main` (기계어를 Host에 둔다. 4절) |
| 202 | `fmt.errorf` | P6 | 도달하지 않음 | 형식 `"Data: %w"`. `FmtErrorfWC` 꼴은 있으나 쓰지 않는다 |
| 207 | `runtime.newobject` | P6 | 도달하지 않음 | errorf nil 가지 |
| 223 | `runtime.makeslice` | P3 | 계약 | `MakesliceC Heap e2eU8Type_addr 1 S` (len 0, cap 96) |
| 240 | `runtime.memmove` | P3 | 계약 | `MemmoveC S`, n = 96, 원천 buf + 132 |
| 262 | `runtime.panicBounds` | P3 루프 | (a) 안 갈림 증명 | `c.AttestingIndices[i]`의 색인 검사 (163–164: `cmp %rdi,%r9; jb`, rdi = 수신자의 len) |
| 264 | `runtime.panicBounds` | P3 루프 | (a) 안 갈림 증명 | `sszSlice0[i*8:(1+i)*8]`의 low ≤ high 검사 (158–159) |
| 266 | `runtime.panicBounds` | P3 루프 | (a) 안 갈림 증명 | 같은 식의 high ≤ cap 검사 (154–155: `(i+1)*8 ≤ cap − 228`). 전제 `len ≤ cap`이 필요하다 |
| 273 | `runtime.morestack_noctxt.abi0` | — | 제외 | 전제 `guard + 48 < rsp` |

newobject 넷: 168(P3, Data 객체), 84·121(P5·P4, errorf nil 가지), 207(P6, errorf nil 가지). P3에 있는 것은 168뿐이다.
panicBounds 셋: 모두 P3의 원소 루프 안이다. 매 바퀴 안 갈림을 증명한다. 전제로 막지 않는다.

계약 인스턴스는 모두 기존 꼴이다. 새 값: `lvU64Type_addr`(esz 8), `lvAdType_addr`(sz 96), `lvFmtMis`, `lvFmtTooBig`.
DWC의 `tw`는 `E2e.Data.e2eIntType_addr`다. Epoch 거부의 `FmtErrorfDDC`와 같은 방식(같은 꼴, 새 형식과 형식 단어)이다.

## 4. AttestationData 호출 (`ad_e2e_accept_main`의 전제)

| 전제 | 호출 지점에서 |
| --- | --- |
| 코드 위치 | `AdUnmarshal`, `SlUnmarshal`, `CiUnmarshal`, `CpUnmarshal`, `EpUnmarshal`가 Host에 있다(문장의 `kA … kE`) |
| 진입 rsp | x − 184(우리 런타임 호출 반환 칸과 같은 자리) |
| 레지스터 | rax = 새 객체 `pd`, rbx = buf + 4, rcx = 128, rdi = cap − 4 |
| 수신자 칸 | 새 객체의 96바이트 0 블록을 8바이트 칸 여덟과 32바이트(R)로 나눈다 |
| 입력 | `in0 … troot`가 buf + 4 … buf + 100에 있다 |
| 스택 | 피호출자 넘침 칸 x − 176, x − 168, x − 152는 우리 spill 40바이트 안이다. 그 아래 전부(fp, l68, sp0–2, rslot, lo)는 우리 scratch `S = Sd + 224` 안이다 |
| 가드 | `guard + 224 < x − 184`, 곧 `guard + 408 < x` |
| 계약 | `MakesliceC u8 1 Sd`, `MemmoveC Sd`, `MakesliceC u8 1 (Sd + 96)`, `MemmoveC (Sd + 96)`, `NewobjectC adCpType_addr 72 (Sd + 96)`를 문장의 가설로 받는다 |
| 힙 | 240바이트 |

결과(rax = 0, rbx = 0, 객체 내용, `Heap (avail − 240)`)를 우리 사후조건에 그대로 옮긴다.

## 5. 원소 루프

루프 머리는 `L_28a`(지시어 147)다. 바퀴는 147–165와 143–146이다.
`[]uint64`의 백킹 배열은 연속 블록 하나다. 그래서 원소별 술어를 쓰지 않는다(`lvElems`도 쓰지 않는다).
불변식 `IaInv i`(`i ≤ n`, `n ≤ 2048`):

- 레지스터: rax = i, rdx = n, rcx = cap − 228(바이트), rbx = buf + 228, rsi = 수신자, rsp = x − 176.
- 배열 A: `ib.take (8·i) ++ replicate (8·(n − i)) 0`. Go 1.26.3 `lu_iter`의 꼴과 같다.
- 수신자: `+8` = A, `+16` = n(경계 검사가 매 바퀴 읽는다), `+24` = n.
- 입력 `ib`(8n바이트)와 나머지 프레임, `R`은 그대로다.

한 바퀴: (i+1)·8 ≤ cap − 228(266 안 갈림, 전제 `len ≤ cap`), i·8 ≤ (i+1)·8(264), 8바이트 읽기, i < 수신자 len(262), 8바이트 쓰기.
루프 끝: i = n에서 `jge`가 간다(148–149).
n = 0이면 바퀴가 없다. 이때 rbx 값은 buf(cap = 228일 때) 또는 buf + 228이다. 읽지 않는다.

## 6. 명세 쪽

- 손 `Desc`(`DefsIa.lean`): `container [attesting_indices: list (uint 8) 2048, data: E2e.prysmAdDesc, signature: byteVector 96]`.
- `PIa`: 지표 목록(길이 ≤ 2048, 필드 `hidx`), `E2e.PAd`, 96바이트 서명. `piaEnc` = iaOff ‖ padEnc ‖ sig ‖ u64Bytes.
- 정리(이후 단위): `ia_accept_spec_stmt`(T1·T2의 `spec_k` 꼴), 거부 명세 넷(P1, P2, P4, P5), `ia_reject_cases_stmt`.
- `Desc` = 생산자 `Desc`: 생산자 파일 `lv/desc/prysm_v1alpha1.IndexedAttestation.desc.json`(sha256 `91e4d752…`)을 렌더한다. `lvdescterm.py`는 `list`와 중첩 `container`를 이미 렌더한다. 이름만 다름을 보인다.
- 거부 완전성: `ia_reject_cases_stmt`는 순수 EthLib 문장이다. "EthLib가 거부하면 P1, P2, P4, P5의 조건 중 하나"를 말한다.
- 그 문장이 기계어의 거부 완전성이 되는 것은 네 거부 경로가 모두 K일 때뿐이다. P4나 P5가 N으로 남으면, 그 이름 대신 "P1·P2 조건 아래의 거부"만 주장한다. P6은 EthLib 쪽 거부가 없어서 완전성의 조건이 아니다.

## 7. 증인 계획

- 수용: n = 0(len 228), n = 1(len 236), n = 2048(len 16612).
- Host: `IaUnmarshal`, `AdUnmarshal`, `SlUnmarshal`, `CiUnmarshal`, `CpUnmarshal`, `EpUnmarshal`, makeslice 모델, newobject 모델, `RtCopy`.
- makeslice: 한 Host에 esz 8(`lvU64Type_addr`)과 esz 1(`e2eU8Type_addr`)이 함께 필요하다. `BumpAllocT`는 esz 24/1이다. 그래서 새 파일에 esz 8/1 분기 모델이 필요하다(`BumpAllocT`의 꼴, 형식 단어 비교 하나).
- newobject: 한 Host에 sz 96(`lvAdType_addr`)과 sz 72(`adCpType_addr`, AttestationData 안의 Checkpoint)가 함께 필요하다. 기존 모델(16/24/32, E2eAd의 72)은 하나의 크기다. 그래서 새 파일에 96/72 분기 모델이 필요하다.
- 거부 증인: P1, P2는 계약이 없다. P4, P5는 `rt_convT64`와 `rt_errorf_dw`(형식과 `tw`가 매개변수)를 쓴다.

## 8. 위험과 판단

- 스택 가드가 `lea -0x30(%rsp),%r12` 꼴이다. T-9가 이 꼴에서 커널 메모리 문제를 보였다. `E2eScal.lea_cmp_be_false`(`StackGuard.lean`)로 닫는다.
- 첫 오프셋 읽기는 32비트(`mov (%rbx),%edx`)다. 문장은 4바이트 목록 `off`와 `off ≠ iaOff`로 적는다.
- 슬라이스 포인터 계산(18–24: `neg`, `sar`, `and`)은 cap − 228의 부호에 따른다. 문장에 `cap < 2^63`을 둔다.
- `ad_e2e_accept_main`의 사후조건은 길다. 우리 사후조건은 그 객체 내용을 그대로 담는다.
- P4·P5의 `rbx` 반환값은 DWC 결론에 없다. 문장은 rax ≠ 0만 말한다(기존 거부 정리와 같다).
