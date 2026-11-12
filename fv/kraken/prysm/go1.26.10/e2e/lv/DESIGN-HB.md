# DESIGN-HB: `HistoricalBatch.UnmarshalSSZ` 손 증명 설계 (T2 이식)

이 파일은 증명 전에 커밋한다. 계획이다. 증명 가능성을 주장하지 않는다.
정리 문장은 `lean/E2eHb/StmtHb.lean`에 있다.
목적은 T2(`SyncCommittee`) 증명의 재사용 양을 재는 것이다.

## 1. 입력

| 항목 | 값 |
| --- | --- |
| Go 소스 | `prysm/_generated/mainnet/phase0.ssz.go` 2693–2729행 |
| `.S`와 데이터 | `lv/link-hb/norm`, `lv/link-hb/data` (`gen/e2e/hblink.py`, `link/conv.py --norm`, `link/check.py` `PASS all`, 묶음 `66e6154a…`) |
| 지시어 수 | 182줄(0부터 센다, 레이블 포함). 명령어 164개 |
| 수신자 배치 | `prysm/ir/ir-mainnet.json` `go_fields`: native 구조체, 크기 48. `BlockRoots` 0, `StateRoots` 24 (ptr, len, cap) |
| ELF | T2와 같다(`c6403c02…911e`). objdump sha256 `580b0da9…`가 `build-ids.txt`와 같다 |

## 2. 경로

| 경로 | Go 조건 | 반환 | 지시어 | 목표 |
| --- | --- | --- | --- | --- |
| 크기 거부 | `len ≠ 524288` | `ssz.ErrSize` | 2–10, 30–35 | K 목표 `hb_reject_size_stmt` |
| 수용 | `len = 524288` | nil | 2–29, 루프 1(40–84, 36–39), 86–103, 루프 2(108–153, 104–107), 155–159 | K 목표 `hb_accept_stmt` |
| morestack, 쓰기 장벽 켜짐 | — | — | 170–181, 22–25 등 | N, 범위 밖(전제 `guard < rsp`, `writeBarrier = 0`) |

거부 경로는 하나다. `panicBounds` 넷은 오류 반환이 아니다. 매 바퀴 안 갈림을 증명한다.

## 3. 피호출자 표

| 지시어 | 대상 | 처리 | 꼴 |
| --- | --- | --- | --- |
| 16, 89 | `runtime.makeslice` | 계약 | `MakesliceC Heap lvSliceType_addr 24 S` (cnt 8192) |
| 57, 125 | `runtime.makeslice` | 계약 | `MakesliceC Heap e2eU8Type_addr 1 S` (len 0, cap 32) |
| 63, 132 | `runtime.memmove` | 계약 | `MemmoveC S` (n = 32) |
| 23, 80, 97, 149 | `runtime.gcWriteBarrier2` | 제외 | 전제 `writeBarrier = 0` |
| 161, 164, 166, 168 | `runtime.panicBounds` | (a) 안 갈림 증명 | 아래 4절 |
| 175 | `runtime.morestack_noctxt.abi0` | 제외 | 전제 `guard < rsp` |

계약 인스턴스는 T2와 같은 셋이다. 새 계약 꼴과 새 인스턴스 값이 없다.
`lvSliceType`의 피연산자(`type__+337600`)는 T2와 같다. `hblink.py data`가 같음을 단언한다.
그래서 `E2eList.Data.lvSliceType_addr`를 그대로 쓴다. 새 `Data` 모듈이 없다.

## 4. T2와 다른 점

| 항목 | T2 | HB | 증명에 주는 영향 |
| --- | --- | --- | --- |
| 틀 | `sub $0x30` | `sub $0x38` | 거부 증명의 상수 하나 |
| 지역 칸 | 3개(i, 3i, 포인터) | 4개(i + 1, 32i, i, 포인터) | 불변식 칸 하나 더 |
| 루프 | 512회, 1개 | 8192회, 2개 | 한 바퀴 증명 둘 |
| 원소 | 48바이트 | 32바이트 | 상수 |
| 꼬리 필드 | AggregatePubkey(48) | 없음 | `sc_agg_seg`를 쓰지 않는다 |
| 색인 계산 | `lea (%rdx,%rdx,2)`, `shl $4` | `shl $5`, `lea 0x1(%rsi)`, `shl $5` | 단계 열이 다르다 |
| 경계 검사 | 바퀴마다 1개(`jae`) | 바퀴마다 2개(`jb` 넘침, `jae` len) | `jb` 안 갈림이 새로 필요하다 |
| 루프 2 원천 | — | `lea 0x40000(%rbx)` | 지시어 하나 더 |
| 수신자 | protoc(크기 88, `state` 0) | native(크기 48) | 필드 오프셋이 다르다 |
| 마지막 호출 | 지시어 100 | 지시어 132 | 반환 칸 값 `k + 133` |
| 힙 | 36912 | 917504 | 상수 |

루프 1과 루프 2의 단계 열도 같지 않다. `nop` 자리가 다르다(48, 74 / 116, 136).
그래서 한 바퀴 정리는 루프마다 따로 쓴다. 지시어 번호를 매개변수로 두지 않는다.

## 5. 루프 불변식

루프 1의 머리는 `L_a0`(지시어 40)다. `sp` = 진입 rsp − 64다.
불변식(i ≤ 8192):

- 레지스터: rax = i, rsp = sp, rbp, r14 = 진입 값.
- 칸: sp + 72 = 수신자, sp + 80 = buf. 지역 넷(sp + 24, 32, 40, 48)은 값을 정하지 않는다.
- 수신자: `+0` = A1, `+8` = 8192(경계 검사가 매 바퀴 읽는다).
- 배열 A1: `lvHdrs 32 ps ++ zz (24·(8192 − i))`.
- 원소: `lvElems ps (brs.take i)`.
- 힙: `Heap (avail − 32·i)`(루프 진입 전 값에서).

루프 2는 `L_1c0`(108)에서 같은 꼴이다. 수신자 `+24` = A2, `+32` = 8192, 입력은 buf + 262144다.
한 바퀴 증명은 T2 `sc_iter`의 순서를 따른다. 귀납은 T2 `sc_loop`의 꼴(`i + j = 8192`)이다.

## 6. 명세 쪽

- 손 `Desc`(`E2eHb/Defs.lean`): `container [block_roots: vector (byteVector 32) 8192, state_roots: 같음]`.
- 한계: 이 작업에서는 생산자 `Desc` 파일을 손 `Desc`보다 먼저 출력했다. T2와 달리 독립성이 약하다.
- `PHb`: 32바이트 벡터 8192개 둘. `phbEnc g` = `g.brs.flatten ++ g.srs.flatten`.
- 명세 다리: T2 `ScSpec`의 순서를 따른다. 원소 폭에 묶이지 않은 보조정리는 가져온다.
- 생산자 `Desc`: `lv/desc/prysm_v1alpha1.HistoricalBatch.desc.json`(sha256 `05642f50…`, 검사기 기록과 같다).
- `lvdescterm.py`로 렌더해 `E2eHb/HbSpecChecker.lean`을 만든다.

## 7. 증인 계획

- HB는 고정 크기다. 증인은 모든 입력에 대한 정리 하나와 구체 입력 셋(0, 대표, 0xff)이다.
- Host: 데이터 레이블, `HbUnmarshal`, `E2eList.BumpAllocT`, `RtCopy`. T2의 모델을 가져온다.
- `bump_makeslice_t1`, `bump_makeslice_t24`는 같은 형식 단어를 쓴다. 그래서 그대로 맞는다.

## 8. 위험

- 8192회 루프의 귀납은 T2와 같은 방식이다. 펼치지 않는다.
- 증인 메모리는 약 1.45 MB다. `simp` 정렬 비용이 T2보다 클 수 있다. 측정 전에는 모른다.
- `jb` 안 갈림 증명은 T2에 없던 단계다. `shl`의 `toNat` 식이 필요하다.
