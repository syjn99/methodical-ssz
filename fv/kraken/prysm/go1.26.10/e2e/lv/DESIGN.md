# DESIGN: LV 손 증명 설계 (T1 SyncAggregate, T2 SyncCommittee)

이 파일은 증명을 시작하기 전에 커밋한다.
정리 문장은 `STATEMENTS.md`와 `lean/E2eList/Stmt*.lean`에 있다.
이 파일은 계획이다. 증명 가능성을 주장하지 않는다.

## 1. 입력

| 항목 | 값 | 근거 |
| --- | --- | --- |
| 기준 커밋 | `6a78c591e8bcd698b7b9313b1c09cb25f3986911` | `SELECTION.md` |
| 대상 ELF sha256 | `c6403c02a110ffd6fe6d31a3c89cd395ac457b5d62e60e2e611b8ab9a8dd911e` | `prysm/go1.26.10/build-ids.txt` |
| `.S`와 데이터 | `lv/link/norm`, `lv/link/data` | `gen/e2e/lvlink.py`, `link/conv.py --norm`, `link/check.py` (`lv/link/RESULT`) |
| 수신자 배치 | `prysm/ir/ir-mainnet.json`의 `go_fields` | 두 타입 모두 크기 88 |
| 명세 | EthLib `deserialize`, 손 `Desc` (`lean/E2eList/Desc.lean`) | consensus-specs altair |
| 생산자 `Desc` | `lv/desc/*.desc.json` | sha256이 `gen/desc/results/main.result.json`의 기록과 같다 |

## 2. 그대로 쓰는 것

- 계약 꼴 `MakesliceC`, `MemmoveC` (`lean/Fk/Contracts.lean`). 새 계약 꼴은 없다.
- `E2e.Data.e2eU8Type_addr`, `E2e.Data.e2eErrSize_addr`. `lvlink.py`가 같은 피연산자임을 확인한다.
- Kraken 단계 전술: `kat`, `klabel`, `load_step`, `store_step_at`, `kunfold`, `ecancel`, `eaddr`.
- 거부 증명: `E2eScal.H4.dd_e2e_reject_size_main`의 본문. 지시어 번호만 바꾼다.
- 명세 다리: `Fv1.Transfer`의 `deserialize_enc`, `accepted_is_enc`. `DdSpec.lean`의 순서를 따른다.
- T1 머리: `E2eScal.dechead_seg` (`Compose.lean`). 틀은 `sub $0x20`, 넘침 칸 `0x38`, `0x30`이다. T1의 `.S`와 같다.
- T1 꼬리: `E2eScal.decepi_seg` (`sub`/`add $0x20`).
- T2 AggregatePubkey 필드: `E2eScal.bytesdec_seg` (`SegN.lean`), n = 48, src = 24576.
- 포인터 꼬리: `E2eScal.bytesdec_tail_seg`.

## 3. 매개화가 필요한 것

- `SegN.lean`의 `bytesdec_seg_z`는 `hn : n = 32 ∨ n = 48 ∨ n = 96`만 받는다.
- T1 SyncCommitteeBits는 n = 64, src = 0이다. 기존 보조정리로 덮이지 않는다.
- 계획: 새 파일에 n = 64 경우의 보조정리를 더한다. `SegN.lean`은 바꾸지 않는다.
- T1 SyncCommitteeSignature는 n = 96이다. `.S` 지시어 50에 `nop`이 `mov $0x60,%ecx`와 `callq` 사이에 있다.
- 그 꼴은 `DdSegNop.lean`의 `nop` 꼴과 같다. 그러나 그 보조정리는 n = 32로 고정이다.
- 계획: n = 96 `nop` 꼴 보조정리를 새 파일에 더한다.
- T2 머리와 꼬리는 `sub $0x30`, 넘침 칸 `0x48`, `0x40`이다. `decHead`, `decEpi` 틀은 `0x20`으로 고정이다.
- 계획: T2 머리와 꼬리는 손 단계로 증명한다. 틀을 매개화하지 않는다.

## 4. 새로 필요한 것

### 4.1 T2 루프 불변식

루프 머리는 `L_a0`(지시어 40)이다. 진입 rsp는 x다.
불변식 `ScInv i`는 `i ≤ 512`에서 다음을 말한다.

- 레지스터: rax = i, rsp = x − 56, rbp = x − 8, r14 = 진입 값.
- 수신자: `+8` = A, `+16` = 512, `+24` = 512. AggregatePubkey 칸 셋은 진입 값 그대로다.
- 배열 A: `lvHdrs 48 (ps.take i) ++ replicate (24·(512 − i)) 0`. `ps`는 지금까지 받은 포인터 i개다.
- 원소: `lvElems ps (pks.take i)`.
- 힙: `Heap (avail − 12288 − 48·i)`.
- 스택: x − 32, x − 24, x − 16은 8바이트이고 값은 정하지 않는다. 넘침 칸 24바이트와 `lo`도 같다.
- 넘침 칸 x + 8 = 수신자, x + 16 = buf. 입력과 `R`, `writeBarrier = 0`, 스택 가드는 그대로다.

한 바퀴(`sc_iter`, 지시어 40–71, 36–39)는 `ScInv i`에서 `ScInv (i + 1)`로 간다.

- makeslice(uint8, len 0, cap 48): 새 블록 p, 0 48바이트, 힙 −48.
- memmove(p, buf + 48i, 48): `pks.flatten`의 i번째 48바이트 조각을 쓴다. 조각 분리 보조정리가 필요하다.
- 경계 검사 `cmp %rsi,%rdi; jae`: rsi = 수신자 `+16` = 512, rdi = i < 512. 분기가 안 갈림을 증명한다.
- 헤더 저장: A + 24i + 8, + 16에 48, A + 24i에 p. 0 블록의 i번째 24바이트를 바꾼다.

종료(지시어 41–42): i = 512에서 `jge`가 간다. 이후는 AggregatePubkey 필드와 꼬리다.
Go 1.26.3 `lu_loop`, `fv_loop`의 귀납 방식(`j`에 대한 귀납, `i + j = n`)을 따른다.
512번 펼치지 않는다.
LcLoop의 `⋆ fun _ => True` 꼬리는 쓰지 않는다.

### 4.2 계약 인스턴스

| 호출 지점 | 계약 | ty | esz | cnt | 스택 창 |
| --- | --- | --- | --- | --- | --- |
| T1 16, 51 | `MakesliceC` | `e2eU8Type_addr` (`type__+387072`) | 1 | 64, 96 | 반환 x − 48, spill x − 40 (24), scratch S |
| T1 31, 67 | `MemmoveC` | | | n = 64, 96 | 반환 x − 48, scratch S |
| T2 16 | `MakesliceC` | `lvSliceType_addr` (`type__+337600`) | 24 | 512 | 반환 x − 64, spill x − 56 (24), scratch S |
| T2 48, 84 | `MakesliceC` | `e2eU8Type_addr` | 1 | 48 | 위와 같다 |
| T2 57, 100 | `MemmoveC` | | | n = 48 | 반환 x − 64, scratch S |

`MakesliceC Heap ty 24 S`는 기존 꼴의 인스턴스다. 새 꼴이 아니다.
esz 24의 추상 모델(`bump_makeslice` 류)은 레포에 없다. esz 8과 esz 1만 있다.
그래서 T2 증인에는 esz 24 모델이 필요하다. 그 모델은 기존 계약 꼴을 만족하는 작은 어셈블리다.
모델을 더하는 일은 증인 단위에서 다시 판단한다.
`lvSliceType`의 abi.Type 바이트는 `lv/link/data/lvSliceType.data`에 있다. 계약은 타입 기술자를 읽지 않는다.

### 4.3 제외 경로

- `runtime.morestack_noctxt.abi0`: 전제 guard < rsp. `jbe`가 안 갈림을 증명한다.
- `runtime.gcWriteBarrier2`: 전제 `writeBarrier = 0`. 분기를 증명한다.
- `runtime.panicBounds`(T2 124): 분류 (a). 매 바퀴 경계 검사가 안 갈림을 증명한다.

### 4.4 명세 다리

- T1: `PSa.toValue`의 비트 필드는 `unpackBits bits 512`다. 512 % 8 = 0이라 패딩 검사가 없다.
- T1 `accepted_is_enc`에는 64바이트에서 `packBits (unpackBits b 512) 64 = b`가 필요하다.
- 이 등식은 2^512 경우라 `decide`로 풀 수 없다. 일반 보조정리가 필요하다.
EthLib `Proofs/Ssz/Codec/CanonicalBits.lean` 등에 후보 이름이 있다. 쓸 수 있는지는 확인하지 않았다.
- T2: `vectorSlices`가 24576바이트를 48바이트 조각 512개로 나눔을 보인다. 그다음 `deserializeEach`를 푼다.
- 두 타입 모두 거부 완전성은 "EthLib가 받음 ⇔ 크기가 맞음"에서 나온다.

## 5. 프레임 표

| 칸 | T1 (`sub $0x20`) | T2 (`sub $0x30`) |
| --- | --- | --- |
| 반환 주소 | x | x |
| rbp 저장 | x − 8 | x − 8 |
| rax 넘침 | x + 8 | x + 8 |
| rbx 넘침 | x + 16 | x + 16 |
| 지역 | x − 16 (포인터) | x − 32 (i), x − 24 (3i), x − 16 (포인터) |
| 피호출자 spill | x − 40 (24) | x − 56 (24) |
| 피호출자 반환 칸 | x − 48 | x − 64 |
| scratch | x − 48 − S | x − 64 − S |
| 끝의 반환 칸 값 | `addrOf (k + 68)` | `addrOf (k + 101)` |

지시어 번호는 `.S` 파일의 0부터 센 줄 번호다. 레이블 줄도 센다.

## 6. 증인 계획

`fv/AGENTS.md`는 주 정리마다 구체 상태의 증인을 요구한다.
T1·T2는 고정 크기다. 증인은 각 타입에 하나다.
증인은 `WitDd*`의 방식으로 Host를 만든다. 계약은 `bump_makeslice1`, `rt_memmove`로 채운다.
T2는 esz 24 makeslice 모델이 없다(4.2). 증인이 없으면 T2는 완료가 아니다.

## 7. 한계

- 호스트는 darwin/arm64다. x86-64 기계어를 실행하지 않았다.
- 손 `Desc`는 consensus-specs 원문 사본 없이 썼다. 생산자 `Desc`와 이름만 다름을 눈으로 확인했다. 정리로는 아직 확인하지 않았다.
- T3 `IndexedAttestation`의 `.S`는 커밋하지 않았다. 링크 검사 (d)가 이 장비의 clang에서 실패했다(`ATTEMPTS.md`).
- T3의 정리 문장은 없다. `AttestationData.UnmarshalSSZ`의 함수 명세 꼴(`AdUAccC`)은 레포에 없다.
