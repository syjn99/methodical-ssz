# DESIGN-DEC: `DataColumnsByRootIdentifier.UnmarshalSSZ`와 왕복 설계

이 파일은 증명 전에 커밋한다. 계획이다. 증명 가능성을 주장하지 않는다.
정리 문장은 `lean/E2eDec/StmtDec.lean`, `lean/E2eDec/StmtComp.lean`에 있다.
T3(`DESIGN-T3.md`)의 꼴을 따른다.

## 1. 입력

| 항목 | 값 |
| --- | --- |
| Go 소스 | `prysm/_generated/mainnet/fulu.ssz.go` 1778–1816행 |
| `.S`와 데이터 | `lv/link-dec` (`check.py` PASS all, 묶음 `7b8d6500…`) |
| 지시어 수 | 229줄. 지시어 번호는 줄 번호 − 1이다 |
| 새 데이터 | 형식 문자열 둘(63, 74바이트). 나머지는 기존 이름과 같음을 `encdeclink.py`가 확인한다 |

## 2. 경로

| 경로 | 조건 | 지시어 | 문장 |
| --- | --- | --- | --- |
| D1 크기 거부 | `len < 36` | 2–10, 175–179 | `dcd_reject_size_stmt` |
| D2 오프셋 거부 | buf[32:36] ≠ 36 | 11–15, 169–173 | `dcd_reject_offset_stmt` |
| D3 수용 | `len = 36 + 8n`, n ≤ 128 | 16–37, 43–55, 62–82, 87–93, 185–203·180–184 루프, 204–208 | `dcd_accept_stmt` |
| D3 명세 | EthLib가 받음 | — | `dcd_accept_spec_stmt` |
| D4 정렬 거부 | `(len − 36) mod 8 ≠ 0` | 67, 131–167 | 문장 없음(5절) |
| D5 초과 거부 | n > 128 | 71, 94–130 | 문장 없음(5절) |
| 왕복 | D3 뒤 인코더 F | — | `dc_unmarshal_then_marshal_stmt` |

## 3. 피호출자

| 지시어 | 대상 | 꼴 |
| --- | --- | --- |
| 23 | `runtime.makeslice` | `MakesliceC Heap e2eU8Type_addr 1 S` (len 0, cap 32) |
| 47 | `runtime.memmove` | `MemmoveC S` (buf → 새 블록, 32바이트) |
| 75 | `runtime.makeslice` | `MakesliceC Heap lvU64Type_addr 8 S` (len = cap = n) |
| 40, 58, 84 | `runtime.gcWriteBarrier2` | 전제 `writeBarrier = 0`. 분기가 안 갈림을 증명한다 |
| 211, 213, 215 | `runtime.panicBounds` | 루프마다 안 갈림을 증명한다(T3 `ia_iter`의 꼴) |
| 99, 136 | `runtime.convT64` | D4, D5. `ConvT64C` |
| 116, 153 | `fmt.errorf` | D4, D5. `FmtErrorfDWC` |
| 121, 158 | `runtime.newobject` | errorf가 nil일 때. DWC의 rax ≠ 0이 막는다 |
| 222 | `runtime.morestack_noctxt.abi0` | 전제 `guard + 16 < rsp` |

새 계약 꼴은 없다.

## 4. 원소 루프

루프 머리는 `L_320`(지시어 185)다. 바퀴는 185–203과 180–184다.
T3 `ia_iter`(147–165, 143–146)와 같은 명령 순서다. 레지스터와 칸만 다르다.
rax = i, rdx = n, rcx = cap − 36, rdi = buf + 36, rsi = 수신자. 수신자 칸: c + 32 = 배열 포인터, c + 40 = len.
불변식의 배열 = `ib.take (8i) ++ replicate (8(n − i)) 0` (T3와 같다).

## 5. D4, D5

- Go 디코더는 BlockRoot를 할당하고 수신자에 쓴 뒤에 정렬과 초과를 검사한다.
- 그래서 D4, D5 문장은 makeslice, memmove, 수신자 쓰기, 쓰기 장벽 전제를 모두 가져야 한다.
- T3의 P4, P5는 할당 전이라 이 꼴을 그대로 쓰지 못한다.
- 왕복이 주 목표라서 D4, D5는 먼저 N으로 둔다. 시간이 남으면 새 문장 파일로 고정한다.

## 6. 왕복

- 기계: 디코더 수용 뒤 인코더 F(`dc_e2e_marshal_fast_main`)를 같은 수신자로 부른다.
- 인코더의 반환 칸 x − 144는 디코더 spill 영역의 첫 8바이트다.
- 인코더 scratch는 디코더의 scratch와 반환 칸을 이은 `S + 8`바이트다.
- 명세: `dc_e2e_spec_roundtrip`(EthLib가 받은 입력은 다시 같은 바이트로 직렬화된다).

## 7. 증인 계획

- D1: 길이 0, 35. D2: 오프셋 0. D3: n = 0, 1, 128.
- D3 Host에는 esz 1과 esz 8의 makeslice가 함께 필요하다. 형식 단어로 가르는 모델을 새 `.S`로 둔다(LV `BumpAllocT.S`의 꼴).
