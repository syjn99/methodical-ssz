# DESIGN-ENC: `DataColumnsByRootIdentifier.MarshalSSZTo` 손 증명 설계

이 파일은 증명 전에 커밋한다. 계획이다. 증명 가능성을 주장하지 않는다.
정리 문장은 `lean/E2eEnc/StmtEnc.lean`에 있다.
선정 이유는 `SELECTION-ENC.md`에 있다.

## 1. 입력

| 항목 | 값 |
| --- | --- |
| Go 소스 | `prysm/_generated/mainnet/fulu.ssz.go` 1754–1776행 |
| `.S` | `lv/link-enc/norm` (`check.py` (a)–(f) PASS, 묶음 `f7cdf5e5…`) |
| 지시어 수 | 118줄. 지시어 번호는 줄 번호 − 1이다 |
| 수신자 배치 | `state` 0, `BlockRoot` 8 (ptr, len, cap), `Columns` 32 (ptr, len, cap), `unknownFields` 56, `sizeCache` 80, 크기 88 |
| 읽는 수신자 칸 | c + 8, c + 16, c + 32, c + 40 |
| 인수 | rax = c, rbx = dst.ptr, rcx = len, rdi = cap |
| 결과 | rax, rbx, rcx = 결과 슬라이스. rdi, rsi = 오류 두 단어 |

## 2. 경로

| 경로 | 조건 | 지시어 | 정리 문장 |
| --- | --- | --- | --- |
| F 용량 충분 | `bl = 32`, `n ≤ 128`, `len + 36 + 8n ≤ cap` | 2–15, 29–44, 50–60, 82–89, 79–81 루프, 100–105 | `dc_marshal_fast_stmt` |
| G 자리 1에서 늘림 | `len ≤ cap < len + 32`, `len + 36 + 8n ≤ nextSliceCap (len + 32) cap` | F에 16–28을 더한다 | `dc_marshal_grow_stmt` |
| RB 길이 거부 | `bl ≠ 32` | 2–11, 70–78 | `dc_reject_bytes_stmt` |
| RT 초과 거부 | `bl = 32`, `len + 36 ≤ cap`, `128 < n < 2^63` | 2–15, 29–44, 50–55, 61–69 | `dc_reject_toobig_stmt` |
| F 명세 | F와 같다 | — | `dc_marshal_spec_stmt` |
| G 명세 | G와 같다 | — | `dc_marshal_grow_spec_stmt` |
| RB 명세 | BlockRoot 길이 ≠ 32 | — | `dc_spec_reject_bytes_stmt` |
| RT 명세 | 원소 수 > 128 | — | `dc_spec_reject_toobig_stmt` |
| G* 그 밖의 늘림 | 자리 2, 자리 3(어느 바퀴든), 여러 번 늘림 | 45–49, 90–99 | 문장 없음. N |
| morestack | `guard + 8 ≥ rsp` | 106–117 | N. 전제 `guard + 8 < rsp`가 막는다 |

- `bl`은 c + 16의 BlockRoot 길이 단어다. `n`은 c + 40의 Columns 길이 단어다.
- RT 경로의 `jg`는 부호 있는 비교다. 그래서 `n < 2^63`을 전제로 둔다. Go `len`은 그 범위다.
- RT는 처음 두 자리가 늘지 않는 경우만 다룬다. 늘리는 RT는 N이다.
- RT에서도 dst에 36바이트가 이미 쓰였다. 사후조건이 그 바이트를 적는다.

## 3. 프레임 (x = 진입 rsp)

| 자리 | 쓰는 지시어 | 경로 | 문장의 이름 |
| --- | --- | --- | --- |
| x | 반환 주소 | 모두 | `ra` |
| x − 8 | 5 (`push %rbp`) | 모두 | `fp` |
| x + 8 | 12 (rax) | F, G, RT | `s1` |
| x + 16 | 8 (rbx) | 모두 | `s2` |
| x + 24 | 16 (rcx) | G | `s3` |
| x − 16 | 17 (root 포인터) | G | `l16` |
| x − 24 | 58 (Columns 포인터) | F, G | `l24` |
| x − 32 | 31 (dst 포인터) | F, G, RT | `l32` |
| x − 40 | 56 (n) | F, G | `l40` |
| x − 48 | 90 (i) | G*만 | 문장에 없음 |
| x − 56 | 32 (cap) | F, G, RT | `l56` |
| x − 64 | 30 (len + 32) | F, G, RT | `l64` |
| x − 72 | 91 (원소 단어) | G*만 | 문장에 없음 |
| x − 136 | growslice spill 40바이트 | G | `spl` |
| x − 144 | 호출 반환 칸 | F, G, RT | `rslot` |
| x − 144 − S | scratch `S` | F, G, RT | `scratch` |

- 각 문장은 그 경로가 쓰는 칸만 전제에 둔다. 나머지는 `R`에 있고 바뀌지 않는다.
- x + 8과 x + 16의 값은 사후조건에 정확히 적는다(rax, rbx).
- 지역 칸, 반환 칸, scratch는 사후조건에서 길이만 정한 존재 변수다.

## 4. 원소 루프 (F와 G에서)

루프 머리는 `L_13a`(지시어 82)다.
한 바퀴는 82–89와 79–81이다.
불변식 `DcInv i`(`i ≤ n ≤ 128`):

- rax = 블록 포인터 `bp`, rbx = len + 36 + 8i, rcx = 블록 용량, rdx = Columns 포인터 pc, rsi = i, r8 = n.
- rsp = x − 136, rbp = x − 8.
- 블록: `bp`에 `pre ‖ root ‖ dcOff ‖ cb.take (8i)`, 그 뒤에 아직 안 쓴 `rest.drop (8i)`.
- 용량: len + 36 + 8n ≤ 용량. 그래서 89의 `jae`가 늘 간다. growslice 94에 닿지 않는다.
- 입력 `cb`, 수신자 칸, 프레임, `R`은 그대로다.

한 바퀴: 83–84 `cmp %r8,%rsi; jge`는 i < n이라 안 간다(`jge_false512`의 꼴).
85 rbx += 8, 86 `mov (%rdx,%rsi,8),%r9`로 8바이트를 읽는다.
88–89 `cmp %rbx,%rcx; jae`는 용량 전제로 간다.
80 `mov %r9,-0x8(%rbx,%rax,1)`로 bp + len + 36 + 8i에 8바이트를 쓴다. 81 rsi += 1.
루프 끝: i = n에서 84의 `jge`가 L_17e(100)로 간다.
n = 0이면 바퀴가 없다.

증명 꼴은 `E2eList/IaLoop.lean`(`ia_iter`, `ia_exit`, `ia_loop`)과 같다.
`Fk.block_split`과 `out_step`의 꼴을 다시 쓴다. 쓰는 블록은 `cb.take (8i) ++ rest.drop (8i)`다.

## 5. 쓰는 바이트와 오프셋

| 지시어 | 주소 | 바이트 |
| --- | --- | --- |
| 36 memmove | dst.ptr + len | BlockRoot 32바이트 |
| 51 `movl $0x24,-0x4(%rbx,%rax,1)` | dst.ptr + len + 32 | `dcOff` = 24 00 00 00 (오프셋 36) |
| 80 (바퀴 i) | dst.ptr + len + 36 + 8i | Columns[i]의 8바이트 |

- 51의 `movl`은 32비트 즉시값 저장이다. 4바이트 `Int.toBytes 4 36` = `dcOff`다.
- 루프의 8바이트 읽기와 쓰기는 같은 바이트다(`toBytes_ofInt_ofBytes`).
- 명세 쪽: `pdcEnc g = root ‖ dcOff ‖ u64Bytes cols`이고 `serialize prysmDcDesc g.toValue = .ok (pdcEnc g)`를 보인다.
- 그 증명은 `E2eList.pia_serialize`, `Fv1.serializeEach_u64`, `Fv1.inl_*`의 꼴을 다시 쓴다.

## 6. 늘림 경로 G

- 15의 `jae`가 안 간다(cap < len + 32).
- 16–23: rcx를 x + 24에, rdx(root 포인터)를 x − 16에 둔다. growslice(rax = dst.ptr, rbx = len + 32, rcx = cap, rdi = 32, rsi = uint8 형식).
- 계약 `GrowsliceC Heap e2eU8Type_addr 1 S`: 옛 블록 `pre`(len바이트), 새 블록 `pre ++ tail`, `nextSliceCap ≤ newCap`.
- 24–28: rdx, rdi = newCap, r8 = len + 32, rcx = len, rbx = 새 포인터를 되찾는다. 29(L_7c)로 이어진다.
- 그 뒤는 F와 같은 코드다. 블록 포인터와 용량만 다르다.
- `hfit`가 자리 2와 3이 늘지 않음을 준다.
- 그래서 F 꼴 보조정리는 블록 포인터·용량을 매개변수로 둔다. F와 G가 그것을 함께 쓴다.

## 7. G* (문장 없음, N)

- 자리 2 또는 루프의 어느 바퀴에서도 growslice가 불릴 수 있다.
- 그 경우를 덮으려면 불변식이 "블록 = 앞서 쓴 바이트 ++ 꼬리"를 블록 포인터와 무관하게 말해야 한다.
- 늘릴 때마다 옛 블록이 사후조건에 남는다. 그 수는 경로마다 다르다.
- 그래서 사후조건에 존재 술어(쓰레기 블록)가 필요하다. 힙 예산도 늘림 횟수에 따라 정해야 한다.
- 이번 단위에서는 문장으로 쓰지 않는다. 보고서에 장애물로 적는다.

## 8. 증인 계획

- F: n = 0, 1, 128. Host는 `DcMarshal`과 `rt_memmove` 모델이다.
- G: n = 0, 1, 128. Host에 `rt_growslice`(esz 1) 모델을 더한다. 용량 128을 담으려면 큰 cap가 필요하다(예: cap 4000, len 3970).
- RB: bl ∈ {0, 31, 33}. RT: n = 129.
- 모델이 기존 Host 꼴(`Fk.WHost`, `E2e.WitCpMR`)로 되지 않으면 그 사실을 적는다.

## 9. 위험과 판단

- 스택 가드는 `lea -0x8(%rsp),%r12` 꼴이다. `E2eScal.lea_cmp_be_false`(N = 8)로 닫는다.
- `add $-0x80,%rsp`와 `sub $-0x80,%rsp`는 음수 즉시값이다. Kraken이 −128로 읽는지 첫 빌드에서 본다.
- 51의 `movl` 꼴(32비트 즉시값을 색인 주소에 저장)은 기존 증명에 없을 수 있다. 막히면 Kraken 요청 목록에 적는다.
- 큰 `simp` 정렬이 증인에서 시간을 쓸 수 있다(LV 보고서 4절). 그때는 원인을 측정한 뒤 설정을 둔다.
