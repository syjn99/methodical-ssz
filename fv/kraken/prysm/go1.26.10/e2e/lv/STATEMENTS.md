# STATEMENTS: LV 손 정리 문장 (T1, T2)

이 문장들은 증명 전에 커밋한다.
커밋 뒤에는 고치지 않는다.
바꿔야 하면 새 이름으로 더하고 이유를 적는다. 원래 문장은 남긴다.
Lean 원문: `lean/E2eList/StmtSa.lean`, `lean/E2eList/StmtSc.lean`.
문장이 쓰는 정의: `lean/E2eList/Defs.lean`, `lean/E2eList/Desc.lean`, `lean/E2eList/Data.lean`, `lean/E2eList/Code.lean`.
모양의 본: `E2eScal.H4.dd_accept_stmt`와 그 명세 정리 넷(`DdReject.lean`, `DdSpecK.lean`).

## 1. 목록

| 이름 | 경로 | 주장 |
| --- | --- | --- |
| `sa_accept_stmt` | T1 수용(기계어) | 160바이트 입력에서 nil을 돌려준다. 두 필드는 새 블록이고 입력 조각과 같다. 힙 160바이트를 쓴다 |
| `sa_reject_size_stmt` | T1 크기 거부(기계어) | rcx ≠ 160이면 `ssz.ErrSize`의 두 단어를 돌려준다. `R`은 그대로다 |
| `sa_accept_spec_stmt` | T1 수용(명세) | EthLib가 `bsA`를 `v`로 받으면 `g.toValue = v`, `bsA = psaEnc g`인 `g`가 있다. 기계어는 `g`를 수신자에 쓴다 |
| `sa_reject_size_spec_stmt` | T1 크기 거부(명세) | `bs.size ≠ 160`이면 EthLib가 거부하고 기계어가 `ssz.ErrSize`를 돌려준다 |
| `sa_reject_complete_stmt` | T1 거부 완전성 | EthLib가 거부하는 입력은 모두 `size ≠ 160`이다 |
| `sc_accept_stmt` | T2 수용(기계어) | 24624바이트 입력에서 nil을 돌려준다. Pubkeys는 길이 512의 새 `[][]byte`이다. 원소 i는 입력 조각 i와 같다. 힙 36912바이트를 쓴다 |
| `sc_reject_size_stmt` | T2 크기 거부(기계어) | rcx ≠ 24624이면 `ssz.ErrSize`의 두 단어를 돌려준다 |
| `sc_accept_spec_stmt` | T2 수용(명세) | EthLib가 받으면 `g : PSc`가 있다. 기계어는 `g`를 수신자에 쓴다 |
| `sc_reject_size_spec_stmt` | T2 크기 거부(명세) | `bs.size ≠ 24624`이면 EthLib가 거부하고 기계어가 `ssz.ErrSize`를 돌려준다 |
| `sc_reject_complete_stmt` | T2 거부 완전성 | EthLib가 거부하는 입력은 모두 `size ≠ 24624`이다 |

T3 `IndexedAttestation`의 문장은 이 단위에 없다.

## 2. 전제

모든 기계어 문장의 공통 전제다.

- 코드 위치: `XUnmarshal.IsInfixAt Host.prog k`와 `LabelsFresh XUnmarshal k`.
- 스택 가드: `guard.toNat < rsp.toNat`. morestack 경로를 막는다.
- 쓰기 장벽: `runtime.writeBarrier`의 4바이트 = 0. 조각이 `h_mem`에 있다.
- 메모리: `h_mem`이 모든 칸을 분리 조각으로 준다. 반환 칸, rbp 칸, 넘침 칸, 지역, spill, 반환 슬롯, scratch `S`, 가드, `Heap avail`, 입력, 수신자 칸, 쓰기 장벽, 나머지 `R`이다.
- 수용의 크기: `rcx = 160` 또는 `rcx = 24624`. 명세 문장은 `rcx.toNat = bsA.size`다.
- 힙: `160 ≤ avail` 또는 `36912 ≤ avail`.
- 계약 가설: `MakesliceC Heap e2eU8Type_addr 1 S`, `MemmoveC S`. T2는 `MakesliceC Heap lvSliceType_addr 24 S`도 받는다.
- 크기 거부는 계약 가설이 없다. 피호출자를 부르지 않는다.

## 3. 사후조건

수용(기계어):

- pc = 반환 주소, rax = 0, rbx = 0, rsp = 진입 rsp + 8, rbp와 r14는 진입 값.
- 반환 칸, rbp 칸, 넘침 칸 둘(진입 rax, rbx), 가드, 입력, `state`, 쓰기 장벽, `R`이 그대로다.
- 지역 x − 16은 마지막 필드 포인터다. T2의 x − 32, x − 24는 8바이트이고 값은 정하지 않는다.
- spill 24바이트와 scratch `S`는 길이만 정한다.
- 반환 슬롯은 마지막 memmove의 복귀 주소다(T1 `addrOf (k + 68)`, T2 `addrOf (k + 101)`).
- 힙은 `Heap (avail − 160)` 또는 `Heap (avail − 36912)`이다.
- T1 수신자: `+8` = p1, `+16` = `+24` = 64, `+32` = p2, `+40` = `+48` = 96. p1에 bits, p2에 sig.
- T2 수신자: `+8` = A, `+16` = `+24` = 512, `+32` = pA, `+40` = `+48` = 48.
- T2 배열: A에 `lvHdrs 48 ps`(원소 헤더 `(ps[i], 48, 48)`), `lvElems ps pks`(ps[i]에 pks[i]), pA에 agg.
- `⋆ True` 꼬리가 없다. 발자국 전체를 적는다.

크기 거부(기계어): pc = 반환 주소, rax = e0, rbx = e1, rsp + 8, rbp, r14. rbp 칸에 진입 rbp, x + 16에 진입 rbx, 나머지는 그대로다.

명세: 수용은 `∃ g, g.toValue = v ∧ bsA = enc g ∧ (기계어 사후조건)`이다.
전제 `Pm`은 `bsA = enc g`인 모든 `g`에 대해 `g`의 조각으로 메모리를 준다.
이 꼴은 `dd_e2e_accept_spec_k`와 같다.

## 4. 판단이 들어간 곳

- 손 `Desc`는 consensus-specs altair의 정의를 기억으로 옮겼다. 레포에 원문 사본이 없다.
- 생산자 `Desc`(`lv/desc/`)는 손 `Desc`를 쓴 뒤에 출력했다. 필드 이름만 다르다(눈으로 확인). 정리는 아직 없다.
- `state` 칸은 읽히지 않는다. 그래도 `ast`로 남겨 그대로임을 적는다(`dd_accept_stmt`와 같다).
- T2 루프 지역 x − 32, x − 24의 끝 값(511, 1533)은 적지 않았다. 죽은 칸이라 길이만 적는다.
- 거부 완전성은 순수 명세 문장이다. 기계어의 다른 오류 반환이 없다는 사실은 `.S`를 읽은 판단이다.
- `MakesliceC`의 esz 24 인스턴스는 새 꼴이 아니라고 판단했다. 형식이 esz를 매개변수로 받는다.
- 스택 가드 전제는 `guard < rsp`다. 피호출자가 가드를 검사하지 않는 계약이라서 여유를 두지 않았다(`dd_accept_stmt`와 같다).
