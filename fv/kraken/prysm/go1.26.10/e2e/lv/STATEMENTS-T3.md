# STATEMENTS-T3: `IndexedAttestation.UnmarshalSSZ` 손 정리 문장

이 문장들은 증명 전에 커밋한다. 커밋 뒤에는 고치지 않는다.
바꿔야 하면 새 이름으로 더하고 이유를 적는다.
Lean 원문: `lean/E2eList/StmtIa.lean`. 쓰는 정의: `DefsIa.lean`, `DataIa.lean`, `CodeIa.lean`, `IncludeIa.lean`.
설계: `DESIGN-T3.md`.

## 1. 목록

| 이름 | 경로 | 주장 |
| --- | --- | --- |
| `ia_reject_size_stmt` | P1 | `len < 228`이면 `ssz.ErrSize`의 두 단어를 돌려준다. `R`은 그대로다 |
| `ia_reject_offset_stmt` | P2 | `len ≥ 228`, `buf[0:4] = off ≠ iaOff`이면 `ssz.ErrInvalidVariableOffset`의 두 단어를 돌려준다 |
| `ia_reject_misaligned_stmt` | P4 | 오프셋 228, `(len − 228) % 8 ≠ 0`이면 convT64와 errorf(DWC)를 거쳐 rax ≠ 0으로 돌아온다. 정확한 프레임이다 |
| `ia_reject_toobig_stmt` | P5 | 오프셋 228, 정렬, `(len − 228)/8 > 2048`이면 같은 꼴로 돌아온다 |
| `ia_accept_stmt` | P3 | 모든 `n ≤ 2048`에서 `iaOff ‖ data ‖ sig ‖ ib(8n)`를 받으면 nil을 돌려준다. 수신자 = (A, n, n), A에 `ib`; Data = 새 객체(내용은 `ad_e2e_accept_main`의 결론); Signature = (psig, 96, 96) = sig. 힙 `8n + 432` |
| `ia_reject_size_spec_stmt` | P1 명세 | `bs.size < 228`이면 EthLib가 거부하고 기계어가 P1 결론에 닿는다 |
| `ia_reject_offset_spec_stmt` | P2 명세 | `bs.size ≥ 228`, `bs[0:4] ≠ iaOff`이면 EthLib가 거부하고 P2 결론에 닿는다 |
| `ia_reject_misaligned_spec_stmt` | P4 명세 | 정렬 조건에서 EthLib가 거부하고 P4 결론에 닿는다 |
| `ia_reject_toobig_spec_stmt` | P5 명세 | 초과 조건에서 EthLib가 거부하고 P5 결론에 닿는다 |
| `ia_accept_spec_stmt` | P3 명세 | EthLib가 `bsA`를 `v`로 받으면 `g.toValue = v`, `bsA = piaEnc g`인 `g`가 있고 기계어가 `g`를 수신자에 쓴다 |
| `ia_reject_cases_stmt` | 순수 명세 | EthLib가 거부하는 입력은 P1, P2, P4, P5 조건 중 하나를 만족한다 |

## 2. 전제

- 코드 위치와 레이블 신선성: `IaUnmarshal`. 수용은 `AdUnmarshal`, `SlUnmarshal`, `CiUnmarshal`, `CpUnmarshal`, `EpUnmarshal`도 받는다.
- 스택 가드: 거부는 `guard + 48 < rsp`, 수용은 `guard + 408 < rsp`(위임의 가드 조건 포함).
- 쓰기 장벽 = 0(수용). 거부 경로는 쓰기 장벽을 읽지 않는다.
- 수용의 입력: `n ≤ 2048`, `len = 228 + 8n`, `len ≤ cap < 2^63`(266 경계 검사와 18–24 포인터 계산).
- 계약 가설(모두 기존 꼴): 수용은 `MakesliceC lvU64Type 8`, `MakesliceC u8 1`, `MemmoveC`, `NewobjectC lvAdType 96`(scratch `Sd + 224`)과 위임의 다섯(scratch `Sd`, `Sd + 96`). P4·P5는 `ConvT64C`, `FmtErrorfDWC`(형식 `lvFmtMis`/`lvFmtTooBig`, `tw = e2eIntType_addr`).
- P4·P5의 오류 전역: 첫 단어 = errorString itab(`he0`), itab + 8의 8바이트 `ity`, `ErrStr e1 esp msg`, 예산 `fs + msg + 8220 ≤ avail`.

## 3. 사후조건

- 수용: pc = 반환 주소, rax = 0, rbx = 0, rsp + 8, rbp, r14. 정확한 프레임(죽은 지역 다섯은 8바이트 값을 정하지 않는다), 입력, `state`, `R`이 그대로다. 반환 칸 = `addrOf (k + 241)`. 힙 `avail − (8n + 432)`.
- P1·P2: rax = e0, rbx = e1. rbp 칸과 rbx 넘침 칸만 바뀐다.
- P4·P5: rax ≠ 0. 인수 배열(32바이트) = `type:int ‖ box ‖ ity ‖ e1`. 상자 `BoxIn bx v hb`, 힙 `avail' + hb.length ≤ avail`. 반환 칸 = `addrOf (k + 117)`(P4), `addrOf (k + 80)`(P5).
- `⋆ True` 꼬리가 없다.

## 4. 판단이 들어간 곳

- 첫 오프셋은 4바이트 목록과 `iaOff`(= `[0xe4, 0, 0, 0]`)로 적었다. 32비트 정수 대신 바이트로 적었다.
- 원소는 바이트 목록 하나(`ib`, 길이 `8n`)로 적었다. `[]uint64` 배열이 연속 블록이기 때문이다. 명세 쪽에서 `u64Bytes g.idx`가 그 목록이다.
- 수용 명세의 힙 전제는 `bsA.size − 228 + 432 ≤ avail`이다. `8n + 432`와 같은 값이다(n = (size − 228)/8).
- P4·P5의 결론에 rbx(오류의 데이터 단어)가 없다. DWC 계약이 그 값을 주지 않는다.
- P6은 문장이 없다. 수용 전제 아래에서 도달하지 않는다(`DESIGN-T3.md` 2절).

## 5. 고정 뒤 문장 정정: P4, P5의 `_nz` (2026-11-12, 사용자 승인)

- 고정 문장 넷(`ia_reject_misaligned_stmt`, `ia_reject_toobig_stmt`, 두 명세 변형)은 쓴 그대로는 증명할 수 없다. 판정은 N이다. 지우거나 고치지 않았다.
- 빈틈: 지시어 103–106(P4)과 66–69(P5)는 `test %rcx,%rcx; je`다. 오류의 itab 단어 `e0`가 0이면 type 단어를 읽지 않고 0을 넘긴다. `FmtErrorfDWC`는 그 자리에 `ity`를 요구한다. Kraken `Host`는 레이블을 임의 주소에 둔다. 그래서 itab 레이블이 0일 때 그 `je`를 반박할 수 없다.
- 정정: 새 파일 `E2eList/StmtIaNz.lean`의 넷(`ia_reject_misaligned_nz_stmt`, `ia_reject_toobig_nz_stmt`, `ia_reject_misaligned_spec_nz_stmt`, `ia_reject_toobig_spec_nz_stmt`)이다.
- 각 정정은 원문에 전제 `(he0nz : e0 ≠ 0)` 하나만 더한다. 스크립트 비교 결과는 정의마다 바뀐 줄 4개(이름 줄과 binder 줄의 옛 줄, 새 줄)다.
- 정정된 전제는 고정 문장보다 강하다. 같은 문장이 아니다.
- 선례: `Fk/LuRejectCall.lean`의 `lu_reject_misaligned_main`(Go 1.26.3)은 전제 `he0 : e0 ≠ 0`과 `hei : e0.toBitVec = (label "go_itab._errors.errorString_error").toBitVec`를 같이 둔다.
- 실제 ELF에서 `e0`은 itab 주소 `0xd28520`이다. `lv/link-t3/RESULT`의 검사 (b) `go_itab._errors.errorString_error = 0xd28520`이 레이블을 이 주소에 묶는다.
- 사용자 결정 목록에 "고정 뒤 문장 정정"으로 올린다.
