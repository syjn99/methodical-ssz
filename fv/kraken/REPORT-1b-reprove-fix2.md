# REPORT-1b-reprove-fix2: 재증명 수정 리뷰의 필수 수정 8개와 거부 경로

기준: 브랜치 `syjn99/ssz-fv-reprove-fix2`, 시작 `28ea489`(재증명 수정 `813a86a` + 리뷰 두 편).
Kraken `6064eec`(main), Lean `nightly-2026-09-21`, EthLib `8621856`, Go 1.26.3, `GOAMD64=v1`.
ELF sha256 `9c850c97…c501`(바뀌지 않았다. 대상 Go 코드와 생성기는 고치지 않았다).
작성 2026-11-06.
시각은 커밋 시각(IST)이다. 외삽하지 않는다.

## 0. 판정

**조건부. 게이트 1은 미통과(자평).**

필수 수정 8개 중 6개를 완료했고 2개(#4·#5의 신뢰 항목, #7)는 부분이다.
거부 경로 3개 중 2개를 닫았고 1개(ListC 원소 오프셋 순서)는 미수행이다.
게이트 1을 막는 조건:

1. ListC 원소 오프셋 순서 거부(`lc_reject_offset_order_main`)와 비어 있지 않은 원소의 오류 전달이 없다(5절, 미수행).
2. 사후조건: `ne_marshal_main`은 결론에서 프레임 `R`을 잃는다. `lc_accept_main`은 `R`을 돌려주지만 죽은 피호출자 스택은 `True`다. 크기 정리 11개는 프레임 `R`을 말하지 않는다(4절 표, X7).
3. 런타임 계약은 추상 모델로만 만족 가능성을 보였다. Go의 실제 할당량, GC 부재, 오류 결과 객체는 신뢰 항목이다(CONTRACTS.md 1e절).
4. 디코더의 EthLib 양방향 수용은 BitVec(1바이트)만 정리로 닫혔다. Scalars는 bool 거부가 더해졌으나 양방향 정리 하나로 묶지 않았다.
5. x86-64 하드웨어 대조를 하지 않았다(이 호스트는 arm64).

수치(마지막 실행, 11절):

- `lake build`: 856 jobs, 성공.
- 공리 두 범위: 정리 `TOTAL 1583 NONSTANDARD 0`(`AXIOMS.txt`), 모든 선언 `TOTAL 8028 NONSTANDARD 0`(`AXIOMS-ALL.txt`). 시작 1432/7334.
- 링크 검사 PASS(검사 (a)–(h)). 자기 시험 24개 기대대로.
- 부정 시험 16개 기대대로(`negative/RESULT`, 08:22:48–08:33:07, 10분 19초). 새 변이 둘: `scrbword`, `blrity`.
- 증인 파일 79개, `*_runs` 선언 80개(고유 이름 59). goval: 위반 0, 값을 읽지 못한 파일 2개(`WitCpM` 기호 길이 dst, 1a `Witness.lean`).
- `go test ./fv/kraken/semtest/`: PASS.
- 세션 시간: 06:51(X0 시작)부터 08:21(마지막 증명 커밋)까지 1시간 30분. 그 뒤 회귀 검사와 보고서.

## 1. 완료 단위

재증명 수정과 같은 6요소다.
요소 6(Go 값)을 넓혔다: 크기·정렬·패딩·bool·타입 워드·블록 안 포함·객체 간 겹침(X3).

1. 계약 또는 정리.
2. 구체 Host에서 전제 전체의 증인. 가변 길이는 빈 값, 1개, 최대.
3. 기계어 정리.
4. 링크 검사 PASS.
5. 부정 시험: 변이가 지정 정리 안에서 실패하고 대조군이 통과한다.
6. Go 값: `lean/tools/wit/goval.py`가 `layout.json`(amd64 배치)으로 검사한다. 읽지 못한 값은 "미검사"로 센다.

## 2. 항목별 결과

| 항목 | 커밋 | 시각 | 결과 |
| --- | --- | --- | --- |
| X0 | — | 06:51 | `.lake` 복사, 빌드 6초. 기준선 일치: 830 jobs, AXIOMS 1432/7334 NONSTANDARD 0, 링크 PASS, selftest 14, negative 14(06:52:42–07:01:19, 8분 37초), go test ok, goval 69/0 |
| X1, X2 | `4facb69` | 06:58 | 링크 검사 (f)·(g). 커밋 메시지의 "자기 시험 14 → 24"는 셈이 틀렸다. 그 커밋에서는 23이고, X4의 (h) 변이를 더해 24가 됐다 |
| X3 | `c4f8e2b` | 07:11 | `layout.go`·`layout.json`, goval 검사 확장, 증인 23개 수정 |
| X4, X5 | `73d07fa` | 07:47 | fmt·convT64·ValidateBitlist 계약 재설계, 모델, joint_models, 증인 8개 재생성, 링크 (g)·(h) |
| X8a, X8b | `877f302` | 07:57 | `sc_reject_bool_main`, `sc_spec_rejects_bool`, `bl_reject_invalid_main`, 증인 둘, 부정 시험 둘 |
| X6 | `a27b103` | 08:02 | ListC 수용·마샬 증인 6개(1×1, 4×16, 0·1·16) |
| X7 | `b147e55` | 08:21 | 사후조건 7개 정리 강화, 조합 정리 `sc_unmarshal_then_marshal`, 조합 증인 둘 |
| X8c | — | — | 미수행(5절) |
| X10, X11 | 이 커밋 | 08:22–08:40 | `tools/RegressFix2.lean`, 부정 시험 전체, 공리, 보고서, CONTRACTS 1e |

### X1. 링크 검사 (f) (astra 1)

방법 (b)를 택했다.
`SHash.lean`은 `shash.sh`가 쓰는 원문과 바이트 단위로 같아야 한다(`link/check.py:133` `shash_text`, `:411`).
주석 제거기를 쓰지 않으므로 해시 문자열 안의 `/-x-/` 변이가 실패한다.
자기 시험 "SHash comment inside a string"(astra `review-reprove-fix-mut-shash-balanced-comment-astra.log`의 변이)이 (f)에서 실패한다.

### X2. 링크 검사 (g) (astra 2)

- Lean 주석은 문자열 상태를 가진 스캐너로 지운다(`check.py:95` `strip_lean_comments`, 문자열과 문자 리터럴 안의 `/-`·`--`는 텍스트).
- FMTS 정의는 이름당 하나이고, 다음 명령 줄(열 0)까지 리스트 리터럴 하나여야 한다(`:178` `lean_bytes`). 같은 줄 접미 식과 다음 줄 `|>.map`이 모두 실패한다.
- 사용 위치는 `label\s+"go_string\._"\s*\+\s*n\s*\)`로 읽는다. 해석하지 못한 `go_string` 텍스트는 실패한다(`:148` `lean_gs_refs`).
- Go 리터럴은 `link/golits.go`(go/parser)가 `fmt.Errorf` 호출의 첫 인수에서만 모은다(`:196`). 주석 속 리터럴은 호출이 아니다.
- 검사 대상은 파일 접두사가 아니라 선언 역할이다(`:457`). 구체 Host 모듈(`instance host : Host := mkHost`)의 선언 중 `[Host]`를 받지 않는 것이 증인이다. 증인만 0 채움 `(z n)`과 레이블 자체를 쓸 수 있다.
- 자기 시험에 넣은 astra 변이: 값 접미 식(같은 줄, 다음 줄), 공백 둘 오프셋, Go 주석 리터럴, Wit 파일의 일반 선언. 더한 변이: Wit 파일의 모르는 배치, 검사 오프셋의 해석 불가 바이트, 합으로 쓴 오프셋, `luTW` 타입 변경((h)).

### X3. Go 값 검사기 (astra 3)

- `lean/tools/wit/layout.go`: `fv/kraken/target`·`target/prysm`의 모든 구조체에 대해 `unsafe.Sizeof`·`Alignof`·`Offsetof` 식을 합성 파일에 두고 go/types(`SizesFor("gc", "amd64")`)로 상수 값을 얻는다. amd64 바이너리를 이 호스트에서 실행하지 않는다. 출력 `layout.json`. Scalars: 크기 24, 정렬 8, `E` 오프셋 16(astra와 같다).
- `goval.py` 검사(`:224`, `:236`, `:286`, `:305`, `:317`): 슬라이스 헤더, 데이터 정렬(원소 크기 기준), 객체 크기·정렬, rsp 8정렬, bool ≤ 1, itab+8 타입 워드(전제가 그 칸을 둘 때만: 0이 아니고 8정렬, 48바이트 abi.Type 블록이 블록 안), 객체 간 겹침, `s_mem` 조각이 객체 경계를 가로지르지 않음.
- 첫 실행 위반: 28개 파일. astra의 셋(WitScA 블록 밖 7바이트, WitScM 수신자·dst 겹침, WitNeM0/1/16 객체 겹침) 외에 새로 찾은 것: 정렬 위반 16개(대부분 `wgen.gen`의 힙 앞 12바이트 때문), itab 타입 워드 0인 증인, WitLcT 다섯째 입력 바이트가 rodata 채움과 겹침, WitCpMR Root cap 칸이 데이터와 겹침, WitLuMR 데이터 비정렬.
- 처리: `wgen.gen`의 힙 앞 4바이트 틈(`CH0 = 0x10010`), `wgen.aligned`, 생성기별 수정, 설정 없는 WitCp·WitFv·WitAd는 한 번 4바이트 이동(`tools/wit/README.md`). BlR·BvR 타입 워드는 X4·X5에서.
- 마지막 실행: 79개 파일, 위반 0, 미검사 2(`WitCpM` dst 기호 길이, 1a `Witness.lean` 기호 n).
- 한계: bump 모델이 돌려주는 힙 할당 주소의 정렬, 증인 전역 오류 값(`ssz.Err*`)의 Go 값은 검사하지 않는다.

### X4. fmt 계약 범위 (astra 4)

`FmtErrorfWC Heap fs RO MsgIn S`(`Contracts.lean:180`), `FmtErrorfDWC Heap fs tw S`(`:212`).
형식은 정의 인수이고 정리가 상수로 고정한다(`bvFmtJ`, `blFmtB`, `luFmtTooBig`, `luFmtMis`).
인수는 실제 호출 모양으로 고정했다: `%w` 하나(rdi = 1, errorString, 타입 워드 = itab+8), 또는 `%d`(int 상자, 타입 워드 `luTW` = `type:int`) + `%w`.
임의 `fs`와 임의 앞 인수 `pre`를 받는 계약은 없다.
예산은 형식과 인수에서 계산한다(`fs + msg + 8192`, `%d`는 20자리 더).
`ConvT64C`(`:109`)는 상자를 말한다: `BoxIn bx v hb`(정적 표 `StaticBox v` 또는 힙 8바이트 = v). 모델 `rt_convT64`(`RtErr.lean:108`)는 bump 힙에 v를 저장한다.
ListU64 증인 WitLuTb·WitLuMa는 실제 bump 힙(8296바이트)과 정적 상자 항목을 둔다(astra의 `emp` 힙 지적).
`joint_models`(`Regress.lean:91`)는 열 계약을 모든 형식·자원 인수에 대해 한 Host·한 힙에서 만족한다. `not_joint_false`가 그대로 닫힌다.

### X5. rodata 메시지 (astra 5)

`vblRO`(`Vbl.lean:76`): ValidateBitlist의 인수 없는 세 메시지(`go_string._+33605/13272/5743`, 실제 코드의 `lea` 피연산자).
`ValidateBitlistErrC`(`:106`)는 사전조건에 `vblRO`를 두고 결론에서 보존한다.
결론의 힙 자원은 16바이트 `ErrObj`와 `%d` 메시지 `hm`뿐이다(`VblMsg`, `:84`: rodata 셋 중 하나이고 `hm = []`, 또는 `hm = msg ≤ 128`).
`F`는 `⋆`로 `vblRO`와 분리되므로 rodata 조각을 가질 수 없다(`tools/RegressFix2.lean` `duplicate_byte_impossible`).
`bl_marshal_reject_main`과 새 `bl_reject_invalid_main`이 이 계약을 쓴다. 증인 WitBlR·WitBlRI는 세 메시지를 그 오프셋에 둔다.
한계: 어느 입력이 어느 메시지인지는 계약이 말하지 않는다.

### X6. ListC 증인 (astra 6)

| 증인 | 정리 | 원소(안쪽 길이) | 리스트 바이트 | 오프셋 | 힙 소비(계산값) | dst cap |
| --- | --- | --- | --- | --- | --- | --- |
| WitLcA1x1 | `lc_accept_main` | [1] | 16 | [4] | 8 + 24 + 8 = 40 | — |
| WitLcA4x16 | `lc_accept_main` | [16,16,16,16] | 544 | [16, 148, 280, 412] | 32 + 96 + 512 = 640 | — |
| WitLcAMix | `lc_accept_main` | [0,1,16] | 160 | [12, 16, 28] | 24 + 72 + 136 = 232 | — |
| WitLcM1x1 | `lc_marshal_main` | [1] | — | — | — | 20 |
| WitLcM4x16 | `lc_marshal_main` | [16,16,16,16] | — | — | — | 548 |
| WitLcMMix | `lc_marshal_main` | [0,1,16] | — | — | — | 164 |

- 힙 소비는 계약 모델(bump makeslice·newobject)과 입력에서 계산한 값이다. 정리 결론에서 꺼낸 값이 아니다. 4×16의 640은 전제 `hav : 8 * 4 + 152 * 4 ≤ avail`의 상한과 같다.
- 안쪽 할당·복사가 실행된다는 근거: 증인이 원래 주 정리를 적용하고, `LuUAccC`가 실제 ListU64 디코더(`lu_uacc_holds`, makeslice 포함)에서 유도된다. 원소 값은 1..m이다.
- 느린 것: 처음 빌드에서 `lcTl_parts`의 `rfl`이 재귀 한도에 걸렸다(4×16, Mix). `maxRecDepth 100000`과 `maxHeartbeats`로 닫혔다. 각 파일은 십여 초다. 보존할 실패 파일은 없다.

### X7. 사후조건과 조합 (astra 7)

- `sc_marshal_main`(`ScMarshal.lean:44–62`)·`sc_marshal_spec_k`: `⋆ True`를 없앴다. 출력, `pre`, 수신자 필드, 반환 주소, 스택 칸 셋(rbp·rax·rbx 값), 가드, `R`을 정확히 돌려준다.
- `lc_accept_main`(`LcAccept.lean:67–78`)·`LcAcceptSpec`: `R`, 입력 머리 `[4,0,0,0]`, 반환 주소를 더했다. 죽은 피호출자 스택은 `lcl_loop`(801줄)의 결론이 이미 `True`로 보내므로 `True`로 남는다(부분).
- `R`을 버리던 7개 중 6개에 `R`을 더했다: `bl_accept_main`(BlSpec 전파), `cp_marshal_reject_main`, `fv_marshal_main`, `lc_marshal_main`, `lu_marshal_main`, `ne_accept_main`(NeSpec 전파). `ne_marshal_main`은 하위 단계 증명에서 `R`을 잃어 기계적 수정이 안 됐다(되돌림).
- 조합: `WitLuComp.lu_compose_runs`(`WitLuComp.lean:151`)는 `lu_unmarshal_then_marshal`의 전체 전제 증인이다. 한 Host에 실제 디코더(5)·인코더(198)·bump makeslice(289). 중간 메모리는 디코더의 최종 메모리에 `ra2`를 `Mem.storeInt`로 쓴 실제 메모리다. `hupd`는 `Mem.storeInt_sep`으로 만족된다.
- Scalars: 새 조합 정리 `sc_unmarshal_then_marshal`(`ComposeSc.lean:22`)과 증인 `WitScComp.sc_compose_runs`(`WitScComp.lean:95`). 호출자의 CALL은 여전히 `hupd` 관계다(실행한 호출자 명령이 아니다).

주 정리 55개의 결론(정규식 `tools`가 아닌 1회 스크립트로 셌다. 결과는 아래):

| 분류 | 수 | 정리 |
| --- | --- | --- |
| `R` 보존, `⋆ True` 없음 | 9 | `bl_marshal_main`, `bv_accept_main`, `bv_marshal_main`, `lu_accept_main`, `sc_accept_main`, `sc_marshal_main`, `sc_reject_bool_main`, `vbv_accept_main`, `vbv_reject_pad_main` |
| `R` 보존, 나머지 `⋆ True`(죽은 스택 등) | 34 | `ad_accept/marshal/reject_size`, `bl_accept`, `bl_marshal_reject`, `bl_reject_invalid/short/offset`, `bv_reject_padding`, `cp_accept/marshal/marshal_reject/reject_size`, `fv_accept/marshal/marshal_reject`, `lc_accept`, `lc_accept_empty`, `lc_marshal`, `lc_reject_short/offset/zero/past/tail`, `lu_marshal/marshal_reject/reject_short/offset/toobig/misaligned`, `ne_accept`, `ne_reject_short/offset`, `ne_size` |
| `R` 없음, `⋆ True` | 1 | `ne_marshal_main` |
| 메모리를 말하나 `R` 이름이 없음(스크립트가 찾지 못함, 수작업 확인 안 함) | 7 | `ad/bl/bv/cp/fv/lc/lu_size_main` |
| 레지스터만 말함 | 4 | `bv/fv/sc_reject_size_main`, `sc_size_main` |

### X8. 거부 경로 (astra 8절 우선순위)

| 경로 | 정리 | EthLib | 증인 | 부정 시험 | 링크 | 상태 |
| --- | --- | --- | --- | --- | --- | --- |
| (a) Scalars bool > 1 | `sc_reject_bool_main`(`ScRejectBool.lean:22`): A–D를 쓴 뒤 `ssz.ErrInvalidSerialization`, E는 쓰지 않음 | `sc_spec_rejects_bool`(`:164`): deserialize가 받지 않음 | WitScRB(모든 e > 1, 24바이트 수신자) | `scrbword`(첫 워드 대신 둘째 워드) | PASS(전역 기호 (b)) | 완료 |
| (b) BitL ValidateBitlist 오류 | `bl_reject_invalid_main`(`BlReject.lean:24`): `ValidateBitlistErrC`(X5 모양) + `FmtErrorfWC Heap blFmtB vblRO VblMsg` | 전제 `¬ blValid tl`(EthLib 규칙). deserialize 수준 정리는 없다 | WitBlRI(꼬리 `[0]`, 실제 bump 힙, 타입 기술자) | `blrity`(itab+16 읽기) | PASS((g) `blFmtB`, 메시지 셋) | 완료 |
| (c) ListC 원소 오프셋 순서, 원소 오류 전달 | 없음 | — | — | — | — | 미수행 |

(c) 미수행 분석: 순서 검사(`target.ListC.UnmarshalSSZ.S` 지시어 276–277, `cmp %r11,%rsi; jb`)는 루프 첫 반복 안이다.
그 앞에 makeslice(75), 쓰기 장벽 분기(80–87), newobject(246), 경계 검사 둘(255–260), 다음 오프셋 읽기(262)가 있다.
오류 분기는 `convT64` 둘(uint64 상자, `type__+49120`)과 `%w` 없는 `%d` 두 개 fmt 호출이다. 새 계약(`FmtErrorfDDC` 모양)과 모델, joint_models 갱신이 필요하다.
`lc_accept_main`의 접두(약 200줄)와 `LcLoop`의 반복 증명 일부를 i = 0으로 옮기는 일이다.
이번 세션의 남은 맥락 예산으로 X9–X11을 먼저 끝냈다. 원소 오류 전달("Items: %w")은 ListU64 거부 정리를 함수 명세로 유도하는 일이 더 필요하다.

나머지 ListC 정렬·원소 수 오류와 Nested 래핑 경로는 하지 않았다(브리프대로 4절 표에 남김).

### X10. 회귀 검사

- 전체 빌드에서 모든 `Fk.Wit*`(80개 `*_runs` 선언)가 다시 빌드됐다.
- 리뷰 Lean 파일(고치지 않음)을 이 트리에서 실행한 결과(`lean/tools/regress-fix2.log`):
  - `review/ReviewReproveFix.lean`: 실패 둘. `Fk.Regress.Joint`의 인수가 늘었다(형식·자원·타입 워드, X4). `bv_errstr`가 `bv_errobj`로 바뀌었다(메시지를 `ErrObj`와 분리, X5). 나머지 항목(blValid 사례, 산술 전제)은 영향이 없다.
  - `review/ReviewReproveFixAstra.lean`: 실패 넷. `Joint` 인수(위와 같음). `pad_derived`의 인덱스(RtErr 11 → 15로 newobject가 89 → 93). `sc_object_short`(블록 57바이트)와 `sc_output_overlaps_object`는 astra 발견 3을 재현하던 정리다. 증인을 고쳐 이제 거짓이다(의도한 실패).
  - `review/ReviewSHashFixAstra.lean`: 통과.
- 새 회귀 파일 `lean/tools/RegressFix2.lean`: 위 항목을 바뀐 계약으로 다시 적고, 고친 발견을 정리로 적는다(`sc_object_whole` 64바이트, `sc_output_after_object`, `ne_objects_apart`). 새 정리·증인 18개의 공리가 표준 셋이다. 오류 없음.
- 자기 시험 24개, 부정 시험 16개 기대대로, go test PASS.

## 3. 증인과 계약 조합의 범위

- `joint_models`: makeslice(1바이트), memmove, growslice, newobject 16, `FmtErrorfNilC`, `FmtErrorfWC`(모든 fs·RO·MsgIn), `FmtErrorfDWC`(모든 fs·tw), `ConvT64C bumpHeap`, `ValidateBitlistC`, `ValidateBitlistErrC`, 한 Host·한 힙.
- 한 증인 안의 조합: WitBlR·WitBlRI(ValidateBitlist 무효 + fmt `%w` + rodata 메시지 셋), WitLuTb·WitLuMa(convT64 bump 상자 + fmt `%d %w`), WitLcA*(makeslice 두 지점 + newobject 24 + 실제 ListU64), WitLuComp·WitScComp(디코더 + 인코더 + 실제 중간 메모리).
- 증인 Host는 Kraken의 추상 Host다(지시어 하나 = 주소 하나). ELF 연결은 링크 검사가 맡는다.

## 4. 게이트 1 표 (X9)

열의 뜻:
- "거부 경로": 디코더 오류 분기 중 기계어 정리로 닫힌 것 / 전체(Go 소스 기준). 남은 경로를 적는다.
- "증인": 빈·1·최대와 안쪽 길이. "Go 값": goval 결과(위반 수, 미검사).
- "추상 모델": 그 타입의 정리가 기대는 계약과 그 모델. Go 정교화는 없다(모든 행 공통).
- "미검사": goval이 읽지 못한 값, 또는 이 세션에서 검사하지 않은 것.
- "조합": 두 호출 조합 정리와 전체 전제 증인.
- "사후": 주 정리 결론의 `R` 보존(X7 표).

| 타입 | 수용 방향 | 거부 경로 (닫힘 / 남음) | 증인 | Go 값 | 추상 모델 | 미검사 | 부정 시험 | 조합 | 사후 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Scalars | EthLib→기계어 + bool 거부(EthLib 거부 정리 포함). 양방향 정리 하나는 없다 | 2/2: 크기, bool > 1 | 고정(수용, 거부, 마샬, 조합) | 위반 0 | 없음(계약 호출 없음) | 전역 오류 값 | scbool, scrbword | `sc_unmarshal_then_marshal` + WitScComp | 수용·마샬·bool 거부 정확, 크기 레지스터만 |
| FixedVec | EthLib→기계어 | 1/1: 크기 | 고정 | 위반 0 | makeslice, memmove | — | loop, control | 없음 | `R` 보존 + True |
| ListU64 | EthLib→기계어 | 4/4: 짧음, 오프셋, 정렬, 초과 | 0·1·16, 거부 둘 | 위반 0 | makeslice, growslice, convT64(상자), fmt `%d %w` | — | offset, maxlen | `lu_unmarshal_then_marshal` + WitLuComp | 수용 정확, 나머지 `R` + True |
| BitVec | 양방향(1바이트) | 2/2: 크기, 패딩 | b < 16, 16 ≤ b | 위반 0 | fmt nil·`%w`, newobject 16 | — | vbvje, bvnochk | `bv_unmarshal_then_marshal`(증인 없음) | 수용·마샬 정확 |
| BitL | EthLib→기계어(규칙 동치) | 3/3: 짧음, 오프셋, ValidateBitlist 오류 | 1, 257바이트 / 2049비트, 꼬리 [0] | 위반 0 | ValidateBitlist 두 계약(rodata), growslice, memmove, fmt `%w` | — | gsnum, blmnochk, blrity | 없음 | `R` 보존 |
| Nested | EthLib→기계어 | 2/4. 남음: S 오류, L 오류(래핑) | 0·1·16 | 위반 0 | newobject 24, Scalars·ListU64 함수 명세 | — | neoff | 없음 | 수용 `R` 보존, 마샬 `R` 없음 |
| List[container] | EthLib→기계어 | 5/9. 남음: 정렬, 원소 수(convT64), 원소 오프셋 순서, 원소 디코드 오류 | 바깥 0·1·4, 안쪽 1×1, 4×16, 0·1·16 | 위반 0 | makeslice 두 지점, newobject 16·24, fmt nil, ListU64 함수 명세 | 힙 소비는 계산값 | nilerr | 없음 | `R` 보존, 죽은 스택 True |
| Prysm 축약 Checkpoint | EthLib→기계어 | 1/1: 크기 | 고정 | 위반 0(마샬 dst 기호 길이 미검사) | makeslice, memmove | WitCpM dst | cplen | 없음 | `R` 보존 |
| Prysm 축약 AttestationData | EthLib→기계어 | 1/1: 크기(하위 Checkpoint 오류 미도달은 정리로 보이지 않았다) | 고정 | 위반 0 | makeslice, memmove, newobject 32 | — | adcopy | 없음 | `R` 보존 |

"완료 단위 전부 충족"이라고 쓸 수 있는 타입: Scalars, ListU64(두 타입 모두 6요소, 조합 전체 증인 포함).
나머지 타입은 6요소를 갖추되 조합이 없거나(FixedVec, BitL, Nested, ListC, Checkpoint, AttestationData) 거부 경로가 남는다(Nested, ListC).
범위 밖으로 옮긴 조건: 하드웨어 대조, Go 런타임 정교화, ListC·Nested의 남은 거부 경로, NeMarshal 사후조건(0절).

## 5. 필수 수정 8개 (astra 재증명 수정 8절)

| # | 필수 수정 | 상태 | 근거 |
| --- | --- | --- | --- |
| 1 | SHash 문자열 인식 | 완료 | `check.py:133`, `:411`. 자기 시험 "SHash comment inside a string" |
| 2 | 형식 상수 전체 값과 모든 참조, Go 파서, 역할 목록 | 완료 | `check.py:95`, `:148`, `:178`, `:196`, `:457`, `golits.go`. 자기 시험 9개 |
| 3 | Go 객체 크기를 실제 배치에서, 패딩·겹침 | 완료 | `layout.go`, `layout.json`, `goval.py:224–330`. 79개 위반 0 |
| 4 | fmt 계약을 실제 형식·인수로, 상자 내용과 자원 | 완료(신뢰 항목 남음: 실제 할당량, GC, 결과 객체) | `Contracts.lean:91–245`, `RtErr.lean:52–150`, `LuRejectCall.lean:117`, `:376`, 링크 (h) |
| 5 | rodata 공유 자원, 안전한 프레임 | 완료(어느 입력이 어느 메시지인지는 말하지 않음) | `Vbl.lean:76–125`, `BlMarshal.lean`, `BlReject.lean`, `RegressFix2.lean` |
| 6 | ListC 비어 있지 않은 원소, 최대 안쪽 길이 | 완료 | WitLcA1x1/4x16/Mix, WitLcM1x1/4x16/Mix |
| 7 | 사후 자원 보존, 전체 조합 증인, 중간 상태 | 부분 | Sc 마샬 정확, 6개 정리 `R` 추가, 조합 증인 둘. 남음: `ne_marshal_main`, ListC 죽은 스택, 크기 정리 |
| 8 | 게이트 표 | 완료 | 4절 |

정리 전제·결론 변화(약화 없음, 강화와 확장만):
- ListU64 거부 둘: 전제에 `StaticBox` 조각, 예산 `msg + 8276`·`msg + 8288`(이전 `msg + 8268`), `fs` 인수 → 상수. 결론 같음.
- BitL 인코더 거부: 전제에 `vblRO`. 결론 같음.
- BitVec 디코더 거부: fmt 인수 모양만 바뀜. 전제·결론 같음.
- 결론 강화: 2절 X7의 9개 정리(BlSpec·NeSpec·LcAcceptSpec·ScSpec 전파 포함).

## 6. 계약 변경 목록과 모델

CONTRACTS.md 1e절에 모았다.

| 계약 | 모델 | 공동 만족 |
| --- | --- | --- |
| `FmtErrorfWC Heap fs RO MsgIn S` | `rt_errorf_w`(모든 인수) | `joint_models` |
| `FmtErrorfDWC Heap fs tw S`(새) | `rt_errorf_dw` | `joint_models` |
| `ConvT64C Heap S`(상자) | `rt_convT64`(bump 힙 8바이트에 v) | `joint_models` |
| `ValidateBitlistErrC Heap S`(rodata) | `rt_validate_bitlist_err`(힙 경우, 빈 메시지) | `joint_models` |

`not_joint_false`는 모든 인수에 대해 닫힌다. `RegressFix2.lean`은 정리가 쓰는 두 조합(`blFmtB vblRO VblMsg`, `bvFmtJ bvRO BvMsg`)으로 다시 적용한다.

## 7. 증인 목록 (이번에 만들거나 다시 만든 것)

| 파일 | 정리 | 길이/값 | Go 값 |
| --- | --- | --- | --- |
| WitScA, WitScM, WitNeM0/1/16 | 수용, 마샬 | 패딩 7바이트 추가 | 위반 0 |
| WitBl1, WitBl257, WitBlM1, WitBlM257, WitBv, WitLcA1, WitLcA4, WitLcE, WitLcP, WitLcT, WitLcZ, WitLuG, WitNe0/1/16, WitVbvR, WitCpMR, WitLuMR, WitCp, WitFv, WitAd | 기존 | 정렬·경계 수정 | 위반 0 |
| WitBlR | `bl_marshal_reject_main` | 2049비트, rodata 셋, 타입 기술자 | 위반 0 |
| WitBvR | `bv_reject_padding_main` | 16 ≤ b, 타입 기술자 | 위반 0 |
| WitLuTb, WitLuMa | ListU64 거부 | n = 17, len 5. bump 힙 8296, 정적 상자 | 위반 0 |
| WitScRB | `sc_reject_bool_main` | 모든 e > 1 | 위반 0 |
| WitBlRI | `bl_reject_invalid_main` | 꼬리 [0] | 위반 0 |
| WitLcA1x1, WitLcA4x16, WitLcAMix | `lc_accept_main` | 2절 X6 표 | 위반 0 |
| WitLcM1x1, WitLcM4x16, WitLcMMix | `lc_marshal_main` | 2절 X6 표 | 위반 0 |
| WitLuComp | `lu_unmarshal_then_marshal` | n = 1 | 위반 0 |
| WitScComp | `sc_unmarshal_then_marshal` | bool 1 | 위반 0 |

미검사: `WitCpM`(dst 기호 길이 `pre`), 1a `Witness.lean`(기호 n). 재증명 수정 때 손으로 확인한 범위(astra 4절)와 같다.

## 8. 생성기 요청 목록

새 생성기 결함은 찾지 않았다.
관찰(결함 아님): ListC 디코더의 원소 오프셋 순서 오류는 `%d` 두 개를 쓰는 `fmt.Errorf`라 `convT64` 두 번과 할당이 있다. 증명 비용의 관찰이다.

## 9. Kraken 요청 목록

- `bsr` 파싱(1b부터). ValidateBitlist가 계약으로 남는 이유다.
- `ecancel`이 `StaticBox (-4 + rcx)` 같은 원자에서 재귀 한도에 걸렸다(LuRejectCall misaligned). `generalize`로 피했다. 원자 정규화 진단이 있으면 좋다.
- `ac_rfl`·`ecancel`의 `@Eq DataMem`과 `@Eq (Std.ExtHashMap …)` 원자 구분(재증명 수정과 같다).
- 구조체 갱신 식의 필드를 여러 줄에 쓰면 열 위치 때문에 파싱 오류가 났다(Lean 문법, Kraken 아님. 기록용).

## 10. 이견

1. **X1 방법.** 브리프가 추천한 (b)를 택했다. 문자열 상태 스캐너는 X2의 Lean 주석 제거에 썼다.
2. **X3 실행 방식.** `GOOS=linux GOARCH=amd64` 바이너리를 이 호스트(arm64 macOS)에서 실행할 수 없다. go/types의 gc amd64 크기 규칙으로 `unsafe.*` 식의 상수 값을 얻었다. 컴파일러가 접는 값과 같은 규칙이라고 판단하지만 교차 컴파일 단언으로 따로 확인하지는 않았다.
3. **X3 범위 확장.** 브리프의 검사 항목 외에 rsp 정렬과 `s_mem` 조각의 객체 경계 검사를 더했다. 그래서 위반 수가 astra의 셋보다 많았다(28개 파일).
4. **X4 설계.** fmt 계약을 둘로 나눴다(`%w` 하나 / `%d %w`). `%w` 계약은 메시지 출처를 `RO`와 `MsgIn` 정의 인수로 받는다. 호출자마다 출처가 달라서다(BitVec rodata 하나, BitL rodata 셋 또는 힙, ListU64 전역 오류 메시지).
5. **X5 메시지와 입력.** `VblMsg`는 메시지를 입력 조건과 묶지 않는다. 묶으면 모델 asm을 경우마다 바꿔야 한다. 모델은 `%d` 경우(빈 메시지)로 만족한다.
6. **X7 범위.** `lcl_loop`와 `ne_marshal_main`의 하위 단계를 다시 쓰지 않았다. 그래서 #7은 부분이다.
7. **X8c 미수행.** 5절과 2절 X8. 맥락 예산 때문에 문서와 회귀를 먼저 끝냈다.
8. **크기 정리의 프레임.** 크기 정리 11개는 메모리 결론이 없거나 `R` 이름을 쓰지 않는다. 이번 브리프의 사후조건 기준으로는 미달이지만 손대지 않았다.

## 11. 재현

```sh
cd fv/kraken/lean && lake build                    # 856 jobs
sh tools/axioms.sh                                  # TOTAL 1583 NONSTANDARD 0; ALL-DECLARATIONS TOTAL 8028 NONSTANDARD 0
python3 tools/wit/goval.py                          # 79 witness files, 0 with a violation, 2 not checked
lake env lean tools/RegressFix2.lean                # 오류 없음, 공리 표준
cd ../../.. && go run fv/kraken/lean/tools/wit/layout.go > fv/kraken/lean/tools/wit/layout.json   # 배치 재생성
python3 fv/kraken/link/check.py fv/kraken/link/out            # PASS all, BUNDLE
python3 fv/kraken/link/check.py --selftest fv/kraken/link/out  # 24 cases
fv/kraken/negative/run.sh <scratch-dir>                        # negative/RESULT, 16 cases
GOROOT=$(go env GOROOT) go test ./fv/kraken/semtest/           # F1, F2 PASS
# 증인 재생성: cd fv/kraken/lean && python3 tools/wit/<w*.py> tools/wit [인수] (tools/wit/README.md)
```

## 12. 1c 증명 생성기 설계 입력

REPORT-1b-reprove-fix 10절 18개에 astra 재증명 수정 9절 보완과 이번 세션의 관찰을 합쳤다.

1. **스택 좌표 세 가지.** 함수 진입 rsp, 호출 직전 rsp, 피호출자 진입 rsp(= 호출 직전 − 8). 좌표 변환과 반환 슬롯 관계를 작은 정리로 고정한다(astra).
2. **계약 조합을 한 Host·한 힙에서 검사한다.** 공동 Host 검사와 실제 할당 자원을 구분한다. `emp` 힙의 숫자 예산을 물리 공간으로 세지 않는다(astra). 이번에 ListU64 증인을 실제 bump 힙으로 바꿨다.
3. **기호 길이 제한은 구체 배치 생성기에만 적용한다**(astra).
4. **자동 완료표.** 선언 의존성과 전체 적용을 기록하고 함수 명세 아래의 외부 계약도 전파한다(astra).
5. **틈은 프레임으로 넘긴다.** 주소 겹침과 타입 별칭 정규화를 생성 단계에서 진단한다(astra). 이번 goval의 객체·조각 경계 검사를 생성기 안으로 옮긴다.
6. **원자 표기를 한곳에서 정규화한다.** 증인 값은 `n#64` 꼴로 쓴다(`(n : BitVec 64)`는 ecancel에서 다른 원자가 됐다, 이번 측정). `StaticBox (-4 + x)` 같은 원자는 `generalize`로 불투명하게 둔다.
7. **배치는 해석된 Lean 식에서 뽑는다.** 이번에 고친 텍스트 파서 우회(문자열 안 주석, 접미 식, 공백)를 기준 사례로 삼는다(astra).
8. **함수 명세는 정리에서 유도한다**(`*_holds`). 하위 계약 의존성도 완료표에 남긴다.
9. **조합 검사.** `hupd` 존재, 전체 조합 증인, 실제 호출자 실행을 각각 완료 항목으로 둔다(astra). 이번 WitLuComp·WitScComp는 앞의 둘이다. 셋째(호출자 명령 실행)는 없다.
10. **Go 값.** 크기·정렬·패딩·bool·유효 타입 워드를 포함하고 `layout.json`(gc amd64 크기)에서 읽는다. 검사를 건너뛴 값은 완료로 표시하지 않는다(astra).
11. **오류 값을 자원으로.** rodata 공유(`vblRO`), 상자 값(`BoxIn`, `StaticBox`), fmt 형식과 인수 타입(`luTW`), 전역 오류 객체를 호출 그래프에 넣는다(astra). 형식은 정의 인수로 고정한다.
12. **링크 검사 대상은 선언 역할과 출처에서 만든다**(astra). 이번 (g)의 역할 분류와 (h)의 런타임 데이터 검사를 일반화한다.
13. **실행 기록 하나에 해시를 묶는다.** 도구 PASS와 함께 공격 변이와 기대 실패 위치도 묶는다(astra).
14. **생성기 수정에는 Go 회귀 시험과 Lean 거부 정리를 함께 갱신한다.**
15. **잘못된 배치의 시간 초과를 증명 난이도로 분류하지 않는다.** 이번 큰 리스트 상수의 `rfl` 재귀 한도는 배치가 아니라 설정 문제였다.
16. **증인 생성 설정을 저장한다.** 설정 없는 WitCp·WitFv·WitAd·WitCpM이 남았다. 재생성 일치를 확인한다(astra).
17. **vcgen 레이블 불변식의 진입·보존 목표를 따로 측정한다**(astra).
18. **시간을 외삽하지 않는다.** 이번 1시간 30분은 따뜻한 캐시와 재사용한 틀의 기록이다.
19. **ListC 자동화 순서**(astra): Scalars 수용·거부 → ListU64 0·1·16과 growslice 지점 → ListC 바깥 0·1·4 × 안쪽 0·1·16 수작업 사례(이번에 수용·마샬 완료) → 혼합 길이와 최대 길이의 오프셋·힙 소비·오류 전달(오류 전달은 남음, X8c) → 생성기로 재현하고 두 호출 조합까지 → 축약 Checkpoint·AttestationData.
20. **1c 고정 기준**(astra): 생성기 소스 `698c202`와 병합 기준 `2d0150b` 구분, Go 1.26.3 linux/amd64 GOAMD64=v1 purego trimpath CGO_ENABLED=0, Kraken `6064eec`, EthLib `8621856`, Lean nightly-2026-09-21, Prysm v7.1.8 `51b5a75`의 축약 두 타입. protobuf 필드를 포함한 실제 Prysm 바이너리 증명으로 이름을 바꾸지 않는다. 범위는 코덱이다.
21. **이번 결과를 완료된 게이트 1의 기준점으로 쓰지 않는다.** 게이트 1은 미통과다(0절).
