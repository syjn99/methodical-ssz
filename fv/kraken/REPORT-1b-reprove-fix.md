# REPORT-1b-reprove-fix: 재증명의 필수 수정과 게이트 잔여

기준: 브랜치 `syjn99/ssz-fv-reprove-fix`, 시작 `df024af`(재증명 `440e079` + 리뷰 두 편).
Kraken `6064eec`(main), Lean `nightly-2026-09-21`, EthLib `8621856`, Go 1.26.3, `GOAMD64=v1`.
ELF sha256 `9c850c97…c501`(바뀌지 않았다. 대상 Go 코드와 생성기는 고치지 않았다).
작성 2026-11-06.
시각은 커밋 시각(IST)이다. 외삽하지 않는다.

## 0. 판정

**조건부. 게이트 1은 완료 단위 기준으로 조건부 통과다(자평, 리뷰 전).**

완료 단위(1절)의 다섯 요소와 이번에 더한 Go 값 열을 모든 주 정리 53개와 `lum_grow_site`가 갖춘다.
리뷰 두 편의 필수 수정 7개를 모두 처리했다. 그중 1개(오류 인터페이스, #5)는 범위가 부분이다(5절 표).

조건(게이트 1의 범위 밖으로 남는 것):

1. 디코더의 EthLib 양방향 수용은 BitVec(1바이트)에서만 정리로 닫혔다. 다른 타입은 "EthLib가 받으면 기계어가 받는다"와 4절 표의 거부 경로만 있다. BitL의 `blValid_iff`는 규칙 동치이고 디코더 양방향이 아니다.
2. 런타임 계약(makeslice, memmove, growslice, newobject, fmt.errorf, convT64, ValidateBitlist)은 추상 모델로 만족 가능성만 보였다. Go 런타임의 정교화는 없다. 형식 전제로 옮기지 못한 신뢰 항목은 CONTRACTS.md 1d절에 있다(rodata 메시지, fmt의 실제 할당량, convT64 상자 내용, GC 부재).
3. 후속 호출 조합은 BitVec와 ListU64 두 타입만 있다. 호출자의 CALL은 `hupd` 관계로 두었다(호출자 기계어의 연속 실행 정리가 아니다).
4. x86-64 하드웨어 대조를 하지 않았다(이 호스트는 arm64).
5. 4절 표에서 "닫히지 않음"인 디코더 거부 경로(Scalars bool, Nested 하위 호출 오류, ListC 일부, BitL ValidateBitlist 오류)는 정리가 없다.

수치(마지막 실행, 11절 재현):

- `lake build`: 830 jobs, 성공.
- 공리 두 범위: 정리 `TOTAL 1432 NONSTANDARD 0`(`AXIOMS.txt`), 모든 선언 `TOTAL 7334 NONSTANDARD 0`(`AXIOMS-ALL.txt`).
- 링크 검사 PASS(검사 (a)–(g)). 자기 시험 14개 기대대로.
- 부정 시험 14개 기대대로(`negative/RESULT`, 전체 실행 8분 21초).
- 증인 파일 69개, 실행 증인 선언(`*_runs`) 70개. Go 값 검사 위반 0(`lean/tools/wit/goval-result.txt`).
- `GOROOT=$(go env GOROOT) go test ./fv/kraken/semtest/`: PASS.
- B0: VC 20, `kfinish`로 닫힘 3, 열림 17(7.1 s).
- 세션 시간: 02:09(X0 시작)부터 03:16(마지막 증명 커밋)까지 1시간 7분. 그 뒤 부정 시험 전체 재실행과 보고서.

## 1. 완료 단위

재증명과 같은 다섯 요소에 하나를 더했다.

1. 계약 또는 정리.
2. 구체 Host에서 전제 전체의 증인. 가변 길이는 빈 값, 1개, 최대.
3. 기계어 정리.
4. 링크 검사 PASS.
5. 부정 시험: 변이가 지정 정리 안에서 실패하고 대조군이 통과한다.
6. **Go 값**(이번에 더함): 증인 상태의 인수 슬라이스, 수신자 슬라이스·포인터 필드가 Go 값이다. 슬라이스 헤더 (p, len, cap)는 len ≤ cap < 2^63이고, cap > 0이면 데이터 p .. p + cap·esz가 Host 메모리 블록 안에 있다. 주 정리는 더 넓은 기계 상태를 허용할 수 있다. 그래서 "추상 전제 만족"(요소 2)과 "Go 값"(요소 6)을 다른 열로 센다.

## 2. 항목별 결과

| 항목 | 커밋 | 시각 | 결과 |
| --- | --- | --- | --- |
| X0 | — | 02:09 | `.lake` 복사, 빌드 4.5초(따뜻한 캐시). 다른 Lean 빌드 없음 |
| X1, X2 | `879fc52` | 02:11 | 링크 검사 (f)·(g) 보강 |
| X3 | `1bdd58f` | 02:12 | semtest 회귀 시험 |
| X5 | `deb6fdc` | 02:43 | BitL·BitVec 오류 객체와 예산(X4의 WitBlR cap 포함) |
| X4 | `e275c57` | 02:43 | Go 값 검사기, 증인 27개 수정 |
| X9 | `118aae8` | 02:54 | 부정 시험 셋(전체 재실행 8분 4초 포함) |
| X8 | `4e350f3` | 02:59 | 증인 12개 |
| X10 | `114cff6` | 03:01 | ListU64 조합 |
| X6, X7 | `e5d7a89` | 03:03 | 문서 |
| X8 보강 | `7ed4082` | 03:05 | `vbv_reject_pad_main` 직접 증인, Scalars 부정 시험 |
| X5 잔여 | `11332e8` | 03:12 | ListU64 거부도 `FmtErrorfWC`, `FmtErrorfC` 삭제 |
| X7(B0) | `46cca80` | 03:16 | 레이블 불변식, VC 재측정 |

### X1. 링크 검사 (f) (astra 1)

- `lean_value`는 주석을 지운 `SHash.lean` 전체가 `module`, 정의 하나, 문자열 리스트 리터럴 하나와 정확히 맞아야 한다(`re.fullmatch`). 접미 연산과 추가 식·선언을 거부한다. Lean 파서는 만들지 않았다.
- 자기 시험에 `|>.take 0` 변이를 더했다. (f)에서 실패한다.
- `shash.sh`는 `LC_ALL=C`로 glob 순서를 고정한다(astra 5절 권고).

### X2. 링크 검사 (g) (astra 2)

- FMTS에 `blFmtB`("B: %w")를 넣었다. 사용 위치 둘(`BlMarshal.lean`)을 Lean 문장에서 읽는다.
- 길이만 고정하는 형식 문자열(`LuRejectCall`의 `fs` 둘)을 FMTLEN으로 검사한다: ELF의 그 오프셋·길이 바이트가 Go 소스의 `fmt.Errorf` 리터럴 전체와 같다.
- 목록 대조: 정리 파일(Wit*.lean 제외)의 모든 `go_string._+off`가 검사 목록에 있어야 한다. 빠지면 (g)가 실패한다.
- 자기 시험: `blFmtB` 값 66→67, 오프셋 526→527, 등록 누락. 모두 (g)에서 실패한다. 자기 시험은 14개다.

정리에 쓰인 고정 데이터와 검사 대상:

| 고정 데이터 | 쓰는 정리 | 검사 |
| --- | --- | --- |
| `lcFmtZero` @ `go_string._+39370` (53) | `lc_reject_zero_main`, LcSpec | (g) 값·오프셋·Go 리터럴 |
| `lcFmtShort` @ `+42000` (63) | `lc_reject_past/tail_main`, LcSpec | (g) |
| `vbvFmt` @ `+27706` (35) | `vbv_reject_pad_main`, `bv_reject_padding_main`, Vbv 결론의 문자열 헤더 (ptr, 35) | (g) |
| `bvFmtJ` @ `+511` (5) | `bv_reject_padding_main` | (g) |
| `blFmtB` @ `+526` (5) | `bl_marshal_reject_main`, `bl_marshal_overlong_rejected` | (g), **이번에 추가** |
| `fs` @ `+40290` (길이 56) | `lu_reject_toobig_main` | (g) FMTLEN, **이번에 추가** |
| `fs` @ `+42646` (길이 68) | `lu_reject_misaligned_main` | (g) FMTLEN, **이번에 추가** |
| itab 레이블 `go_itab._errors.errorString_error` | BitL·BitVec·ListU64·ListC 거부, ValidateBitlist 계약 | (b) 기호와 주소, (c) 신선성 |
| itab + 8의 타입 워드 | 같은 정리 | 값은 전제의 임의 리스트(`ity`, `t8`). 고정 데이터가 아니다 |
| `ssz.Err*` 전역 두 워드 | 거부 정리 | (b). 값은 전제(e0, e1) |
| `type__+…` 타입 기술자 | 계약 호출의 rax | (b). 계약 모델은 내용을 읽지 않는다 |
| `runtime.writeBarrier`, 스택 가드 | 대부분 | (b), 값은 전제 |

### X3. semtest (astra 5, Claude F-1)

- `f12_test.go`: F1은 256바이트 전수(0x00–0x0f 수용, 0x10–0xff 거부, 수용 값 확인). F2는 `[1]`·2047·2048비트 수용, 2049비트·258바이트·`[0]`·`[]` 거부를 인코더와 디코더 둘 다로 본다.
- 수정 전 반례는 커밋 `37efd44`에 있다(주석에 해시만).
- `cases.why`의 `bv_padding_counterexample`를 새 정리 이름으로 바꿨다. `gen-expected.sh`로 `expected.txt`를 다시 만들었다(`BV U 10`: `nil` → `other`).
- REPORT-1b-reprove 8절 재현에 go test를 더했다.

### X4. Go 값 (astra 4)

`WitBlR`의 수신자 헤더를 (p, 257, 257)로 고쳤다(X5 커밋).
`lean/tools/wit/goval.py`: 증인 파일의 `block`(`++` 사슬)과 시작 레지스터를 복원해 Go 값을 검사한다.
일부 증인은 생성 설정이 저장되지 않아(`WitAd`, `WitCp`, `WitFv`, `WitCpM`) 생성기 안이 아니라 생성된 파일을 검사한다(이견 1).

처음 실행의 위반과 처리:

| 증인 | 위반 | 처리 | 추상 전제 만족 | Go 값 |
| --- | --- | --- | --- | --- |
| `WitBlR` | 수신자 (p, 257, 0) | cap 257 | 이전에도 예 | 고친 뒤 예 |
| `WitAd`, `WitCp`, `WitFv` | 입력 cap 0 < len | rdi = len(파일 직접) | 예 | 예 |
| `WitBv`, `WitBvR`, `WitVbv` | 입력 cap 0 < 1 | cap 1(생성기) | 예 | 예 |
| `WitAdM` | BeaconBlockRoot cap 0, Source/Target Root의 cap 칸에 root 데이터(겹침) | cap 칸 셋(gap) | 예 | 예 |
| `WitCpM` | Root cap 칸에 root 데이터 | cap 칸, 주소 이동(파일 직접) | 예 | 예 |
| `WitFvM`, `WitLuM0/1/16`, `WitNeM0/1/16` | 수신자 슬라이스 cap 칸 없음 | cap 칸(gap) | 예 | 예 |
| `WitLuMR` | (nil, 17, ?) | 데이터 136바이트, cap 17 | 예 | 예 |
| `WitFvMR` | dst cap 64인데 데이터 32 | dst 64바이트 | 예 | 예 |
| `WitRj{Lu,Bl,Lc}Of` | 입력 len 32인데 4바이트만 | 32바이트 | 예 | 예 |
| `WitRjNeOf` | 입력 앞 24바이트가 스택 칸과 겹침 | 입력 32바이트 따로 | 예 | 예 |
| `WitSz{Sc,Fv,Bv,Cp,Ad}` | 수신자가 반환 슬롯을 가리킴 | nil 수신자(고정 크기 SizeSSZ는 읽지 않음) | 예 | 예 |
| `WitSz{Lu,Bl}` | 같음 | 완전한 헤더 (p, 3, 3)와 데이터 | 예 | 예 |
| `WitLuTb`, `WitLuMa` | 입력 len 140·5인데 4바이트 뒤가 다른 칸(검사기가 못 봄) | 입력 전체를 따로(X5 잔여 커밋) | 예 | 예 |

- 마지막 실행: 69개 파일 위반 0. `WitCpM`의 dst(기호 길이 `pre`)와 1a `Witness.lean`(기호 n)은 손으로 확인했다: len = cap − 40과 len = cap.
- 한계: 검사기는 "블록 안"만 본다. 서로 다른 값의 겹침은 보지 않는다. `WitLuTb`의 겹침은 손으로 찾았다(이견 1).
- 생성기 보강: gap 원자를 `Eq (α := Std.ExtHashMap (BitVec 64) UInt8)`로 쓴다. `sep_true`의 F 텍스트는 `@Eq DataMem`으로 정교화되어 `ac_rfl`이 다른 원자로 봤다(측정). `huN` 뒤 `BitVec.reduceAdd`를 한 번 더 한다. `gen`에 `heap_end`(힙을 블록 끝에)를 더했다.

### X5. 오류 인터페이스 적용 조건 (astra 3)

- `ValidateBitlistC S`를 입력으로 나눴다. 유효 입력: 전제 `blValid`, 결론 rax = 0, 할당 없음. 무효 입력 `ValidateBitlistErrC Heap S`: 예산 `8192 ≤ avail`, 결론 rax = itab, rbx = e, `ErrStr e sp msg`(16바이트 errorString + 메시지, msg ≤ 128), `avail' + 16 + msg ≤ avail ≤ avail' + 8192`.
- `ErrStr e sp msg`(Contracts): 객체 (sp, len)와 메시지 바이트.
- `FmtErrorfWC Heap S`: 마지막 인수 = (itab + 8의 타입 워드, e), `ErrStr`가 발자국에 있고 보존, 예산 `fs + msg + 8192 ≤ avail`. BitL·BitVec·ListU64의 모든 `%w` 호출이 쓴다. 제한 없는 `FmtErrorfC`와 `rt_errorf`는 지웠다.
- `VbvPadC`(실제 코드에서 유도): 오류 객체 = (`go_string._+27706`, 35). `bv_reject_padding_main`은 이것으로 `ErrStr`를 만든다(`bv_errstr`).
- ListU64 거부: 전역 오류의 첫 워드 e0 = errorString itab(전제 `hei`), 데이터 e1의 `ErrStr`, 예산 `msg + 8268 ≤ avail`.
- 모델: `RtVbl` 무효 분기가 bump 힙 16바이트(빈 메시지 errorString)를 쓴다. `rt_validate_bitlist`, `rt_validate_bitlist_err`, `rt_errorf_w`. `joint_models`는 아홉 계약을 한 Host·한 힙에서 함께 만족한다.
- 증인: `WitBlR`(힙 16640, `heap_end`), `WitBvR`(힙 8248), `WitLuTb`·`WitLuMa`(전역 오류 객체와 메시지 "err").
- 옮기지 못한 것(CONTRACTS 1d 표): rodata 메시지(계약은 힙 바이트로 모델한다. 실제 Go에 적용하려면 `F`가 rodata를 갖지 않아야 한다), fmt의 실제 할당량(예산은 코드를 읽은 값), convT64 상자 내용, GC 부재.

### X6. 문서 (astra 6)

- CONTRACTS.md: 오래된 행 넷(BitL 공동 증인, `bv_reject_padding_main`·`bl_marshal_reject_main` 증인, ListC 호출 지점 증인, memmove "X4")을 고쳤다. 새 계약 행과 1c 행을 더했다. 1d절을 "옮긴 것"과 "옮기지 못한 것"으로 나눴다. 4절에 Go 값 검사를 적었다.
- REPORT-1b-reprove 0절의 "필수 수정 1–7을 처리했다"를 표로 바꿨다(완료 5, 부분 2).

### X7. 문구와 B0 (astra 7)

- R5: "명령어 수와 니모닉 열은 같다. 피연산자와 저장 순서는 다르다. 새 ELF에 맞춰 재증명했다."
- B0: 레이블 `L_37`(bool 바이트 0)과 `L_3b`(합류)에 불변식 `ScInv`를 넣었다(rsp·rax·rbp·r14, 반환 슬롯, `Mem.Mapped`, `Mem.WritesOnly`, 필드 적재 등식, 바이트 15 조건).

| 명세 | VC | 닫힘 | 열림 |
| --- | --- | --- | --- |
| 재증명 R9(레이블 `False`) | 16 | 3 | 13 |
| 재증명 수정 X7(`ScInv`) | 20 | 3 | 17 |

- 열린 것의 종류(기본 `grind`로 근사): 메모리 매핑(`isSome`) 11, 레이블 가로채기 4, 레이블 진입 1. 남은 VC는 저장 뒤 적재와 `WritesOnly` 합성의 메모리 보조정리가 필요하다.
- 결론(main 유지)은 바뀌지 않는다. `vcgen/B0.md` 끝 절.

### X8. 증인 (게이트 잔여 1·2)

| 정리 | 증인 | 계약(한 Host·한 힙) | 길이 |
| --- | --- | --- | --- |
| `lc_accept_main` | `WitLcA1`, `WitLcA4` (빈 리스트 `WitLcE`) | `bump_makeslice`(두 호출 지점), `bump_newobject24`, `lu_uacc_holds`(실제 ListU64 디코더) | 0·1·4 원소 |
| `lc_marshal_main` | `WitLcM0/1/4` | 없음(빠른 경로) | 0·1·4 원소 |
| `lc_size_main` | `WitLcS0/1/4` | 없음 | 원소 길이 [], [1], [0,1,2,16] |
| `ne_size_main` | `WitNeS0/1/16` | 없음 | L 0·1·16 |
| `lum_grow_site` | `WitLuG` | `rt_growslice`, bump 힙 | dst (p, 2, 3), len + 4 = 6 > cap 3 |
| `vbv_reject_pad_main` | `WitVbvR`(직접, 이전에는 간접뿐) | `rt_errorf_nil`, `bump_newobject16` | 1바이트, 16 ≤ b |

- 모든 증인 상태가 Go 값이다. ListC 원소는 완전한 ListU64 객체(포인터, len, cap)와 데이터다.
- 느린 것은 없었다. 각 증인 파일은 수 초에 닫혔다. 실패해서 보존한 파일은 없다.
- 시도에서 배운 것: `interval_cases`가 이 모듈에서 보이지 않아 `match`로 바꿨다. `decide`는 증명 항 안의 자유 변수(`hi`)를 거부해 `rfl`로 바꿨다. gen의 쓰기 장벽 칸이 전제에 없으면 그 칸을 R로 넘긴다.

### X9. 부정 시험 (게이트 잔여 3)

| 이름 | 변이 | 지정 정리 | 결과 |
| --- | --- | --- | --- |
| `neoff` | Nested L 오프셋 비교 28 → 29 | `ne_accept_main` | 그 안에서 실패 |
| `cplen` | Checkpoint 크기 비교 40 → 41 | `cp_accept_main` | 그 안에서 실패 |
| `adcopy` | AttestationData BeaconBlockRoot 복사 32 → 31 | `ad_accept_main` | 그 안에서 실패 |
| `scbool` | Scalars bool 비교 1 → 2 | `sc_accept_main` | 그 안에서 실패(브리프 밖, 이견 4) |

전체 14개 기대대로(`negative/RESULT`).

### X10. 게이트 표와 조합

- 조합 `lu_unmarshal_then_marshal`(`Fk/Compose.lean`): ListU64 디코더가 `[4,0,0,0] ++ bs`를 받아 돌아온 뒤 같은 수신자로 인코더를 부르면 dst에 `[4,0,0,0] ++ bs`를 쓴다. 두 번째 호출의 전제는 가정하지 않는다. 수신자 (p, n, n), `bs`, 저장된 rbp, rsp + 16 spill, 스택 가드는 `lu_accept_main`의 결론에서 온다. 인코더의 rsp − 24, rsp − 16 칸은 디코더의 발자국 밖이라 호출자가 dst와 함께 R0로 넘긴다.
- 게이트 표는 4절이다.

## 3. 증인과 계약 조합의 범위

- `joint_models`: makeslice(1바이트), memmove, growslice, newobject 16, `FmtErrorfNilC`, `FmtErrorfWC`, convT64, `ValidateBitlistC`, `ValidateBitlistErrC`, 한 Host·한 힙.
- 한 증인 안의 조합: `WitBlR`(ValidateBitlist 무효 + fmt %w, 한 힙), `WitBvR`·`WitVbvR`(실제 ValidateBitvector + fmt nil + newobject 16), `WitLcA*`(makeslice 두 지점 + newobject 24 + 실제 ListU64), `WitBl1/257`(ValidateBitlist + growslice + memmove), `WitLuG`(growslice), `WitLuTb`·`WitLuMa`(convT64 + fmt %w).
- 한 Host에 newobject 모델은 하나다(같은 레이블). 16·24·32를 한 증인에서 함께 쓰지 않는다.
- 증인 Host는 Kraken의 추상 Host다(지시어 하나 = 주소 하나). ELF 연결은 링크 검사가 맡는다.

## 4. 게이트 1 표 (완료 단위 기준)

"수용 방향": `EthLib→기계어`는 EthLib가 받는 입력에서 기계어가 nil을 돌려준다는 정리다. `양방향`은 그 역(기계어가 nil이면 EthLib가 받는다)도 정리로 닫혔다는 뜻이다.
"거부 경로": 디코더의 오류 반환 분기 중 기계어 정리로 닫힌 것 / 전체(Go 소스 기준, 래핑 경로 포함).
"Go 값": 그 타입의 모든 증인이 1절 요소 6을 만족한다.
링크 검사는 모든 대상 함수에 PASS다.

| 타입 | 디코더 수용 | 수용 방향 | 디코더 거부 경로 | 인코더 | 증인(빈·1·최대) | Go 값 | 부정 시험 | 조합 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Scalars | `sc_accept_main` | EthLib→기계어 | 1/2: 크기. 닫히지 않음: bool > 1 | `sc_marshal_main` | 고정 | 예 | scbool | 없음 |
| FixedVec | `fv_accept_main` | EthLib→기계어 | 1/1: 크기 | `fv_marshal_main`, `…_reject_main`(len(W) ≠ 4) | 고정 | 예 | loop, control | 없음 |
| ListU64 | `lu_accept_main` | EthLib→기계어(EthLib 쪽 `lu_spec_accepts_iff`. 경로 정리를 합친 양방향 정리는 없다) | 4/4: 짧음, 오프셋, 정렬, 초과 | `lu_marshal_main`, `…_reject_main`, `lum_grow_site` | 0·1·16 | 예 | offset, maxlen | `lu_unmarshal_then_marshal` |
| BitVec | `bv_accept_main` | **양방향(1바이트)**: `bv_spec_accepts_iff` + 수용·거부 정리 | 2/2: 크기, 패딩 | `bv_marshal_main`(패딩 거부 정리 없음) | b < 16, 16 ≤ b | 예 | vbvje, bvnochk | `bv_unmarshal_then_marshal` |
| BitL | `bl_accept_main` | EthLib→기계어(규칙 동치 `blValid_iff`. 디코더 양방향으로 세지 않는다) | 2/3: 짧음, 오프셋. 닫히지 않음: ValidateBitlist 오류 | `bl_marshal_main`, `…_reject_main` | 1, 257바이트 / 2049비트 | 예 | gsnum, blmnochk | 없음 |
| Nested | `ne_accept_main` | EthLib→기계어 | 2/4: 짧음, 오프셋. 닫히지 않음: S 오류, L 오류(래핑) | `ne_marshal_main`, `ne_size_main` | 0·1·16 | 예 | **neoff** | 없음 |
| List[container] | `lc_accept_main`, `lc_accept_empty_main` | EthLib→기계어 | 5/9: 짧음, 오프셋, 꼬리, 0 오프셋, 끝 넘음. 닫히지 않음: 정렬·원소 수(convT64), 원소 오프셋 순서, 원소 디코드 오류 | `lc_marshal_main`(빠른 경로), `lc_size_main` | 0·1·4 | 예 | nilerr | 없음 |
| Prysm 축약 Checkpoint | `cp_accept_main` | EthLib→기계어 | 1/1: 크기 | `cp_marshal_main`, `…_reject_main` | 고정 | 예 | **cplen** | 없음 |
| Prysm 축약 AttestationData | `ad_accept_main` | EthLib→기계어 | 1/1: 크기(하위 Checkpoint 오류는 40바이트 고정이라 도달하지 않는다. 정리로 보이지 않았다) | `ad_marshal_main`(Root 길이 거부 정리 없음) | 고정 | 예 | **adcopy** | 없음 |

게이트 1 판정: **완료 단위 기준 조건부 통과(자평).**
조건은 0절 1–5다.
리뷰 전이다.
리뷰가 "게이트 1에는 양방향 수용이나 모든 거부 경로가 필요하다"고 정하면 판정은 미통과로 바뀐다.

## 5. 필수 수정 7개 (astra 재증명 9절)

| # | 필수 수정 | 상태 | 근거 |
| --- | --- | --- | --- |
| 1 | SHash 정의 전체 검사, `.take 0` 시험 | 완료 | X1 |
| 2 | `blFmtB`를 (g)에, 값·오프셋 변이 | 완료 | X2(등록 누락 변이와 목록 대조도) |
| 3 | F1·F2 Go 시험을 거부 동작으로 | 완료 | X3 |
| 4 | `WitBlR` 용량, Go 값 검사 | 완료 | X4(증인 27개 수정, 검사기는 겹침을 보지 않는다) |
| 5 | 오류 인터페이스와 fmt 적용 조건 | 부분 | X5: 데이터 포인터, 오류 객체, 예산, `%w` 형태를 형식 전제로. rodata 메시지·fmt 실제 할당량·GC·convT64 상자는 신뢰 항목 |
| 6 | CONTRACTS 오래된 행, "1–7 처리" 문구 | 완료 | X6 |
| 7 | G3 문구, B0 불변식 | 완료 | X7: 문구를 고쳤다. 불변식을 넣고 다시 셌다(VC 20, 닫힘 3, 열림 17). 남은 VC를 닫는 일은 범위 밖이다 |

게이트 최소 잔여 6개(astra 9절):

| # | 잔여 | 상태 |
| --- | --- | --- |
| 1 | ListC 수용·마샬·크기, Nested 크기, `lum_grow_site` 증인 | 완료(X8) |
| 2 | 빈·1·최대 | 완료(X8) |
| 3 | Nested·Checkpoint·AttestationData 부정 시험 | 완료(X9) |
| 4 | 타입별 후속 호출 조합 | 부분: BitVec, ListU64 |
| 5 | Go 불변식을 형식 전제로 | 부분: 오류 경로(X5). 슬라이스 불변식은 증인 검사(X4)이고 주 정리 전제가 아니다 |
| 6 | 수용 방향·거부 범위 표 | 완료(4절) |

## 6. 생성기 요청 목록

새 생성기 결함은 찾지 않았다.
관찰(결함 아님):

- BitVec 인코더는 `ValidateBitvector(c.J, 4)` 뒤 `len(c.J) != 1` 검사를 그대로 둔다(재증명 관찰과 같다. 정리로 확인하지 않았다).
- 디코더 오류 경로 중 정리가 없는 것은 4절 표에 있다. 생성기 동작의 문제로 보지 않는다.

## 7. Kraken 요청 목록

- `bsr` 파싱(1b부터). `ssz.ValidateBitlist`가 계약으로 남는 이유다.
- `ac_rfl`·`ecancel`의 원자 비교가 `@Eq DataMem`과 `@Eq (Std.ExtHashMap (BitVec 64) UInt8)`를 다른 원자로 본다(X4 측정). `DataMem`은 약어다. 정규화하거나 진단에서 타입 차이를 보여 주면 도움이 된다.
- `ecancel` PANIC(`Lean.Expr.appFn!`, 재증명과 같다).
- vcgen: cfg 불변식에 메모리 관계(`Mem.WritesOnly`, 저장 뒤 적재)를 쓴 예제와, 저장 뒤 `isSome`·`WritesOnly` 합성 보조정리의 `grind` 집합.

## 8. 이견

1. **X4 검사 위치.** 브리프는 증인 생성기 안의 검사를 말한다. 일부 증인은 생성 설정이 없어 생성된 Lean 파일을 읽는 검사기(`goval.py`)로 했다. 생성기도 고쳤다. 검사기는 값 사이의 겹침을 보지 않는다. `WitLuTb`·`WitLuMa`의 버퍼 겹침은 손으로 찾았다.
2. **X5 계약 모양.** `ValidateBitlistC`에 rbx 결론을 더하는 대신 입력별 두 계약으로 나눴다. 무효 경로는 할당이 있어 같은 `F` 보존을 말할 수 없다. 모델의 오류 메시지는 빈 문자열이다(최소 모델, 유효한 Go 값). `FmtErrorfC`는 지웠다.
3. **X8 원소 내용.** ListC 수용·마샬 증인의 원소는 빈 ListU64다. 원소 최대 길이(16)는 `lc_size_main` 증인([0,1,2,16])과 ListU64 증인이 덮는다.
4. **브리프 밖 추가.** `vbv_reject_pad_main` 직접 증인(`WitVbvR`)과 Scalars 부정 시험(`scbool`). 재증명 게이트 표에 Scalars 행이 없었다.
5. **X10 조합 범위.** 호출자 CALL은 `hupd` 관계로 둔다(BitVec 조합과 같다). 호출자 기계어의 연속 실행 정리는 아니다.
6. **B0 VC 종류.** 종류별 수는 `kfinish` 대신 기본 `grind`로 닫아 본 근사다(닫힘 4 대 3).
7. **게이트 판정.** 완료 단위를 모두 갖췄으므로 조건부 통과로 자평했다. 양방향 수용과 모든 거부 경로를 게이트에 넣으면 미통과다(4절).

## 9. 재현

```sh
cd fv/kraken/lean && lake build                    # 830 jobs
sh tools/axioms.sh                                  # TOTAL 1432 NONSTANDARD 0; ALL-DECLARATIONS TOTAL 7334 NONSTANDARD 0
python3 tools/wit/goval.py                          # 69 witness files, 0 with a violation
cd ../../.. && python3 fv/kraken/link/check.py fv/kraken/link/out            # PASS all, BUNDLE
python3 fv/kraken/link/check.py --selftest fv/kraken/link/out                  # 14 cases
fv/kraken/negative/run.sh <scratch-dir>                                         # negative/RESULT, 14 cases
GOROOT=$(go env GOROOT) go test ./fv/kraken/semtest/                           # F1, F2 PASS
cd fv/kraken/vcgen && lake env lean Vg/ScAccept.lean   # 17 `finish` failures (B0, 기록용)
# 증인 재생성: cd fv/kraken/lean && python3 tools/wit/<w*.py> tools/wit [인수] (tools/wit/README.md)
```

## 10. 1c 증명 생성기 설계 입력 (REPORT-1b-reprove 9절 + astra 재증명 10절 + 이번 세션)

1. **스택 좌표 세 가지를 따로 둔다.** 함수 진입 rsp, 호출 직전 rsp, 피호출자 진입 rsp(= 호출 직전 − 8). 좌표 변환과 반환 슬롯 위치를 작은 정리로 고정한다.
2. **계약 조합을 한 Host·한 힙에서 검사한다.** 크기별 같은 레이블의 모델 충돌(newobject 16·24·32)을 검사한다. 필요하면 타입 기술자로 분기하는 모델을 쓴다.
3. **기호 길이는 구체 증인 배치 생성기에서만 거부한다.** 주 정리의 기호 길이까지 금지하지 않는다.
4. **자동 완료표.** 문자열 grep 대신 선언 의존성과 전체 적용을 기록한다. 함수 명세의 하위 계약 의존성을 전파한다. 변이 실패 위치와 대조군 결과를 연결한다.
5. **틈은 프레임으로 넘긴다.** 겹침, 주소 넘침, 조각 누락을 먼저 진단한다. gap 원자는 블록 원자와 같은 타입(`@Eq (Std.ExtHashMap …)`)으로 쓴다.
6. **원자 표기를 한곳에서 정규화한다.** `BitVec.ofNat`/`OfNat`/`#64` 형태, `huN` 뒤의 `reduceAdd`. 출력 문자열의 동일성에 의존하지 않는다.
7. **배치는 정리 문장에서 뽑는다.** 가능하면 Lean의 해석된 식에서 뽑는다. 임의 정리 문법을 정규식으로 처리하지 않는다.
8. **함수 명세는 정리에서 유도한다**(`*_holds`). 하위 계약 의존성도 완료표에 남긴다.
9. **조합 검사를 생성한다.** 중간 상태의 존재와 실제 호출자 실행을 함께 확인한다. 디코더 발자국 밖의 스택 칸은 호출자 프레임으로 넘긴다(`lu_unmarshal_then_marshal`).
10. **추상 전제 만족과 Go 값을 따로 검사한다.** 슬라이스 len ≤ cap < 2^63, 데이터가 블록 안, 포인터 객체가 블록 안. 값 사이의 겹침(입력 버퍼와 rodata 등)도 검사한다(이번 검사기에 없다).
11. **오류 값을 자원으로 둔다.** `%w` 인수는 (itab + 8의 타입 워드, e)와 `ErrStr e sp msg`. 상자 값, 문자열 자원, 전역 오류 객체를 호출 그래프에 넣는다. 할당 예산을 형식 전제로 둔다.
12. **링크 검사 대상과 증명의 고정 데이터 목록을 대조한다**(X2의 오프셋 목록 대조).
13. **실행 기록 하나에 해시를 묶는다.** 생성 Go, ELF, objdump, `.S`, SHash, 정리, 증인.
14. **생성기 수정에는 Go 회귀 시험과 Lean 거부 정리를 함께 갱신한다**(X3).
15. **잘못된 배치의 시간 초과를 증명 난이도나 기호 길이 한계로 분류하지 않는다.**
16. **증인 생성 설정을 저장한다.** 설정이 없는 증인은 다시 만들 수 없어 손으로 고쳤다(`WitAd`, `WitCp`, `WitFv`, `WitCpM`).
17. **vcgen 명세는 도달 가능한 모든 레이블에 메모리 관계 불변식을 둔다.** `False` 불변식은 명세 결함이다(B0).
18. **시간 기록.** 이번 1시간 7분은 따뜻한 캐시와 재사용한 틀의 기록이다. 일반 타입 비용으로 외삽하지 않는다. 1c는 ListC 증인을 수작업 기준 사례로 두고 그 형태를 자동화한다.
