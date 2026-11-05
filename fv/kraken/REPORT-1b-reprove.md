# REPORT-1b-reprove: 고친 생성기 위의 재증명 (Kraken x64)

기준: 브랜치 `syjn99/ssz-fv-reprove`, 시작 `2d0150b`(1b-fix `f452384` + 생성기 수정 `698c202` 병합).
Kraken `6064eec`(main), Lean `nightly-2026-09-21`, EthLib `8621856`, Go 1.26.3, `GOAMD64=v1`.
새 ELF sha256 `9c850c97…c501`(`link/out/build-ids.txt`).
작성 2026-11-06.
시각은 커밋 시각(IST)이다. 외삽하지 않는다.

## 0. 판정

**조건부. 게이트 1은 미통과다.**
F1·F2는 거부 정리로 바뀌었다.
`ssz.ValidateBitvector`는 계약이 아니라 기계어 정리다.
1b-fix 리뷰의 필수 수정 1–7을 처리했다.
주 정리 53개 중 48개에 직접 증인이 있다.
그러나 완료 단위의 다섯 요소를 모든 주 정리가 갖추지는 않았다.

조건(게이트 1 통과에 남은 것):

1. 증인 없는 주 정리 넷: `lc_accept_main`, `lc_marshal_main`, `lc_size_main`, `ne_size_main`. 그리고 `lum_grow_site`. `vbv_reject_pad_main`은 간접 증인뿐이다(3절).
2. 부정 시험이 없는 타입이 있다: Nested, Checkpoint, AttestationData(4절 표).
3. 디코더의 EthLib 양방향 수용은 BitVec(1바이트)과 BitL(규칙 동치)에서만 닫혔다. 다른 타입은 "EthLib가 받으면 기계어가 받는다"와 길이·오프셋 거부만 있다.
4. 계약은 추상 모델로만 만족 가능성을 보였다. Go 런타임의 정교화는 없다(CONTRACTS.md 1d절).
5. x86-64 하드웨어 대조를 하지 않았다(이 호스트는 arm64).

수치(마지막 실행, 7절 재현):

- `lake build`: 804 jobs, 성공.
- 공리 검사 두 범위: 정리 범위 `TOTAL 1296 NONSTANDARD 0`(`AXIOMS.txt`), 모든 선언 범위 `TOTAL 6648 NONSTANDARD 0`(`AXIOMS-ALL.txt`).
- 링크 검사 PASS(검사 (a)–(g)). 자기 시험 10개 기대대로.
- 부정 시험 10개 모두 기대대로(`negative/RESULT`): 변이 8개가 지정 정리 안에서 실패, 대조군 통과, 링크 변이 `nopret`이 (d)에서 실패. 전체 실행 5분 57초.
- 고유 주 정리(`*_main`) 53개. 직접 증인이 있는 것 48개. 실행 증인 선언(`*_runs`) 57개.
- 세션 시간: 2026-11-05 22:54(작업 시작)부터 2026-11-06 01:19(마지막 증명 커밋)까지 2시간 25분. 그 뒤 부정 시험 전체 실행과 보고서.

## 1. 완료 단위

1b-fix와 같다.

1. 계약 또는 정리.
2. 구체 Host에서 전제 전체의 증인. 가변 길이는 빈 값, 1개, 최대를 고정 길이로.
3. 기계어 정리.
4. 링크 검사 PASS.
5. 부정 시험: 변이가 지정 정리 안에서 실패하고 대조군이 통과한다.

## 2. 항목별 결과

### R0. 준비 (22:54–23:01)

- 1b-fix 워크트리의 `.lake`(798 MB)를 복사했다. `pgrep`으로 다른 Lean 빌드가 없음을 확인했다.
- `TOOLS.md` 첫 표에 생성기(`2d0150b`, 생성기 소스 = `698c202`), Go 1.26.3과 빌드 플래그, Prysm 축약 타입 출처(v7.1.8 `51b5a75`), gohashtree `v0.0.5-beta`, go-bitfield 버전, 대상 생성 명령을 고정했다.

### R1. 대상 재생성 (23:01, 커밋 `1b200b9`)

- 세 묶음을 `go run ./cmd/ssz gen`으로 다시 생성했다(명령은 TOOLS.md).
- 이전 생성 파일과의 차이는 브리프가 예상한 세 종류뿐이다.
  - BitVec 마샬·언마샬: `ssz.ValidateBitvector(…, 4)`와 `fmt.Errorf("J: %w")`.
  - BitL 마샬: `len(c.B) > 2048` 대신 `ssz.ValidateBitlist(c.B, 2048)`와 `fmt.Errorf("B: %w")`.
  - 첫 오프셋 `> size` 3줄 삭제 4곳.
  - Prysm 축약 타입의 생성 파일은 같다.
- `link/build.sh`가 `ssz.ValidateBitvector`도 덤프한다. 새 ELF, objdump, `.S`, `SHash.lean`을 다시 만들었다.
- 이전 ELF의 주소를 재사용하지 않았다. Lean 정리 안의 문자열 오프셋(`go_string._+…`, +40)과 기호 이름은 새 ELF에서 읽어 바꿨다.
- `conv.py`: 같은 주소의 기호 동률을 nm 출력 순서와 무관하게 고른다. `runtime.noptrbss`는 Go objdump와 같은 `runtime.zerobase`가 된다.
- 링크 검사 (a)–(g) PASS. 명령어 2927개 중 2877개 바이트 동일, 50개 패딩.

### R2. 링크 검사 보강 (23:01, `1b200b9`)

- (f): `SHash.lean`에서 주석을 지운 뒤 `Fk.sHash` 정의의 리스트 값만 읽는다. 정의가 정확히 하나여야 한다.
- 자기 시험에 "해시는 주석에, `Fk.sHash := ["end"]`" 변이를 더했다. (f)에서 실패한다(astra 1b-fix 발견 2).
- (g): 오프셋을 Lean 정리 문장(`<name>.At (label "go_string._" + off)`)에서 읽는다. Go 리터럴은 줄 번호가 아니라 내용으로 찾는다. 형식 문자열 넷(`lcFmtZero`, `lcFmtShort`, `vbvFmt`, `bvFmtJ`)을 대조한다.

### R3. ValidateBitvector (23:01–23:58, `2a97c5c`)

objdump로 먼저 확인했다: `bsr`가 없다. 시프트, 비교, `setne`, `shr %cl,%dl`뿐이다.
Kraken main으로 기계어 정리를 세웠다. 계약이 아니다.

| 정리 | 내용 |
| --- | --- |
| `vbv_accept_main` | 임의의 `bits`(`bits % 8 ≠ 0`), 길이 = `bits/8 + 1`, 마지막 바이트 `>> (bits % 8) = 0` → nil. 결론에 반환 슬롯, 저장된 rbp, spill, 스택 가드, 입력을 남긴다 |
| `vbv_reject_pad_main` | 같은 길이, 패딩 비트가 서면 `fmt.errorf`(인수 0개, nil) → `newobject` 16바이트 `errors.errorString` → itab. 계약 `FmtErrorfNilC`, `NewobjectC 16` |
| `VbvAccC`, `VbvPadC` | 위 정리에서 유도한 함수 명세(`vbv_acc_holds`, `vbv_pad_holds`). 가정이 아니다 |
| `bv_accept_main` | BitVec 디코더(새 프레임 0x48). `b < 16` → nil, J = (p, 1, 1). 스택 조각 9개를 존재 양화로 돌려준다 |
| `bv_reject_padding_main` | `16 ≤ b` → `VbvPadC` → itab+8 읽기 → `fmt.errorf("J: %w")`(`FmtErrorfC`) → 오류. F1 반례 정리 `bv_padding_counterexample`를 대체한다 |
| `bv_spec_one`, `bv_spec_accepts_iff` | EthLib는 `#[b]`를 `b < 16`일 때만 받는다 |
| `bv_marshal_main` | 인코더도 먼저 ValidateBitvector를 부른다. `b < 16` 전제가 생겼다. 스택 조각을 돌려준다 |

- 1바이트 입력에서 기계어의 수용 집합과 EthLib의 수용 집합이 같다: `bv_accept_main`(b < 16 → nil), `bv_reject_padding_main`(16 ≤ b → 오류), `bv_spec_accepts_iff`. `len ≠ 1`은 `bv_reject_size_main`.
- 인코더의 패딩 거부 정리(`bv_marshal`의 오류 경로)는 증명하지 않았다. 디코더만 했다.
- 일반 `bits`의 패딩 없는 경우(`bits % 8 = 0`)의 수용 정리는 쓰지 않았다. BitVec(bits = 4)에 필요 없다.

### R4. ValidateBitlist (23:58–00:32, `5d69ba3`)

`bsr`가 있어 계약으로 남는다.

- `Fk/Vbl.lean`(새 기반 모듈)로 `blValid`, `ValidateBitlistC`를 옮겼다.
- `blValid_iff`: 한도 2048에서 EthLib `unpackDelimited`가 받음 ⟺ `1 ≤ n ≤ 257 ∧ 마지막 바이트 ≠ 0 ∧ (n = 257 → 마지막 = 1)`. `highestBit`의 성질은 256개 값 전수 `decide`로 얻었다.
- 계약 강화: 무효 입력이면 rax = errorString itab. Go 1.26.3에서 이 함수의 오류는 모두 `%w` 없는 `fmt.Errorf`라 `errors.New`를 거친다. 이것은 신뢰 항목이다.
- 모델 `Fk/RtVbl.S`: `bsr` 없이 `blArith`를 계산한다. `rt_validate_bitlist`: 모든 `S`에서 `ValidateBitlistC`를 만족한다.
- BitL 마샬(새 코드: 오프셋 → ValidateBitlist → 바이트 append):
  - `bl_marshal_main`: `blValid` → `4 ‖ c.B`를 쓰고 nil. 스택 조각 14개를 돌려준다.
  - `bl_marshal_reject_main`: `¬ blValid` → itab+8 읽기 → `fmt.errorf("B: %w")` → nil 슬라이스와 오류.
  - `bl_marshal_rejects_overlong`: 258바이트와 2049비트는 무효, 2048비트는 유효.
  - `bl_marshal_overlong_rejected`: F2 입력(258바이트)에 거부 정리를 적용했다. 이전 반례 정리 `bl_marshal_overlong`를 대체한다.
- BitL 디코더: growslice 뒤 레지스터 배치(rdx와 rsi의 역할 교환)와 저장 순서만 바뀌었다. 증명 블록을 재배열했다.

### R5. 첫 오프셋 분기 삭제 (00:39, `d8650a9`)

- G3는 기계어를 바꾸지 않았다. 네 디코더의 새·옛 `.S`에서 명령어 수와 순서가 같다. 바뀐 것은 문자열 오프셋과 레지스터 배치뿐이다.
- 그래서 지울 정리가 없다. 브리프가 예로 든 `lc_reject_past`는 첫 **원소** 오프셋의 정리다. G3와 관계없다.
- SPEC.md 3절(오류표)과 3.1절에 적었다.

### R6. 증인 (00:39–01:19, 8커밋)

주 정리별 증인(직접). 생성기는 `lean/tools/wit/*.py`다.

| 정리 | 증인 | 계약을 얻는 방법 | 길이 |
| --- | --- | --- | --- |
| `sc_accept_main` | `WitScA` | — | 고정 |
| `sc_marshal_main` | `WitScM` | — | 고정 |
| `sc_size_main`, `sc_reject_size_main` | `WitSzSc`, `WitRjScSz` | — | — |
| `fv_accept_main` | `WitFv`(1b-fix) | `bump_makeslice`, `rt_memmove` | 고정 |
| `fv_marshal_main`, `fv_marshal_reject_main` | `WitFvM`, `WitFvMR` | `rt_memmove` | 고정 |
| `fv_size_main`, `fv_reject_size_main` | `WitSzFv`, `WitRjFvSz` | — | — |
| `lu_accept_main` | `Witness`(1a·1b) | `bump_makeslice` | 0·1·16 |
| `lu_marshal_main` | `WitLuM0/1/16` | — | 0·1·16 |
| `lu_marshal_reject_main` | `WitLuMR` | — | 17 |
| `lu_reject_short/offset_main` | `WitRjLuSh/Of` | — | — |
| `lu_reject_toobig_main`, `lu_reject_misaligned_main` | `WitLuTb`, `WitLuMa` | `rt_convT64`, `rt_errorf` 한 Host | — |
| `lu_size_main` | `WitSzLu` | — | n = 3 |
| `vbv_accept_main` | `WitVbv` | — | 1바이트 |
| `vbv_reject_pad_main` | 간접(`WitBvR`) | — | — |
| `bv_accept_main` | `WitBv` | `vbv_acc_holds`(실제 코드), `bump_makeslice1` | b < 16 |
| `bv_reject_padding_main` | `WitBvR` | `vbv_pad_holds`(실제 코드, 안에서 `rt_errorf_nil`·`bump_newobject16`), `rt_errorf` 한 힙 | 16 ≤ b |
| `bv_marshal_main` | `WitBvM` | `vbv_acc_holds` | b < 16 |
| `bv_size_main`, `bv_reject_size_main` | `WitSzBv`, `WitRjBvSz` | — | — |
| `bl_accept_main` | `WitBl1`, `WitBl257` | `rt_validate_bitlist`, `rt_growslice`, `rt_memmove` 한 힙 | 1바이트(빈 비트리스트 포함), 257바이트(2048비트) |
| `bl_marshal_main` | `WitBlM1`, `WitBlM257` | `rt_validate_bitlist`, `rt_memmove` | 1, 257 |
| `bl_marshal_reject_main` | `WitBlR` | `rt_validate_bitlist`, `rt_errorf` | 2049비트 |
| `bl_reject_short/offset_main`, `bl_size_main` | `WitRjBlSh/Of`, `WitSzBl` | — | — |
| `ne_accept_main` | `WitNe0/1/16`(1b-fix) | `sc_uacc_holds`, `lu_uacc_holds`, `bump_newobject24` | 0·1·16 |
| `ne_marshal_main` | `WitNeM0/1/16` | — | 0·1·16 |
| `ne_reject_short/offset_main` | `WitRjNeSh/Of` | — | — |
| `lc_accept_empty_main` | `WitLcE` | X15 = 0(`zmms0`) | 빈 리스트 |
| `lc_reject_zero/past/tail_main` | `WitLcZ/P/T` | `rt_errorf_nil`, `bump_newobject16` 한 힙 | — |
| `lc_reject_short/offset_main` | `WitRjLcSh/Of` | — | — |
| `cp_*`, `ad_*` | `WitCp`, `WitCpM`, `WitCpMR`, `WitAd`, `WitAdM`, `WitSzCp/Ad`, `WitRjCpSz/AdSz` | 1b-fix와 같음 + `rt_memmove` | 고정 |

증인 없음: `lc_accept_main`, `lc_marshal_main`, `lc_size_main`, `ne_size_main`, `lum_grow_site`.
`vbv_reject_pad_main`은 직접 증인이 없다. `WitBvR`의 실행이 호출 지점에서 그 전제를 모두 만족시킨다(간접).

측정에서 배운 것:

- **틈 조각.** 정리의 전제에 없는 메모리(프레임 사이의 틈)를 `sep_true`로 버리면, 소스에 쓴 리터럴 주소의 틈 조각을 `ac_rfl`·`ecancel`이 맞추지 못했다. 출력은 같았다. 틈을 정리의 프레임 `R`에 레지스터 기준 주소(`rsp − 24` 등)나 레이블 기준 주소로 넘기니 닫혔다. 1b-fix가 `lc_accept_empty_main`에서 만난 "표기가 같은 두 원자" 실패와 같은 원인으로 본다(추측). 이 방법으로 `WitLcE`가 닫혔다.
- **`BitVec.ofNat` 정규화.** 길이 보조정리(`bl2048_len`)로 고친 `BitVec.ofNat 64 257`은 `BitVec.ofNat_eq_ofNat`를 다시 적용해야 블록 쪽 원자와 같아진다. 둘 다 `257#64`로 보인다. 원자 집합을 `pp.explicit` 출력으로 비교해 찾았다.
- **`UInt64` 리터럴.** 블록에 `(1 : UInt64).toBitVec`을 쓰면 정규화되지 않는다. `(1 : BitVec 64)`로 쓴다.
- **레이블 덧셈.** `0x10000 + Int64.ofNat j`는 `Int64.toBitVec_add`로 풀리지 않을 때가 있다. 레이블 보조정리를 숫자 하나로 정리해 둔다(`label_itab`).
- **시간 초과는 배치 오류였다.** `lu_reject_misaligned` 증인이 heartbeat 400만에서 91초 시간 초과했다. 원인은 내 블록 배치였다(인수 배열을 `toobig`의 rsp − 72/−56에 두었다. 이 정리는 rsp − 40/−24를 쓴다). `exact`가 다른 주소의 항을 펼치다 멈췄다. 배치를 고치니 5초에 통과했다.
- **기호 길이.** 이번 증인은 모두 고정 길이다. 기호 길이 시도는 하지 않았다.

### R7. 조합 가능한 결론 (01:01–01:04, `153f5ea`, `6e029fc`)

| 정리 | 결론에 더한 것 |
| --- | --- |
| `vbv_accept_main`, `vbv_reject_pad_main` | 반환 슬롯, 저장된 rbp, spill, (거부) 프레임·호출 슬롯·scratch, 스택 가드, 입력, (거부) 오류 객체 |
| `bv_accept_main` | 스택 조각 9개(존재 양화), 스택 가드, 쓰기 장벽 |
| `bv_marshal_main` | 스택 조각 8개, 수신자 헤더, J 바이트, 스택 가드 |
| `bl_marshal_main` | 스택 조각 14개, 수신자 헤더, 스택 가드 |
| `ad_accept_main` | 입력 7조각, 스택 조각 9개, 반환 슬롯, 스택 가드, 쓰기 장벽 |
| `ad_marshal_main` | 수신자 그래프(헤더, 루트 포인터, Source·Target 객체) |

조합 검사 `bv_unmarshal_then_marshal`(`Fk/Compose.lean`):

- BitVec 디코더가 돌아온 뒤, 호출자가 같은 수신자로 인코더를 부른다.
- 호출자의 `call`은 "반환 슬롯만 새 반환 주소로 바뀐 메모리"라는 전제(`hupd`)로 둔다.
- 두 번째 호출의 전제는 가정하지 않는다. 수신자 그래프, 저장된 rbp 칸, spill, 반환 슬롯, scratch(위 8바이트가 새 호출 슬롯), 스택 가드가 모두 디코더의 결론에서 나온다.
- 결과: 인코더가 `b`를 dst에 붙인다.

남은 것: FixedVec·Checkpoint 수용, FixedVec·Checkpoint·Scalars·ListU64·Nested·ListC 마샬과 Nested·ListC 수용의 결론은 바꾸지 않았다(r14와 `R`, 일부는 `⋆ True`).

### R8. 계약 신뢰 항목 (01:07, `6a4d7ef`)

- CONTRACTS.md 1d절: "추상 모델 증명"(`rt_*`, `bump_*`)과 "Go 정교화"(없음)를 구분했다.
- 계약별 신뢰 항목과 형식 전제로 옮기지 못한 이유를 표로 적었다. `FmtErrorfC`의 인수 유효성, `%w`의 `Error()` 종료, fmt의 실제 할당량, `ConvT64C`의 상자 내용, 할당기·GC, `ValidateBitlistC`의 itab 절.
- 형식 전제로 옮긴 것은 없다(이견 2).

### R9. B0 (01:05–01:06, `2759032`)

- `funspec … at s`의 `s`는 호출 전 상태다. spill 칸은 호출 전 `rsp + 8`이다. 1b 명세의 `rsp + 8`이 맞았고, 1b-fix의 `rsp + 16`이 틀렸다.
- 입력과 스택 블록의 분리를 더했다.
- VC 16개, `kfinish`로 닫힘 3, 열림 13(11.7 s, 최대 113 MB).
- VC 종류: 분기 가로채기 4, 메모리 매핑(`isSome`) 10, 진입 일치 1, 그 밖 1.
- 레이블 불변식은 넣지 않았다. 도달 가능한 레이블 둘(`L_37`, `L_3b`)의 불변식이 `False`라 그 분기 VC는 명세 결함이다.
- 결론은 바뀌지 않는다: main에 남는다. REPORT-1b 2절과 REPORT-1b-fix 11절에 정정을 적었다.

### R10. 문서와 회귀 검사 (01:07–01:09, `6a4d7ef`, `064e987`)

- CONTRACTS.md의 오래된 "모델 없음" 행을 고쳤다. 모든 계약에 모델이 있다.
- `Fk/Regress.lean`: `joint_models`(한 Host·한 힙에서 계약 8개가 함께 성립), `not_joint_false`, `old_input_excluded`(1b growslice 반례 입력 배제). 호출 증인(`*_runs`)이 세 번째 종류다. `review/Review1b.lean`의 타입 오류 로그는 역사 자료로만 둔다.
- 공리 검사 두 범위: `tools/axioms.sh`가 정리 범위(`AXIOMS.txt`)와 모든 선언 범위(`AXIOMS-ALL.txt`)를 쓴다.
- REPORT-1b-fix 9.3절의 `bv_marshal_main` 누락은 이 보고서의 R6 표로 대신한다(정정을 9.3절에 적었다).
- 고유 주 정리 53개, 실행 증인 선언 57개를 구분해 적었다(0절).

### 생성기 수정 리뷰의 재증명 항목 12개

| # | 항목 | 결과 |
| --- | --- | --- |
| 1 | 생성기·Go·런타임·Prysm 배치·gohashtree 고정 | TOOLS.md 첫 표 |
| 2 | `ValidateBitvector` 호출을 코드에 포함하고 명세와 연결, 오류 반환·경계 | `vbv_*`, `bv_spec_accepts_iff`. 경계: 길이 불일치 경로(`ErrBytesLength`)의 ValidateBitvector 정리는 쓰지 않았다(BitVec 디코더는 그 전에 `len ≠ 1`을 거른다) |
| 3 | BitL 마샬의 `ValidateBitlist`, 2048 받고 2049 거부 | `bl_marshal_main`, `bl_marshal_reject_main`, `bl_marshal_rejects_overlong` |
| 4 | 첫 오프셋 분기 제거에 맞춘 링크·분기 증명 | R5: 기계어가 같다. 링크 자료는 다시 만들었다 |
| 5 | 주소·레이블·스택 크기·호출 위치를 재사용하지 않음 | 새 ELF에서 읽었다. 문자열 오프셋 +40, BitVec·BitL 프레임 새로 |
| 6 | G2 사후조건을 호출 당시 prefix 보존으로 | 마샬 정리의 결론은 `pre`(dst[:len])와 쓴 바이트만 말한다. 용량 안 나머지 바이트는 말하지 않는다. 거부 정리는 nil 슬라이스와 `pre` 보존을 말한다 |
| 7 | 위임 호출 계약을 따로 | 이 대상에는 위임 타입이 없다. Nested·ListC의 하위 호출은 함수 명세(`ScUAccC`, `LuUAccC`)로 정리에서 유도한다 |
| 8 | 진행형 Bitlist의 `.progressiveBitList none`과 로컬 한도 분리 | 이 대상에 진행형 bitlist가 없다. 하지 않았다 |
| 9 | F1·F2 반례를 거부 정리로, 성공 경로의 값 보존·증인 재확인 | R3, R4. 증인 `WitBv`, `WitBvR`, `WitBvM`, `WitBl*`, `WitBlR` |
| 10 | 새 런타임 호출을 포함한 주 정리의 전제 만족·링크 | 증인(R6), 링크 PASS, `joint_models` |
| 11 | 제자리 해시의 주소 동일성 전제 | 이 세션의 정리는 HTR을 다루지 않는다. 해당 없음 |
| 12 | HTR의 비정규 bitfield 입력은 검증 밖 | 해당 없음. 정리의 범위는 인코딩·디코딩이다 |

## 3. 증인과 계약 조합의 범위

- 같은 Host·같은 힙에서 함께 성립함을 보인 계약 묶음:
  - `joint_models`: makeslice(1바이트), memmove, growslice, newobject 16, fmt.errorf 두 계약, convT64, ValidateBitlist.
  - `WitBvR`: 실제 ValidateBitvector(안에서 fmt.errorf nil·newobject 16) + 인수 1개 fmt.errorf.
  - `WitBl1/257`: ValidateBitlist + growslice + memmove.
  - `WitLuTb`, `WitLuMa`: convT64 + 인수 1개 fmt.errorf.
  - `WitAd`(1b-fix): makeslice + memmove + newobject 32.
- 한 Host에 newobject 모델은 하나만 둘 수 있다(같은 레이블). 그래서 16·24·32를 한 증인에서 함께 쓰지는 않는다.
- 모든 증인 Host는 Kraken의 추상 Host다(지시어 하나 = 주소 하나). 실제 ELF 주소 배치가 아니다. ELF 연결은 링크 검사가 맡는다.

## 4. 게이트 1 표 (완료 단위 기준)

"증인"은 같은 Host에서 전제 전체를 만족하는 구체 상태와 실행 정리다.
"양방향"은 디코더에서 EthLib가 받는 입력 ⟺ 기계어가 nil을 돌려주는 입력이 기계어 정리로 닫혔는지다.
링크 검사는 모든 대상 함수에 PASS다.

| 종류 | 디코더 수용 | 증인 | 양방향 | 인코더 | 증인 | 거부·크기 | 증인 | 부정 시험 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| ListU64 | `lu_accept_main` | 0·1·16 | 부분(길이·오프셋·정렬·초과 거부) | `lu_marshal_main`, `…_reject_main` | 0·1·16, 17 | 4경로, 크기 | 모두 | offset, maxlen |
| FixedVec | `fv_accept_main` | 있음 | 부분(크기) | `fv_marshal_main`, `…_reject_main` | 있음 | 크기 | 있음 | loop, control |
| bitvector | `bv_accept_main` | b < 16 | **있음(1바이트)** | `bv_marshal_main` | 있음 | 크기, 패딩 | 있음 | vbvje, bvnochk |
| bitlist | `bl_accept_main` | 1, 257바이트 | **규칙 동치**(`blValid_iff`; 디코더의 무효 입력 오류 경로는 정리 없음) | `bl_marshal_main`, `…_reject_main` | 1, 257, 2049비트 | 짧음, 오프셋, 크기 | 모두 | gsnum, blmnochk |
| 중첩 container | `ne_accept_main` | 0·1·16 | 부분 | `ne_marshal_main` | 0·1·16 | 짧음, 오프셋, 크기 | 크기 **없음** | **없음** |
| List[container] | `lc_accept_main`, `lc_accept_empty_main` | 빈 리스트만 | 부분 | `lc_marshal_main` | **없음** | 5경로, 크기 | 크기 **없음** | nilerr |
| Prysm 축약 Checkpoint | `cp_accept_main` | 있음 | 부분(크기) | `cp_marshal_main`, `…_reject_main` | 있음 | 크기 | 있음 | **없음** |
| Prysm 축약 AttestationData | `ad_accept_main` | 있음 | 부분(크기) | `ad_marshal_main` | 접두사 3 | 크기 | 있음 | **없음** |

게이트 1 판정: **미통과.**
List[container] 수용(원소 ≥ 1)·인코더·크기, Nested 크기의 증인과 세 타입의 부정 시험이 없다.

## 5. 생성기 요청 목록

이 세션에서 새 생성기 결함은 찾지 않았다.
관찰 둘을 적는다(결함이 아니다).

- BitVec 인코더는 `ValidateBitvector(c.J, 4)` 뒤에 `len(c.J) != 1` 검사를 그대로 둔다. ValidateBitvector가 길이도 검사하므로 뒤 검사는 도달하지 않는다(추측: 정리로 확인하지 않았다).
- BitL 인코더는 오프셋 4를 dst에 쓴 뒤 ValidateBitlist를 부른다. 실패하면 nil 슬라이스를 돌려준다. G2 문서(오류 시 `dst[:len]` 보존, 용량 안 나머지는 말하지 않음)와 맞는다.

## 6. Kraken 요청 목록

- `bsr` 파싱(1b부터). `ssz.ValidateBitlist`가 계약으로 남는 유일한 이유다.
- `ecancel`의 PANIC(`Lean.Expr.appFn!`): `bumpHeap`이 있는 목표와 일부 큰 증인 목표에서 실패할 때 PANIC한다. `Eq.mp` + `ac_rfl`로 우회했다.
- 같은 출력의 두 원자를 `ac_rfl`·`ecancel`이 다르게 본다(R6 측정). 원자 비교 진단(어느 원자가 남았는지)을 출력하면 도움이 된다.
- vcgen 쪽(1b-fix와 같다): `@[spec]` 형태 추가, main 합류 일정.

## 7. 이견

1. **R3의 범위.** 일반 `bits`의 패딩 없는 수용 정리와 길이 불일치 정리는 쓰지 않았다. BitVec(bits = 4)의 디코더는 그 전에 길이를 거르고, 인코더의 길이 불일치 경로는 증명하지 않았다.
2. **R8 형식화.** 형식 전제로 옮긴 신뢰 항목이 없다. 인수 유효성과 `Error()` 종료는 Go 타입 기술자·fmt 동작 모델 없이 쓸 수 없다. `ConvT64C`의 상자 내용은 넣을 수 있지만, 호출자 정리(`LuRejectCall`)와 모델을 함께 바꿔야 하고 이 세션의 정리에 쓰이지 않는다. 문서로 구분했다.
3. **R9 레이블 불변식.** 넣지 않았다. B0는 채택 평가이고 결론(main 유지)에 영향이 없다고 판단했다. 대신 열린 VC 중 명세 결함인 것(도달 가능한 레이블의 `False` 불변식)을 구분해 적었다.
4. **R7 범위.** 모든 주 정리의 결론을 바꾸지 않았다. 바꾼 정리와 조합 검사 하나만 했다(2절 R7 표).
5. **`ValidateBitlistC` 강화.** 무효 입력의 itab 절을 더했다. BitL 인코더의 거부 경로가 오류의 type 워드를 읽기 때문이다. 이 절은 Go 코드를 읽은 결과이고 신뢰 항목이다.
6. **증인 위치.** 증인마다 파일을 나눴다(한 파일에 전역 Host 인스턴스 하나).
7. **부정 시험의 지정 정리.** `bvnochk`의 처음 변이(디코더의 `je` → `jmp`)는 수용 정리에서 먼저 실패했다(같은 지시어가 수용 경로에도 있다). 거부 경로에만 있는 지시어(`jne` → `jmp`)로 바꿨다.
8. **부정 시험 복제본.** 전체 실행에서 `nopret`이 처음에 UNEXPECTED였다. 원인은 R2의 (g)다. (g)는 `ssz/unmarshal.go`를 읽는데, `negative/run.sh`의 복제본에 그 파일이 없었다. 복제본에 그 파일을 복사하도록 고쳤다. 다시 실행하니 (d)에서 실패했다(기대대로).

## 8. 재현

```sh
cd fv/kraken/lean && lake build                    # 804 jobs
tools/axioms.sh                                     # TOTAL 1296 NONSTANDARD 0; ALL-DECLARATIONS TOTAL 6648 NONSTANDARD 0
cd ../../.. && python3 fv/kraken/link/check.py fv/kraken/link/out            # PASS all, BUNDLE
python3 fv/kraken/link/check.py --selftest fv/kraken/link/out                  # 10 cases
fv/kraken/negative/run.sh <scratch-dir>                                         # negative/RESULT
cd fv/kraken/vcgen && lake env lean Vg/ScAccept.lean   # 13 `finish` failures (B0, 기록용)
GOROOT=$(go env GOROOT) go test ./fv/kraken/semtest/   # 저장소 루트. F1·F2 거부 회귀 시험(재증명 수정 X3에서 추가)
# 대상 재생성: TOOLS.md "대상 생성"
# 증인 재생성: cd fv/kraken/lean && python3 tools/wit/<w*.py> tools/wit [인수]
```

## 9. 1c 증명 생성기 설계 입력 (1b-fix 10.2절에 이어)

1. **스택 좌표 세 가지를 따로 둔다.** 함수 진입 rsp, 호출 직전 rsp(호출자 프레임 기준), 피호출자 진입 rsp(= 호출 직전 − 8). vcgen의 `funspec`은 호출 직전 좌표를 쓴다. Fk 정리는 진입 좌표를 쓴다. B0의 spill 좌표 오류가 이 혼동에서 나왔다.
2. **계약 조합을 한 Host·한 힙에서 검사한다.** 주 정리를 만들 때 그 정리가 쓰는 계약 모두의 모델을 한 Host에 넣어 증인을 낸다(`joint_models`, `WitBvR`). 같은 레이블의 모델은 하나만 둘 수 있으므로 크기별 모델(newobject 16·24·32)은 증인을 나눈다.
3. **미지원 기호 길이는 입력 단계에서 거부한다.** `wgen`의 `layout`은 길이가 정수가 아니면 주소를 증가시키지 않는다. 생성기는 이를 조용히 넘기지 말고 오류로 멈춘다.
4. **증인 없는 정리는 자동 완료표에서 미완료로 표시한다.** 이 보고서의 4절 표를 생성기가 `*_main` 이름과 `*_runs`의 참조에서 만든다(R6에서 쓴 grep 방식).
5. **틈은 프레임으로 넘긴다.** 전제에 없는 메모리를 `sep_true`로 버리지 말고, 레지스터·레이블 기준 주소의 조각으로 정리의 `R`에 넘긴다. 리터럴 주소 원자의 불일치를 피한다.
6. **블록 원자의 표기를 고정한다.** 길이 등식으로 고친 `BitVec.ofNat`에는 `BitVec.ofNat_eq_ofNat`를 다시 적용한다. `UInt64` 리터럴 대신 `BitVec` 리터럴을 쓴다. 레이블 보조정리는 숫자 하나로 정리한다.
7. **배치는 정리 문장에서 읽는다.** 사람이 쓴 배치는 틀린다(`misaligned` 시간 초과). 생성기는 정리의 `h_mem`을 파싱해 주소와 길이를 뽑는다.
8. **함수 명세는 정리에서 유도한다.** 우리 코드(`ValidateBitvector`, Scalars, ListU64)는 계약이 아니라 `*_holds`로 명세를 만든다. 생성기는 호출 그래프에서 이 유도를 자동으로 붙인다.
9. **조합 검사를 생성한다.** 디코드 → 같은 수신자 마샬처럼, 앞 정리의 결론이 다음 정리의 전제를 덮는지 확인하는 정리를 타입마다 하나 낸다(`bv_unmarshal_then_marshal`).
