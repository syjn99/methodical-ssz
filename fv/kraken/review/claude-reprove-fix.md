# 재증명 수정 세션 재검사 (Claude Fable, 2026-11-06)

대상: 워크트리 `ssz-fv-reprove-fix`, 브랜치 `syjn99/ssz-fv-reprove-fix`, 시작 `df024af`, tip `813a86a`(커밋 12개).
세션 자평: 조건부. 게이트 1은 완료 단위 기준 조건부 통과(`REPORT-1b-reprove-fix.md` 0절).
재검사 시각: 03:27–03:40(깨끗한 빌드 포함). 로그 `review-reprove-fix-claude-verify.log`.

## 1. 수치 재현

| 항목 | 보고서 | 재검사 | 일치 |
| --- | --- | --- | --- |
| `lake build` | 830 jobs | 830, 3분 39초(`lake clean` 뒤) | 예 |
| AXIOMS | TOTAL 1432 NONSTANDARD 0 | 같음. 커밋본과 바이트 동일 | 예 |
| AXIOMS-ALL | TOTAL 7334 NONSTANDARD 0 | 같음. 커밋본과 바이트 동일 | 예 |
| 링크 검사 | PASS, 번들 `1e118b6c…` | PASS all, 번들 `1e118b6cf44cc10c…f39ac6` | 예 |
| 자기 시험 | 14 기대대로 | 14 기대대로(새 4개: `.take 0`, blFmtB 값, 오프셋, 미등록) | 예 |
| 부정 시험 | 14 기대대로, 8분 21초 | 14 기대대로, 8분 27초(03:31–03:39). `negative/RESULT`와 같은 실패 위치 | 예 |
| go test semtest | PASS | `ok … 0.393s` | 예 |
| goval | 69 파일, 위반 0 | 69/0. 미검사: `WitCpM` dst(기호 길이), 1a `Witness.lean` | 예 |
| ELF sha256 | `9c850c97…c501` | 같음(재생성 안 함, 커밋본 해시) | 예 |
| 주 정리 `*_main` | 53 | 53(고유 이름). 53개 모두 + `lum_grow_site`가 `Wit*.lean`에서 참조됨 | 예 |
| `*_runs` 선언 | 70 | 70(선언 수). 고유 이름은 55(같은 이름이 여러 Wit 파일에 있다) | 예 |
| 증인 파일 | 69 | 69 | 예 |
| B0 | VC 20, 닫힘 3, 열림 17 | `lake env lean Vg/ScAccept.lean` 오류 17 | 예 |
| 금지 전술 | 없음 | `sorry/admit/native_decide/bv_decide/axiom` 0건(설명문 2줄 제외) | 예 |

## 2. 직접 검사

### 2.1 링크 검사 변이(사본 `linkmut2/`, 워크트리 밖)

| 변이 | 결과 |
| --- | --- |
| `SHash.lean` 끝에 `|>.take 0` | FAIL (f) "not exactly one definition whose value is one list literal" |
| `blFmtB` 첫 바이트 66 → 67 | FAIL (g) "no fmt.Errorf literal equal to Lean blFmtB" |
| SHash 리스트 첫 항목에 `"/-"` 삽입(주석 제거기 우회 시도) | FAIL (f) |
| `LuRejectCall.lean`의 FMTLEN 오프셋 40290 → 40291 | FAIL (g) "does not place a string at go_string._+40290" |
| 정리 파일(`Regress.lean`)에 미등록 오프셋 `go_string._ + 999` 추가 | FAIL (g) "offsets used by theorems but not checked: {999}" |
| 변이 없음 | PASS all |

astra 재증명 필수 수정 1·2는 닫혔다. 재빌드 전이: `Fk/Code.lean:4`가 `public import Fk.SHash`이고 모든 정리 모듈이 `Fk.Code`에 의존하므로 SHash 변경은 전체 재빌드를 유발한다.

### 2.2 Lean (`ReviewReproveFix.lean`, exit 0)

- `Fk.Regress.joint_models`: 아홉 계약(`MakesliceC`, `MemmoveC`, `GrowsliceC`, `NewobjectC 16`, `FmtErrorfNilC`, `FmtErrorfWC`, `ConvT64C`, `ValidateBitlistC`, `ValidateBitlistErrC`)이 한 Host·`bumpHeap`에서 함께 성립한다. `#print` 결과로 아홉 항을 확인했다.
- `¬ blValid []`, `¬ blValid [0]`, `blValid [1]`, `¬ blValid (2049비트)`, `¬ blValid (258바이트)`: semtest `f12_test.go`의 거부 사례와 `ValidateBitlistErrC`의 전제 `¬ blValid buf`가 같은 집합이다.
- `ValidateBitlistErrC`의 예산 부등식 `avail' + 16 + msg ≤ avail ≤ avail' + 8192`은 모델의 소비(16, 빈 메시지)로 만족된다.
- `lu_unmarshal_then_marshal`의 산술 전제(n = 1, dlen = 0, cap = 12)는 만족 가능하다.
- 새 증인 4개(`lc_accept_runs`, `bl_marshal_reject_runs`, `vbv_reject_pad_runs`, `lum_grow_runs`)와 `lu_unmarshal_then_marshal`, `bv_errstr`의 공리: 표준 셋만.

### 2.3 계약 모양 대조(Go 1.26.3 소스)

- `fmt.Errorf`(`$GOROOT/src/fmt/errors.go`): `errorf`가 nil이면 `errors.New(format)`. 그래서 `ssz.ValidateBitlist`의 인수 없는 세 메시지(`unmarshal.go:54, 65, 77`)는 rodata 문자열을 가리키는 `*errorString`이고, `%d`가 있는 한 메시지(`:59`)만 힙 문자열이다. CONTRACTS.md 1d의 "rodata 메시지는 `F` 밖" 신뢰 항목은 정확하다.
- `FmtErrorfWC`의 `%w` 인수 형태(itab + 8의 타입 워드, 데이터 포인터 e)는 Go의 `error → any` 변환과 맞다.
- `ValidateBitlistErrC`가 rax = errorString itab을 결론으로 두는 근거(모든 오류가 `%w` 없는 `fmt.Errorf`)는 소스와 맞다. 단, `:59`의 메시지는 `errorf`가 만든 `*errorString`이므로 itab은 같다.

## 3. 발견

- **F-1 (경미, 수치 표기).** 보고서의 "`*_runs` 70개"는 선언 수다. 고유 이름은 55다(`lc_accept_runs`가 WitLcA1·WitLcA4·WitLcE에 각각 있다). 재증명 보고서(57)와 비교할 때 기준을 적어야 한다.
- **F-2 (경미, 범위).** 조합 정리 둘(`bv_unmarshal_then_marshal`, `lu_unmarshal_then_marshal`)에는 `_runs` 증인이 없다. 완료 단위(1절)는 `*_main`과 `lum_grow_site`에만 적용했다. 조합의 전제 집합이 만족 가능하다는 근거는 산술 전제 확인(2.2)뿐이다.
- **F-3 (경미, 검사기 한계).** `goval.py`는 값 사이 겹침을 보지 않는다(보고서 이견 1이 인정). 증인 Host에서 rodata 문자열(`vbvFmt`, `blFmtB`)과 오류 객체·입력 버퍼의 분리는 `⋆`가 보장하므로 Lean 증명이 겹침을 배제한다. 검사기의 한계는 "Go 값" 열의 근거를 Lean 쪽에 두는 한 결함이 아니다.
- 새 생성기 결함 없음(세션 6절과 같다).

## 4. 판정(astra 검토 전)

조건부. 재증명 리뷰의 필수 수정 7개는 보고서 5절 표대로 닫혔다(#5 부분은 신뢰 항목 표로 정직하게 남겼다). 게이트 1 통과 여부는 게이트 정의에 달려 있다. 세션의 완료 단위 기준으로는 통과이고, 양방향 수용과 모든 거부 경로를 요구하면 미통과다. 제 의견은 "완료 단위 기준 조건부 통과"를 받아들이되, 4절 표의 "닫히지 않음" 중 BitL의 ValidateBitlist 오류 경로(계약 `ValidateBitlistErrC`가 이미 있으므로 정리 하나로 닫힌다)와 Scalars bool > 1은 1c 전에 닫는 것이 맞다.

## 5. astra 검토(03:42–03:55)의 재현

astra 판정: 조건부, 게이트 1 미통과, 필수 수정 8개. 제가 사본에서 재현한 것:

| astra 발견 | 재현 | 결과 |
| --- | --- | --- |
| 1. SHash 문자열 안의 균형 주석 `/-x-/` | 첫 해시 문자열 8자 뒤에 삽입 | PASS all(결함 확인). 제 2.1의 단독 `/-` 변이는 FAIL이었다. 주석 제거기가 문자열 안팎을 구분하지 않는다 |
| 2a. `blFmtB` 정의 뒤 `|>.map (fun b => b + 1)` | 같은 변이 | PASS all(결함 확인). `lean_value`가 첫 리스트 리터럴만 읽는다 |
| 2b. 사용 위치 한 곳을 `label  "go_string._" + 527`(공백 둘) | 같은 변이 | PASS all(결함 확인). 정규식이 공백 하나만 허용하고, 다른 위치의 526이 남아 목록 대조도 통과 |
| 3. Scalars Go 객체 크기 | `unsafe.Sizeof`(GOARCH=amd64) | 24(정렬 8). `goval.py:39`의 표는 16(SSZ 크기). `WitScA` 블록은 57바이트(0x10000–0x10039)인데 수신자 객체는 [0x10028, 0x10040)이라 블록 밖 7바이트 |
| 4. `FmtErrorfWC`의 형식·인수 범위 | astra 로그 `reprove-fix-fmt-runtime.log` 확인 | `%100000w`가 100000바이트를 만들고 예산은 8201. 계약은 생성 코드의 형식으로 제한하지 않는다. 재현은 astra 파일로 갈음 |
| 5. rodata 메시지와 `ErrStr`의 분리 | 계약 문장 재확인 | `ValidateBitlistErrC`는 모든 `F`에 양화하고 `ErrStr`를 힙 조각으로 새로 꺼낸다. 실제 Go의 rodata 메시지를 `F`가 가지면 겹친다. 제 2.3의 "rodata 신뢰 항목 정확"은 서술의 정확성이지 계약의 적용 가능성이 아니다. astra가 맞다 |
| 6. ListC 원소가 빈 리스트뿐 | 보고서 이견 3 | 비공허성에는 충분하고 중첩 최대 입력 증인은 아니다. astra 의견에 동의 |

제 2.1은 다섯 변이가 모두 FAIL이라 "필수 수정 1·2는 닫혔다"고 썼다. astra의 세 변이로 그 판단을 철회한다. 필수 수정 1·2·4·5는 부분이다.

## 6. 최종 판정

조건부. 게이트 1 미통과(astra와 같다). 세션의 "완료 단위 기준 조건부 통과" 자평은 요소 4(링크 검사)와 요소 6(Go 값)이 실제로는 충족되지 않아 성립하지 않는다.

다음 세션(재증명 수정 2)에 넣을 것: astra 필수 수정 8개 전부. 그중 1·2·3은 도구 수정이라 짧다. 4·5는 계약 재설계(형식·인수 타입으로 좁힌 fmt 계약 네 개, rodata 메시지 자원을 사전조건으로)다. 6·7은 증인·조합이다. 8은 게이트 표 정정이다. astra가 제안한 1c 전 거부 경로 우선순위(Scalars bool > 1, BitL ValidateBitlist 오류, ListC 원소 오프셋 순서)를 같은 세션에 넣는다.
