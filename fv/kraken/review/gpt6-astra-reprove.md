# 재증명 세션 리뷰

판정: **조건부**. 게이트 1: **미통과**.

F1·F2의 수정은 새 기계어와 연결됐다. 계약의 공동 만족과 많은 호출 증인도 확인했다.
그러나 링크 검사 우회 두 개, 실제 Go 상태와 다른 증인, 실패하는 Go 회귀 시험이 남았다.
새로운 Lean 모순은 찾지 못했다. 이것은 모든 실제 Go 호출의 전제를 증명했다는 뜻이 아니다.

대상은 `~/orca/workspaces/methodical-ssz/ssz-fv-reprove`의 `440e079`다.
`2d0150b` 이후 18개 커밋을 확인했다. 변경 범위는 `fv/kraken`이다.
원본은 읽기만 했다. 빌드, 재생성, 변이는 지정 scratchpad의 사본에서 실행했다.
아래 저장소 경로와 줄 번호는 대상 원본 기준이다.
`E`는 사용자가 지정한 scratchpad를 뜻한다.

## 1. 필수 발견

### 1. 링크 검사 (f)가 실제 SHash 값을 검사하지 않는다. 중요도 중간

`lean_value`는 첫 리스트 리터럴까지만 읽는다. 뒤의 Lean 식은 검사하지 않는다.
근거: `fv/kraken/link/check.py:71`, `fv/kraken/link/check.py:86`.

기존 정의 마지막에 `.take 0`을 붙였다.
실제 `Fk.sHash` 값은 빈 리스트가 된다. 그런데 링크 검사는 `PASS all`을 출력했다.
별도 Lean 파일에서 `example : Fk.sHash = [] := rfl`도 통과했다.

재현: `E/reprove-link-shash-tail.log`, `E/ReviewSHashTake.lean`.
주석 해시 우회는 고쳤다. 실제 정의 값 검사라는 이전 요구는 아직 충족하지 못했다.

이 발견은 현재 제출된 SHash가 틀렸다는 뜻은 아니다.
검사기가 검사했다고 주장하는 값과 Lean 값이 달라도 통과한다는 뜻이다.
SHash는 `.S` 변경을 Lake에 알리는 의존성이다. 이 검사는 증명과 기계어의 연결에 속한다.
근거: `fv/kraken/link/shash.sh:2`, `fv/kraken/lean/Fk/Code.lean:4`.

수정: 생성된 정의 전체가 허용된 리스트 리터럴인지 검사하라.
접미 연산과 추가 식을 거부하라. `.take 0` 변이를 자기 시험에 넣어라.
복잡한 Lean 파서를 새로 만들 필요는 없다.

### 2. 링크 검사 (g)가 BitL의 새 형식 문자열을 누락한다. 중요도 중간

검사 목록에는 `lcFmtZero`, `lcFmtShort`, `vbvFmt`, `bvFmtJ`만 있다.
`blFmtB`는 없다. 근거: `fv/kraken/link/check.py:65`.

`blFmtB`의 첫 바이트를 66에서 67로 바꿨다. `B: %w`가 `C: %w`가 된다.
ELF와 생성 Go 파일은 그대로 뒀다. 링크 검사는 통과했다.
재현: `E/reprove-link-blfmt-byte.log`.

이 값은 실제 거부 정리의 메모리 전제에 들어간다.
근거: `fv/kraken/lean/Fk/BlMarshal.lean:352`, `fv/kraken/lean/Fk/BlMarshal.lean:387`.
따라서 잘못된 전제를 가진 정리가 ELF와 연결됐다고 잘못 판정할 수 있다.

대조 변이도 실행했다. `vbvFmt`의 사용 오프셋을 바꾸면 (g)가 실패했다.
재현: `E/reprove-link-vbvfmt-offset.log`.
현재 검사 방식 전체가 무효인 것은 아니다. 새 호출의 검사 등록이 빠졌다.

수정: `blFmtB`와 모든 사용 위치를 검사하라.
형식 문자열 값, 사용 오프셋, 누락 등록을 각각 부정 시험으로 고정하라.

### 3. BitL 거부의 오류 인터페이스 연결은 아직 실제 Go 계약이 아니다. 중요도 높음

`ValidateBitlistC`는 무효 입력에서 itab만 보장한다.
오류 데이터 포인터인 rbx는 규정하지 않는다. 오류 객체 자원과 할당 예산도 없다.
근거: `fv/kraken/lean/Fk/Vbl.lean:36`, `fv/kraken/lean/Fk/Vbl.lean:44`.

실제 호출자는 rbx를 인터페이스 데이터로 저장한 뒤 `%w`에 넘긴다.
근거: `fv/kraken/link/out/norm/target.BitL.MarshalSSZTo.S:39`, 같은 파일 `:42`, `:48`.
그러나 `FmtErrorfC`는 인터페이스의 유효성을 형식 전제로 요구하지 않는다.
주석에서만 유효성과 `Error()` 종료를 신뢰한다.
근거: `fv/kraken/lean/Fk/Contracts.lean:144`, 같은 파일 `:147`.

문제는 증인에서 구체적으로 보인다.
`RtVbl`은 오류 경로에서 rbx를 바꾸지 않는다. 길이 257이면 rbx는 257이다.
`WitBlR`의 메모리 블록은 0x10000부터 시작한다. 0x101은 그 블록 밖이다.
`RtErr`는 이 데이터 포인터를 읽지 않고 rax에 1을 넣는다.
근거: `fv/kraken/lean/Fk/RtVbl.S:1`, 같은 파일 `:16`,
`fv/kraken/lean/Fk/WitBlR.lean:86`, `fv/kraken/lean/Fk/RtErr.S:1`.

이 증인은 약한 추상 계약의 공동 만족을 증명한다.
유효한 Go 오류 인터페이스를 만들고 `%w`로 감싸는 실행의 증인은 아니다.
`WitBlR`는 힙도 `fun _ => emp`, 예산도 0으로 둔다.
근거: `fv/kraken/lean/Fk/WitBlR.lean:142`.

현재 조건부 기계어 정리가 거짓이라는 발견은 아니다.
실제 Go 적용에 필요한 가정이 계약 바깥에 남았다는 발견이다.
CONTRACTS 1d의 추상 모델 구분은 옳다. 하지만 그 구분만으로 이전 필수 수정 3을 완료할 수 없다.
근거: `fv/kraken/CONTRACTS.md:75`, 같은 파일 `:85`,
`fv/kraken/review/gpt6-astra-1bfix.md:435`.

수정: 오류의 itab, 데이터 포인터, 객체와 문자열 자원을 연결하라.
실제 호출에서 사용하는 오류 형태로 fmt 계약을 제한하라.
할당과 프레임 보존 가정도 명시하라. Go 전체 런타임을 이번 단계에서 증명할 필요는 없다.
그러나 적용 불가능한 보편 계약을 그대로 실제 Go 계약으로 취급하면 안 된다.

### 4. BitL 거부 증인은 Go 슬라이스 불변식을 위반한다. 중요도 중간

`WitBlR`의 수신자 헤더는 길이 257, 용량 0이다.
정리 적용에서도 용량 인수 `c`에 0을 넘긴다.
근거: `fv/kraken/lean/Fk/WitBlR.lean:105`, 같은 파일 `:107`, `:138`.

`bl_marshal_reject_main`에는 이 입력 슬라이스의 `len ≤ cap` 조건이 없다.
그래서 증인은 정리의 전제를 정확히 만족한다. 약화된 사본을 사용한 것은 아니다.
하지만 일반적인 Go 슬라이스의 증인으로는 부족하다.
근거: `fv/kraken/lean/Fk/BlMarshal.lean:367`, 같은 파일 `:382`, `:390`.

리뷰 Lean 파일에서 헤더 바이트를 직접 확인했다.
근거: `E/ReviewReproveAstra.lean:79`.
문서도 `len ≤ cap < 2^63`을 Go 값의 불변식으로 적고 있다.
근거: `fv/kraken/CONTRACTS.md:125`.

수정: 이 증인의 용량을 최소 257로 바꿔라.
증인 생성기가 Go 값의 불변식을 별도로 검사하게 하라.
정리가 더 넓은 기계 상태를 허용하는 것은 유지할 수 있다.
추상 전제 만족과 Go 값으로서의 실제성을 완료표에서 구분하라.

### 5. F1·F2 Go 시험이 수정 전 성공 동작을 기대한다. 중요도 중간

`go test -count=1 ./fv/kraken/semtest`를 사본에서 실행했다.
두 시험이 모두 실패했다.

- F1 시험은 0x10을 수용해야 통과한다. 새 코드는 패딩 오류를 반환했다.
- F2 시험은 258바이트 bitlist를 마샬해야 통과한다. 새 코드는 길이 오류를 반환했다.

근거: `fv/kraken/semtest/f12_test.go:14`, 같은 파일 `:24`.
실행 로그: `E/reprove-semtest.log`.
Claude의 `verify-reprove.log:42`에도 이 패키지의 실패가 있다.
이것은 아키텍처 실행 실패가 아니다. Go 수준 기대값이 오래됐다.

수정: 현재 대상에서는 거부를 기대하는 회귀 시험으로 바꿔라.
수정 전 반례는 이전 커밋이나 별도 역사 자료로 보존하라.
2047·2048·2049비트와 빈 인코딩, 종료 비트만 있는 입력을 포함하라.
보고서 재현 표에 이 시험을 넣어라.

### 6. 완료 문구와 G3 문구가 실제 범위보다 강하다. 중요도 중간

보고서 0절은 이전 필수 수정 1–7을 처리했다고 말한다.
하지만 레이블 불변식, 형식 전제로 옮길 신뢰 항목, 누락 증인과 전체 조합 자원은 남았다.
보고서 자신도 이를 인정한다.
근거: `fv/kraken/REPORT-1b-reprove.md:14`, 같은 파일 `:177`, `:183`, `:191`.
이전 요구: `fv/kraken/review/gpt6-astra-1bfix.md:429`.

CONTRACTS에는 지금도 다음과 같은 오래된 행이 있다.

- `bl_accept_main`의 공동 증인이 없다고 적었다. 실제로 `WitBl1/257`이 있다.
- `bv_reject_padding_main`, `bl_marshal_reject_main`의 증인이 없다고 적었다.
- 모든 새 형식 문자열을 (g)가 검사한다고 적었다. `blFmtB`는 빠졌다.

근거: `fv/kraken/CONTRACTS.md:31`, 같은 파일 `:45`.

R5의 “명령어 수와 순서가 같다”도 정정해야 한다.
네 디코더의 명령어 이름 순서는 같다. 전체 피연산자와 저장 순서는 같지 않다.
ListC는 rdi 저장과 rbx 저장의 순서가 바뀌었다. BitL도 레지스터와 저장 순서가 바뀌었다.
근거: `fv/kraken/REPORT-1b-reprove.md:107`,
`fv/kraken/link/out/norm/target.ListC.UnmarshalSSZ.S:71`, `E/reprove-g3-diff.log`.

권장 문구:
“G3의 삭제 대상 검사는 이전 기계어에서도 별도 분기로 남지 않았다.
새 빌드에는 재배치, 레지스터 배치와 저장 순서 변화가 있다. 이를 새 ELF에 맞춰 재증명했다.”

## 2. 공허성, 계약, 유도 명세

### 새 계약의 공동 만족

`joint_models`는 한 Host에서 여덟 계약을 함께 증명한다.
힙을 받는 계약들은 같은 `bumpHeap`을 사용한다.
정리는 모든 `S`와 `ty`에 대해 성립한다.
근거: `fv/kraken/lean/Fk/Regress.lean:28`, 같은 파일 `:80`, `:84`.

포함 범위는 makeslice, memmove, growslice, newobject 16, fmt 두 계약, convT64, ValidateBitlist다.
따라서 이 구체 모델에서 여덟 계약의 결합만으로 `False`를 얻을 수 없다.
리뷰 파일에서 `¬ (Joint S ty → False)`를 다시 검사했다.
근거: `E/ReviewReproveAstra.lean:8`.

다만 `joint_models` 자체는 한 구체 호출 상태의 증인이 아니다.
각 호출의 메모리 분리, 레지스터, 예산 조건은 해당 `*_runs`가 추가로 보여야 한다.
또한 ty의 내용을 읽지 않는 모델이므로 실제 타입 기술자의 일관성을 증명하지 않는다.
16·24·32바이트 newobject를 동시에 처리하는 일반 Go 할당기 모델도 아니다.
보고서가 모델을 분리한 사실은 정확하다.
근거: `fv/kraken/REPORT-1b-reprove.md:227`, `fv/kraken/CONTRACTS.md:68`.

`old_input_excluded`는 이전 반례의 newLen = 2^63이 새 예산 조건을 위반함을 말한다.
모든 가능한 모순을 배제하는 정리가 아니다. 실제 append 호출의 증인도 아니다.
근거: `fv/kraken/lean/Fk/Regress.lean:95`.

### Vbv 함수 명세

`vbv_acc_holds`는 `vbv_accept_main`을 적용한다.
`vbv_pad_holds`는 `vbv_reject_pad_main`을 적용한다.
유도 과정에서 호출 상태의 분리 전제를 없애지 않는다.
근거: `fv/kraken/lean/Fk/Vbv.lean:464`, 같은 파일 `:506`.

수용 명세는 해당 실제 validator 코드에서 나온다.
패딩 거부 명세는 `FmtErrorfNilC`와 `NewobjectC 16`에 의존한다.
따라서 “가정이 아닌 정리”라는 설명에는 이 외부 계약 의존성을 함께 써야 한다.
실제 validator 코드를 넣은 Host에서 두 유도 명세를 다시 인스턴스화했다.
근거: `E/ReviewReproveAstra.lean:12`, 같은 파일 `:15`.

`FmtErrorfNilC`의 인수 0개·퍼센트 없음 분리는 Go 1.26.3 코드와 맞는다.
로컬 `GOROOT/src/fmt/errors.go:35`는 이 경우 nil을 반환한다.
외부 `Errorf`는 이후 `errors.New`를 부른다. 내부 `errorf`와 외부 `Errorf`를 혼동하면 안 된다.
근거: 같은 파일 `:23`, `:31`.

`NewobjectC 16` 모델과 ListC·Vbv의 nil 오류 경로는 이번에 실질적으로 보강됐다.
반면 fmt의 유효한 인터페이스, convT64 상자 내용, GC, 타입 기술자, 실제 스택 여유는 여전히 신뢰 항목이다.
`MemmoveC`의 비겹침 제한은 호출자의 분리 전제와 맞는다. Go memmove의 전체 명세는 아니다.
근거: `fv/kraken/CONTRACTS.md:54`, 같은 파일 `:83`.

## 3. F1·F2와 EthLib 연결

F1 거부 정리는 `b : UInt8`과 `16 ≤ b.toNat`을 받는다.
따라서 길이 1의 모든 0x10–0xff를 덮는다. 특정 0x10만의 정리가 아니다.
근거: `fv/kraken/lean/Fk/BvSpec.lean:470`.
`bv_spec_accepts_iff`는 EthLib `deserialize bvDesc #[b]`의 성공과 `b < 16`을 연결한다.
근거: 같은 파일 `:680`.
리뷰에서도 임의 b에 대한 동치와 패딩 거부 실행을 검사했다.
근거: `E/ReviewReproveAstra.lean:21`, 같은 파일 `:24`.

조건부 기계어 수용·거부 정리와 이 명세 동치를 합치면 1바이트 수용 집합이 일치한다.
일반 bits 전체, 길이 오류 validator 경로, 인코더 패딩 오류 경로까지 증명한 것은 아니다.
보고서의 범위 제한은 적절하다.
근거: `fv/kraken/REPORT-1b-reprove.md:86`.

`blValid`는 EthLib `unpackDelimited (some 2048)`의 성공으로 정의된다.
`blValid_iff`는 다음 규칙과 동치임을 증명한다.
길이는 1–257이다. 마지막 바이트는 0이 아니다. 길이 257이면 마지막 바이트는 1이다.
근거: `fv/kraken/lean/Fk/Vbl.lean:34`, 같은 파일 `:70`, `:73`.

경계는 맞는다. 리뷰 Lean 파일에서 다음을 확인했다.

| 인코딩 | 뜻 | 결과 |
| --- | --- | --- |
| `[1]` | 빈 비트리스트 | 수용 |
| `[]`, `[0]` | 종료 비트 없음 | 거부 |
| 0 바이트 255개 뒤 255 | 2047비트 | 수용 |
| 0 바이트 256개 뒤 1 | 2048비트 | 수용 |
| 0 바이트 256개 뒤 2 | 2049비트 | 거부 |

근거: `E/ReviewReproveAstra.lean:30`.
`highestBit_fin`의 전수 검사는 커널이 확인하는 `decide`다. `native_decide`가 아니다.
근거: `fv/kraken/lean/Fk/Vbl.lean:62`.

`bl_marshal_rejects_overlong`만으로 실행 거부가 증명되는 것은 아니다.
이 정리는 명세 쪽의 경계 사실이다.
실행 거부는 `bl_marshal_reject_main`과 그 적용인 `bl_marshal_overlong_rejected`가 담당한다.
근거: `fv/kraken/lean/Fk/BlMarshal.lean:364`, 같은 파일 `:619`, `:636`.
BitL의 핵심 수용 검사는 여전히 `ValidateBitlistC`에 의존한다.
디코더의 모든 무효 bitlist 거부 경로까지 닫힌 것도 아니다.
근거: `fv/kraken/REPORT-1b-reprove.md:241`.

objdump에서 ValidateBitvector의 `bsr` 부재를 확인했다.
`shr %cl,%dl`은 있다. ValidateBitlist에는 `bsr`가 있다.
근거: `fv/kraken/link/out/norm/ssz.ValidateBitvector.S:25`,
`fv/kraken/link/out/norm/ssz.ValidateBitlist.S:22`.

## 4. 증인 전수와 빠진 부분

목록을 다시 셌다. 고유 `*_main`은 53개다. `*_runs` 선언은 57개다.
주 정리 48개가 증인에서 직접 참조된다.
`Witness.growslice_call_runs`는 호출 계약의 증인이다. 57을 주 정리 개수로 해석하면 안 된다.
기록: `E/reprove-witness-inventory.json`.

증인들은 원래 주 정리를 적용한다. `eventually_mono`는 결과를 좁혀 내보낸다.
이 과정이 주 정리의 전제를 약화한 사본을 만드는 것은 아니다.
대표 근거: `fv/kraken/lean/Fk/WitBlR.lean:137`, `fv/kraken/lean/Fk/WitBlM257.lean:126`.
다만 발견 3·4처럼 원래 전제 자체가 실제 Go 상태보다 약할 수 있다.

`WitBvR`는 실제 ValidateBitvector 코드를 Host에 넣고 `vbv_pad_holds`를 쓴다.
임의의 패딩 바이트에 대해 실행한다. `vbv_reject_pad_main`의 간접 증인으로 인정할 수 있다.
직접 호출 증인이 있다는 뜻으로 세면 안 된다.
근거: `fv/kraken/lean/Fk/WitBvR.lean:176`, `fv/kraken/REPORT-1b-reprove.md:148`.

`WitBl1/257`은 ValidateBitlist, growslice, memmove를 같은 Host에서 쓴다.
할당 계약에는 같은 bump 힙을 쓴다. 257바이트 경우의 예산은 8706이다.
이것은 계약 세 개를 각각 다른 Host에서 증명한 뒤 합친 주장이 아니다.
근거: `fv/kraken/lean/Fk/WitBl257.lean:155`, `fv/kraken/REPORT-1b-reprove.md:224`.

원본에서 빠진 목록은 정확하다.

| 정리 | 리뷰 판단 |
| --- | --- |
| `lc_accept_main` | 원소 1–4의 전체 상태·공동 계약 증인이 없다 |
| `lc_marshal_main` | 객체별 분리 조건까지 포함한 전체 증인이 없다 |
| `lc_size_main` | 원본에는 없다. 리뷰에서 빈 리스트의 전체 실행 증인을 추가했다 |
| `ne_size_main` | 원본에는 없다. 포인터·스택 조각에서 즉시 모순은 찾지 못했다 |
| `lum_grow_site` | 수치 예시는 가능하다. 실제 호출 지점의 전체 증인은 없다 |

근거: `fv/kraken/REPORT-1b-reprove.md:147`, `fv/kraken/lean/Fk/NeSize.lean:20`.
리뷰의 ListC 크기 증인은 `E/ReviewReproveAstra.lean:60`이다.
빈 리스트 한 건이 원본의 완료표나 최대 크기 증인을 대신하지 않는다.

Claude의 `ReviewReprove.lean`은 일부 수치·리스트 조건을 확인한다.
ListC와 growslice의 전체 Host·메모리 전제를 함께 인스턴스화하지 않는다.
또한 48행의 `가정 → True`는 가정의 만족 가능성을 보여 주지 않는다.
근거: `E/ReviewReprove.lean:14`, 같은 파일 `:21`, `:48`.
이 파일만으로 남은 정리의 비공허성이 닫혔다고 판단하면 안 된다.

새 계약 결합에서 `전제 → False`는 얻지 못했다. 구체 공동 모델이 이를 반박한다.
증인이 없는 나머지 전체 정리에는 같은 강도의 인증을 주지 않는다.

## 5. 재생성과 링크

TOOLS의 명령 세 개로 대상 Go 파일을 사본에서 다시 생성했다.
세 파일의 SHA-256이 모두 기존 값과 일치했다.
같은 Go 1.26.3으로 `link/build.sh`도 실행했다.

- ELF: `9c850c97066b9d33d6e4c5ef0a385dcbe2c984ae774a527cdedd18d2b72ac501`.
- objdump: `aa08e280dfda0e46b4675b91b01ef793849fb2ec86a19ce676a60a89c0597fa7`.

둘 다 제출 산출물과 일치했다.
기록: `E/reprove-regeneration.log`, `E/reprove-regeneration-status.json`.
재생성 뒤 링크 검사도 다시 통과했다. 로그는 `E/reprove-link-regenerated.log`다.
명령 근거: `fv/kraken/TOOLS.md:25`, `fv/kraken/link/build.sh:9`.

SHash는 항목 순서만 달라졌다. 파일명과 해시 쌍은 같다.
셸 파일명 확장 순서에 의존하므로 재현성을 높이려면 `LC_ALL=C`를 고정하는 것이 좋다.
근거: `fv/kraken/link/shash.sh:12`.

새 주소와 프레임을 사용했다는 주장은 산출물로 뒷받침된다.
새 ELF부터 `.S`까지 일치하며, 새 프레임을 사용하는 정리도 빌드된다.
다만 과거 세션의 작업 순서를 이 결과만으로 증명할 수는 없다.
Prysm 대상은 여전히 protobuf 필드를 뺀 축약 구조체다. 실제 Prysm 바이너리 정리가 아니다.
근거: `fv/kraken/TOOLS.md:15`.

`conv.py`의 기호 동률 처리는 정렬된 기호 목록에서 결정된다.
동일 주소 기호 선택이 nm 출력 순서에 흔들리지 않는다.
선택된 레이블과 오프셋은 링크 검사가 실제 ELF 주소와 대조한다.
근거: `fv/kraken/link/conv.py:43`, 같은 파일 `:54`.

G3 비교 결과는 다음과 같다. 숫자는 지시어가 아닌 명령어 개수다.

| 디코더 | 이전 | 현재 | 전체 명령어 동일 |
| --- | --- | --- | --- |
| ListU64 | 175 | 175 | 아니오 |
| Nested | 142 | 142 | 아니오 |
| ListC | 395 | 395 | 아니오 |
| BitL | 124 | 124 | 아니오 |

이전 기준은 `2d0150b`에 남은 재생성 전 `.S`다.
네 경우 모두 명령어 이름의 열은 같다. 피연산자까지 같다는 증거는 아니다.
G3 때문에 별도 거부 정리를 삭제할 필요가 없다는 판단은 타당하다.
`lc_reject_past`는 첫 원소 오프셋을 검사한다. 삭제된 컨테이너 첫 오프셋 검사와 다르다.
기록: `E/reprove-g3-diff.log`.

## 6. 조합 검사와 신뢰 문구

`bv_unmarshal_then_marshal`은 두 번째 호출의 전체 전제를 가정하지 않는다.
첫 정리의 결론에서 수신자, 입력 바이트, 스택 조각을 얻는다.
scratch를 나눠 다음 호출 슬롯을 확보한다.
근거: `fv/kraken/lean/Fk/Compose.lean:79`, 같은 파일 `:82`, `:87`, `:92`.

초기 전제에는 목적지 공간과 용량이 있다. 이는 필요한 호출자 자원이다.
중간에는 반환 슬롯만 바꾸고 프레임을 보존하는 `hupd` 관계를 요구한다.
근거: 같은 파일 `:46`, `:63`, `:70`.
이 관계는 두 번째 함수의 전체 전제를 숨겨 가정한 것은 아니다.
하지만 실제 호출자 기계어가 두 함수를 연속 호출하는 단일 실행 정리는 아니다.
두 번째 레지스터 상태를 직접 구성한다.
근거: 같은 파일 `:76`.

따라서 자원 전달 검사로는 유효하다.
“호출자 CALL까지 증명한 연속 실행”이라고 쓰면 과장이다.
다음 단계에서는 중간 상태 구성의 존재와 호출자 코드를 포함한 구체 조합 증인을 추가하라.
최종 결론도 일부 자원을 `True`로 버린다. 반복 조합의 일반 해법은 아직 아니다.
근거: 같은 파일 `:75`, `:103`.

CONTRACTS 1d는 추상 모델과 Go 정교화를 올바르게 구분한다.
다음 연결을 더 명시해야 한다.

- ValidateBitlist의 itab만으로 `%w` 인수의 유효성을 얻을 수 없다.
- ConvT64의 비영 포인터만으로 상자 내용과 타입을 얻을 수 없다.
- 임의 scratch 크기의 추상 모델은 Go 함수의 실제 스택 사용량을 보장하지 않는다.
- 쓰기 장벽 0 보존은 실제 GC가 없는 실행 범위를 요구한다.
- 유도된 함수 명세에도 하위 외부 계약 의존성은 남는다.

근거: `fv/kraken/CONTRACTS.md:65`, 같은 파일 `:83`, `:92`.
이 항목은 “모델 있음”으로 해소되지 않는다.

## 7. B0 재측정

spill 좌표 정정은 맞다.
`funspec … at s`의 s는 호출 전 상태다.
CALL이 반환 주소를 넣으면 피호출자 진입 rsp는 8 감소한다.
피호출자 진입의 rsp+16은 호출 전 rsp+8이다.
근거: `fv/kraken/vcgen/Vg/ScAccept.lean:38`, 같은 파일 `:42`, `:55`.

직접 실행에서 `finish` 오류 13개가 나왔다. 약 12.48초였다.
별도 사본에서 VC 생성 직후 목표 수를 출력했다. 16개였다.
기록: `E/reprove-b0.log`, `E/reprove-b0-count.log`, `E/ReviewB0CountAstra.lean`.
따라서 16개 중 3개가 닫힌다는 수치는 재현됐다.

그러나 도달 가능한 두 레이블의 불변식이 여전히 `False`다.
근거: `fv/kraken/vcgen/Vg/ScAccept.lean:57`.
이 VC는 자동화가 약해서 열린 것이 아니라 현재 명세가 닫힐 수 없어서 열린 것이다.
“main에 남는다”는 현재 작업 비용의 선택으로는 타당하다.
vcgen의 실제 완료 비용을 판단하는 정상 명세 벤치마크로는 부족하다.
이전 필수 수정 1을 완료로 표시하려면 레이블 불변식을 넣고 다시 측정해야 한다.

## 8. 재현 결과

무거운 Lean 작업은 순차 실행했다. 실행 전 프로세스를 확인했다.
기본 빌드는 따뜻한 캐시를 사용했다. 깨끗한 빌드 시간으로 해석하면 안 된다.

| 실행 | 결과 | 시간 |
| --- | --- | --- |
| `lake build` | 성공, 804 jobs | 4.14초 |
| `sh tools/axioms.sh` | 1296 / 6648, 각각 NONSTANDARD 0 | 10.72초 |
| `link/check.py` | PASS, 2927 명령어, 동일 바이트 2877, 패딩 50 | 2.40초 |
| `link/check.py --selftest` | 10개 기대 결과 일치 | 7.41초 |
| `negative/run.sh` | 10개 기대 결과 일치 | 375.93초 |
| 추가 기계어 변이 | 3개 지정 정리에서 실패 | 113.96초 |
| 리뷰 Lean 파일 | 통과 | 로그 참조 |
| B0 | 예상된 13개 미해결 목표 | 12.48초 |
| Go semtest | F1·F2 두 시험 실패 | 위 발견 5 |

로그는 `E/reprove-{build,axioms,link,selftest,negative}.log`에 있다.
시간은 `E/reprove-run-status.json`, `E/reprove-extra-status.json`에 있다.

추가 기계어 변이는 다음과 같다.

| 변이 | 최초 오류 |
| --- | --- |
| ValidateBitvector의 `shr %cl,%dl`을 `shr $0x3,%dl`로 변경 | `Fk/Vbv.lean:196`, `vbv_accept_main` 내부 |
| BitL 마샬의 ValidateBitlist 호출을 nop으로 변경 | `Fk/BlMarshal.lean:189`, `bl_marshal_main` 내부 |
| ListU64 첫 오프셋의 jne를 무조건 점프로 변경 | `Fk/LuAccept.lean:126`, `lu_accept_main` 내부 |

기록: `E/reprove-extra-negative.log`.
변이 위치 숫자는 원래 스크립트의 0부터 세는 지시어 인덱스와 구분했다.

부정 시험 실행기는 종료 코드와 최초 오류의 지정 정리 범위를 함께 검사한다.
대조군은 성공해야 한다. 다른 위치의 실패는 `FAIL-ELSEWHERE`로 분류한다.
링크 변이는 (d)의 실제 실패도 요구한다.
근거: `fv/kraken/negative/run.sh:60`, 같은 파일 `:64`, `:83`, `:112`.
이번 직접 실행에서 대조군도 통과했다.

공리 검사의 6648은 모든 Lean 환경 선언의 수가 아니다.
`Fk`, `Fv1`, `Fv` 모듈의 정리·정의·인스턴스·내부 선언 수다.
각 선언에 `collectAxioms`를 적용하므로 사용한 외부 의존성의 공리도 따라간다.
Kraken와 EthLib의 사용하지 않은 모든 선언을 전수 감사한 것은 아니다.
근거: `fv/kraken/lean/tools/AxiomsAll.lean:27`, 같은 파일 `:31`, `:33`.

Fk 소스에서 금지된 증명 우회 사용은 찾지 못했다.
허용 공리는 `propext`, `Classical.choice`, `Quot.sound`다.
리뷰 Lean 파일도 이 범위 안에서 확인했다.
`bv_omega`와 `bv_decide`를 같은 것으로 세지 않았다.

## 9. 필수 수정 목록과 게이트 최소 잔여 목록

현재 결과를 정리하기 위한 필수 수정은 다음과 같다.

1. SHash 정의 전체를 검사하고 `.take 0` 우회를 막아라.
2. `blFmtB`를 (g)에 넣고 값·오프셋 변이를 시험하라.
3. F1·F2 Go 시험을 새 거부 동작에 맞춰 갱신하라.
4. `WitBlR`의 용량을 고쳐라. Go 값 불변식을 증인 검사에 넣어라.
5. 오류 인터페이스와 fmt 호출의 적용 조건을 연결하라. 단순 itab 보장을 실제 오류 객체 보장으로 오해하지 마라.
6. CONTRACTS의 오래된 행과 “1–7 처리” 문구를 고쳐라. 완료·부분·보류를 구분하라.
7. G3의 명령어 동일성 문구를 고쳐라. B0 불변식을 보강하거나 해당 요구를 미완료로 표시하라.

현재 선택한 타입 전체를 게이트 1 완료로 판정하려면 다음도 필요하다.

1. ListC 수용·마샬·크기, Nested 크기, `lum_grow_site`의 전체 전제 증인을 완성하라.
2. 가변 크기 완료 단위에 빈 값·1개·최대를 적용하라. 단순 증인 선언 수로 대체하지 마라.
3. Nested, Checkpoint, AttestationData의 지정 정리 부정 시험을 추가하라.
4. 필요한 사후 자원을 남기고 타입별 후속 호출 조합을 확인하라.
5. 계약 적용에 필요한 Go 불변식을 형식 전제로 옮겨라. 실제 런타임 정교화 부재는 계속 명시하라.
6. 수용 방향과 거부 경로의 범위를 타입별로 고정하라. BitL 규칙 동치를 디코더 양방향 증명으로 세지 마라.

전체 Go 런타임 증명을 게이트의 숨은 추가 요구로 만들 필요는 없다.
명시적인 조건부 게이트는 가능하다. 다만 조건이 실제 호출에서 충족 가능한 형태여야 한다.
현재 보고서가 정한 완료 단위조차 아직 모두 충족하지 못했다.
근거: `fv/kraken/REPORT-1b-reprove.md:35`, 같은 파일 `:247`.
실제 x64 하드웨어 대조도 미실행 상태로 유지해야 한다.

## 10. 1c 브리프에 넣을 것

보고서 9절의 아홉 설계 입력은 방향이 맞다. 다음 보완을 넣어라.

| 기존 입력 | 리뷰 보완 |
| --- | --- |
| 스택 좌표 세 가지 | 좌표 변환과 반환 슬롯 위치를 작은 정리로 고정하라 |
| 한 Host·한 힙 | 크기별 동일 레이블 충돌을 검사하라. 필요하면 타입 기술자로 분기하는 모델을 써라 |
| 기호 길이 거부 | 구체 증인 배치 생성기의 제한으로 한정하라. 주 정리의 기호 길이까지 금지하지 마라 |
| 자동 완료표 | 문자열 grep 대신 실제 선언 의존성과 전체 적용을 기록하라 |
| 틈을 프레임으로 전달 | 겹침, 주소 넘침, 조각 누락을 먼저 진단하라 |
| 원자 표기 고정 | 정규화 규칙을 한곳에 두어라. 출력 문자열의 동일성에 의존하지 마라 |
| 정리 문장에서 배치 추출 | 가능하면 Lean의 해석된 식에서 추출하라. 임의 정리 문법을 정규식으로 처리하지 마라 |
| 함수 명세 유도 | 하위 계약 의존성도 완료표에 전파하라 |
| 조합 검사 생성 | 중간 상태의 존재와 실제 호출자 실행을 함께 확인하라 |

추가 입력:

- 추상 전제 만족과 Go 값의 유효성을 별도 검사하라.
- 오류 인터페이스, 상자 값, 문자열 자원을 호출 그래프에 포함하라.
- 링크 검사 대상 목록과 증명의 고정 데이터 사용 목록을 대조하라.
- 생성 Go, ELF, objdump, `.S`, SHash, 정리, 증인의 해시를 한 실행 기록에 묶어라.
- 변이 실패 위치와 대조군 결과를 자동 완료표에 연결하라.
- 새 생성기 수정에는 Go 회귀 시험과 Lean 거부 정리를 함께 갱신하라.
- 잘못된 배치의 시간 초과를 증명 난이도나 기호 길이 한계로 분류하지 마라.

2시간 25분은 이번 작업의 기록으로만 사용하라.
재사용한 틀, 따뜻한 캐시, 빠진 완료 단위 때문에 일반 타입 비용으로 외삽할 수 없다.
보고서는 기호 길이를 이번에 시험하지 않았다고 정확히 적었다.
근거: `fv/kraken/REPORT-1b-reprove.md:156`, 같은 파일 `:157`.
1c는 우선 ListC의 남은 증인을 수작업 기준 사례로 닫은 뒤 그 형태를 자동화하는 편이 좋다.

미확인: 실제 x64 하드웨어 실행과 Go 런타임의 계약 정교화는 확인하지 않았다.
남은 위험: 추상 모델의 성공만으로 실제 Go 오류 처리와 GC 실행까지 검증했다고 해석하면 안 된다.
