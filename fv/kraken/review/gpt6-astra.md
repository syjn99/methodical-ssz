조건부

MiniRV 없이 Kraken으로 진행하는 방향은 타당하다. 그러나 현재 결과만으로 1b 실행 가능성이 입증됐다고 판정할 수는 없다. `lu_accept_main`의 전제 전체가 모순임을 Lean으로 증명했다. 실제 bitlist 검증 코드에는 Kraken이 지원하지 않는 `bsr`도 나온다.

따라서 “직선 경로, 루프, 외부 호출을 모두 재현했다”는 평가는 수정해야 한다. 직선 경로와 루프는 인정한다. 외부 호출을 포함한 전체 수용 정리는 계약 수정과 재검사가 필요하다. 이 문제들은 MiniRV 복귀를 요구하지 않는다. 근거: `REPORT.md:28`, `lean/Fk/LuAccept.lean:53`, `ReviewKraken.lean:95`, `kraken-bitlist-v1.objdump:21`.

대상은 `~/orca/workspaces/methodical-ssz/ssz-fv-kraken`, 브랜치 `syjn99/ssz-fv-kraken`, 커밋 `ee39240`이다. 아래 저장소 경로는 별도 표시가 없으면 `fv/kraken/` 기준이다. `ReviewKraken.lean`과 `review-kraken-*.log`는 이 문서와 같은 scratchpad에 있다. 대상 워크트리는 수정하지 않았다.

먼저 수정해야 할 발견은 다음과 같다.

1. **`lu_accept_main`은 공허하다.** 공허하다는 뜻은 모든 전제를 동시에 만족하는 실행 상태가 없다는 것이다.

   `hms`는 모든 `cnt`, 기계 상태, 반환 주소, 프레임에 대해 정상 반환과 새 메모리를 요구한다. 프레임은 호출이 보존해야 하는 나머지 메모리다. 바깥쪽 `n ≤ 16`은 이 내부 양화를 제한하지 않는다. 근거: `lean/Fk/LuAccept.lean:30`, `lean/Fk/LuAccept.lean:53`.

   `cnt = 2^61`은 두 64비트 레지스터에 들어간다. 계약은 `8 * cnt = 2^64`바이트를 새 블록으로 요구한다. Kraken의 `List.At`에서 이 블록은 모든 64비트 주소를 포함한다. 계약은 동시에 반환 주소 8바이트와 이 블록이 서로소라고 요구한다. 이는 모순이다. 근거: `lean/Fk/LuAccept.lean:59`, `upstream/Kraken/Mem.lean:34`, `upstream/Kraken/Separation.lean:11`.

   `ReviewKraken.lean:68`은 이 모순을 증명한다. `ReviewKraken.lean:95`는 원래 정리의 전제 목록을 그대로 받아 `False`를 증명한다. 원래 `h_mem`의 반환 슬롯과 scratch 조각으로 계약 입력을 구성했다. 새로운 실행 가정은 추가하지 않았다. 세 공리 `propext`, `Classical.choice`, `Quot.sound`만 사용한다. 결과: `review-kraken-lean.log:1`.

   최소 수정은 계약의 입력 범위를 실제 호출 범위로 제한하는 것이다. 그러나 `cnt ≤ 16`만 추가하면 실제 Go 계약이 완성되지는 않는다. 유효한 타입 인수, 가용 힙, 런타임 소유 메모리, 스택, 종료 조건도 명시해야 한다. 현재 `hms`는 `rax`의 타입조차 제한하지 않는다. 근거: `lean/Fk/LuAccept.lean:53`.

   실제 Go `makeslice`는 타입 크기를 읽고, 곱셈 넘침과 할당 한도를 검사한다. 실패하면 정상 반환하지 않는다. 이는 현재 계약과 다르다. 근거: `/usr/local/go/src/runtime/slice.go:102`, [Go 런타임 소스](https://go.dev/src/runtime/slice.go).

   호출 전 메모리는 반환 슬롯, 스택, 런타임 소유 힙, 호출자 프레임으로 나누는 것이 적절하다. 호출 후에는 힙에서 출력 블록의 소유권을 분리한다. 할당기 내부 상태는 변경을 허용하고 호출자 프레임은 보존한다.

   수정 후에는 빈 목록, 1개, 16개에 대한 전제 만족 사례를 남겨야 한다. 할당을 포함한 작은 Kraken 실행 사례도 필요하다. 수정하지 않으면 `lu_accept_main`으로 어떤 사후조건도 공허하게 주장할 수 있다.

2. **C12의 `bits.Len8` 표 조회 설명은 현재 amd64 빌드에서 틀리다.**

   저장소의 `ssz.ValidateBitlist`를 임시 드라이버에서 빌드했다. 설정은 Go 1.26.3, linux/amd64, `GOAMD64=v1`, `purego`, `CGO_ENABLED=0`이다. `bits.Len8` 호출 위치에 `bsr %r8d,%r8d`가 나왔다. Kraken 런타임 파서는 이를 거부했다. 근거: 저장소 루트 `ssz/unmarshal.go:48`, `kraken-bitlist-v1.objdump:21`, `review-kraken-instructions.log:2`.

   Go 소스의 표 조회 구현만 보면 이 사실을 놓친다. 컴파일러는 `Len8`을 전용 연산으로 바꾼다. v1에서는 `BSRL`, v3에서는 `LZCNTL`로 낮추는 규칙이 있다. 근거: `/usr/local/go/src/cmd/compile/internal/ssagen/intrinsics.go:996`, `/usr/local/go/src/cmd/compile/internal/ssa/_gen/AMD64.rules:105`.

   `GOAMD64=v3` 변경만으로 해결되지 않는다. Kraken은 `lzcnt`도 거부한다. 해당 명령어를 Kraken에 추가하거나, 검증 대상 빌드 변경을 명시적으로 선택해야 한다. bitlist 핵심 검사를 통째로 신뢰하는 계약으로 가리는 방식은 권하지 않는다. 근거: `REPORT.md:48`, `review-kraken-instructions.log:3`.

   같은 빌드에는 `nopw (%rax,%rax,1)`도 나왔다. 현재 `NORM` 표는 이 문자열을 포함하지 않는다. 따라서 C4도 아홉 함수의 기존 패딩에 한정된 완료다. 근거: `kraken-bitlist-v1.objdump:8`, `link/conv.py:74`, `review-kraken-instructions.log:1`.

3. **현재 함수 정리는 1b 조합에 필요한 메모리 보존을 충분히 반환하지 않는다.**

   `sc_marshal_spec_k`는 추가한 16바이트를 EthLib 직렬화와 연결한다. 그러나 기존 `dst[:len]`의 보존은 결론에 없다. `⋆ True`는 나머지 메모리의 이전 값을 잊는다. 따라서 “append 전체의 정확성”과 “추가 구간의 정확성”을 구분해야 한다. 근거: `lean/Fk/ScSpec.lean:86`, `lean/Fk/ScSpec.lean:97`.

   `sc_accept_main`, `sc_reject_size_main`, `sc_size_main`도 호출 후 스택 포인터 보존 조건을 결론에 충분히 남기지 않는다. 중첩 container에서 다음 함수를 호출하려면 이런 조건이 필요하다. 내부 증명에 필요한 사실이 있어도 현재 최상위 정리에서 자동으로 꺼낼 수는 없다. 근거: `lean/Fk/ScAccept.lean:36`, `lean/Fk/ScReject.lean:27`, `lean/Fk/ScSize.lean:10`.

   최소 수정은 필요한 프레임, 입력, 접두사, 호출 후 레지스터 조건을 사후조건에 남기는 것이다. 루프 정리는 이미 `R`, `rsp`, `rbp`를 보존한다. 이 형식을 재사용할 수 있다. 근거: `lean/Fk/LuLoop.lean:162`. 수정하지 않으면 중첩 타입마다 하위 증명을 다시 펼쳐야 한다.

4. **실제 ELF와 Host를 연결하는 검사가 여전히 필요하다.**

   ELF는 빌드된 실행 파일이다. Host는 Kraken의 프로그램과 주소 배치다. 현재 정리들은 임의의 Host에 대해 함수 포함 관계와 레이블 조건을 받는다. 실제 ELF에 해당하는 Host 인스턴스를 제공하지 않는다. 근거: `upstream/Kraken/X64/WP/Host.lean:25`, `lean/Fk/LuAccept.lean:28`, `lean/Fk/Labels.lean:72`.

   `LabelsFresh`는 함수 앞의 레이블 충돌만 배제한다. 내부 첫 출현 조건은 별도 보조정리가 확인한다. 외부 레이블의 존재, 변환 전후 이름 대응, 실제 주소 배치는 이 조건에서 나오지 않는다. 근거: `lean/Fk/Labels.lean:75`, `lean/Fk/Labels.lean:81`.

   전역과 외부 함수 레이블을 정의하지 않은 Host에서는 주소가 `-1`이다. `all.S`는 대상 함수들만 담는다. 이를 그대로 실행 프로그램으로 사용하면 외부 기호가 연결되지 않는다. 근거: `link/conv.py:122`, `upstream/Kraken/X64/Semantics.lean:819`.

   1b 전에 명령어 크기, 실제 주소, 전역·외부 기호, 레이블 유일성을 확인하는 검사를 추가해야 한다. 수정하지 않으면 정리와 ELF가 다른 프로그램을 가리켜도 파서와 Lean 검사가 통과할 수 있다.

정리별 판정은 다음과 같다.

| 정리 | 인정하는 내용 | 남는 제한 |
| --- | --- | --- |
| `sc_accept_main` | 16바이트 입력의 두 bool 경우를 실행한다. 필드 5개와 nil 반환을 증명한다. | 분리 메모리와 두 레이블 전제를 받는다. 실제 호출자 연결은 없다. `lean/Fk/ScAccept.lean:20` |
| `sc_unmarshal_accept_spec_k` | EthLib가 수용한 입력을 Go 필드 배치와 연결한다. | 성공 입력만 다룬다. `lean/Fk/ScSpec.lean:29` |
| `sc_reject_size_main` | 길이가 16이 아니면 전역의 두 단어를 반환한다. | 두 단어가 올바른 비nil 오류라는 초기화 명세는 별도다. `lean/Fk/ScReject.lean:20` |
| `sc_size_main` | 반환 주소로 돌아가며 `rax = 16`이다. | 직렬화 길이와의 연결 정리는 별도로 만들 수 있다. `lean/Fk/ScSize.lean:8` |
| `sc_marshal_main`, `sc_marshal_spec_k` | 용량이 충분한 경우 새 구간과 반환 슬라이스 정보를 증명한다. | 기존 접두사 보존과 용량 부족 경로는 없다. `lean/Fk/ScMarshal.lean:24`, `lean/Fk/ScSpec.lean:68` |
| `lu_iter`, `lu_exit`, `lu_loop` | 원소 복사, 경계 검사, 귀납을 Kraken에서 증명한다. | 전체 함수의 할당 계약과 독립된 성과다. `lean/Fk/LuLoop.lean:23`, `lean/Fk/LuLoop.lean:153` |
| `lu_accept_main` | Lean이 조건부 명제를 검사했다. | 전제 모순 때문에 실제 수용 실행의 근거로 사용할 수 없다. `ReviewKraken.lean:95` |

Scalars와 루프의 명시적 전제에서 같은 모순은 발견하지 않았다. 다만 이번 검토에서 이들 모두의 구체적인 ELF Host 존재 정리를 만들지는 않았다. 커널 통과와 실제 호출 가능성은 별개다.

Scalars의 EthLib 연결은 형식만 갖춘 결론이 아니다. `accepted_is_enc`가 실제로 `g`를 제공한다. 따라서 `P : ∀ g, bs = scEncode g → ...`는 대응하는 `g`가 없어 공허해지는 구조가 아니다. 그 `g`를 `sc_accept_main`에 적용한다. 근거: `lean/Fv1/Transfer.lean:31`, `lean/Fk/ScSpec.lean:52`.

ListU64의 EthLib 연결은 아직 없다. `lu_accept_main`은 원소 바이트 복사만 말한다. `SpecList`와 `Transfer`를 복사한 사실이 함수 연결 정리를 대신하지 않는다. 현재는 계약부터 고친 뒤 연결해야 한다. 근거: `REPORT.md:24`, `lean/Fk/LuAccept.lean:62`.

실제 Go 호출자가 전제를 보장하는지도 구분해야 한다.

| 전제 | 호출자 보장 여부 |
| --- | --- |
| 인수 레지스터와 spill 슬롯 | 고정한 Go 내부 호출 규약에서 정당화할 수 있다. 실제 호출 지점과 연결하는 정리가 필요하다. |
| bool 값 0 또는 1, 유효 슬라이스의 길이·용량 | 정상 Go 값에는 타당하다. 임의의 기계 상태나 unsafe 값에는 자동 적용되지 않는다. |
| 입력·출력·수신자·스택의 서로소 | 메모리 배치에 대한 추가 전제다. 중첩 타입과 공유 슬라이스에는 별도 검사가 필요하다. |
| 스택 가드보다 큰 `rsp` | 빠른 경로 전제다. Go가 호출할 수 있다는 사실만으로 스택 확장 분기를 배제할 수는 없다. |
| `LabelsFresh`와 함수 포함 관계 | 호출 규약의 사실이 아니다. 링크 산출물에서 증명해야 한다. |
| 쓰기 장벽 전역 0 | 일반 Go 호출자의 보장이 아니다. 가비지 수집 상태에 따라 달라진다. |
| 현재 `hms` | 실제 호출자가 보장할 수 없다. 전제 전체에서 모순을 도출했다. |

호출 규약은 함수 인수, 반환값, 스택을 전달하는 규칙이다. Go의 amd64 규약은 R14와 X15에 특별한 역할을 준다. SysV 규약을 그대로 적용해서는 안 된다. 근거: `/usr/local/go/src/cmd/compile/abi-internal.md:130`, `/usr/local/go/src/cmd/compile/abi-internal.md:413`, [Go 내부 호출 규약](https://go.dev/src/cmd/compile/abi-internal).

nil 수신자 문제는 사라지지 않았다. Kraken의 `⋆`는 메모리 조각의 실제 키 집합이 서로소임을 뜻한다. 이는 1a의 거리 기반 `Sep`보다 직접적이다. 하지만 주소 0도 키가 될 수 있다. `ReviewKraken.lean:136`에서 주소 0과 주소 4096의 두 조각이 분리 가능함을 증명했다. 근거: `upstream/Kraken/Separation.lean:11`, `upstream/Kraken/Mem.lean:34`.

더구나 `Effects.All`은 읽기·쓰기·실행 접근 요구를 그대로 통과시킨다. 메모리 조각의 존재만으로 운영체제 매핑, 접근 권한, 정규 주소 여부를 증명하지 않는다. 주소 유효성과 주소 넘침 배제는 실제 호출 연결 조건에 추가해야 한다. 근거: `upstream/Kraken/X64/OmniSemantics.lean:20`. 이는 Kraken 위 증명의 오류가 아니라 실제 기계로 옮길 때 필요한 조건이다.

자체 보조정리 439줄은 명령어 의미론의 우회가 아니다. `load_step`과 `store_step`은 Kraken의 분리 메모리 정리를 사용한다. `estep`은 `Host.eventually_of_interp`와 `eventually_trans`를 사용한다. `kunfold`와 `kat`은 Kraken의 해석 함수를 펼치고 이 정리들을 적용한다. 근거: `lean/Fk/Step.lean:64`, `lean/Fk/Step.lean:72`, `lean/Fk/Step.lean:110`, `lean/Fk/Step.lean:121`.

Fk 소스에는 `axiom`, `opaque`, `sorry`, `admit`, `native_decide` 선언이나 사용이 없다. `decide`는 여러 곳에 있다. `Bytes.lean`에는 `bv_decide`도 있다. 이번에는 57개 이름 있는 정리의 공리를 모두 조회했다. 모두 표준 공리 세 개의 부분집합이었다. `sorryAx`와 `Lean.ofReduceBool`은 없었다. 근거: `lean/Fk/Bytes.lean:15`, `KrakenAllAxioms.lean:1`, `review-kraken-all-axioms.log:1`.

커밋된 `AXIOMS.txt`는 11개 정리만 직접 조회한다. 그 정리들이 사용한 보조정리는 의존성에 포함된다. 그러나 Fk 전체 57개 정리의 전수 목록은 아니다. “모든 정리”라는 문구에는 전체 목록을 붙이는 편이 정확하다. 이번 57개 조회로 실제 공리 문제는 발견하지 않았다. 근거: `lean/scripts/Axioms.lean:1`, `TOOLS.md:71`.

표준 공리만 사용했다는 사실은 전제의 일관성을 보장하지 않는다. 이번 `hms` 반례가 그 차이를 보여준다.

변환기는 현재 아홉 함수에서는 다음 검사를 통과했다.

| 확인 | 결과 |
| --- | --- |
| 저장된 ELF 해시 | `bd3cb69823aab5f1056a4d009ca9b007cdb91f073032385c611863c58fbd2a7a`와 일치 |
| 함수 수와 명령어 수 | 9개, 582개 |
| ELF 바이트와 objdump 바이트 | 모두 일치 |
| LLVM의 독립 디코딩 | 582개 명령어의 바이트와 시작 경계가 일치 |
| 함수 범위와 내부 분기 | 기호 크기와 연속 바이트 범위가 맞는다. 내부 분기는 명령어 시작을 가리킨다. |
| `conv.py` 재생성 | 커밋된 정규화 어셈블리와 일치 |
| LLVM 출력과 Go 출력의 Kraken 구문 트리 | 9개 함수 모두 일치 |
| 정규화된 패딩 | 8곳 |

근거: `check-kraken-link.py:1`, `review-kraken-link.log:1`, `KrakenCompare.lean:1`, `review-kraken-llvm-ast.log:1`. 구문 트리는 파서가 만든 명령어 자료구조다. 양쪽 구문 비교에는 같은 변환기를 사용했다. 따라서 이 검사는 변환기 자체의 의미 보존 증명을 대신하지 않는다.

변환기의 구체적인 취약점도 재현했다. RIP는 명령어 주소 레지스터다. RIP 상대 주소는 다음 명령어 주소에 변위를 더해 계산한다.

| 항목 | 관찰과 필요한 검사 |
| --- | --- |
| 입력 행 누락 | `//`가 없는 명령어 행을 조용히 버린다. 주소 연속성과 전체 바이트 수가 맞지 않으면 실패해야 한다. `link/conv.py:65`, `review-kraken-link.log:13` |
| 내부 분기 | 명령어 중간 주소를 목표로 주면 정의되지 않은 레이블을 출력한다. 목표가 명령어 시작인지 확인해야 한다. `link/conv.py:87`, `review-kraken-link.log:14` |
| 이름 정리 | `pkg.f[uint8]`와 `pkg.f_uint8_`가 같은 이름이 된다. 원래 기호와 새 이름의 일대일 대응을 확인해야 한다. `link/conv.py:29`, `review-kraken-link.log:15` |
| RIP 상대 주소 | `현재 주소 + 원래 바이트 길이 + 변위` 계산은 맞다. 결과 기호 주소와 오프셋을 ELF에 대조해야 한다. `link/conv.py:98` |
| 크기 0 기호 | 가장 가까운 앞 기호를 쓰는 방식은 주소식을 만들 수 있다. 해당 메모리의 실제 소유 범위까지 증명하지는 않는다. `link/conv.py:41` |
| 즉시값 부호 | 변환기는 문자열을 유지한다. Kraken 파서는 64비트 비트 패턴으로 처리한다. 현재 대상에서는 LLVM과 구문 트리가 같았다. `upstream/Kraken/X64/Parser/Basic.lean:291` |
| 메모리 피연산자 | 레지스터·인덱스·배율은 유지하고 RIP 부분만 바꾼다. 새 명령어와 주소 크기 접두사는 별도 검사해야 한다. `link/conv.py:96` |
| nop 정규화 | 명령어를 삭제하지 않고 하나의 `nop`으로 바꾼다. 실제 ELF와 연결할 때 원래 크기를 유지해야 한다. `link/conv.py:102` |

현재 582개 명령어에서 잘못된 변환은 발견하지 않았다. 그러나 변환 실패를 모두 거부하지 않는 현재 구현은 1b 확대에 부족하다. 재생성 일치와 파서 통과만으로 연결 검사를 완료했다고 표시하면 안 된다.

전역 읽기를 분리 메모리 조각으로 표현하는 방식 자체는 건전하다. Kraken은 레이블 주소를 계산한 뒤 데이터 메모리에서 읽는다. README의 제외 범위를 “전역 쓰기만 불가능하다”라고 좁혀 해석할 근거는 없다. 초기화, 주소 배치, 실행 중 갱신을 사용자가 연결해야 한다는 한계를 남겨야 한다. 근거: `upstream/README.md:62`, `upstream/Kraken/X64/Semantics.lean:313`, `upstream/Kraken/X64/Semantics.lean:819`.

objdump의 RIP 상대 참조 42곳을 세었다. 같은 명령어가 여러 번 실행되는 횟수는 아니다.

| 기호 | 참조 수 | 용도 |
| --- | --- | --- |
| `type:*` | 16 | 타입 주소 계산 |
| `ssz.ErrInvalidSerialization` | 2 | 오류 인터페이스 두 단어 |
| `ssz.ErrSize` | 6 | 오류 인터페이스 두 단어 |
| `ssz.ErrBytesLength` | 2 | 오류 인터페이스 두 단어 |
| `runtime.writeBarrier` | 2 | FixedVec와 ListU64의 플래그 읽기 |
| `ssz.ErrListTooBig` | 4 | 인코더와 디코더 오류 |
| `go:string.*` | 4 | 오류 문자열 주소 |
| `go:itab.*errors.errorString,error` | 2 | 오류 타입 정보 주소 |
| `ssz.ErrIncorrectListSize` | 2 | 오류 인터페이스 두 단어 |
| `ssz.ErrInvalidVariableOffset` | 2 | 오류 인터페이스 두 단어 |

근거: `review-kraken-link.log:10`. `ssz.ErrOffset` 참조는 없다. 소스의 해당 분기는 앞선 검사 때문에 도달할 수 없다. 근거: 저장소 루트 `fv/kraken/target/types.ssz.go:231`, `fv/kraken/target/types.ssz.go:240`.

증명한 Scalars 거부 경로의 직접 전역 읽기는 `ErrSize`다. ListU64 수용 경로는 `writeBarrier`를 읽고 타입 주소를 전달한다. 이 경로들에서 누락된 직접 RIP 전역 읽기는 발견하지 않았다. 다만 `hms`는 타입 기술자의 메모리와 런타임 내부 접근을 검증하지 않는다. 오류 경로를 넓히면 itab를 통한 간접 읽기도 추적해야 한다. 근거: `link/out/norm/target.ListU64.UnmarshalSSZ.S:34`, `link/out/norm/target.ListU64.UnmarshalSSZ.S:41`, `link/out/norm/target.ListU64.UnmarshalSSZ.S:67`.

쓰기 장벽은 가비지 수집기에 포인터 변경을 알리는 장치다. 입구에서 플래그가 0이어도 `makeslice`가 가비지 수집을 시작할 수 있다. 현재 계약은 임의 프레임을 보존하므로 이 플래그도 그대로라고 요구한다. 이는 일반 런타임 동작의 보장이 아니다. 근거: `lean/Fk/LuAccept.lean:73`, `lean/Fk/LuAccept.lean:181`, `/usr/local/go/src/runtime/malloc.go:1336`, `/usr/local/go/src/runtime/mgc.go:259`.

1a의 `hinit`, `noBarrier`와 전역 값 전제의 역할은 비슷하다. 그러나 전체 계약의 강도가 같지는 않다. 1a `makesliceC`에는 힙 범위와 크기 조건이 있다. 새 `hms`에는 그 조건이 없고, 실제 Kraken 실행의 정상 종료를 모든 상태에 요구한다. 따라서 계약 표를 형식만 바꾸어 그대로 옮길 수는 없다. 근거: 저장소 루트 `fv/phase1/lean/Fv1/Contracts.lean:61`, `lean/Fk/LuAccept.lean:53`.

K0의 nightly 호환성 주장은 확인했다. Fk 파일 14개와 복사 명세 4개를 `lake env lean`으로 각각 검사했다. 기존 의존성 산출물은 재사용했다. 모든 소스 검사가 통과했다. 근거: `review-kraken-recheck.log:4`, `review-kraken-recheck.log:269`, `review-kraken-recheck.log:522`.

v4.35.0에서 `Lean.mkMarkdownDocComment`가 없고, 지정 nightly에서 존재함도 재현했다. Kraken 파서 지원 코드가 이 함수를 사용한다. 따라서 보고된 첫 실패 원인과 일치한다. 다른 잠재적인 v4.35.0 호환성 문제까지 없다고 보장하지는 않는다. 근거: `upstream/Kraken/SyntaxAffixed.lean:86`, `review-kraken-api-v435.log:1`, `review-kraken-api-nightly.log:1`.

기본 빌드는 `Fk`만 대상으로 한다. `Fk`는 `Fv1.SpecList`를 import하지 않는다. 현재 캐시에도 `SpecList.olean`은 없었다. 따라서 기존 572 jobs 빌드를 “복사 명세 전부 검사”의 근거로만 사용할 수는 없다. 이번에는 `SpecList.lean`을 직접 검사했고 통과했다. 최소 수정은 기본 검사 대상에 해당 명세를 포함하는 것이다. 근거: `lean/lakefile.toml:2`, `lean/lakefile.toml:25`, `lean/Fk.lean:1`, `review-kraken-recheck.log:522`.

nightly 고정 자체가 증명을 무효로 만들지는 않는다. 위험은 갱신 때의 API 변화, 증명 시간 변화, 의존성 재빌드다. Kraken 커밋, Lean 날짜, EthLib와 전이 의존성 커밋을 함께 고정해야 한다. Go 버전과 `GOAMD64`도 고정해야 한다. 현재 `build.sh`는 `GOAMD64`를 지정하지 않는다. 근거: `lean/lake-manifest.json:1`, `lean/lean-toolchain:1`, `link/build.sh:7`.

비용표는 관찰 기록으로는 유용하다. 그러나 학습 효과를 보정한 “Kraken이 더 싸다”는 결론은 자료에서 나오지 않는다.

| 비교 | 판단 |
| --- | --- |
| 첫 함수 4시간 대 24분 | ListU64 전체 수용과 Scalars 길이 거부를 비교한다. 같은 작업이 아니다. |
| Scalars 수용·거부 7분 대 36분 | Kraken이 더 느린 관찰도 있다. |
| marshal 25분 대 17분 | 빠른 경로에 한정한 개선 신호다. |
| 루프 30분 대 9분 | 재사용한 방법에서 유망한 결과다. 독립된 생산성 추정은 아니다. |
| ListU64 전체 4시간 대 61분 | 현재 Kraken 결과는 모순된 계약을 사용한다. 수정 비용과 EthLib 연결 비용도 빠졌다. |
| 빌드 62초 대 19.7초 | 파일 수와 검증 범위가 다르다. 공통 범위의 비교가 필요하다. |

근거: `REPORT.md:96`, `COST.md:38`, `COST.md:42`. 커밋 시간표에도 오차가 있다. `COST.md:19`는 문서 작업 종료를 00:40으로 적었다. 실제 tip 시각은 00:12:04이다. 세션 시작을 21:30으로 잡으면 약 2시간 42분이다. 이 기록을 정밀한 작업별 실측으로 취급해서는 안 된다. 근거: `review-kraken-commits.log:16`.

Kraken을 선택할 근거는 자체 명령어 모델과 디코더의 유지 부담을 줄이는 데 있다. 439줄은 증명 보조 코드이며 MiniRV 전체를 다시 만든 것은 아니다. 다만 명령어 확장, 런타임 계약, 링크 검사, 조합 정리의 비용은 남는다. 동일한 비공허 계약과 동일한 사후조건을 갖춘 대표 함수에서 다시 시간을 재는 것이 맞다.

“옮길 것·버릴 것”은 대체로 타당하다. EthLib 명세, 값 추상화, 오류 분류, 루프 불변식, 대상 타입, 회귀 사례는 옮길 수 있다. `SpecFixed`와 크기 명세는 아키텍처 독립 부분을 분리해야 한다. 계약은 이름과 의도만 재사용하고 전제를 다시 설계해야 한다. 근거: `REPORT.md:112`, `REPORT.md:115`.

MiniRV와 RISC-V 전용 Sail 증명은 Kraken의 의존성에서 제외해도 된다. 과거 검토와 재현 자료까지 삭제할 이유는 없다. Sail 보증이 빠진 부분은 신뢰 기반 문구에 남겨야 한다. 링크·대조·부정 사례 절차는 새 x64 구현으로 옮겨야 한다. 근거: `REPORT.md:117`, `REPORT.md:119`, `REPORT.md:137`.

C1–C16은 다음과 같이 갱신하는 것이 맞다. 아래 조건 중 MiniRV 복귀를 직접 요구하는 것은 없다.

| 조건 | 검토 판정 |
| --- | --- |
| C1 | 현재 함수에서 유효하다. 보조정리는 Kraken 의미론을 사용한다. |
| C2 | 레이블 해석 보조정리는 완료다. 실제 Host와 ELF 연결은 미완료다. |
| C3 | 런타임 파서를 쓰는 우회는 타당하다. 현재 5개 파서 일치 검사는 유용하다. |
| C4 | 현재 8개 패딩만 처리했다. 실제 bitlist 코드의 새 nop 형태가 남는다. |
| C5 | 전역을 분리 조각으로 표현할 수 있다. 주소, 초기화, 실행 중 안정성 조건은 남는다. |
| C6 | 미완료다. 현재 `hms`는 모순이다. 할당 자원과 런타임 소유 메모리를 포함해 다시 작성해야 한다. |
| C7 | 빠른 경로의 제한이다. 일반 Go 호출 보장이 아니다. 할당 중 가비지 수집도 포함해야 한다. |
| C8 | 루프 정리는 인정한다. 프레임을 보존하는 좋은 재사용 지점이다. |
| C9 | 독립 산술 보조정리는 타당하다. 정확한 커널 내부 원인까지 일반화하지 않는다. |
| C10 | `generalize` 우회는 타당하다. 대규모 함수의 비용은 별도 측정해야 한다. |
| C11 | 자동화 개선 과제다. 현재 보조정리를 쓰면 당장 필수 수정은 아니다. |
| C12 | 가능성 목록에서 실제 차단 항목으로 올려야 한다. `ValidateBitlist`에 `bsr`가 나온다. |
| C13 | 필요하다. `growslice` 계약과 접두사 보존을 함께 증명해야 한다. |
| C14 | 첫 반나절 평가를 권한다. 새 자동화가 계약의 모순을 자동으로 해결하지는 않는다. |
| C15 | 완료 기준으로 분류해야 한다. 장비 확보만으로 끝나지 않는다. 메모리 비교가 필요하다. |
| C16 | 고정 nightly에서 가능하다. 새 브랜치의 nightly로 올리면 전체 폐포를 다시 검사해야 한다. |

추가 조건도 필요하다.

| 추가 조건 | 완료 기준 |
| --- | --- |
| C17. 실행 파일 연결 | 바이트 전수 대응, 명령어 경계, 크기, 분기 목표, 전역 주소, 외부 기호, 레이블 유일성을 검사한다. |
| C18. 계약 비공허성 | 실제 크기 범위와 런타임 자원을 명시한다. 할당 전후를 만족하는 실행 증인을 만든다. |
| C19. 실제 호출 조건 | 유효 주소, 접근 권한, 별칭 정책, 스택과 가비지 수집 조건을 정리한다. |
| C20. 함수 조합 | 입력과 접두사 보존, 반환 스택, 필요한 레지스터를 사후조건에 남긴다. |
| C21. 명세와 범위 | ListU64 EthLib 연결, 실패 경로, 타입별 크기·인코더·디코더 완료표를 만든다. |
| C22. 검사 민감도 | 입력 누락을 실패 처리한다. 의미 변이는 지정 의미 정리에서 실패하게 한다. 주소만 바꾼 사례는 통과하게 한다. |

명령어 후보도 구체적으로 분리해야 한다. SSE는 x86 벡터 명령어 집합이다. XMM은 벡터 레지스터이고 GPR은 일반 레지스터다. `bsr`, `lzcnt`, `tzcnt`, `popcnt`, `bt`, `div`, `cqo`, `rep movsb`, `pxor`, `xorps`, XMM/GPR `movq`, `xchg`를 파서에 넣었다. 모두 거부됐다. `movups`와 `movslq`는 통과했다. 따라서 SSE 전체가 없다고 표현하면 틀리다. 이번에 실제 필수임을 확인한 것은 `bsr`다. 나머지 후보의 필요 여부는 전체 1b 빌드에서 결정해야 한다. 근거: `review-kraken-instructions.log:1`, `upstream/Kraken/X64/Syntax.lean:198`.

하드웨어 대조는 x86-64 Linux에서 수행해야 한다. 현재 Kraken 실행기의 `StateSummary`는 레지스터와 플래그만 비교한다. 수신자, 입력, 출력 접두사, 스택 경계의 메모리도 비교해야 이 작업에 충분하다. 근거: `upstream/KrakenRunnerX64.lean:28`.

`vcgen`은 검증 조건을 자동으로 만드는 도구다. 보관된 브랜치는 `a4cce2e`, Lean은 `nightly-2026-10-29`이다. `CallingConvention`은 고정된 두 경우의 열거형이 아니다. 보존 레지스터 목록과 인수 영역 함수를 갖는 구조체다. 따라서 Go 규약을 표현할 여지는 있다. 다만 R14, X15와 Go 스택 동작을 실제 증명으로 시험해야 한다. 근거: `vcgen-src/lean-toolchain:1`, `vcgen-src/Kraken/FunSpec.lean:10`.

Nic에게는 기존 질문에 세 가지를 추가하는 것이 좋다. 유한 메모리에서 할당 자원을 전달하는 권장 계약 형식을 묻는다. `Effects.All`이 버리는 접근 요구를 실제 주소 유효성과 연결하는 방법을 묻는다. 실제 ELF의 크기와 전역 주소를 가진 Host를 만드는 권장 절차를 묻는다. 질문 2는 사용자 정의 호출 규약과 X15 처리로 구체화한다. 질문 7에는 메모리 대조를 포함한다. 이 검토에서는 메시지를 보내지 않았다.

보고서의 이견 1, 3은 수용한다. 자체 단계 보조정리와 런타임 파서 사용은 의미론 우회가 아니다. 이견 2, 5는 범위 제한으로 수용한다. 이견 4는 실제 크기 연결 조건을 붙여 수용한다. 이견 6은 완료 조건으로 승격해야 한다. 이견 7은 1b 조합 전에 보완해야 한다. 이견 8은 `accepted_is_enc`가 있어 타당하다. 이견 9의 별도 경로 배치는 확인했다. 근거: `REPORT.md:153`, `REPORT.md:158`, `lean/Fk/ScSpec.lean:52`.

1b 새 세션에는 다음 순서를 권한다.

1. 현재 커밋과 이번 반례를 고정한다. `lu_accept_main`의 기존 완료 판정을 철회한다. `hms`의 크기, 타입, 힙, 프레임 조건을 다시 작성한다.
2. 첫 반나절에 `vcgen` 브랜치를 평가한다. Scalars 성공·거부와 ListU64 루프를 같은 사후조건으로 옮긴다. 수정한 할당 계약을 한 번 합성한다. 전체 명세 폐포의 빌드, 공리, 증명 시간, 메모리 사용량을 기록한다.
3. 반나절 종료 때 main과 vcgen 중 하나를 고정한다. Go 호출 규약과 프레임 보존이 안 되면 현재 main 보조정리를 유지한다. 자동화 선택을 이유로 계약 검사를 생략하지 않는다.
4. 1b 타입 목록과 Prysm 커밋을 초기에 고정한다. 기존 로드맵의 후보는 `Checkpoint`, `AttestationData`다. 실제 스키마와 생성 설정을 확인한 뒤 최종 목록으로 삼는다. 근거: 같은 scratchpad의 `roadmap-final.md:200`.
5. 타입 전체와 호출하는 SSZ 보조 함수를 먼저 빌드한다. 명령어, 외부 호출, 전역 목록을 만든다. `ValidateBitlist`의 `bsr`부터 처리한다. 지원하지 않는 명령어를 조용히 지우거나 신뢰 계약으로 숨기지 않는다.
6. 링크 검사 도구를 추가한다. 현재 임시 검사의 바이트·경계·LLVM 대조를 재사용한다. 외부 기호, Host 배치, 레이블 유일성, 잘못된 입력 거부를 추가한다.
7. x86-64 Linux 실행 환경을 확보한다. 명령어 대조와 함수 전체 대조를 구분한다. 같은 입력으로 Go 실행, Kraken 실행, 명세 결과와 메모리를 비교한다.
8. 수정한 ListU64 수용 정리와 EthLib 연결을 먼저 완료한다. `growslice` 한 경로와 접두사 보존도 완료한다. 이후 bitvector, bitlist, 고정 중첩 container, 가변 중첩 container, List[container] 순서로 진행한다.
9. Prysm 두 타입은 필요한 구성 요소가 준비되면 연결한다. List[container]에서는 여러 할당의 비중첩과 기존 객체 보존을 명시한다. 각 타입에 빈 값, 최대 값, 초과, 잘못된 offset과 오류 후 메모리 사례를 둔다.

신뢰 기반 문구는 다음처럼 바꾸는 것이 정확하다.

> 이 결과는 지정된 Kraken x64 어셈블리 의미론 위의 조건부 정리다. Scalars 성공 경로는 EthLib SSZ 명세와 연결됐다. ListU64 원소 루프도 증명됐다. 전체 ListU64 수용 정리는 현재 모순된 할당 계약을 사용하므로 실행 보장으로 인정하지 않는다. 실제 ELF 주소 배치와 Go 호출 상태의 연결은 별도 조건이다. 이 프로젝트의 하드웨어 대조는 아직 실행하지 않았다. 접근 권한과 가비지 수집 등 런타임 환경도 별도 조건이다. MiniRV의 RISC-V 전용 Sail 증명은 이 결과에 적용되지 않는다.

최종적으로 “조건부”는 유지하되 조건의 이유를 바꿔야 한다. 단순한 자동화 불편과 대조 미실행만 남은 상태가 아니다. 계약의 비공허성과 실제 bitlist 명령어 지원이 먼저다. 이 두 문제와 연결 검사를 해결하는 방향으로 Kraken 작업을 계속할 수 있다. 현재 증거로 MiniRV 복귀가 필요하다고 판정할 이유는 없다.

이번 검토에서 직접 수행한 확인은 다음과 같다.

| 확인 | 결과와 산출물 |
| --- | --- |
| 기준 커밋과 변경 경로 | `ee39240`, 16개 커밋, 변경은 `fv/kraken` 아래 |
| ELF 해시·바이트·경계 | 9개 함수, 582개 명령어 통과. `review-kraken-link.log` |
| LLVM/Go 구문 비교 | 9개 함수 일치. `review-kraken-llvm-ast.log` |
| 파서 재검사 | 기존 9개 함수 통과. `review-kraken-parse.log` |
| 원래 공리 파일 | 11개 출력이 커밋본과 정확히 일치 |
| 확대 공리 조회 | 이름 있는 정리 57개, 표준 공리만 사용. `review-kraken-all-axioms.log` |
| Lean 소스 검사 | Fk 14개와 명세 4개 통과. 의존성 캐시 재사용. `review-kraken-recheck.log` |
| 공허성·nil 확인 | 새 Lean 정리 3개 공리 조회 통과. `ReviewKraken.lean`, `review-kraken-lean.log` |
| K0 API 확인 | v4.35.0 실패, 지정 nightly 성공. `review-kraken-api-*.log` |
| bitlist 최소 빌드 | 실제 `bsr`와 추가 nop 확인. `kraken-bitlist-v1.objdump` |
| 후보 명령어 검사 | 12개 후보 형태 거부, 지원 형태 2개 통과, 추가 nop 거부. `review-kraken-instructions.log` |

재현은 대상의 `fv/kraken/lean` 디렉터리에서 `lake env lean <scratchpad>/ReviewKraken.lean`으로 할 수 있다. 전체 검토 보조 파일은 이 문서와 같은 디렉터리에 있다. 검사는 순차로 실행했다.

생략: 의존성 전체 클린 빌드, 하드웨어 실행, vcgen 증명 이식, 전체 1b·Prysm 빌드는 수행하지 않았다.
위험: 현재 `lu_accept_main`을 유효한 할당 포함 실행 증거로 사용하면 모순된 전제에 의존한다.
