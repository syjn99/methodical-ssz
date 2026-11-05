조건부.

게이트 1은 미통과로 판단한다.
현재의 “조건부 통과” 표시는 철회해야 한다.
Kraken 접근 자체는 계속할 가치가 있다.
그러나 공허한 BitL 수용 정리와 실제 함수에 맞지 않는 오류 계약이 남았다.
링크 검사는 의미가 바뀐 명령어도 통과시켰다.

검토 대상은 `syjn99/ssz-fv-phase1b`, HEAD `4e37f2e`다.
아래 저장소 경로는 `~/orca/workspaces/methodical-ssz/ssz-fv-phase1b` 기준이다.
`K`는 `fv/kraken`, `L`은 `fv/kraken/lean`이다.
`E`는 이 보고서가 있는 scratchpad 디렉터리다.
대상 워크트리는 수정하지 않았다.
검토 시작과 종료 때 기존 변경은 `K/negative/RESULT` 하나였다.
그 변경은 오프셋 변이 오류 위치가 114줄에서 126줄로 바뀐 내용이다.

**발견 1. P0. `GrowsliceC`가 다시 공허한 정리를 만든다.**

`newLen`에 상한이 없다.
할당할 크기와 `avail`의 관계도 없다.
그런데 사후조건은 `newLen ≤ newCap < 2^63`을 요구한다.
근거: `L/Fk/Contracts.lean:115`, `L/Fk/Contracts.lean:125`.

계약에 `rbx = rdi = 2^63`, `old = []`를 넣는다.
그러면 `num ≤ newLen`과 `old.length = esz * (newLen - num)`이 성립한다.
빈 `old`는 메모리를 소유하지 않는다.
기존 반환 슬롯, scratch, Heap 조각을 그대로 사용할 수 있다.
계약의 결론은 `2^63 ≤ newCap < 2^63`이다.
이는 모순이다.
원래 호출자의 길이가 작아도 계약의 전칭 양화 때문에 모순을 피하지 못한다.

다음 세 정리의 전제 전체에서 `False`를 Lean으로 증명했다.

| 대상 | 검토 증명 | 원본 근거 |
| --- | --- | --- |
| `bl_accept_main` | `E/Review1b.lean:63` | `L/Fk/BlAccept.lean:59`, `L/Fk/BlAccept.lean:85` |
| `bl_unmarshal_accept_spec_k` | `E/Review1b.lean:93` | `L/Fk/BlSpec.lean:256`, `L/Fk/BlSpec.lean:283` |
| `lum_grow_site` | `E/Review1b.lean:126` | `L/Fk/LuGrow.lean:26`, `L/Fk/LuGrow.lean:36` |

일반 모순 보조정리는 `E/Review1b.lean:30`이다.
반환 슬롯의 초기값이 임의여도 적용하는 증명은 `E/Review1b.lean:49`다.
`Eventually`에서 실제 도달 상태가 존재한다는 보조정리도 사용했다.
따라서 도달 관계의 다른 공허성에 기대지 않는다.
검증 로그는 `E/gpt6-1b-counterexample.log:1`이다.
사용 공리는 `propext`, `Classical.choice`, `Quot.sound`뿐이다.

B2.5 완료 표시와 BitL 수용 완료 표시를 철회해야 한다.
근거: `K/REPORT-1b.md:58`, `K/REPORT-1b.md:79`.
`CONTRACTS.md`의 “이 형식에서 이전 모순은 생기지 않는다”는 판단도 철회해야 한다.
근거: `K/CONTRACTS.md:57`.

수정은 우리 쪽 계약의 일이다.
서명 있는 길이 범위, `oldCap`, 성장 정책, 할당 한도, 소유 자원을 함께 제한해야 한다.
`newLen < 2^63`만 추가해서 완료 처리하면 안 된다.
수정 계약과 실제 호출 전제의 공동 증인을 먼저 만들어야 한다.
Kraken 수정은 이 결함의 해결 조건이 아니다.

**발견 2. P1. `FmtErrorfC`는 실제로 호출하는 `fmt.errorf`와 다르다.**

계약은 모든 인수 상태에서 `rax ≠ 0`을 요구한다.
근거: `L/Fk/Contracts.lean:95`, `L/Fk/Contracts.lean:102`.
그러나 Go 1.26.3의 내부 함수 `fmt.errorf`는 서식 변환이 필요 없으면 nil을 반환한다.
공개 함수 `fmt.Errorf`가 이후 `errors.New`를 실행한다.
근거: `/usr/local/go/src/fmt/errors.go:23`, `/usr/local/go/src/fmt/errors.go:35`.
검토용 소스 사본은 `E/gpt6-1b-fmt-errors.go:23`이다.

ListC의 `zero`, `past`, `tail` 오류는 인수 없는 일반 문자열이다.
근거: `K/target/types1b.ssz.go:243`, `K/target/types1b.ssz.go:254`, `K/target/types1b.ssz.go:280`.
기계어는 실제로 `fmt.errorf`를 호출한다.
nil이면 `runtime.newobject`로 오류 객체를 만드는 분기도 있다.
근거: `K/link/out/norm/target.ListC.UnmarshalSSZ.S:158`, `K/link/out/norm/target.ListC.UnmarshalSSZ.S:194`.
그런데 증명은 계약의 `rax ≠ 0`으로 그 분기를 배제한다.
근거: `L/Fk/LcReject.lean:396`, `L/Fk/LcReject.lean:407`.

내부 함수를 직접 호출하는 Go 시험도 실행했다.
두 일반 문자열에서 내부 함수는 nil, 공개 함수는 오류를 반환했다.
서식 인수가 있는 대조 사례에서는 내부 함수도 오류를 반환했다.
근거: `E/gpt6-1b-fmt-probe.go:9`, `E/gpt6-1b-fmt-probe.log:1`.
시험은 arm64 Go 1.26.3에서 실행했다.
고정 amd64 ELF의 분기 역시 역어셈블 결과로 확인했다.
근거: `E/gpt6-1b-fmt-errorf.objdump:1`.

따라서 ListC 거부 세 경로는 실제 실행 경로를 증명하지 않는다.
이 문제는 `%w`의 오류 정체를 생략한 정도가 아니다.
근거: `K/REPORT-1b.md:226`의 설명은 범위를 너무 좁게 잡았다.
ListU64의 서식 인수 있는 호출도 현재의 전칭 계약 전체를 정당화하지 못한다.
계약을 인수 조건에 맞게 나누고, nil 반환 뒤 객체 생성 경로를 증명해야 한다.

**발견 3. P1. 링크 검사가 NOP를 `retq`로 바꾼 파일을 통과시킨다.**

검사기는 원본 명령어가 NOP 정규화 목록에 있으면 새 명령어를 확인하지 않는다.
근거: `K/link/check.py:299`.
검토 사본에서 `target.BitVec.UnmarshalSSZ.S:9`의 `nop`를 `retq`로 바꿨다.
원본 주소는 `0x4b7297`이다.
원본 바이트는 `660f1f840000000000`이다.
변이 바이트는 `c3`이다.
검사기는 이를 `padding`으로 기록하고 `PASS all`을 출력했다.
근거: `E/gpt6-1b-nop-mutation.log:97`, `E/gpt6-1b-nop-mutation.log:166`.

현재 원본의 49개 정규화 결과는 로그상 NOP다.
이번 발견은 원본에 `retq` 변이가 있다는 뜻이 아니다.
검사기가 그 변이를 배제하지 못한다는 뜻이다.
따라서 C17과 C22의 완료 표시는 과도하다.
근거: `K/REPORT-1b.md:142`, `K/REPORT-1b.md:147`.

정규화 위치에서도 새 명령어와 허용된 인코딩을 검사해야 한다.
`all.S`와 개별 파일의 명령어 내용도 비교해야 한다.
현재는 레이블 목록만 비교한다.
근거: `K/link/check.py:230`.
또한 `.S` 변경 때 `SHash.lean` 갱신을 자동으로 확인해야 한다.
현재 Lake는 정교화기가 읽는 `.S` 파일을 직접 추적하지 않는다.
근거: `K/link/shash.sh:2`, `L/Fk/Include.lean:20`.

**발견 4. P1. 주 정리의 증인과 조합 가능한 사후조건이 아직 부족하다.**

적용 규칙은 주 정리마다 전제 전체의 구체 증인을 요구한다.
가변 길이는 빈 값, 1개, 최대 길이를 요구한다.
증인 없는 정리를 완료로 표시하지 말라고 명시한다.
근거: `ssz-fv-kraken@b6793b7:fv/AGENTS.md:66`.

`lu_accept_runs`는 이전 공허성 수정을 실제로 뒷받침한다.
구체 Host와 범프 할당기에서 `n ≤ 16`과 모든 입력 바이트를 다룬다.
빈 값, 1개, 16개 예제도 있다.
근거: `L/Fk/Witness.lean:172`, `L/Fk/Witness.lean:185`.
다만 이것은 Go 런타임 자체의 증명이 아니다.
`bump_makeslice`는 원소 크기 8, scratch 크기 0인 계약만 증명한다.
근거: `L/Fk/Bump.lean:42`.
바이트 할당과 여러 계약의 동시 만족을 자동으로 보장하지 않는다.

또한 많은 결론이 입력, 프레임 `R`, 스택 조각, `r14`를 버린다.
아래는 대표 사례다.

| 정리 | 결론에서 확인한 누락 | 근거 |
| --- | --- | --- |
| `fv_accept_main`, `bv_accept_main` | `R`, 스택 조각, `r14` | `L/Fk/FvAccept.lean:66`, `L/Fk/BvAccept.lean:40` |
| `ne_accept_main` | 입력, `R`, Heap, `r14`, `rbp` | `L/Fk/NeAccept.lean:114` |
| `lc_accept_main` | 외부 오프셋, `R`, 스택, `r14`, `rbp` | `L/Fk/LcAccept.lean:66` |
| `lc_accept_empty_main` | 입력, 스택, `r14` | `L/Fk/LcAcceptEmpty.lean:37` |
| `cp_accept_main`, `ad_accept_main` | `R`, 스택, `r14` | `L/Fk/CpAccept.lean:56`, `L/Fk/AdAccept.lean:78` |
| `ad_marshal_main`, `ne_marshal_main` | 수신자 그래프, `R`, 스택, `r14` | `L/Fk/AdMarshal.lean:79`, `L/Fk/NeMarshal.lean:251` |
| `lc_marshal_main` | 수신자 헤더, `R`, 스택, `r14` | `L/Fk/LcMarshal.lean:863` |

접두사 `pre` 보존은 확인했다.
그러나 접두사 보존만으로 함수 전체의 조합 조건이 충족되지는 않는다.
“디코더 수용 정리가 스택과 프레임을 돌려준다”는 일반화는 틀렸다.
근거: `K/REPORT-1b.md:220`.
C20은 Scalar와 ListU64를 Nested에서 사용하는 예제에 한정하면 성과가 있다.
전체 주 정리의 완료 조건으로는 부분 완료다.
근거: `K/REPORT-1b.md:114`, `K/REPORT-1b.md:145`.

**공허성 검토 범위와 나머지 주 정리의 판단.**

메모리 배치가 가능하다는 사실과 계약을 포함한 모든 전제의 만족 가능성은 다르다.
아래 “배치 가능”은 분리 조각과 수치 조건을 검토한 판단이다.
새로운 전체 Host 증명을 만들었다는 뜻은 아니다.
표에서 “미확정”인 계약의 공동 만족을 안전하다고 승인하지 않는다.

| 주 정리 묶음 | 판단과 구체 배치 근거 |
| --- | --- |
| `lu_accept_main` | 비공허성 증인이 있다. 수정은 인정한다. `L/Fk/Witness.lean:172`. |
| Scalar 수용·마샬·크기·길이 거부 | 계약이 없다. 필드와 스택을 서로 떨어진 영역에 둘 수 있다. `L/Fk/ScAccept.lean:26`. |
| `fv_accept_main` | 수신자 32바이트는 1+31로 분할한다. 입력 32+32와 별도다. Heap 예산은 32다. 두 계약의 공동 증인은 없다. `L/Fk/FvAccept.lean:50`. |
| `bv_accept_main`, F1 | 입력 1바이트와 수신자 헤더 24바이트를 분리할 수 있다. 바이트용 MakesliceC 증인이 없다. `L/Fk/BvAccept.lean:28`. |
| `bv_marshal_main`, 크기·길이 거부 | 외부 계약이 없다. 입력·출력·스택을 분리할 수 있다. 고유한 모순은 찾지 못했다. `L/Fk/BvSpec.lean:159`. |
| `bl_accept_main`, 수용 spec | 전제에서 False를 증명했다. 발견 1 참조. |
| `bl_marshal_main`, F2 | GrowsliceC를 쓰지 않는다. 분리된 원천·목적지와 MemmoveC를 쓴다. 전체 증인은 없다. `L/Fk/BlMarshal.lean:57`, `L/Fk/BlMarshal.lean:230`. |
| `ne_accept_main` | 스택 블록과 호출 슬롯은 인접하며 겹치지 않는다. 두 객체와 최대 128바이트에 예산 176을 둔다. NewobjectC 두 종류와 LuUAccC의 공동 만족은 미확정이다. `L/Fk/NeAccept.lean:92`, `L/Fk/NeAccept.lean:110`. |
| `ne_marshal_main` | 외부 계약이 없다. nil 아닌 S·L과 별도 출력 영역을 둔다. 원소 0·1·16을 배치할 수 있다. `L/Fk/NeMarshal.lean:217`. |
| `lc_accept_main` | 외부 길이 1·4와 내부 길이 0·16의 offset 구조는 명세에서 유도한다. 예산은 640이다. 3종 계약의 공동 증인은 없다. `L/Fk/LcAccept.lean:32`, `L/Fk/LcAcceptSpec.lean:163`. |
| `lc_accept_empty_main` | 계약이 없다. 입력은 `[4,0,0,0]`이고 X15=0을 둔다. 수신자 8+16바이트와 스택을 분리할 수 있다. `L/Fk/LcAcceptEmpty.lean:23`. |
| `lc_marshal_main` | 계약이 없다. 서로소 원소들을 분리곱으로 묶어 `Objs`를 구성할 수 있다. 임의 원소를 꺼내는 `hObjs`와 모순되지 않는다. `L/Fk/LcMarshal.lean:476`, `L/Fk/LcMarshal.lean:836`. |
| `cp_accept_main` | 입력 8+32, 수신자 32, 힙 32를 분리할 수 있다. MakesliceC·MemmoveC 공동 만족은 미확정이다. `L/Fk/CpAccept.lean:32`. |
| `cp_marshal_main` | 출력 8+32와 원천을 분리할 수 있다. MemmoveC 증인이 없다. `L/Fk/CpMarshal.lean:29`. |
| `ad_accept_main` | 8번 호출은 3종 계약을 재사용한다. 힙 예산은 3×32+2×32=160이다. 수신자 56과 입력 128의 조각은 겹치지 않는다. 공동 증인은 없다. `L/Fk/AdAccept.lean:47`. |
| `ad_marshal_main` | 128바이트 출력을 7조각으로 나눈다. Source와 Target를 별도 객체로 놓을 수 있다. MemmoveC 증인은 없다. `L/Fk/AdMarshal.lean:37`. |
| ListU64의 포맷 오류 거부 | 논리 모순은 추가로 증명하지 않았다. 실제 Go에 대한 FmtErrorfC와 ConvT64C 정당화가 부족하다. `L/Fk/LuRejectCall.lean:91`, `L/Fk/LuRejectCall.lean:326`. |
| ListC의 포맷 오류 거부 | 실제 Go 경로와 불일치한다. 발견 2 참조. |
| 나머지 크기·짧음·오프셋 거부 | 오류 전역, 입력, 스택을 분리할 수 있다. 전체 증인과 실제 ELF Host 연결은 별도 작업이다. `L/Fk/LuReject.lean:38`, `L/Fk/NeReject.lean:35`, `L/Fk/AdSpec.lean:35`. |

배치 검토에서는 작은 주소 구간들을 충분히 떨어뜨리고, guard=0, 큰 rsp, 충분한 cap을 선택할 수 있다.
빈 조각은 메모리를 소유하지 않으므로 길이 0 자체가 분리 모순을 만들지는 않는다.
ListC의 `hObjs`는 원소들을 유한 분리곱으로 구성하면 각 원소 외의 조각을 `Rest`로 둘 수 있다.
다만 실제 Go에서 가능한 모든 별칭까지 다루는 것은 아니다.
공유 객체, 입력과 수신자의 중첩, 출력과 원천의 중첩은 추가 명세가 필요하다.

**런타임 계약의 나머지 건전성.**

`MemmoveC`는 원천과 목적지가 서로소인 경우만 말한다.
따라서 Go memmove의 겹침 처리와 모순되지는 않는다.
그러나 겹치는 호출을 정당화하지도 않는다.
근거: `L/Fk/Contracts.lean:55`, `L/Fk/Contracts.lean:60`.

`NewobjectC`는 Heap을 감소시키며 새 영 블록을 분리한다.
이 형식은 이전의 무자원 할당 계약보다 낫다.
근거: `L/Fk/FunSpecs.lean:28`.
하지만 실제 타입 기술자의 내용, 할당기 상태, 스택 가드, 할당 중 GC 조건을 아직 연결하지 않았다.
`MakesliceC` 역시 서명 있는 int 범위와 Go의 `maxAlloc` 조건을 모두 적지 않는다.
근거: `L/Fk/Contracts.lean:40`, `/usr/local/go/src/runtime/slice.go:102`.

`ConvT64C`에는 큰 값의 8바이트 할당 예산 조건이 없다.
반환 포인터가 올바른 boxed uint64를 가리킨다는 조건도 없다.
근거: `L/Fk/Contracts.lean:78`, `/usr/local/go/src/runtime/iface.go:400`.
그 포인터를 fmt에 넘기므로, 다음 계약에 유효 인수 조건을 추가하면 이 누락이 드러난다.
`∃ avail'`만으로는 “힙이 줄어든다”는 설명도 보장하지 않는다.
`avail' ≤ avail` 같은 관계가 없다.

`FmtErrorfC`는 문자열, 인수 배열, 인터페이스 값의 유효성도 요구하지 않는다.
실제 fmt는 그 메모리를 읽고 사용자 포맷 메서드를 호출할 수 있다.
모든 인수에 대한 종료와 프레임 보존은 너무 강하다.
실제 내부 함수는 반환 슬롯 위의 인수 spill 영역도 쓴다.
현재 계약의 scratch는 반환 슬롯 아래뿐이다.
근거: `L/Fk/Contracts.lean:95`, `E/gpt6-1b-fmt-errorf.objdump:8`.

`ValidateBitlistC`의 수용 집합 자체는 Go 소스의 검사와 맞는다.
두 정의 모두 빈 입력, 마지막 0바이트, 구분 비트로 계산한 길이 초과를 거부한다.
근거: `ssz/unmarshal.go:30`, `L/.lake/packages/EthLib/EthLib/Serialization/Ssz/Codec/Deserialize.lean:217`.
그러나 계약에는 실패 경로의 오류 할당 자원이 없다.
입력 cap, goroutine 상태, 스택 조건도 없다.
근거: `L/Fk/BlAccept.lean:35`.
“`bsr`만 들어오면 바로 이 계약을 증명한다”는 예상은 과도하다.
현재 BitL 호출에 필요한 성공 입력 전용 계약부터 증명하는 편이 범위가 작다.

쓰기 장벽 0은 최초 상태만의 조건으로 충분하지 않다.
할당 중 바뀌지 않는다는 가정을 계약의 프레임 보존이 숨기고 있다.
보고서는 이 점을 인정한다.
근거: `L/Fk/Contracts.lean:32`, `K/CONTRACTS.md:45`.
실제 런타임 연결에는 레지스터 불변식, 읽기 전용 전역, 변경 가능한 런타임 상태를 구분해야 한다.

**함수 명세 조합은 어디까지 맞는가.**

`sc_uacc_holds`는 실제 `sc_accept_main`을 호출한다.
bool 값 조건은 `Scalars.e : Bool`에서 유도한다.
레이블 조건도 전달한다.
근거: `L/Fk/FunSpecs.lean:68`.

`lu_uacc_holds`는 MakesliceC, `S < 2^60`, 길이, cap, guard, Heap 조건을 유지한다.
스택 블록을 분해하고 호출 뒤 다시 합친다.
틈에 있는 두 스택 조각은 프레임으로 전달한다.
근거: `L/Fk/FunSpecs.lean:119`, `L/Fk/FunSpecs.lean:133`.
이 두 유도에서 전제를 빠뜨린 문제는 찾지 못했다.

다만 Nested 주 정리는 여전히 `ScUAccC`, `LuUAccC`를 인수로 받는다.
동일 Host에서 피호출자 코드와 두 유도 정리를 넣는 최종 증인이 필요하다.
근거: `L/Fk/NeAccept.lean:111`, `L/Fk/NeSpec.lean:181`.
함수 명세 유도의 존재와 전체 호출 그래프의 비공허성 증명은 구분해야 한다.

**EthLib 연결과 왕복 주장의 범위.**

의존성의 EthLib HEAD는 `862185680cf23ccf54d44eb25b63b26c5020597b`와 일치했다.
Desc의 uint 폭은 비트가 아니라 바이트다.
`uint 8`은 uint64에 맞는다.
요청한 Bitvector4, Bitlist2048, Nested, ListC, Checkpoint, AttestationData의 Desc에 스키마 오류는 찾지 못했다.
근거: `L/Fv1/SpecBitVec.lean:20`, `L/Fv1/SpecBitList.lean:20`, `L/Fv1/SpecNested.lean:19`, `L/Fv1/SpecListC.lean:19`, `L/Fv1/SpecPrysm.lean:22`.

`toValue`는 유효한 논리 값의 SSZ 정보를 보존한다.
포인터 주소, cap, Go 패딩, protobuf 상태까지 보존한다는 뜻은 아니다.
BitVec의 정의역은 `b < 16`이다.
그러므로 단사성이 F1의 잘못된 입력 수용을 감추는 증명이 되지는 않는다.
근거: `L/Fv1/SpecBitVec.lean:26`, `L/Fv1/SpecBitVec.lean:64`.

ListC 단사성도 실제로 존재한다.
BitL 단사성은 왕복 정리 안에 증명되어 있다.
근거: `L/Fk/RoundTrip1b.lean:36`, `L/Fk/RoundTrip1b.lean:60`.
`SPEC.md`의 “ListC 단사는 하지 않았다”는 문구는 오래됐다.
근거: `K/SPEC.md:29`.

`accepted_is_enc`는 EthLib의 역직렬화 정준성에서 올바르게 유도한다.
입력 조각 전제를 제공하면 기계어 수용으로 이어지는 wrapper가 여러 타입에 있다.
근거: `L/Fv1/Transfer.lean:31`, `L/Fk/FvSpec.lean:41`, `L/Fk/AdLink.lean:17`.
`P : ∀ g, bs = enc g → ...` 자체는 숨은 공허성이 아니다.
EthLib 수용에서 해당 g가 존재함을 얻고 `P`를 적용한다.

그러나 `bv_unmarshal_accept_spec_k`에는 기계 상태나 `Eventually`가 전혀 없다.
결론은 `∃ g, g.toValue = v ∧ bs = #[g.b]`뿐이다.
근거: `L/Fk/BvSpec.lean:117`.
별도의 `bv_accept_main`과 합칠 수 있지만, 현재 완료표가 지목한 정리 자체는 기계어 연결 정리가 아니다.
근거: `K/REPORT-1b.md:78`, `K/SPEC.md:75`.

`fv_marshal_spec_k`, `lc_marshal_spec_k`도 바이트 식의 명세 정리다.
기계어 실행을 포함하는 최종 wrapper와 구분해야 한다.
근거: `L/Fk/FvSpec.lean:87`, `L/Fk/LcMarshal.lean:1061`.
왕복 정리들은 EthLib에서 `enc g`를 다시 읽는 정리다.
실제 인코더 실행 뒤 디코더를 실행하는 연속 기계 실행 정리는 아니다.
근거: `L/Fk/RoundTrip1b.lean:20`, `L/Fk/RoundTrip1b.lean:54`.

역방향 “기계어가 받으면 EthLib도 받는다”는 전체 정리가 없다.
BitVec에서는 F1 때문에 그 명제가 거짓이다.
Scalar bool 오류, Nested 감싼 오류, ListC 루프 오류, BitL 검증 실패 경로는 비어 있다.
근거: `K/SPEC.md:46`, `K/SPEC.md:58`, `K/SPEC.md:64`, `K/SPEC.md:73`.
FixedVec, Checkpoint, AttestationData는 고정 길이 수용·거부 조각이 가장 완결되어 있다.
그 경우도 런타임 계약과 실제 상태 전제 안에서만 결론이 나온다.
ListU64의 네 거부 경로에는 발견 2의 계약 정정이 먼저 필요하다.

**F1과 F2는 재현되며, F2 수정 범위를 넓혀야 한다.**

기존 Go 시험 두 개를 시험 결과 캐시 없이 다시 실행했고 모두 통과했다.
근거: `E/gpt6-1b-f12.log:1`.
F1 Lean 정리는 EthLib의 paddingBits 오류와 기계어 nil 반환을 함께 말한다.
근거: `L/Fk/BvSpec.lean:124`.
F2 Lean 정리는 258바이트 출력의 EthLib 거부와 마샬 성공을 함께 말한다.
근거: `L/Fk/BlMarshal.lean:230`.
F2는 공허한 GrowsliceC를 사용하지 않고 MemmoveC만 사용한다.
다만 두 반례의 기계어 실행 전제에 대한 독립적인 전체 증인은 아직 없다.
Go 시험이 실제 생성 코드의 결함을 별도로 확인한다.

생성기는 bitlist의 MaxSize를 바이트 배열 길이에 그대로 적용한다.
근거: `sszgen/render/marshal.go:252`, `sszgen/render/marshal.go:348`.
상한을 단순히 257바이트로 바꾸면 수정이 끝나지 않는다.
257바이트에서 마지막 바이트가 2이면 논리 길이는 2049비트다.
빈 배열과 마지막 0바이트도 현재 인코더가 받는다.
추가 Go 시험에서 이 세 입력은 마샬에 성공하고 디코더에서 거부됐다.
정상 2048비트 입력은 양쪽에서 성공했다.
근거: `E/gpt6-1b-bitlist-edges.go:7`, `E/gpt6-1b-bitlist-edges.log:1`.

로컬에 있는 fastssz v1.0.0에서도 같은 단위 오류를 코드 수준에서 확인했다.
TypeBitList 마샬은 `validate()`를 부르고, 검사는 `len(field)`와 `v.s`를 비교한다.
bitlist의 `s`에는 bit maxSize를 넣는다.
근거: `~/go/pkg/mod/github.com/ferranbt/fastssz@v1.0.0/sszgen/generator/marshal.go:65`, `validate.go:17`, `generator.go:1160`.
fastssz 최신판과 실제 Prysm 고정 의존성 버전의 실행 시험은 하지 않았다.
따라서 모든 fastssz 버전에 같은 문제가 있다고 단정하지 않는다.

**Prysm 두 타입의 완료 표현.**

현재 대상은 Prysm의 SSZ 필드를 옮긴 별도 Go 구조체다.
protobuf 필드와 원래 패키지 타입 배치가 다르다.
근거: `K/target/prysm/types.go:1`, `K/REPORT-1b.md:225`.
기계어 정리의 필드 주소도 이 축약 구조체에 맞는다.
근거: `L/Fk/AdAccept.lean:69`.

“Prysm 2타입 완료”는 제목과 게이트 요약에서 사용할 수 없다.
다음 문구가 정확하다.

> Prysm v7.1.8의 두 SSZ 스키마를 옮긴 축약 Go 구조체의 생성 코드를 검토했다.
> 정리는 고정 시험 ELF의 일부 경로를 다룬다.
> 실제 Prysm 구조체 배치와 Prysm 바이너리는 증명 대상이 아니다.

실제 Prysm 적용에는 원본 타입으로 재생성·재컴파일하고, 배치·타입 기술자·링크·증인을 다시 검사해야 한다.

**재현 결과와 공리 검사의 범위.**

모든 쓰기 작업은 E 아래 사본에서 수행했다.
무거운 Lean 작업은 순서대로 하나씩 실행했다.
프로세스 목록에서 다른 활성 빌드가 없는지 확인했다.

| 검사 | 결과 | 증거 |
| --- | --- | --- |
| 원본 `link/check.py` | 28함수, 2751명령어, 2702바이트 동일, 49 NOP 정규화 | `E/gpt6-1b-copy/fv/kraken/link/out/RESULT` |
| 원본 번들 | `1e9216712e235dce09548ad7fa96a1f6defbba89c6a741c3468bfe02f444906c` 일치 | 같은 RESULT 마지막 줄 |
| `check.py --selftest` | 기존 6사례 예상 결과 일치 | `E/gpt6-1b-copy/fv/kraken/link/out/SELFTEST` |
| `negative/run.sh` | offset·maxlen·loop 실패, control 성공 | `E/gpt6-1b-negative.log:1` |
| 추가 `cmp 4 → cmp 5` | `Fk.FvLoop` 빌드 실패, `fv_iter`의 50줄에서 실패 | `E/gpt6-1b-extra-mutation.log:41` |
| 추가 NOP → retq | 링크 검사가 잘못 성공 | `E/gpt6-1b-nop-mutation.log:97` |
| `tools/axioms.sh` | `TOTAL 597 NONSTANDARD 0` | `E/gpt6-1b-copy/fv/kraken/AXIOMS.txt` |
| 모든 선언으로 확장한 공리 검사 | `TOTAL 4033 NONSTANDARD 0` | `E/gpt6-1b-all-axioms.log:1` |
| 공허성 Lean 반례 | 세 원본 정리의 전제에서 False | `E/Review1b.lean:63`, `E/gpt6-1b-counterexample.log:1` |
| F1·F2 Go 시험 | 둘 다 성공 | `E/gpt6-1b-f12.log:1` |

원본 AXIOMS 도구는 import된 Fk·Fv1·Fv의 공개 정리만 열거한다.
내부 선언과 def는 원래 검사에서 빠진다.
근거: `L/tools/Axioms.lean:26`.
이번에는 그 두 필터를 제거한 검사도 실행했다.
같은 세 모듈 계열의 4,033개 선언에서 비표준 공리는 없었다.
이 수치는 전체 Kraken·EthLib 환경의 모든 선언 수가 아니다.
의존한 공리는 재귀적으로 조회한다.
import하지 않은 vcgen 평가 모듈은 포함하지 않는다.

대상 Lean 소스에서 금지된 선언·전술 사용도 검색했다.
`sorry`, `admit`, 새 `axiom`, `opaque`, `native_decide`, `bv_decide` 사용은 발견하지 못했다.
`Std.Tactic.BVDecide` import와 `bv_omega`는 `bv_decide` 호출과 다르다.
근거: `L/Fk/Step.lean:6`, `L/Fk/Step.lean:23`.
그러나 비표준 공리 0개는 계약의 일관성을 보장하지 않는다.
이번 GrowsliceC 반례도 표준 공리만 사용한다.

부정 시험 도구는 종료 코드를 버리고 `error: Fk/` 문자열만 찾는다.
다른 종류의 빌드 실패를 PASS로 기록할 수 있다.
예상 변이 결과와 대조군 결과가 다르더라도 스크립트가 성공할 수 있다.
근거: `K/negative/run.sh:31`.
이번 재현에서는 실제 지정 모듈 오류와 대조군 빌드 성공을 확인했다.
도구 자체에는 종료 코드와 지정 정리 오류 위치 검사를 추가해야 한다.

하드웨어 대조는 실행하지 않았다.
기존 스크립트는 amd64 Go 출력과 arm64 Go 출력을 비교한다.
Kraken 실행 결과와 CPU 실행 결과를 비교하는 도구는 아니다.
기대값도 검사 대상 Go 코드로 생성한다.
근거: `K/semtest/run.sh:20`, `K/semtest/gen-expected.sh:4`.
이는 아키텍처 간 회귀 검사로는 유용하다.
독립 명세 대조와 Kraken 메모리 의미론 검증을 대신하지 못한다.
적용 규칙의 알려진 답 요구도 충족하지 않는다.
근거: `ssz-fv-kraken@b6793b7:fv/AGENTS.md:99`.

**B0 판단은 다시 측정해야 한다.**

main을 유지하는 결정은 툴체인과 의미론 변경 비용 때문에 합리적이다.
그러나 현재 B0 실패를 vcgen의 자동화 부족만으로 해석하면 안 된다.

평가 예제는 SSZ 입력 16바이트와 Go 수신자 첫 16바이트가 같다고 요구한다.
근거: `K/vcgen/Vg/ScAccept.lean:35`.
Scalar 필드의 SSZ 위치는 0,1,3,7,15다.
Go 구조체의 위치는 0,2,4,8,16이다.
근거: `L/Fk/ScAccept.lean:28`, `L/Fk/ScAccept.lean:40`.
예를 들어 B=1이고 나머지 필드와 패딩이 0이면 두 배열은 다르다.
따라서 평가 사후조건 자체가 틀렸다.

Mapped·writes 영역도 `rsp+8`을 지정한다.
실제 명령어와 main 증명은 `rsp+16`을 쓴다.
근거: `K/vcgen/Vg/ScAccept.lean:30`, `K/vcgen/Vg/ScAccept.lean:37`, `L/Fk/ScAccept.lean:27`.
로그에 남은 `rsp+16` 적재 의무는 단순 전술 부족으로 볼 수 없다.
근거: `K/vcgen/b0-goals.txt:4`.

“12/16 VC가 열렸다”는 정확한 수치도 저장 로그만으로 독립 재현하지 못했다.
`b0-scaccept.txt`에는 오류 세 줄이 있고, `b0-goals.txt`에는 잘린 목표 16개가 있다.
근거: `K/vcgen/b0-scaccept.txt:1`, `K/vcgen/b0-goals.txt:1`.
이번 리뷰에서 별도 vcgen 툴체인을 재빌드하지 않았다.
올바른 필드별 사후조건과 스택 영역으로 평가를 고친 뒤 다시 측정해야 한다.

**비용과 신뢰 문구의 정정.**

커밋 간격을 같은 에이전트의 틀 복사 시간이라고 한 단서는 적절하다.
근거: `K/REPORT-1b.md:197`, `K/REPORT-1b.md:223`.
그러나 5분짜리 growslice 사례는 공허했다.
이를 근거로 한 6–9시간 외삽은 철회해야 한다.
근거: `K/REPORT-1b.md:201`.
계약당 증인 30–60분과 ValidateBitlist 1–2시간도 검증된 생산성 수치가 아니다.
계약 수정, 런타임 상태, 실패 경로, 실제 ELF Host 연결 비용이 빠졌다.
근거: `K/REPORT-1b.md:210`, `K/REPORT-1b.md:211`.
고정 수치 대신 다음 세션에서 작은 완료 단위 하나의 수정·증인·재검사 시간을 측정해야 한다.

다음 신뢰 문구를 권한다.

> 정리는 고정 Kraken 의미론과 명시한 외부 함수 가설 아래의 조건부 결과다.
> 일부 런타임 계약에는 구체 실행 증인이 없다.
> 현재 BitL 수용과 growslice 지점 정리는 모순된 전제 때문에 사용할 수 없다.
> 오류 계약 일부는 고정 Go 바이너리의 실제 동작과 다르다.
> 런타임·GC·접근 권한·전체 기계 왕복·실제 Prysm 바이너리는 증명하지 않았다.
> 링크 검사와 하드웨어 대조에도 미완료 항목이 있다.

**필수 수정 목록.**

1. GrowsliceC의 모순을 고치고, 관련 세 정리의 완료 표시를 철회한다.
2. `fmt.errorf`와 `fmt.Errorf`를 구분하고, ListC 오류 세 경로를 실제 nil 분기로 다시 증명한다.
3. 런타임 계약에 인수 유효성, 자원 예산, 스택 창, 전역 상태를 명시한다.
4. 각 주 정리의 전체 전제 증인을 만든다. 가변 길이는 빈 값·1개·최대 길이를 포함한다.
5. 입력·수신자·접두사·프레임·스택·보존 레지스터를 결론에 남긴다.
6. NOP 정규화 검사를 고치고, `retq` 변이를 필수 부정 시험으로 추가한다.
7. 부정 시험의 종료 코드와 지정 정리 실패를 검사한다. SHash 갱신도 강제한다.
8. BitVec 기계어 연결 wrapper와 실제 기계 실행 조합 정리를 추가한다.
9. F1·F2 수정 뒤 수용·거부·인코딩 정리를 새 ELF에 맞춰 다시 증명한다.
10. 실제 Prysm 증명과 축약 스키마 시험을 구분한다. 조건표와 완료표를 정정한다.
11. B0 예제의 Go 배치와 스택 명세를 고친 뒤 vcgen을 다시 평가한다.
12. EthLib 기대값과 Kraken·CPU 메모리 대조를 별도로 준비한다.

1–8, 10–11은 현재 Kraken을 수정하지 않고 우리 쪽에서 진행할 수 있다.
9는 생성기 수정 세션의 일이다.
12는 x86-64 Linux 실행 환경도 필요하다.
Nic에게 요청할 항목은 `bsr`, 파서 정교화기 보완, vcgen 명세 형태, 메모리 대조 도구다.
계약 모순과 잘못된 함수 명세는 Nic의 기능 추가로 해결되지 않는다.

**다음 세션 브리프에 넣을 내용.**

- 첫 완료 단위를 “코드가 빌드됨” 대신 “전제 증인 + 기계어 정리 + 링크 + 부정 시험”으로 정한다.
- 이번 `Review1b.lean` 세 모순 정리를 회귀 자료로 유지한다.
- 계약을 고치면 작은 정상 호출의 구체 증인을 먼저 증명한다.
- ListC `zero/past/tail`에서 내부 fmt nil 반환 뒤의 객체 생성 경로를 다룬다.
- F1은 0x10뿐 아니라 모든 상위 패딩 비트를 검사한다.
- F2는 빈 배열, 끝 0, 2048비트, 2049비트, 258바이트를 검사한다.
- BitL은 성공 입력 전용 ValidateBitlist 증명과 전체 오류 계약을 분리해서 계획한다.
- 생성기 수정 시 ELF, objdump, `.S`, SHash, 정리, 공리 목록, 기대값을 함께 갱신한다.
- 1c 증명 생성기는 계약 가설과 증인을 함께 출력하도록 설계한다.
- 1c는 함수별 배치 명세와 보존 프레임을 입력으로 받도록 설계한다.
- 1c 성능 측정은 이번 계약·링크 결함을 수정한 기준선에서 시작한다.
- 게이트 1 재심사는 위 필수 수정과 실제 완료 범위 표를 기준으로 한다.

검토 한계: 모든 주 정리의 새 Host 증인을 이 리뷰에서 구현하지 않았다.
전체 clean build, vcgen 재빌드, x86-64 하드웨어 대조, 최신 fastssz 검증은 하지 않았다.
확인한 공허성·오류 계약·링크 검사 결함만으로 현재 게이트 1 통과를 승인할 수 없다.
