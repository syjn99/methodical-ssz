# REPORT: Kraken x64 코덱 검증의 현재 상태

기준: 수정 3(링크 재설계, `claude/ssz-fv-reprove-fix3`). 메모리 최적화 `e6e386d` 위다.
방향은 `DIRECTION.md`, 세션 이력은 `HISTORY.md`, 고정 버전은 `TOOLS.md`에 있다.

## 0. 판정

**조건부. 게이트 1 미통과.**

게이트 1을 막는 조건:

1. ListC 원소 오프셋 순서 거부는 첫 쌍만, 원소 오류 전달(`"Items: %w"`)은 짧은 원소 하나(ListU64가 `ssz.ErrSize`를 돌려주는 경우)만 닫았다(4절 7). 정렬·원소 수·끝 오프셋 초과 거부는 없다.
2. 런타임 계약은 추상 모델로만 만족 가능성을 보였다. Go 런타임 정교화는 없다(3절).
3. 디코더의 EthLib 양방향 수용 정리는 BitVec(1바이트)뿐이다.
4. x86-64 하드웨어 대조를 하지 않았다. 이 호스트는 arm64다.

수정 3에서 닫은 것: 링크 검사 (f)(g)(h)·역할 분류·`golits.go` 삭제(Lake 입력과 ELF 데이터 include로 대체), 오류 증인의 타입 기술자와 초기화된 오류 전역, Scalars 비nil 거부, 사후조건 잔여 넷, ListC 원소 오프셋 순서 거부(첫 쌍), 게이트 표 정정.

1c(phase1c, 생성기와 Prysm 목록)는 10절이다. 게이트 1c 미통과.

수치(수정 3 끝, 차가운 프로젝트 빌드 뒤):

- `lake build`: 867 jobs, 성공(차가운 프로젝트 빌드 Built 163, 의존성은 따뜻함, 메모리 감시 아래).
- 공리: 정리 `TOTAL 1658 NONSTANDARD 0`(`AXIOMS.txt`), 모든 선언 `TOTAL 8477 NONSTANDARD 0`(`AXIOMS-ALL.txt`).
- 시험 타입 9개. 증인 파일 81개.
- 링크 검사 PASS(검사 (a)–(f)). 자기 시험 11개 기대대로. `data.py --check`: 재생성 = 추적 파일.
- 부정 시험 20개 기대대로(`negative/RESULT`, FAIL 17 + 대조군 PASS 3).
- goval: 81 파일, 위반 0, 미검사 2. 오류 증인의 타입 기술자 6곳과 오류 전역 20곳을 검사한다.
- `go test ./fv/kraken/semtest/`: PASS(F1, F2).

## 1. 완료 단위

주 정리 하나의 완료는 여섯 요소를 모두 가진다.

1. 계약 또는 정리.
2. 구체 Host에서 전제 전체의 증인. 가변 길이는 빈 값, 1개, 최대.
3. 기계어 정리.
4. 링크 검사 PASS. 정리가 읽는 데이터는 ELF include다(`Fk/Data.lean`).
5. 부정 시험: 변이가 지정 정리 안에서 실패하고 대조군이 통과한다.
6. Go 값: `lean/tools/wit/goval.py`가 `layout.json`(gc amd64 배치)으로 검사한다. 읽지 못한 값은 미검사로 센다.

추상 증인(요소 2)과 Go 값 완료(요소 6)는 다른 주장이다.
요소 6은 크기·정렬·패딩·bool·슬라이스·겹침을 본다.
수정 3부터 `%w` 증인의 타입 기술자(Size_, Kind_)와 오류 전역의 초기화도 본다.
중간 상태의 Go 값은 보지 않는다.

## 2. 게이트 1 표

열의 뜻:

- "거부 경로": 디코더 오류 분기 중 기계어 정리로 닫힌 것 / 전체(Go 소스 기준).
- "증인": 빈·1·최대와 안쪽 길이.
- "Go 값": goval 결과. 1절의 범위만 본다.
- "추상 모델": 그 타입의 정리가 기대는 계약. 모든 계약은 추상 모델만 있다.
- "조합": 두 호출 조합 정리와 전체 전제 증인.
- "사후": 주 정리 결론의 자원. "동일"은 메모리 전체가 같다는 결론이다. 이것은 프레임 보존보다 강하다.

| 타입 | 수용 방향 | 거부 경로 (닫힘 / 남음) | 증인 | Go 값 | 추상 모델 | 부정 시험 | 조합 | 사후 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Scalars | EthLib→기계어 + bool 거부(EthLib 거부 정리 포함) | 2/2: 크기, bool > 1. 비nil: `sc_reject_bool_err`(전역 초기화 전제 `e0 ≠ 0`) | 고정(수용, 거부, 마샬, 조합). 거부 증인의 전역은 초기화된 값 | 위반 0. 전역 초기화 검사 | 없음 | scbool, scrbword | `sc_unmarshal_then_marshal` + WitScComp | 수용·마샬·bool 거부 정확, 마샬 r14 보존. 크기 동일 |
| FixedVec | EthLib→기계어 | 1/1: 크기 | 고정 | 위반 0 | makeslice, memmove | loop, control | 없음 | `R` + True. 크기 동일 |
| ListU64 | EthLib→기계어 | 4/4: 짧음, 오프셋, 정렬, 초과 | 0·1·16, 거부 둘 | 위반 0. 오류 증인의 타입 기술자 = ELF(Lean 이름 `errorStringPtrType`이 근거, goval은 Size_·Kind_만 본다), 전역 초기화. `%d`의 int 기술자 내용은 증인에 없음 | makeslice, growslice, convT64(상자), fmt `%d %w` | offset, maxlen | `lu_unmarshal_then_marshal` + WitLuComp | 수용 정확, 나머지 `R` + True. 크기 동일 |
| BitVec | 양방향(1바이트) | 2/2: 크기, 패딩 | b < 16, 16 ≤ b | 위반 0. 오류 증인 타입 기술자 = ELF(근거는 Lean 이름, goval은 Size_·Kind_) | makeslice, fmt nil·`%w`, newobject 16 | vbvje, bvnochk | `bv_unmarshal_then_marshal`(증인 없음) | 수용·마샬 정확. 크기 동일 |
| BitL | EthLib→기계어(규칙 동치) | 3/3: 짧음, 오프셋, ValidateBitlist 오류 | 1, 257바이트 / 2049비트, 꼬리 [0] | 위반 0 | ValidateBitlist 두 계약(rodata), growslice, memmove, fmt `%w` | gsnum, blmnochk, blrity | 없음 | `R` 보존. 크기 동일 |
| Nested | EthLib→기계어 | 2/4. 남음: S 오류, L 오류(래핑) | 0·1·16 | 위반 0 | newobject 24, Scalars·ListU64 함수 명세 | neoff | 없음 | 수용·마샬·크기 `R` 보존 |
| List[container] | EthLib→기계어 | 7/10: 짧음, 오프셋, 0 오프셋, 짧은 첫 오프셋 둘, 원소 오프셋 순서(`lc_reject_offset_order_main`, 원소 2개 이상의 첫 쌍), 원소 디코드 오류(`lc_reject_item_main`, 원소 1개, 1–3바이트, ListU64의 `ErrSize`). 남음: 정렬(`%d`), 원소 수(`%d %w`), 원소 끝 오프셋 초과(`%d`) | 바깥 0·1·4, 안쪽 1×1, 4×16, 0·1·16. 순서 거부: 오프셋 [8, 4](`WitLcO`). 원소 오류: [4,0,0,0, 1,2](`WitLcI`) | 위반 0 | makeslice 두 지점, newobject 16·24, fmt nil·`%d %d`(`FmtErrorfDDC`)·`%w`(`FmtErrorfWC`), convT64, ListU64 함수 명세 둘(`LuUAccC`, `LuURejShortC`) | nilerr, lcorder, lcitems | 없음 | `R`과 죽은 스택(`lcStk`) 보존. 크기 동일 |
| Prysm 축약 Checkpoint | EthLib→기계어 | 1/1: 크기 | 고정 | 위반 0. `WitCpM` dst 기호 길이 미검사 | makeslice, memmove | cplen | 없음 | `R` 보존. 크기 동일 |
| Prysm 축약 AttestationData | EthLib→기계어 | 1/1: 크기. 하위 Checkpoint 오류 미도달은 정리가 없다 | 고정 | 위반 0 | makeslice, memmove, newobject 32 | adcopy | 없음 | `R` 보존. 크기 동일 |

"크기 동일" 정리 여덟: `ad_size_main`, `bl_size_main`, `bv_size_main`, `cp_size_main`, `fv_size_main`, `lc_size_main`, `lu_size_main`, `sc_size_main`.
`ne_size_main`은 `R`을 보존한다.

타입 전체 완료로 표시할 수 있는 타입은 없다.
Scalars와 ListU64는 수용·마샬 조합 증인만 완료다.
Scalars의 비nil 오류 연결과 Size 사후조건은 수정 3에서 닫았다. 조합은 `hupd`와 전체 증인까지다. 실제 호출자 명령 실행은 없다.
ListU64 오류 증인의 타입 기술자와 전역은 수정 3에서 채웠다. `%d` 인수의 int 기술자 내용은 증인에 없다.
나머지 타입은 조합이 없거나 거부 경로가 남는다.

Go 값 미검사의 종류별 집계(goval, 81 파일):

| 종류 | 검사함 | 미검사 |
| --- | --- | --- |
| 값 | 크기·정렬·패딩·bool·슬라이스·겹침 | 2 파일: `WitCpM` dst(기호 길이), 1a `Witness`(대상 없음) |
| 자원 조각(`s_mem`) | 1123 조각 | 42 조각(기호 길이나 주소. `WitLcO`의 정적 상자 둘 포함) |
| 타입 내용 | `%w` 증인 6개의 `*errors.errorString` 기술자(Size_, Kind_) | `%d` 인수의 int·uint64 기술자 내용(증인 2개) |
| 런타임 전역 | `ssz.Err*` 전역 20곳의 초기화(itab, errorString) | `runtime.writeBarrier` 값, `staticuint64s` 항목(정리 `staticBox_of_lt`가 표와 연결). 증인은 쓰는 항목만 값으로 놓는다(`WitLcO`: 4와 8). 표의 나머지 자리는 0 채움 바이트다. 정리가 읽지 않는다. `WitLcO`의 표 주소 66012는 8의 배수가 아니다. goval은 정적 표를 보지 않는다 |

Prysm 두 타입은 v7.1.8 `51b5a75` 스키마를 옮긴 축약 구조체다.
protobuf 필드가 있는 실제 Prysm 바이너리의 증명이 아니다.

## 3. 신뢰 항목

| 항목 | 신뢰 내용 | 지금의 검사 | 다음 조치 |
| --- | --- | --- | --- |
| Lean 커널, Kraken x64 의미론, EthLib 명세 | 공유 기반 | 없음 | 유지 |
| Kraken = 실제 CPU | 하드웨어 대조를 하지 않았다 | 없음(arm64 호스트) | x86-64 Linux 기계 또는 CI |
| ELF → Lean 프로그램 | objdump, `link/conv.py`, `include_x64_rt` | 링크 검사 (a)–(e): 독립 디코더 셋, 심볼·변위 | 유지 |
| ELF → Lean 데이터 | `link/data.py`, `data_include`(`Fk/Include.lean`) | 링크 검사 (f): 데이터 파일 = ELF 바이트, 포인터 워드 = 심볼 + 오프셋, 같은 줄 규칙(출력 가능한 ASCII와 `\n`만). `data.py --check`: 재생성 = 추적 파일. 해시는 RESULT 묶음 | 유지 |
| 정리가 include 정의를 쓰는가 | 정리의 전제는 정리 문장으로 읽는다. 검사 도구는 Lean 소스를 읽지 않는다(해시용 `Code.lean`, `AXIOMS.txt`만). 임의 Host 선언이나 이름 가림(astra 수정 2 발견 1)을 잡는 도구는 없다 | 없음(설계상, DIRECTION 3절) | 1c: 해석된 선언에서 의존성을 뽑는다 |
| 항목 id와 주소 | 검사 (f)는 파일 = ELF만 본다. 다른 주소와 그 자리 바이트로 바꾼 파일도 (f)는 PASS다. 증명된 코드가 `lea`하는 항목(형식 문자열 9개, `int`·`uint64` 타입 워드)은 증명이 묶는다(데이터 변이 `logs/34`). 계약만 쓰는 항목 넷(`vblMsgE/Z/B`, `staticuint64s`)은 계약 가설이 묶는다 | 증명, 계약 가설 | 유지 |
| 형식 문자열의 내용 | Lean이 묶는 것은 길이(`*_len`)와 nil 형식의 `%` 없음(`*_nopct`)뿐이다. `%w`·`%d` 동사 모양과 계약(`FmtErrorfWC`·`DWC`·`DDC`)의 대응은 계약 가설이다. 내용을 바꾼 형식도 증명은 통과한다 | 없음 | 형식 본문을 Lean 보조 정리로 고정(남은 일) |
| 재빌드 추적 | Lake가 `needs`의 `input_dir`(norm, data, `Fk/*.S`) 내용을 입력 해시에 넣는다 | X1 실험(수정 3 커밋 본문) | 유지 |
| 오류 전역의 값 | Go의 패키지 초기화가 `(itab, errorString)`을 넣는다 | 정리의 전제(`sc_reject_bool_err`의 `e0 ≠ 0`), 증인은 초기화된 값 | 런타임 초기화 정교화 |
| Go 값 | 증인이 실제 Go 값이다 | goval(크기·정렬·패딩·bool·겹침). 타입 내용·오류 전역·중간 상태 미검사 | 1c X2: Lean 술어로 |
| 런타임 계약 | Go 1.26.3 런타임이 계약을 만족한다 | 추상 모델(`rt_*`, `bump_*`)과 `joint_models`(한 Host·한 힙) | 2단계(HTR) 뒤 |
| fmt 할당량, GC | 할당이 예산 안이다. 호출 중 GC가 없다(`runtime.writeBarrier` = 0이 `F`에 있다) | 없음 | 런타임 정교화 |
| fmt 결과 객체 | 결론은 rax ≠ 0만 말한다 | 없음 | 하위 오류 전달 전에 결과 객체 계약을 정한다 |
| `VblMsg` | 어느 입력이 어느 메시지인지 말하지 않는다 | rodata 셋 소유는 형식 전제 | 유지(거부 명세에 충분) |
| ValidateBitlist | 수용 집합 = EthLib 규칙. `bsr`가 있는 Go 코드는 증명하지 않았다 | 계약 + 모델 `rt_validate_bitlist` | Kraken `bsr` 지원 |
| memmove | 겹치지 않는 범위만 | 호출자의 `⋆` | 유지 |
| 스택 가드, X15 = 0 | 빠른 경로 전제 | 정리 전제 | 유지 |
| Go 배치 | `layout.json`은 go/types의 gc amd64 크기 규칙이다. amd64 실행으로 확인하지 않았다 | `layout.go` | x86-64 기계 |

계약의 형식, 모델, 증인은 `CONTRACTS.md`에 있다.

## 4. 남은 항목 (astra 수정 2 필수 8)

| # | 필수 수정 | 상태 | 처리 계획(DIRECTION 4절) |
| --- | --- | --- | --- |
| 1 | Lean 참조 검사의 역할과 이름 해석 | 삭제로 닫음: 역할 분류를 지웠다. rodata 바이트·주소, `type:int`, `staticuint64s`는 include 정의를 쓴다. 쓰지 않는 include 정의: `errorStringItab`(+`_addr`), `errorStringPtrType_addr`, `intType`·`uint64Type` 바이트, `Err*_addr` 6개. 정리는 `label "ssz.Err*"`와 `label "go_itab…" + 8`을 직접 쓰고 itab 워드는 임의 `ity`다(증명이 이 표기를 강제한다). 남은 한계는 3절 "정리가 include 정의를 쓰는가" | 수정 3 X2 |
| 2 | (h)의 전체 식과 타입 동일성 | 삭제로 닫음: (h)를 지웠다. 바이트와 포인터 워드를 include한다. 리뷰의 itab 변이는 자기 시험이 FAIL로 잡는다. 항목 id ↔ 주소는 증명이 묶는다(3절) | 수정 3 X2 |
| 3 | Go 형식 호출의 실제 대상 | 삭제로 닫음: `golits.go`를 지웠다. 형식 바이트는 ELF에서 온다. 형식 내용·동사 모양과 계약의 대응은 계약 가설이다(3절) | 수정 3 X2 |
| 4 | 오류 타입 자료와 전역 불변식을 증인에. Scalars 비nil 거부 | 닫힘: `sc_reject_bool_err`, 증인 18개의 전역 초기화, `%w` 증인 5개의 ELF 기술자 | 수정 3 X3 |
| 5 | 배치 재생성 뒤 goval. 미검사 종류별 집계 | 닫힘: 재생성 바이트 동일, 2절 집계 표 | 수정 3 X6, X7 |
| 6 | 사후조건: NeMarshal, ListC 스택, Scalars Size, r14 | 닫힘 | 수정 3 X4 |
| 7 | ListC 원소 오프셋 순서와 원소 오류 전달 | 수작업 기준 사례 둘 닫힘: 순서 거부(`lc_reject_offset_order_main`, `lcl_order`, `FmtErrorfDDC`, `WitLcO`, lcorder), 짧은 원소 하나의 오류 전달(`lc_reject_item_main`, `lcl_itemerr`, `LuURejShortC`·`lu_urej_short_holds`, `WitLcI`, lcitems). 일반 반복과 다른 원소 오류는 남음 | 수정 3 X5, 리뷰 M4 |
| 8 | 게이트 표 정정 | 닫힘(2절) | 수정 3 X6 |

7의 남은 부분은 게이트 완료를 주장하기 전에 필요하다.
순서 거부 정리는 반복 0(첫 쌍)만 진입부터 증명했다. `lcl_order`는 임의 반복 i의 루프 보조 정리다. 앞 원소를 수용한 뒤의 반복은 `lcl_loop`과 잇는 일이 남았다.
순서 거부의 추가 전제: 인수 배열(진입 rsp − 104부터 32바이트), spill rsp − 200·− 192, `lcFmtOrder` 바이트, `StaticBox e`·`StaticBox 4n`. `lc_accept_main`은 바꾸지 않았다.
원소 오류 전달은 원소 1개(1–3바이트)만 진입부터 닫았다. ListU64의 짧은 입력 거부를 함수 명세 `LuURejShortC`로 두고 `lu_reject_short_frame`(프레임을 보존하는 새 정리, `lu_reject_short_main`은 그대로)에서 유도했다. 추가 전제: 초기화된 `ssz.ErrSize`(itab, `ErrObj`), itab+8의 타입 워드, 인수 배열(진입 rsp − 120부터 16바이트), spill rsp − 200·− 192, `lcFmtItems`. 빈 원소(0바이트)는 `lc_mask` 조건 때문에 제외했다. ListU64의 다른 거부(정렬, 초과)는 fmt가 만든 오류라 `FmtErrorfWC`의 errorString 인수 계약과 맞지 않는다(결과 객체 계약이 필요).

알려진 한계(수정 3 리뷰 권고 중 고치지 않은 것):
- goval의 기술자 검사는 Size_·Kind_만 본다. 증인 기술자가 ELF 바이트라는 근거는 Lean 이름 `errorStringPtrType`이다(S3).
- 부정 시험 대조군 `control`, `lcorderctl`은 바뀌지 않은 파일이라 Lake 캐시 재생이다. 다시 증명하지 않는다(S4). `lcitemsctl`은 파일을 바꾸므로 다시 빌드한다. lcorder와 lcitems의 지정 정리는 주 정리가 부르는 루프 보조 정리(`lcl_order`, `lcl_itemerr`)다. 변이 지시어가 거부 경로에만 있고, 진입부 변이는 `LcAccept`를 먼저 깨기 때문이다(`negative/run.sh` 주석).
- `lu_reject_short_frame`(`Fk/LcItems.lean`)은 `lu_reject_short_main`(`Fk/LuReject.lean`)과 전제가 같고 결론만 강하다. 같은 경로를 두 번 증명한다. 옛 정리를 새 정리에서 유도하면 중복이 없어진다. 이번에는 문서만 고쳤다(R5).
- 증인은 `runtime.staticuint64s` 표 중 쓰는 항목만 놓는다. `WitLcO`는 표 레이블을 입력 버퍼 뒤로 옮겼다(S7).
- 형식 문자열 본문을 Lean 보조 정리로 고정하지 않았다(S9). 3절 "형식 문자열의 내용"을 본다.

## 5. 발견

생성기 결함(F1, F2, G1–G3, H1)은 `syjn99/ssz-gen-fixes` `698c202`가 고쳤다.
지금 ELF는 그 생성기의 출력이다.

- **F1**: BitVec 디코더가 패딩 비트가 선 바이트를 받았다. 지금은 `bv_reject_padding_main`이 거부를 증명한다.
- **F2**: BitL 인코더의 길이 검사가 비트가 아니라 바이트를 셌다. 지금은 `bl_marshal_reject_main`이 거부를 증명한다.
- `semtest/f12_test.go`가 두 결함의 Go 회귀 시험이다.

관찰(결함 아님): ListC 원소 오프셋 순서 오류는 `%d` 두 개의 `fmt.Errorf`라 `convT64` 두 번과 할당이 있다.
관찰(도구): `link/check.py`가 `link/__pycache__`를 만든다. `.gitignore`에 없다. `python3 -B`로 돌린다.
관찰(도구): `negative/run.sh`의 `cp -Rc`는 macOS 형식이다. Linux에서는 `/workspace/tooling/fv/compat-bin`의 `cp` 대체가 필요하다.
관찰(계약): `MakesliceC`·`NewobjectC`의 타입 인수(`type__ + n`)와 원소 크기 `esz`의 대응은 계약 가설이다. 타입 기술자 내용을 include해 연결하지 않았다.
관찰(결함 아님): `u64v` 증인 정리는 `decide`가 아니라 `simp`로 증명한다. `decide`는 9.69 GiB에서 OOM이다. 근거 `memopt/REPORT.md`.

## 6. Kraken 요청 목록

- `bsr` 파싱. ValidateBitlist가 계약으로 남는 이유다.
- 정교화기 `include_x64`의 조건 코드 `g, ge, nl, nle, s, ns, o, no, p, np`. 지금은 `Fk/Include.lean`의 `include_x64_rt`로 우회한다.
- 다바이트 nop(`nopl (%rax)`, `data16 nop`) 파싱. 지금은 `link/conv.py --norm`이 `nop`으로 바꾼다.
- `kstep` 안 `grind` 시간 초과를 잡는 방법. 지금은 `Fk/Step.lean`의 `load_step`/`store_step`을 쓴다.
- `ecancel`의 원자 비교: `StaticBox (-4 + rcx)` 같은 원자에서 재귀 한도에 걸린다. `@Eq DataMem`과 `@Eq (Std.ExtHashMap …)` 원자를 구분하지 못한다. 지금은 `generalize`로 피한다.
- vcgen 갈래의 `@[spec]` 형태(`vcgen/B0.md`).

## 7. 1c 설계 입력

1. 스택 좌표 셋을 작은 정리로 고정한다: 함수 진입 rsp, 호출 직전 rsp, 피호출자 진입 rsp(= 호출 직전 − 8).
2. 계약 조합을 한 Host·한 힙에서 검사한다. `emp` 힙의 숫자 예산을 물리 공간으로 세지 않는다.
3. 기호 길이 제한은 구체 배치 생성기에만 둔다.
4. 선언 의존성과 전체 적용으로 완료표를 만든다. 함수 명세 아래의 외부 계약도 전파한다.
5. 주소 겹침과 타입 별칭을 생성 단계에서 진단한다. goval의 경계 검사를 생성기 안으로 옮긴다.
6. 증인 값은 `n#64` 꼴로 쓴다. `StaticBox (-4 + x)` 같은 원자는 `generalize`로 불투명하게 둔다.
7. 배치는 해석된 Lean 식에서 뽑는다. 소스 철자에서 선언 역할을 추정하지 않는다.
8. 함수 명세는 정리에서 유도한다(`*_holds`). 하위 계약 의존성도 완료표에 남긴다.
9. 조합은 셋을 따로 완료 항목으로 둔다: `hupd` 존재, 전체 조합 증인, 실제 호출자 명령 실행. 지금은 앞의 둘만 있다.
10. Go 값 미검사를 값, 자원 조각, 타입 내용, 런타임 전역으로 나눈다. 중간 상태와 두 번째 호출의 Go 값도 본다.
11. 오류 값을 자원으로 둔다: rodata, 상자 값, fmt 형식과 인수 타입, 전역 오류 객체. 오류 전역의 초기화와 비nil 조건을 명세 그래프에 넣는다.
12. 타입 자료는 크기와 종류만으로 식별하지 않는다. pointee와 메서드 연결을 넣는다.
13. 사후조건을 셋으로 분류한다: 메모리 동일성, 명시적 자원 보존, `True`로 버린 자원.
14. 링크 변이와 Lean 빌드를 한 기록에 묶는다. 검사기 단독 PASS를 증명 성공으로 쓰지 않는다.
15. 생성기를 고치면 Go 회귀 시험과 Lean 거부 정리를 함께 갱신한다.

## 8. 재현

전제: git 체크아웃(작업 트리 깨끗함), `lean/`과 `vcgen/`의 Lake 패키지를 미리 받아 둠.
메모리(이 호스트: 9.69 GiB, 스왑 없음): Lake 5.0.0의 `lake build`는 `-j`가 없고 CPU 제한과 무관하게 Lean 여러 개를 동시에 띄운다.
fix3의 차가운 빌드(4 CPU)는 세션 익명 메모리 최대 7.30 GiB였다(`streams/fix3/logs/246`). 리뷰의 2 CPU 실행은 6 GiB 감시를 넘었다.
모듈을 하나씩 빌드하면 최대 프로세스 4.61 GiB, 세션 3.32 GiB다. `WitLcI` 단독은 VmRSS 1.82 GiB다(리뷰 fix3-r3).
작은 기계에서는 모듈을 하나씩 빌드하거나 메모리 감시(예: `streams/fix3/tools/memcap.py`)를 둔다. fix3 스트림은 커널 OOM kill을 한 번 겪었다(`WitLcI` 첫 빌드).
저장소 루트에서 `. /workspace/tooling/fv/env.sh` 뒤에 아래 블록을 그대로 `sh`로 돌린다.
`SCR`는 워크트리 밖의 빈 디렉터리다. 한 단계라도 실패하면 멈춘다.
부정 시험은 사례마다 복제 하나(약 1.1 GiB)를 만들고 다음 사례 전에 지운다.

```sh
set -eu
: "${SCR:?SCR must be an empty directory outside the worktree}"
python3 -B fv/kraken/link/data.py --check fv/kraken/link/out      # 23 files, 0 differ
(cd fv/kraken/lean && lake build)                                 # 867 jobs
(cd fv/kraken/lean && sh tools/axioms.sh)                         # NONSTANDARD 0 (두 범위)
(cd fv/kraken/lean && lake env lean tools/RegressFix2.lean)       # 오류 없음
(cd fv/kraken/lean && for f in ../review/*.lean; do
  [ "$f" = ../review/Review1bFixB0.lean ] || { echo "== $f"; lake env lean "$f"; }; done)
(cd fv/kraken/vcgen && lake build Kraken.FunSpec && lake env lean ../review/Review1bFixB0.lean)
GOROOT=$(go env GOROOT) go run fv/kraken/lean/tools/wit/layout.go > fv/kraken/lean/tools/wit/layout.json
git diff --exit-code fv/kraken/lean/tools/wit/layout.json         # 바이트 동일
(cd fv/kraken/lean && python3 -B tools/wit/goval.py)              # 81 files, 위반 0
python3 -B fv/kraken/link/check.py fv/kraken/link/out             # PASS all, BUNDLE
python3 -B fv/kraken/link/check.py --selftest fv/kraken/link/out  # 11 cases
: > fv/kraken/negative/RESULT
for c in offset maxlen loop gsnum nilerr vbvje bvnochk blmnochk neoff cplen adcopy scbool scrbword blrity lcorder lcorderctl lcitems lcitemsctl control nopret; do
  PATH=/workspace/tooling/fv/compat-bin:$PATH fv/kraken/negative/run.sh "$SCR" "$c"   # Linux: cp -c 대체
  rm -rf --one-file-system -- "$SCR/neg-$c"
done                                                              # 20 cases, run.sh는 UNEXPECTED면 실패
GOROOT=$(go env GOROOT) go test -count=1 ./fv/kraken/semtest/    # F1, F2 PASS
git diff --exit-code fv/kraken/AXIOMS.txt fv/kraken/AXIOMS-ALL.txt fv/kraken/link/out/RESULT fv/kraken/negative/RESULT
```

대상 재생성과 증인 재생성 명령은 `TOOLS.md`와 `lean/tools/wit/README.md`에 있다.

## 9. 1c 입력 (include 정의와 데이터 파일)

인터페이스 전체는 `TOOLS.md` "ELF 데이터 include"에 있다. 1c는 같은 형식으로 자기 ELF의 데이터 파일을 만든다.

| Lean 이름 | 데이터 파일 | 뜻 |
| --- | --- | --- |
| `Fk.Data.<id> : List UInt8` | `link/out/data/<id>.data` | 그 구간의 ELF 바이트. 포인터 워드가 있으면 `[Host]`에 의존한다 |
| `Fk.Data.<id>_addr : BitVec 64` | 같은 파일의 `at` 줄 | `(label "<레이블>" + <오프셋>).toBitVec`. 오프셋 0이면 `+ 0`이 없다 |
| `Fk.Data.intType_size_kind` 등 | — | 포함된 바이트에 대한 구조 정리(Size_, Kind_, Elem, itab 타입 워드·메서드, `staticuint64s` 표) |
| `Fk.staticBox_of_lt` | `staticuint64s.data` | `StaticBox v`의 바이트 = `Int.toBytes 8 v` (v < 256) |

생성기가 데이터 파일을 내는 규칙:

1. 항목 표(id, 레이블, 오프셋, 길이, 포인터 슬롯)는 코드가 쓰는 주소와 길이다(`lea sym+off(%rip)`, `mov $len`). 바이트는 ELF에서 읽는다. 손으로 쓰지 않는다.
2. 포인터 슬롯은 `word <레이블> <오프셋>`으로 쓴다. 레이블은 그 값 이하의 가장 가까운 심볼이다. 같은 주소에 여럿이면 변환된 코드가 쓰는 레이블을 고른다.
3. 레이블 이름은 `conv.py`의 정리 규칙을 따른다(`go:string.*` → `go_string._`).
4. 파일마다 `link/check.py` (f)가 ELF와 다시 비교한다. 파일은 Lake `input_dir` 입력이다.
5. Go 1.26.10 ELF는 자기 데이터 파일과 표를 자기 이름공간에 둔다. Go 1.26.3 값을 다시 쓰지 않는다.
6. 오류 전역은 주소만 뽑는다. 값은 런타임 초기화가 정한다. 거부 정리의 비nil 결론은 `e0 ≠ 0` 같은 초기화 전제를 둔다.
7. 증인은 오류 전역을 초기화된 값으로 두고 `%w` 타입 워드가 ELF 기술자(`errorStringPtrType`)를 가리키게 한다. goval이 전역의 초기화와 기술자의 Size_·Kind_를 검사한다.

## 10. 1c: 생성기와 Prysm 목록 (phase1c 스트림, 브랜치 `claude/ssz-fv-phase1c`)

**판정: 게이트 1c 미통과.** 손 사례 9개 타입의 손 주 정리 58개는 생성기가 다시 만들었다(문장 SAME, Lean 통과). 그러나 생성 증명은 손 증명 글을 틀로 쓴 것이다. Prysm 범위 안 132개 타입 중 모든 의무를 통과한 타입은 0개다.
상세: 스트림 보고서(`$RUN/streams/phase1c/REPORT.md`), `gen/x4/README.md`, `prysm/go1.26.10/X5.md`, `prysm/TYPES.md`, `prysm/GENERATOR-FINDINGS.md`.

### 10.1 게이트 1c 표: 손 사례 9개 타입 (Go 1.26.3 ELF, `Gen1cX4`)

요소 번호는 1절과 같다. "생성"의 뜻은 10.3절. 수는 `gen/x4/results/*.json`에서 센다.

| 타입 | 1 문장(생성, 손과 SAME) | 2 증인(다시 겨눔) | 3 기계어 정리 | 4 링크 | 5 부정 시험(변이/기대대로) | 6 Go 값 | 생성 방식 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| Scalars | 6 | 1 (조합) | 6 | PASS | 6/6 | 손 증인 값(P7 goval)만 | 지시 걷기 |
| ListU64 | 9 | 5 | 9 | PASS | 11/11 | 같음 | 지시 걷기 + 루프 틀 |
| ListC | 11 | 14 | 11 | PASS | 13/13 | 같음 | 걷기 + 루프 틀, marshal은 고정 틀 |
| Checkpoint | 5 | 3 | 5 | PASS | 5/5 | 같음 | 고정 틀 |
| AttestationData | 4 | 2 | 4 | PASS | 4/4 | 같음 | 고정 틀 |
| BitVec | 6 | 3 | 6 | PASS | 5/5 | 같음 | 고정 틀 |
| FixedVec | 5 | 3 | 5 | PASS | 5/5 | 같음 | 고정 틀 |
| BitL | 7 | 6 | 7 | PASS | 7/7 | 같음 | 고정 틀 |
| Nested | 5 | 6 | 5 | PASS | 5/5 | 같음 | 고정 틀 |

- 4 링크: 생성 정리는 `Fk.Code`(이 ELF의 `.S`)를 그대로 쓴다. `link/out/RESULT` BUNDLE `91757cbd…` 그대로.
- 2 증인: 손 증인(gen/wit 재생성)에서 적용하는 정리만 생성 정리로 바꿨다. 거부 정리 다수와 Scalars accept 등은 증인이 없다.
- 6 Go 값: 다시 겨눈 증인 모듈에서 goval을 다시 돌리지 않았다. 증인 값은 손 증인과 같다(P7: 76/76 바이트 같음, goval 오류 0).
- 공리: 생성 정리 모두 `propext`, `Classical.choice`, `Quot.sound`만(`axioms-*.json`).
- `uses.py`: 고정 틀 정리 32개는 Gen1cX4 선언을 따라가도 손 `*_main`을 쓰지 않는다(대조군 잡힘).
- 시도하지 않음(이유 있음): 손 정리가 없는 고정 목록 행(조합 행 대부분, AttestationData r2/r3·marshal_reject, reject_spec), EthLib 쪽 부분 행(`*_spec_accepts_iff`), `lum_grow_site`, `lu_reject_short_frame`.

### 10.2 Prysm 범위 안 132개 타입 (Go 1.26.10, 실험 기준선)

- 링크 표: 함수 136개, `conv.py --norm` + `check.py` (a)–(f) PASS, BUNDLE `1bdfc4f0…`(`prysm/go1.26.10/link/RESULT`).
- size: 46개 타입 생성 + Lean 통과, 변이 46/46, 공리 표준만. 86개는 가변 크기라서 틀이 없다.
- 디코더·인코더: 134개 의무 모두 생성기 단계에서 거부. 계약 부재 2(Checkpoint·AttestationData 디코더가 손 작성 `primitives.*.UnmarshalSSZ`를 부른다), 자동화 한계 132(틀이 없는 필드 조합). 고정 틀을 억지로 댄 Lean 실행 4개는 모두 오류(첫 오류는 `X5.md`).
- 모든 의무를 통과한 타입: 0. 타입당 고정 목록 의무 평균 약 28개(전체 3676) 중 size 하나만 증명됐다.

### 10.3 신뢰 항목 (1c에 더해지는 것)

1. "생성"은 손 증명 글을 기계어에서 읽은 값으로 틀에 맞춘 것이다. 생성 전술 줄 중 손 증명에 글자 그대로 있는 줄: 지시 걷기 정리는 88–100%(예: Scalars accept 130/146, ListU64 정렬 거부 191/217, ListC accept 294/298), 고정 틀 정리는 `intro` 한 줄 빼고 100%. 손 증명 없이 새 모양을 증명하는 능력은 보이지 않았다.
2. 고정 틀(`gen/x4/anchor.py`)은 코드에서 레이블 위치와 기호 피연산자만 정한다. 정규화한 함수가 손 코드와 같아야 쓴다.
3. Go 1.26.10은 새 실험 기준선이다. Go 1.26.3 정리는 옮기지 않았다. 그 런타임 계약(makeslice, growslice, memmove, newobject, fmt.errorf …)은 Go 1.26.10 런타임 소스로 다시 읽지 않았다(미확인 가정).
4. Prysm 손 작성 원시 타입 메서드(Slot, Epoch, ValidatorIndex, Gwei, CommitteeIndex; 함수 24개)는 명세가 없다. 계약으로 둘지 함수 명세로 증명할지는 사용자 결정 대기다. 52개 생성 타입이 이것을 부른다.
5. Prysm 135개 타입의 Desc는 독립 명세와 대조하지 않는다(일관성 검사만). 9개 손 타입만 EthLib 명세와 대조한다.
6. 변환기: `conv.py --norm`에 `%riz` 규칙을 더했다(인덱스 없는 SIB, 같은 주소). Go 1.26.3 변환 결과는 바이트가 같다. 검사기 `check.py`의 LLVM 줄 읽기에서 10바이트 명령어의 마지막 바이트를 버리던 결함을 고쳤다(검사가 더 엄격해짐).
7. 호스트는 arm64다. x86-64 하드웨어 대조는 하지 않았다.

### 10.4 실패 분류

| 분류 | 어디서 | 수 |
| --- | --- | --- |
| 자동화 한계 | Prysm 디코더·인코더(틀 없음), 가변 크기 size | 132 + 86 |
| 계약 부재 | Prysm Checkpoint·AttestationData 디코더(손 작성 primitives 호출) | 2 |
| 새 명령어 | `%riz` 피연산자(Kraken 파서)는 변환 규칙으로 닫음(18/18 파싱) | 0 남음 |
| 생성기 결함(sszgen 698c202) | D1: IR의 중첩 container 필드 키(출력 코드에는 영향 없음, `GENERATOR-FINDINGS.md`) | 1 |
| 손 사례 X4 막힘 | Scalars reject_size 설계 1(3회 실패, 설계 2로 통과) | 0 남음 |

우리 도구의 결함(이 스트림에서 찾고 고침): x4gen 정리 없는 모듈(리뷰 r7 S4), 부정 시험 평가기의 정리 범위(손 글의 빈 줄), memcap 세션 최대값 표기(복사본에서), `check.py` 10바이트 명령어.

### 10.5 2단계(HTR) 입력

- 생성기가 가진 것: Desc(독립 검사기와 결합), 고정 목록 의무, 증인 생성(gen/wit), 기호 길이·`n#64` 정규화, include 어댑터(API v3). HTR 의무도 같은 고정 목록 형식에 넣을 수 있다.
- HTR 전에 필요한 것: 지시 걷기 틀의 범위(바이트 벡터·컨테이너 필드, 프레임 있는 함수, 함수 호출), 손 작성 primitives의 명세 결정, Go 1.26.10 런타임 계약의 재확인, 가변 크기 size 틀.
- gohashtree 경로(HTR)는 1c에서 손대지 않았다.

## 11. 실제 Prysm `v1alpha1.Checkpoint` 인코더·디코더 종단 증명 (prysm-e2e 스트림, 브랜치 `claude/ssz-fv-prysm-e2e`)

**판정: 조건부.** 실제 protoc 타입 `v1alpha1.Checkpoint`의 디코더(수용, 크기 거부)와 인코더(빠른 경로, growslice 경로, `ErrBytesLength` 거부, 명세 정렬)와 SizeSSZ가 Go 1.26.10 ELF `c6403c02…911e`의 기계어에서 증명됐다. Epoch 디코더는 수용과 길이 거부 둘 다 증명됐다. 기계어 수준 합성(E5) `cp_e2e_unmarshal_then_marshal`은 디코더 진입에서 시작해 `cp_e2e_accept_main`과 `cp_e2e_marshal_main`을 잇고, 한 Host의 증인 `WitCpC`가 있다(리뷰 e2e-r1 M1 수정). 인코더 growslice 경로 `cp_e2e_marshal_grow_main`은 첫 append 지점이 자라는 경우다(전제 `len + 40 ≤ nextSliceCap (len + 8) cap`).
INBOX 009(세션 4)에서 나머지 용량 경우를 새 정리로 덮었다. 기존 정리 문장은 바꾸지 않았다.
첫 지점이 맞고 둘째 지점이 자라는 경우(`len + 8 ≤ cap < len + 40`)는 `cp_e2e_marshal_grow2_main`이 증명한다.
첫 지점이 자라는 모든 경우(`cap < len + 8`, `cap = 0`과 nil `dst` 포함, `nextSliceCap` 전제 없음)는 `cp_e2e_marshal_grow_any_main`이 다룬다.
그 결론은 코드의 분기 그대로 둘 중 하나다. 왼쪽: growslice가 준 용량이 `len + 40` 이상이면 반환까지 증명했다. 오른쪽: 용량이 작으면 둘째 growslice 호출 진입의 정확한 상태까지 증명했다.
세션 5(INBOX 010 M1)에서 같은 전제의 더 강한 정리 `cp_e2e_marshal_grow_any_sharp`를 더했다. 결론은 세 경우이고 모두 정확한 프레임을 적는다.
(A) 첫 새 블록에 Root가 들어가면 반환한다. (B) 첫 호출 뒤 남은 힙 `av1`이 둘째 호출의 예산 `2·nextSliceCap (len + 40) C1 + 8192` 이상이면 둘째 growslice를 지나 반환한다.
(C) 남은 힙이 그 예산보다 작으면 둘째 호출 진입의 정확한 상태에 있고 `Heap av1`, `av1 < 2·nextSliceCap (len + 40) C1 + 8192`이다.
**(C) 뒤의 실행은 증명하지 않았다(막힘, 차분만).** `GrowsliceC` 결과는 남은 힙을 `avail' + newCap ≤ avail`(상한)으로만 준다. 그래서 둘째 호출의 예산 전제만 유도할 수 없다(FINDINGS T-7, 리뷰 e2e-r3 S7). 그 사실이 있으면 기존 보조정리 `cpw_tail_grow`가 반환을 준다.
컨트롤러 결정(INBOX 010): 새 계약 형식은 없다. 남은 영역은 사용자 결정 전까지 "막힘 / 차분만"이다. "Checkpoint 인코더 완전"을 주장하지 않는다. 이 영역의 증거는 Go 차분 검사뿐이다(`enc-w-len30-spare0`, `enc-w-len10-spare0`).
growslice 뒤의 거부(`cap < len + 8`, `len(Root) ≠ 32`)는 `cp_e2e_marshal_reject_grow_main`이 증명한다. 에폭 8바이트는 새 블록의 `[len, len+8)`에 있고 호출자 배열은 바뀌지 않는다(C-1 형식).
경우 덮기 정리 `cp_e2e_marshal_cover`(`len(Root) = 32`)와 `cp_e2e_marshal_reject_cover`(`len(Root) ≠ 32`)는 `len ≤ cap`인 모든 용량을 위 정리들로 나눈다. 덮기 정리의 결론은 출력 바이트(`dst ++ serialize`, EthLib 독립 Desc)와 프레임 `R`이고 나머지는 `⋆ True`다. 정확한 메모리 회계는 각 정리에 있다.
세션 5(INBOX 010 M2)에서 프레임을 적은 덮기 정리 2개를 더했다. 기존 덮기 정리는 그대로 둔다.
`cp_e2e_marshal_cover_framed`의 결론은 구성 정리 사후조건의 선언이다: (1) 빠른 경로, (2) 첫 append가 맞고 둘째가 자람, (3A)/(3B)/(3C) `cp_e2e_marshal_grow_any_sharp`의 세 경우.
각 경우는 용량 범위, 수신자 72바이트, 스택 칸, 가드 워드, 호출자 배열(`pre ++ spare`), 새 블록, `Heap`, `R`을 이름으로 적는다. `⋆ True`는 없다.
반환 경우의 출력 블록은 `pre ++ bs`이고 `serialize prysmCpDesc g.toValue = .ok bs`다. (2)에서 호출자 배열은 `pre ++ epoch ++ spare[8:]`이다(C-1). (3)에서 호출자 배열은 바뀌지 않는다.
`cp_e2e_marshal_reject_cover_framed`: `len + 8 ≤ cap`이면 에폭이 호출자 배열 `dst + len`에 있다(`blk = dst`, C-1). `cap < len + 8`이면 호출자 배열은 바뀌지 않고 에폭은 새 블록 `nb`에만 있다.
증인 `WitCpWF.covf_runs`(len 30, cap 30 + n)와 `covf_runs_nil`은 실행이 닿는 용량 범위를 결론에 적는다. (3A)/(3B)/(3C) 중 어느 것인지는 `GrowsliceC`가 용량과 남은 힙을 숨기므로 정리로 정할 수 없다(리뷰 e2e-r3 S2, 아래 조건 4).
조건:

1. 런타임 계약 `MakesliceC`(uint8, esz 1, cnt 32), `MemmoveC`, `GrowsliceC`(uint8, esz 1, 인코더 첫 지점과 둘째 지점), `ConvT64C`, `FmtErrorfDDC`(Epoch 형식, `type:int`)는 가설이다. Go 1.26.10 소스를 다시 읽었고 바뀌지 않았다(`prysm/go1.26.10/e2e/RUNTIME-1.26.10.md`). 정교화 증명은 없다.
2. 전제: 스택 가드, `runtime.writeBarrier` = 0, 힙 여유, 레이블 신선성, 전역 주소(링크 검사 (a)–(f) PASS), `ssz.ErrSize`와 `ssz.ErrBytesLength`의 초기화된 값(값은 패키지 init이 쓴다; 정리는 두 워드를 그대로 돌려주고 non-nil은 결론이 아니다; non-nil과 서로 다름은 Go 차분의 `errors.Is`만 본다).
3. x86-64 하드웨어에서 실행하지 않았다. Go 차분 검사는 같은 소스의 arm64 빌드다.
4. 첫 growslice 뒤 둘째 growslice가 필요한 실행(첫 성장 용량 `< len + 40`)은 남은 힙이 둘째 호출의 예산 이상이면 반환까지 증명했다(`cp_e2e_marshal_grow_any_sharp` (B)). 예산보다 작으면 둘째 호출 진입까지만 증명했다((C)). 남은 힙의 하한은 기존 `GrowsliceC` 형식에 없다(T-7). 그 영역은 Go 차분 검사만 있다(막힘, 사용자 결정 대기). 증인 모델 `rt_growslice`(새 용량 `2·newLen + 192`)는 이 분기를 실행하지 않는다. 증인 결론은 닿는 용량 범위를 적는다(`WitCpWF`). (3A)/(3B)/(3C) 중 어느 것인지는 증인 정리로 정할 수 없다. `GrowsliceC`의 결과는 새 용량과 남은 힙을 범위로만 준다. 그래서 어떤 런타임 모델을 써도 계약을 거친 증인은 이 셋을 구별하지 못한다(리뷰 e2e-r3 S2: 부분 수행, 이유는 OUTBOX 009). 오류 워드의 non-nil은 증명하지 않았다(차분만).

Epoch 길이 거부의 기존 계약 형식 `StaticBox`는 `Fk.Data`(Go 1.26.3 이름공간)의 `staticuint64s`와 `staticuint64s_addr`를 읽는다. `E2e.ep_static_table`(바이트 2048개 같음)과 `E2e.ep_static_addr`(주소 같음, 둘 다 `runtime.staticuint64s` 레이블)가 이것을 Go 1.26.10 include에 잇는다. Go 1.26.3의 사실은 쓰지 않는다(리뷰 e2e-r2 N3, `RUNTIME-1.26.10.md` 2절).
손 작성 `(*primitives.Epoch).UnmarshalSSZ`는 함수 명세 `EpUAccC`로 증명했다(`ep_uacc_holds`). 디코더 주 정리에는 Epoch에 대한 가설이 없다.
`Epoch.MarshalSSZTo`는 인코더에 인라인된다(`-gcflags=-m=2`, `prysm/go1.26.10/e2e/CALLGRAPH.md`). 인라인된 몸체는 인코더 정리 안에서 증명했다.
명세는 consensus-specs에서 손으로 쓴 `E2e.prysmCpDesc`다. Desc 검사기의 Desc와는 필드 이름만 다르다(`prysmCpDesc_checker`). EthLib의 `serialize`/`deserialize`는 컨테이너 필드 이름을 쓰지 않으므로 두 Desc의 직렬화와 역직렬화는 모든 값과 모든 바이트 배열에서 같다(`prysmCpDesc_serialize_checker`, `prysmCpDesc_deserialize_checker`, 리뷰 S1).
Go 1.26.3 증명은 옮기지 않았다. 모든 지시 색인, 오프셋, 레이블, 프레임은 Go 1.26.10 `.S`에서 다시 유도했다.

표는 `prysm/go1.26.10/e2e/e2e.json`, `negative/result.json`, `differential.json`, `axioms.json`에서 프로그램이 만든다.
표의 행은 부정 시험 사례를 하나씩 정확히 한 번 센다. 세션 5에서 A2/A3 단위(Slot, CommitteeIndex, AttestationData 디코더, 명세 다리)와 도달 불가 보조정리의 행을 더했다(리뷰 e2e-r3 S5). 7b5e956의 표 합 98은 E2e 모듈 사례 96건 중 `cpu-*` 2건을 빼고 E2eAd의 `cps-*` 4건을 더한 값이었다.
AttestationData 인코더(A4–A6)는 시작하지 않았다.
감사 AU-11: "나머지" 칸은 `gen/e2e/table.py`가 정리 문장에서 읽는다. `⋆ True`는 결론의 나머지 메모리를 말하지 않는다는 뜻이다. 이런 정리는 5개다: `cp_e2e_marshal_decoded_receiver`, `cp_e2e_marshal_spec_k`, `cp_e2e_unmarshal_then_marshal`, `cp_e2e_marshal_cover`, `cp_e2e_marshal_reject_cover`. 정확한 프레임은 각 구성 정리와 `*_framed` 덮기 정리에 있다. 합성 `cp_e2e_unmarshal_then_marshal`에는 프레임을 적은 판이 없다.
감사 AU-06(세션 7): 덮기 증인 4개는 E2e 쪽 전술 `wit_split_n`(`E2e/WitSplit.lean`)을 쓴다. `Fk/WHost.lean`은 그대로다. 같은 방법으로 한 번씩 잰 정교화 시간: WitCpW 265.6→39.2초, WitCpWF 262.7→35.0초, WitCpWR 517.7→47.7초, WitCpWRF 590.8→43.4초(`opt1/AU-06.json`). 이름 있는 선언의 문장과 공리는 같다.
감사 AU-07(세션 7): `E2eScal.P2EncCp`는 바꾸지 않았다. 시도 3번에서 빨라지지 않았다. 느린 omega는 `hfit` 곁목표가 아니고 위치를 찾지 못했다(`opt1/AU-07.json`).
감사 AU-12: `cp_e2e_marshal_decoded_receiver`는 따름 정리이고 자기 증인이 없다. `WitCpM`은 `cp_e2e_marshal_main`을 실행한다. `*_spec_here`(`ep`, `sl`, `ci`, `cpu`, `cpm`)는 명세가 그 호스트에서 성립함을 보인다. 주 정리 전제의 만족 가능성(비공허성)은 실행 증인(`*_runs`)이 보인다.

| 정리 | 의무 | 문장 | 증인 | 기계어 정리 | 나머지 | 링크 | 부정 시험 | Go 값 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `E2e.ep_unmarshal_accept_main` | callee accept (function spec source) | done | done | done | exact frame | done | 5/5 통과 | differential only (uint64 receiver; no GoVal theorem; epoch-len8 cases) |
| `E2e.ep_uacc_holds (EpUAccC)` | function spec | done | done | done | n/a | done | via ep_unmarshal_accept_main | differential only (uint64 receiver; no GoVal theorem) |
| `E2e.cp_e2e_accept_main (+ cp_e2e_accept_tail)` | accept | done | done | done | exact frame | done | 9/9 통과 | before: witCpA_recv_pre (witness block); after: cp_after_decode_goValue on the conclusion fragments, every p ≠ 0 (MakesliceC does not state non-nil) + witCpA_recv_post; IR layout (not ELF abi.Type) + differential |
| `E2e.cp_e2e_reject_size_main` | reject (ssz.ErrSize) | done | done | done | exact frame | done | 4/4 통과 | differential only (receiver unchanged; no GoVal theorem) |
| `E2e.cp_e2e_reject_complete + cp_e2e_reject_size_spec` | reject_complete / reject_spec | done | done (WitCpRS.cp_reject_spec_runs on Array.replicate n 0x11, n = 39, 41, 0; review e2e-r1 S6) | done | n/a (cp_e2e_reject_complete); exact frame (cp_e2e_reject_size_spec) | n/a | 2/2 통과 | n/a (spec level) / differential |
| `E2e.cp_e2e_accept_spec_k` | accept against EthLib | done | done (WitCpAS.cp_accept_spec_runs on pcpEnc g0 for 3 closed g0; review e2e-r1 S6) | done | exact frame | done | 2/2 통과 | via cp_e2e_accept_main (witCpA_recv_pre/post) |
| `E2e.cp_e2e_marshal_main` | marshal (fast path) | done | done | done | exact frame | done | 7/7 통과 | witCpM_recv (witness block, offset 8); IR layout + differential |
| `E2e.cp_e2e_marshal_decoded_receiver` | encoder on a decoded-form receiver (not compose_hupd; review e2e-r1 M1) | done | corollary; no own witness (WitCpM runs cp_e2e_marshal_main on a decoded-form receiver; audit AU-12) | done | `⋆ True` | done | 3/3 통과 | witCpM_recv (witness block) + differential |
| `E2e.cp_e2e_marshal_reject_main` | marshal_reject | done | done (WitCpMR: empty prefix rl 31/33/0; P5: 5-byte prefix rl 31/0; review e2e-r2 N5) | done | exact frame | done | 4/4 통과 | witCpMR_recv (witness blocks, len(Root) 31/33/0); IR layout + differential |
| `E2e.cp_e2e_marshal_grow_main` | marshal (capacity too small: first growslice site; GrowsliceC esz 1, premise len + 40 ≤ nextSliceCap (len + 8) cap) | done | done (WitCpG: len 30, cap 36, rt_growslice + rt_memmove, 3 value instances) | done | exact frame | done | 9/9 통과 | witCpG_recv (witness block, offset 0x20a0); IR layout + differential (enc-grow-cap0, enc-grow-len30-cap36) |
| `E2e.ep_unmarshal_reject_len_main` | callee reject (standalone) | done | done (WitEpR: len 7 and 9 static box, len 300 heap box; review e2e-r2 N5) | done | exact frame | done | 7/7 통과 | differential (epoch-len7/9) |
| `E2e.cp_e2e_marshal_spec_k + cp_e2e_size_main (+ size_spec)` | marshal against EthLib / size | done | done (WitCpS; spec_k via WitCpM) | done | `⋆ True` (cp_e2e_marshal_spec_k); exact frame (cp_e2e_size_main) | done | 8/8 통과 | n/a (size) / via marshal |
| `E2e.cp_layout / cpGoValue (Go-value element)` | go value | done | evaluated on WitCpA/WitCpM/WitCpMR receivers; WitCpW/WitCpWR receivers (GoValW) | done | n/a | n/a | 7/7 통과 | this is the Go-value predicate (slice-header sanity only; IR layout, not ELF abi.Type) |
| `E2e.cp_e2e_unmarshal_then_marshal` | compose_hupd / compose_witness (decoder entry → cp_e2e_accept_main → hupd → cp_e2e_marshal_main) | done | done (WitCpC: one Host with CpUnmarshal, EpUnmarshal, BumpAlloc1, RtCopy, CpMarshal; real middle memory by storeInt) | done | `⋆ True` | done | 7/7 통과 | witCpC_recv: before from the witness block, after = cp_after_decode_goValue (every p ≠ 0) + differential roundtrip |
| `E2e.prysmCpDesc_serialize_checker / deserialize_checker` | spec bridge: codec equality with the checker Desc (review e2e-r1 S1) | done | n/a (spec level) | done | n/a | n/a | 4/4 통과 | n/a |
| `E2e.cpw_head_fit / cpw_head_grow (prefixes to L_7b)` | segment lemmas (first capacity test; first growslice, GrowsliceC esz 1) | done | via WitCpW / WitCpWR (cover instances) | done | exact frame | done | 4/4 통과 | n/a (segment) |
| `E2e.cpw_tail_fit / cpw_tail_rej / cpw_tail_grow / cpw_tail_grow_call (tails from L_7b)` | segment lemmas (second capacity test; second growslice; ErrBytesLength) | done | via WitCpW / WitCpWR; cpw_tail_grow via cp_e2e_marshal_grow2_main | done | exact frame | done | 9/9 통과 | n/a (segment) |
| `E2e.cp_e2e_marshal_grow2_main` | marshal: first append fits, second grows (len + 8 ≤ cap < len + 40; GrowsliceC esz 1) | done | done (WitCpW.cov_runs n = 8, 39 through the cover) | done | exact frame | done | 2/2 통과 | differential (enc-w-len30-spare8/20/39); witness receiver: GoValW.witCpW_recv (review e2e-r3 S1) |
| `E2e.cp_e2e_marshal_grow_any_main` | marshal: first append grows, every cap < len + 8 (no nextSliceCap premise); left: returns; right: reaches the 2nd growslice call — the run after it is NOT proved (GrowsliceC does not chain, T-7) | done | done (WitCpW.cov_runs n = 0, 3 and cov_runs_nil: left disjunct; right disjunct not exercised by the model) | done (partial: right disjunct ends at the call) | exact frame | done | 2/2 통과 | differential (enc-w-len30-spare0/3, enc-w-len10-spare0, enc-grow-cap0); witness receiver: GoValW.witCpW_recv (review e2e-r3 S1) |
| `E2e.cp_e2e_marshal_grow_any_sharp` | marshal: first append grows, every cap < len + 8 (same premises as grow_any_main; GrowsliceC esz 1, MemmoveC). (A) returns through the first block; (B) returns through the second growslice when the heap left av1 ≥ 2·nextSliceCap(len+40, C1) + 8192; (C) entry of the second call with Heap av1 and av1 below that budget — the run after (C) is NOT proved (no lower bound on the remaining heap in GrowsliceC, T-7; blocked / differential only pending a user decision) | done | premises: WitCpW / WitCpWF (n = 0, 3, nil dst) through the covers; which of (A)/(B)/(C) a run takes is not decidable through GrowsliceC (it hides the returned capacity and heap); the witness model takes (A) | done (partial: (C) ends at the call) | exact frame | done | 4/4 통과 | differential (enc-w-len30-spare0/3, enc-w-len10-spare0, enc-grow-cap0); witness receiver: GoValW.witCpW_recv (review e2e-r3 S1) |
| `E2e.cp_e2e_marshal_reject_grow_main` | marshal_reject after the first growslice (cap < len + 8, len(Root) ≠ 32; C-1 form on the new block) | done | done (WitCpWR.rej_runs n = 0, 3; rej_runs_nil) | done | exact frame | done | 2/2 통과 | differential (enc-w-rej-len30-spare0/3: caller array unchanged); witness receivers: GoValW.witCpWR_recv (rl 0/31/33/48), rl 49 not a Go value (witCpWR_recv_bad); rej_runs allows any rl ≠ 32, a Go caller only rl ≤ 48 (review e2e-r3 S1) |
| `E2e.cp_e2e_marshal_cover` | case cover len(Root) = 32 × every len ≤ cap, against EthLib (dst ++ serialize; ⋆ True remainder) or at the 2nd growslice call | done | done (WitCpW: cap = len, len+3, len+8, len+39, len+40, nil dst) | done | `⋆ True` | done | 2/2 통과 | differential; witness receiver: GoValW.witCpW_recv (review e2e-r3 S1) |
| `E2e.cp_e2e_marshal_reject_cover` | case cover len(Root) ≠ 32 × every len ≤ cap (ErrBytesLength words; some block holds pre ++ epoch) | done | done (WitCpWR: cap = len, len+3, len+8, len+40, nil dst; rl 31/0/33) | done | `⋆ True` | done | 2/2 통과 | differential; witness receivers: GoValW.witCpWR_recv (rl 0/31/33/48), rl 49 not a Go value (witCpWR_recv_bad); rej_runs allows any rl ≠ 32, a Go caller only rl ≤ 48 (review e2e-r3 S1) |
| `E2e.cp_e2e_marshal_cover_framed` | case cover len(Root) = 32 × every len ≤ cap with the exact frame (no ⋆ True): disjunction of the member postconditions (1) cp_e2e_marshal_main, (2) cp_e2e_marshal_grow2_main, (3A)/(3B)/(3C) cp_e2e_marshal_grow_any_sharp; returned block pre ++ bs with serialize = .ok bs (EthLib); (3C) is the entry of the second growslice call (T-7) | done | done (WitCpWF.covf_runs: cap = len, len+3, len+8, len+39, len+40 with the reached capacity range in the conclusion; covf_runs_nil) | done (partial: (3C) ends at the call) | exact frame | done | 4/4 통과 | differential (accept cases); witness receiver: GoValW.witCpW_recv (review e2e-r3 S1) |
| `E2e.cp_e2e_marshal_reject_cover_framed` | case cover len(Root) ≠ 32 × every len ≤ cap with the exact frame: len + 8 ≤ cap: epoch in the caller's array (blk = dst, C-1); cap < len + 8: caller's array pre ++ spare unchanged, epoch in the new block only | done | done (WitCpWRF.rejf_runs: cap = len, len+3, len+8, len+40, nil dst; rl 31/0/33/48) | done | exact frame | done | 3/3 통과 | differential (reject cases); witness receivers: GoValW.witCpWR_recv (rl 0/31/33/48), rl 49 not a Go value (witCpWR_recv_bad); rej_runs allows any rl ≠ 32, a Go caller only rl ≤ 48 (review e2e-r3 S1) |
| `E2eAd.sl_unmarshal_accept_main + sl_uacc_holds (SlUAccC)` | callee accept primitives.Slot (function spec source) | done | done (WitSl, 3 values) | done | exact frame (sl_unmarshal_accept_main); n/a (sl_uacc_holds) | done | 5/5 통과 | n/a (uint64 receiver) |
| `E2eAd.ci_unmarshal_accept_main + ci_uacc_holds (CiUAccC)` | callee accept primitives.CommitteeIndex (function spec source) | done | done (WitCi, 3 values) | done | exact frame (ci_unmarshal_accept_main); n/a (ci_uacc_holds) | done | 5/5 통과 | n/a (uint64 receiver) |
| `E2eAd.ad_e2e_head / ad_e2e_root / ad_e2e_src / ad_e2e_tgt` | segment lemmas of the AttestationData decoder (size test, Slot, CommitteeIndex, Root, Source, Target) | done | via WitAdA | done | exact frame | done | 13/13 통과 | n/a (segment) |
| `E2eAd.ad_e2e_accept_main` | accept v1alpha1.AttestationData (callees via sl/ci/cp_uacc_holds; Source/Target always new, N-3) | done | done (WitAdA, 3 inputs) | done | exact frame | done | 5/5 통과 | partial (full receiver and both 72-byte objects in the conclusion; no Lean Go-value predicate for AttestationData) |
| `E2eAd.ad_e2e_reject_size_main` | reject (ssz.ErrSize) | done | done (WitAdR len 127/129/0) | done | exact frame | done | 2/2 통과 | n/a (receiver unchanged; error words as they are) |
| `E2eAd.ad_e2e_accept_spec_k (+ reject_size_spec, reject_complete)` | accept / reject against EthLib | done | via WitAdA / WitAdR | done | exact frame | done | 2/2 통과 | via ad_e2e_accept_main |
| `E2e.prysmAdDesc_serialize_checker / deserialize_checker / pad_spec_accepts_iff` | spec bridge AttestationData (codec equality with the checker Desc) | done | n/a (spec level) | done | n/a | n/a | 6/6 통과 | n/a |
| `E2e.cp_e2e_epoch_err_unreachable; E2eAd.ad_e2e_{slot,ci,source,target}_err_unreachable` | unreachable_mc (own column; not reject coverage) | done | n/a (local lemmas) | done | exact frame | done | 4/4 통과 | n/a |

| unreachable_mc 행 | 정리 | 상태 | reject 범위에 셈 |
| --- | --- | --- | --- |
| phase0.ssz.go:1988 fmt.Errorf("Epoch: %w") (decoder) | E2e.cp_e2e_epoch_err_unreachable | done | 아니요 |
| phase0.ssz.go:1964 fmt.Errorf("Epoch: %w") (encoder) | none needed: removed by the compiler (inlined Epoch.MarshalSSZTo cannot fail; no fmt.errorf call in the machine code, CALLGRAPH.md) | absent from the code | 아니요 |
| AttestationData decoder fmt.Errorf("Slot: %w") | E2eAd.ad_e2e_slot_err_unreachable | done | 아니요 |
| AttestationData decoder fmt.Errorf("CommitteeIndex: %w") | E2eAd.ad_e2e_ci_err_unreachable | done | 아니요 |
| AttestationData decoder fmt.Errorf("Source: %w") | E2eAd.ad_e2e_source_err_unreachable | done | 아니요 |
| AttestationData decoder fmt.Errorf("Target: %w") | E2eAd.ad_e2e_target_err_unreachable | done | 아니요 |

공리 전체 검사(감사 AU-10): `gen/e2e/axioms_gate.py`가 E2e, E2eAd, E2eScal의 모듈 76개를 프로그램으로 나열한다. 선언 2705개(정리 2282개)의 공리 집합이 모두 표준이고 `sorryAx`는 0개다(gate 작업 254, `axioms-gate.json`). 손 목록 129개 이름은 "있어야 함" 검사로 남는다. 빠진 이름은 0개다. 부정 대조: `sorry`를 쓰는 임시 정리 `E2e.sorry_ctl'`을 더하면 FAIL이다(작업 256).
부정 시험 전체: 154/154 통과 (`negative/result.json`). Go 차분: 59건, 불일치 0건 (`differential.json`). 공리: 79개 이름, 판정 PASS (`axioms.json`).

비용 기록(PROOF-PLAN §4): `prysm/go1.26.10/e2e/COST.json`은 `gen/e2e/cost.py`가 gate 기록(`records.jsonl`)과 작업 로그에서 만든다. 모듈과 정리마다 gate 안 벽시계 초, 실행 수, 실패한 실행 수, 프로세스 최대 RSS, memcap 종료 수다. gate 밖의 시간(생각, 편집)은 들어 있지 않다. 감사 AU-16: 모듈의 `gate_s`는 "누적 gate 초"다. 실패와 성공을 합친 모든 시도의 합이고 빌드 시간이 아니다. `last_ok_run_gate_s`는 마지막 성공 실행의 gate 초이고 통제된 냉 빌드가 아니다. 냉 빌드 초는 따로 잰 곳에만 적는다. `cost.py`와 `tcost.py`는 마지막 작업 번호를 인수로 받아 출력의 `source`에 적는다. 그래서 스트림이 진행해도 같은 출력이 나온다. `COST.json`은 상한 213(작업 212개, 15151.6초)이고, 커밋된 값과 같다. `TEMPLATE-COST.json`은 작업 214–247이다.

부정 시험 등급(리뷰 e2e-r2 N1): `negative.py`는 결과마다 `class`를 적는다. Lean의 "(deterministic) timeout" 오류는 `timeout_heartbeat`, 사례별 제한(300초) 초과는 `timeout_wall`이다. Lean의 "maximum recursion depth" 오류는 `recursion_limit`이다. 세 자원 등급은 통과가 아니다. 하트비트 시간 초과였던 문장 변이 2건은 명확하게 실패하는 변이로 바꿨다: `cpmr-stmt-noown`(전제에서 `dst[len..len+8]` 소유 삭제, C-1 저장 단계에서 실패), `cpg-stmt-growle`(`cap < len + 8`을 `≤`로), 그리고 코드 변이 `cpg-oldcap`(첫 지점 growslice oldCap 인수)을 더했다. 시도한 `cpg-stmt-noroot`는 300초 제한에 걸려서 넣지 않았다(gate 작업 126). 세션 3의 전체 실행(gate 작업 139, 사례별 300초): 73/73, 시간 초과 0. `cpg-newptr`(작업 125에서 489.7초 뒤 정리 안 실패)는 300초를 넘어 뺐다. 등급은 첫 오류 줄로 정한다. `ep-load8`은 첫 오류가 정리 안의 `ecancel` 실패이고 뒤의 오류 하나가 하트비트 시간 초과다(`later_resource_error`에 적음). `sl-load8`, `ci-load8`도 같다.
감사 AU-04: 첫 오류가 구문 오류, 알 수 없는 식별자, 알 수 없는 상수이면 등급은 `wrong_target`이다. 통과가 아니다. 변이가 목표에 닿지 않았다는 뜻이다. 다시 분류한 결과 `cps-stmt-u-rax`, `cps-stmt-m-mm`, `ada-m-nohms` 3건이 `inside`에서 `wrong_target`으로 바뀌었다. `scal/negative-result.json`(18건)은 바뀌지 않았다.
그 3건을 형 약화 변이로 바꿨다. 이름은 두고 전제의 형을 `True`로 바꾼다. 사례마다 gate 작업 하나다(작업 251–253). 세 건 모두 `inside`다. 첫 오류는 그 전제를 쓰는 자리의 "Application type mismatch"다(`hms`/`hmm`의 형 `True`, 기대 형 `MakesliceC …`/`MemmoveC S`). 이것은 증명이 그 자리에서 전제를 쓴다는 것을 보인다. 전제 없이는 정리가 거짓이라는 것은 보이지 않는다.
감사 AU-05: `lake env lean`은 trace를 검사하지 않는다. 그래서 `negative.py`와 `axioms.py run`은 먼저 `lake build --no-build <가져오는 모듈>`을 실행한다. 종료 코드가 0이 아니면 아무 사례도 실행하지 않는다. 세션 7: gate 작업 248 `lake build --no-build E2e E2eAd E2eScal` 종료 3(E2eAd 5개 모듈 trace 낡음), 작업 249 `lake build E2eAd` 종료 0, 작업 250 같은 검사 종료 0.
세션 4 작업 202에서 3건(`cpw-tr-jne`, `cpw-tc-lea`, `cpw-hg-jae`)은 "outside"였다. 같은 파일의 앞 정리가 같은 지시문을 지나기 때문이다. 변이는 실패했다. 작업 203에서 `cpw-tr-err1`, `cpw-tc-stmt-num`, `cpw-hg-spill`로 바꿨다(리뷰 e2e-r3 S6, `e2e.json` `negative_suite.removed`).
`ci-load8`은 세션 4 결과 파일에 없었다. 세션 5 작업 213에서 다시 실행했다: 안 실패, 하트비트 오류가 뒤에 있다(리뷰 e2e-r3 S4).
결과 파일은 여러 작업의 결과를 사례 id로 합친 것이다. 모든 사례는 사례별 300초 제한으로 실행됐다. 한 번의 실행으로 전부를 돌리지 않았다(실행당 gate 20분 제한).

리뷰 e2e-r1 처리(세션 2): M1 수정(진짜 합성 `cp_e2e_unmarshal_then_marshal`), S1 증명(`E2e.SpecEq`), S2 문구 유지(`cp_e2e_epoch_err_unreachable`은 지시 18에서 rax = 0이면 지시 47에 닿는다는 국소 보조정리이고, rax = 0은 `ep_uacc_holds`가 준다; 둘을 잇는 단일 정리는 쓰지 않았다), S3 E2e include 파일과 `e2e/AXIOMS.txt`의 sha256을 `e2e.json` `e2e_include_sha256`에 기록, S4 재현 줄, S5 adjustframe 행, S6 증인 `WitCpAS`·`WitCpRS`, S7 사례별 900초 제한으로 전체 부정 시험을 실행(gate 작업 125: 73건; 리뷰 e2e-r2 N1에 따라 다시 분류하면 안 실패 53, 대조 18, Lean 하트비트 시간 초과 2: `cpmr-stmt-dst-unchanged` 482초, `cpg-stmt-e8off` 480초), S8 차분 확장(수신자 불변, 오류 정체성과 반대 오류 아님, Epoch 오류 문구, C-1 바이트를 호출자 배열에서 관찰), S9 참조 행 G-2, G-3.

수용기 메모: 정리의 수신자 배치는 `prysm/ir/ir-mainnet.json` `go_fields`(gc amd64 규칙)다. `state` 0, `Epoch` 8, `Root` 16, `unknownFields` 40, `sizeCache` 64, 크기 72.
Go 값 요소: `E2e.GoVal`의 `cpGoValue`로 증인 수신자를 확인했다. 디코더 앞과 인코더 증인의 수신자는 증인 블록에서 읽는다(`recvAt`). 디코더 뒤의 수신자는 손으로 쓰지 않는다: `cpAfterDecode`는 `cp_e2e_accept_main` 결론이 `rax .. rax + 72`에 적는 조각들이고, `cp_after_decode_goValue`가 모든 Go 값 앞 수신자, 모든 입력 8바이트, 모든 `p ≠ 0`에서 Go 값임을 증명한다. `MakesliceC`는 `p ≠ 0`을 말하지 않으므로 이것은 조건이다(리뷰 e2e-r2 N4). 술어는 슬라이스 헤더의 건전성만 본다(Epoch 값, Root 내용은 보지 않는다). Epoch 두 행과 `cp_e2e_reject_size_main`에는 GoVal 정리가 없다: Go 값 칸은 "differential only"다. 배치는 IR(go/types)에서 왔다. ELF abi.Type은 이름 있는 기호가 없어서 읽지 않았다(신뢰 항목).
인코더 스택 임시 영역 32바이트 중 8–31바이트는 X15 내용이다. X15 = 0을 가정하지 않아서 결론에서 존재 양화다.
디코더 정리는 메모리 상한 6 GiB 안에 들도록 `L_b4`(지시 47)에서 둘로 나눴다(`cp_e2e_accept_tail`).
합성 E5: 디코더가 남긴 저장 rbp(x − 8), rbx 보관(x + 16), `p`(x − 32), 0 두 워드(x − 48, x − 40)가 인코더의 `fp`, `s2`, `l32`, `t30`이다(x = 두 진입의 rsp). 인코더 칸 x − 16, x − 24, x − 64…x − 49는 디코더 발자국 밖이라 호출자가 dst와 함께 준다. 인코더 반환 칸 x − 120과 그 아래 스크래치는 디코더 스크래치의 아래 부분이다(`S ≥ 24`, 인코더 `S − 24`, `MemmoveC`의 두 인스턴스). 합성 정리에는 코드 변이 부정 시험을 두지 않는다. 지난 코드 변이 4건(`cpx-dec-cmp41`, `cpx-ep-load8`, `cpx-enc-len33`, `cpx-enc-newlen16`)은 상수 이름 바꿈 때문에 가져온 주 정리의 적용에서 형 불일치로 실패했다. 바뀌지 않은 사본도 같이 실패하므로 지시문의 증거가 아니다(리뷰 e2e-r2 N2). 그래서 뺐다. 두 반쪽의 지시문 증거는 `cpa-*`, `cpm-*` 코드 변이다. 합성의 부정 시험은 문장 변이 6건과 대조 1건이다.

재현(모두 gate와 memcap 6 GiB 안에서):

```sh
python3 -I -B fv/kraken/gen/e2e/callgraph.py <objdump> prysm/go1.26.10/e2e/callgraph.json <m2.log>
python3 -I -B fv/kraken/gen/e2e/e2elink.py filter <out> <objdump> <elf> <nm>
mkdir -p <out>/norm && python3 -I -B fv/kraken/link/conv.py <out>/target.objdump <out>/p1bin-amd64.nm <out>/norm --norm
python3 -I -B fv/kraken/gen/e2e/e2elink.py data <out> && python3 -I -B fv/kraken/link/check.py <out>
# <nm> = p1bin-amd64.nm, sha256 88ee8b9a…40ac (e2e.json link_check_inputs; 커밋하지 않음, 감사 AU-17)
GOROOT=$(go env GOROOT) go test -count=1 ./ssz/ ./sszgen/... ./fv/kraken/semtest/    # 검사점 gate 목록 (감사 AU-17)
(cd fv/kraken/lean && lake build E2e.<모듈>)            # 모듈 하나씩: Epoch WitEp Spec CpAccept WitCpA CpReject WitCpR CpSpecK CpMarshal WitCpM Compose CpCompose WitCpC CpMarshalG WitCpG CpMarshalR WitCpMR CpSpecM WitCpS EpReject WitEpR GoVal CpWTail CpWTailG CpWHead CpWGrow CpWGrowAny CpWCover WitCpW WitCpWR CpWSharp CpWCoverF WitCpWF WitCpWRF GoValW
python3 -I -B fv/kraken/gen/e2e/axioms.py run fv/kraken/gen/e2e/Axioms.lean prysm/go1.26.10/e2e/axioms.json   # lake build --no-build 먼저 (감사 AU-05)
python3 -I -B fv/kraken/gen/e2e/axioms_gate.py run prysm/go1.26.10/e2e/axioms-gate.json <dump.tsv>   # E2e/E2eAd/E2eScal의 모든 선언 (감사 AU-10)
python3 -I -B fv/kraken/gen/e2e/negative.py fv/kraken/gen/e2e/negcases.json <work> prysm/go1.26.10/e2e/negative/result.json
python3 -I -B fv/kraken/gen/e2e/differential.py cases <c.json>; go run ./fve2e/cpcheck <c.json> > <o.json>   # Prysm 임시 트리, Go 1.26.10
python3 -I -B fv/kraken/gen/e2e/differential.py check <c.json> <o.json> prysm/go1.26.10/e2e/differential.json
```
