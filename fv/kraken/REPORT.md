# REPORT: Kraken x64 코덱 검증의 현재 상태

기준: 수정 3(링크 재설계, `claude/ssz-fv-reprove-fix3`). 메모리 최적화 `e6e386d` 위다.
방향은 `DIRECTION.md`, 세션 이력은 `HISTORY.md`, 고정 버전은 `TOOLS.md`에 있다.

## 0. 판정

**조건부. 게이트 1 미통과.**

게이트 1을 막는 조건:

1. ListC 원소 오류 전달(`"Items: %w"`)의 정리가 없다(4절 7). 원소 오프셋 순서 거부는 첫 쌍만 닫았다.
2. 런타임 계약은 추상 모델로만 만족 가능성을 보였다. Go 런타임 정교화는 없다(3절).
3. 디코더의 EthLib 양방향 수용 정리는 BitVec(1바이트)뿐이다.
4. x86-64 하드웨어 대조를 하지 않았다. 이 호스트는 arm64다.

수정 3에서 닫은 것: 링크 검사 (f)(g)(h)·역할 분류·`golits.go` 삭제(Lake 입력과 ELF 데이터 include로 대체), 오류 증인의 타입 기술자와 초기화된 오류 전역, Scalars 비nil 거부, 사후조건 잔여 넷, ListC 원소 오프셋 순서 거부(첫 쌍), 게이트 표 정정.

수치(수정 3 끝, 차가운 프로젝트 빌드 뒤):

- `lake build`: 863 jobs, 성공(프로젝트 모듈 Built 161, 의존성은 따뜻함).
- 공리: 정리 `TOTAL 1627 NONSTANDARD 0`(`AXIOMS.txt`), 모든 선언 `TOTAL 8287 NONSTANDARD 0`(`AXIOMS-ALL.txt`).
- 시험 타입 9개. 증인 파일 80개.
- 링크 검사 PASS(검사 (a)–(f)). 자기 시험 10개 기대대로.
- 부정 시험 18개 기대대로(`negative/RESULT`, FAIL 16 + 대조군 PASS 2).
- goval: 80 파일, 위반 0, 미검사 2. 오류 증인의 타입 기술자 5곳과 오류 전역 19곳을 검사한다.
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
| ListU64 | EthLib→기계어 | 4/4: 짧음, 오프셋, 정렬, 초과 | 0·1·16, 거부 둘 | 위반 0. 오류 증인의 타입 기술자 = ELF, 전역 초기화. `%d`의 int 기술자 내용은 증인에 없음 | makeslice, growslice, convT64(상자), fmt `%d %w` | offset, maxlen | `lu_unmarshal_then_marshal` + WitLuComp | 수용 정확, 나머지 `R` + True. 크기 동일 |
| BitVec | 양방향(1바이트) | 2/2: 크기, 패딩 | b < 16, 16 ≤ b | 위반 0. 오류 증인 타입 기술자 = ELF | makeslice, fmt nil·`%w`, newobject 16 | vbvje, bvnochk | `bv_unmarshal_then_marshal`(증인 없음) | 수용·마샬 정확. 크기 동일 |
| BitL | EthLib→기계어(규칙 동치) | 3/3: 짧음, 오프셋, ValidateBitlist 오류 | 1, 257바이트 / 2049비트, 꼬리 [0] | 위반 0 | ValidateBitlist 두 계약(rodata), growslice, memmove, fmt `%w` | gsnum, blmnochk, blrity | 없음 | `R` 보존. 크기 동일 |
| Nested | EthLib→기계어 | 2/4. 남음: S 오류, L 오류(래핑) | 0·1·16 | 위반 0 | newobject 24, Scalars·ListU64 함수 명세 | neoff | 없음 | 수용·마샬·크기 `R` 보존 |
| List[container] | EthLib→기계어 | 6/10: 짧음, 오프셋, 0 오프셋, 짧은 첫 오프셋 둘, 원소 오프셋 순서(`lc_reject_offset_order_main`, 원소 2개 이상의 첫 쌍). 남음: 정렬(`%d`), 원소 수(`%d %w`), 원소 끝 오프셋 초과(`%d`), 원소 디코드 오류(`%w`) | 바깥 0·1·4, 안쪽 1×1, 4×16, 0·1·16. 순서 거부: 오프셋 [8, 4](`WitLcO`) | 위반 0 | makeslice 두 지점, newobject 16·24, fmt nil·`%d %d`(`FmtErrorfDDC`), convT64, ListU64 함수 명세 | nilerr, lcorder | 없음 | `R`과 죽은 스택(`lcStk`) 보존. 크기 동일 |
| Prysm 축약 Checkpoint | EthLib→기계어 | 1/1: 크기 | 고정 | 위반 0. `WitCpM` dst 기호 길이 미검사 | makeslice, memmove | cplen | 없음 | `R` 보존. 크기 동일 |
| Prysm 축약 AttestationData | EthLib→기계어 | 1/1: 크기. 하위 Checkpoint 오류 미도달은 정리가 없다 | 고정 | 위반 0 | makeslice, memmove, newobject 32 | adcopy | 없음 | `R` 보존. 크기 동일 |

"크기 동일" 정리 여덟: `ad_size_main`, `bl_size_main`, `bv_size_main`, `cp_size_main`, `fv_size_main`, `lc_size_main`, `lu_size_main`, `sc_size_main`.
`ne_size_main`은 `R`을 보존한다.

타입 전체 완료로 표시할 수 있는 타입은 없다.
Scalars와 ListU64는 수용·마샬 조합 증인만 완료다.
Scalars의 비nil 오류 연결과 Size 사후조건은 수정 3에서 닫았다. 조합은 `hupd`와 전체 증인까지다. 실제 호출자 명령 실행은 없다.
ListU64 오류 증인의 타입 기술자와 전역은 수정 3에서 채웠다. `%d` 인수의 int 기술자 내용은 증인에 없다.
나머지 타입은 조합이 없거나 거부 경로가 남는다.

Go 값 미검사의 종류별 집계(goval, 80 파일, 수치는 수정 3 X3 시점의 79 파일 기준이고 `WitLcO`는 미검사 0):

| 종류 | 검사함 | 미검사 |
| --- | --- | --- |
| 값 | 크기·정렬·패딩·bool·슬라이스·겹침 | 2 파일: `WitCpM` dst(기호 길이), 1a `Witness`(대상 없음) |
| 자원 조각(`s_mem`) | 1057 조각 | 40 조각(기호 길이나 주소) |
| 타입 내용 | `%w` 증인 5개의 `*errors.errorString` 기술자(Size_, Kind_) | `%d` 인수의 int·uint64 기술자 내용(증인 2개) |
| 런타임 전역 | `ssz.Err*` 전역 19곳의 초기화(itab, errorString) | `runtime.writeBarrier` 값, `staticuint64s` 항목(정리 `staticBox_of_lt`가 표와 연결) |

Prysm 두 타입은 v7.1.8 `51b5a75` 스키마를 옮긴 축약 구조체다.
protobuf 필드가 있는 실제 Prysm 바이너리의 증명이 아니다.

## 3. 신뢰 항목

| 항목 | 신뢰 내용 | 지금의 검사 | 다음 조치 |
| --- | --- | --- | --- |
| Lean 커널, Kraken x64 의미론, EthLib 명세 | 공유 기반 | 없음 | 유지 |
| Kraken = 실제 CPU | 하드웨어 대조를 하지 않았다 | 없음(arm64 호스트) | x86-64 Linux 기계 또는 CI |
| ELF → Lean 프로그램 | objdump, `link/conv.py`, `include_x64_rt` | 링크 검사 (a)–(e): 독립 디코더 셋, 심볼·변위 | 유지 |
| ELF → Lean 데이터 | `link/data.py`, `data_include`(`Fk/Include.lean`) | 링크 검사 (f): 데이터 파일 = ELF 바이트, 포인터 워드 = 심볼 + 오프셋. 해시는 RESULT 묶음 | 유지 |
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
| 1 | Lean 참조 검사의 역할과 이름 해석 | 닫힘: 역할 분류를 지웠다. 정리는 include 정의의 이름을 쓴다 | 수정 3 X2 |
| 2 | (h)의 전체 식과 타입 동일성 | 닫힘: (h)를 지웠다. 바이트와 포인터 워드를 include한다. 리뷰의 itab 변이는 자기 시험이 FAIL로 잡는다 | 수정 3 X2 |
| 3 | Go 형식 호출의 실제 대상 | 닫힘: `golits.go`를 지웠다. 형식 바이트는 ELF에서 온다 | 수정 3 X2 |
| 4 | 오류 타입 자료와 전역 불변식을 증인에. Scalars 비nil 거부 | 닫힘: `sc_reject_bool_err`, 증인 18개의 전역 초기화, `%w` 증인 5개의 ELF 기술자 | 수정 3 X3 |
| 5 | 배치 재생성 뒤 goval. 미검사 종류별 집계 | 닫힘: 재생성 바이트 동일, 2절 집계 표 | 수정 3 X6, X7 |
| 6 | 사후조건: NeMarshal, ListC 스택, Scalars Size, r14 | 닫힘 | 수정 3 X4 |
| 7 | ListC 원소 오프셋 순서와 원소 오류 전달 | 부분: 순서 거부는 닫힘(`lc_reject_offset_order_main`, `lcl_order`, `FmtErrorfDDC`·`rt_errorf_dd`·`joint_models`, `WitLcO`, 부정 시험 lcorder). 원소 오류 전달은 없음 | 다음 세션 |
| 8 | 게이트 표 정정 | 닫힘(2절) | 수정 3 X6 |

7의 남은 부분은 게이트 완료를 주장하기 전에 필요하다.
순서 거부 정리는 반복 0(첫 쌍)만 진입부터 증명했다. `lcl_order`는 임의 반복 i의 루프 보조 정리다. 앞 원소를 수용한 뒤의 반복은 `lcl_loop`과 잇는 일이 남았다.
순서 거부의 추가 전제: 인수 배열(진입 rsp − 104부터 32바이트), spill rsp − 200·− 192, `lcFmtOrder` 바이트, `StaticBox e`·`StaticBox 4n`. `lc_accept_main`은 바꾸지 않았다.
원소 오류 전달은 시작하지 않았다. 필요한 것: ListU64 거부 정리(`lu_reject_misaligned_main` 등)에서 유도한 거부 함수 명세, 지시어 295–297(`callq ListU64.UnmarshalSSZ; test; jne`) 뒤 `"Items: %w"` 블록의 루프 보조 정리, 진입부, 증인.

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

저장소 루트에서 시작한다.

```sh
cd fv/kraken/lean && lake build                                 # 856 jobs
sh tools/axioms.sh                                               # NONSTANDARD 0 (두 범위)
lake env lean tools/RegressFix2.lean                             # 오류 없음
for f in ../review/*.lean; do lake env lean $f; done             # Review1bFixB0.lean은 vcgen/에서
cd ../../.. && go run fv/kraken/lean/tools/wit/layout.go > fv/kraken/lean/tools/wit/layout.json
python3 fv/kraken/lean/tools/wit/goval.py                        # 위반 0
python3 -B fv/kraken/link/check.py fv/kraken/link/out            # PASS all, BUNDLE
python3 -B fv/kraken/link/check.py --selftest fv/kraken/link/out # 10 cases
PATH=/workspace/tooling/fv/compat-bin:$PATH fv/kraken/negative/run.sh <워크트리 밖 scratch>  # 18 cases; Linux는 cp -c 대체 필요
GOROOT=$(go env GOROOT) go test -count=1 ./fv/kraken/semtest/    # F1, F2 PASS
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
7. 증인은 오류 전역을 초기화된 값으로 두고 `%w` 타입 워드가 ELF 기술자(`errorStringPtrType`)를 가리키게 한다. goval이 둘을 검사한다.
