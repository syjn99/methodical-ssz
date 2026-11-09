# DIRECTION: 코덱 검증의 방향 (2026-11-06)

이 문서는 다음 세션들이 따르는 방향이다. 세부 규칙은 `fv/AGENTS.md`, 현재 상태는 `REPORT.md`에 있다.

## 1. 목표

methodical-ssz가 생성한 x86-64 코드가 EthLib SSZ 명세대로 수용·거부·인코딩한다는 것을 Kraken x64 위에서 증명한다. 증명은 생성기 결함을 드러내는 수단이다(F1·F2·G1–G3·H1이 그 예). 다음 목표는 Prysm Fulu 타입 전체에 대한 자동 증명(1c)이다. 결과를 빨리 낸다. 검사기를 보강하는 일보다 결과를 내는 일을 앞에 둔다.

## 2. 현재 상태 (0ef30e3)

게이트 1 미통과. 시험 타입 9개의 디코더·인코더·크기 함수 주 정리 55개, 증인 선언 80개, 부정 시험 16개, 공리 비표준 0. 남은 것은 `REPORT.md`의 게이트 표와 신뢰 항목에 있다. 리뷰 세 번(재증명, 수정, 수정 2)이 공통으로 지적한 것: 링크 검사 (g)(h)가 Lean·Go 소스의 철자를 읽어서 변형에 뚫린다.

## 3. 신뢰 기반(TCB)과 결정

| 항목 | 지금 | 결정 |
| --- | --- | --- |
| Lean 커널, Kraken x64 의미론, EthLib 명세, Kraken = 실제 CPU | 신뢰 | 유지. 공유 기반 |
| ELF → Lean 프로그램(objdump, conv.py, include) | 독립 디코더 셋 교차 + 심볼·변위 검사 (a)–(e) | 유지. con-agua보다 엄격하며 뚫린 적 없음 |
| 재빌드 추적 (f) SHash | 해시 파일 + 원문 비교 | **삭제.** `lakefile.toml`의 라이브러리 `needs`에 `.S`·데이터 파일을 `input_file`로 등록한다(con-agua `ConAgua/AsmFile/Include.lean` 37–39행 방식). 파일 내용이 모듈 입력 해시에 들어가 Lake가 재빌드한다 |
| 손으로 쓴 상수 + (g)(h) + 역할 분류 + golits.go | Lean·Go 소스 정규식 | **삭제.** 변환기가 ELF에서 rodata·itab·타입 기술자·`staticuint64s`를 바이트 파일로 뽑아 코드처럼 include한다. 정리는 손 상수 대신 그 정의를 쓴다. "Lean 상수 = ELF 바이트"는 (a)와 같은 해시 묶음이 된다. con-agua DESIGN.md `ldc` 항목과 같은 구조(상수는 프로그램 항의 일부, 바이트의 실제성은 변환기 신뢰) |
| Go 값 검사(goval, layout.go) | Python, go/types 표 | 1c X2에서 Lean 술어로 옮기고 배치를 include한 abi.Type에서 읽는다. 지금은 유지 |
| Go 런타임 계약 | 추상 모델로 무모순만 | 유지. 런타임 함수 증명은 2단계(HTR) 뒤 |

원칙: 바이너리의 바이트에 대해 말할 수 있는 것은 Lean 정리로 만든다. 바깥 도구는 "바이트를 Lean에 옮기는 변환기" 하나만 남긴다. Python 검사기를 더 똑똑하게 만드는 수정은 하지 않는다.

## 4. 순서

1. **정리 세션**(ssz-fv-cleanup, 반나절): 코드·주석·보고서·아티팩트를 줄인다. 정리 문장은 바꾸지 않는다.
2. **수정 3 = 링크 재설계**(ssz-fv-reprove-fix3, 1일) ∥ **1c**(ssz-fv-phase1c, 5일). 같은 지점에서 분기. 1c는 첫 이틀 동안 `lean/Fk`·`link/`를 건드리지 않는 일(Prysm Fulu 타입 목록·명령어 통계, `Desc` 검사기, 생성기 골격)을 하고, 수정 3 in-review 뒤 그 위로 rebase해 X1·X2를 include 설계로 만든다.
3. 수정 3의 범위: `input_file` 등록과 SHash 삭제, 데이터 include와 (g)(h)·역할 분류·golits.go 삭제, 오류 증인에 실제 타입 기술자와 초기화된 오류 전역, Scalars 비nil 거부 정리, 사후조건 잔여(NeMarshal R, ListC 스택, sc_size, r14), ListC 원소 오프셋 순서 거부, 게이트 표 정정(astra 수정 2 리뷰 8절).

## 5. 고정 기준

생성기 소스 `698c202`, 병합 기준 `2d0150b`. Go 1.26.3 linux/amd64 GOAMD64=v1 purego trimpath CGO_ENABLED=0. Kraken `6064eec`, EthLib `8621856`, Lean nightly-2026-09-21. ELF `9c850c97…c501`. Prysm 축약 두 타입은 v7.1.8 `51b5a75`. 1c의 Prysm 소스는 `ab15ff70c72a568c870b2de662474685a95de294`(slice + `ssz-size`), fork Fulu, 생성은 임시 워크트리에서만. 고정 배열 핀과 같다고 주장하지 않는다. 1c의 대상 컴파일러는 Go 1.26.10이다. 새 실험 기준선이며 이름공간이 따로다(`prysm/go1.26.10/MANIFEST.md`, ELF `c6403c02…911e`). Go 1.26.3 ELF `9c850c97…c501`의 정리는 이 기계어에 옮겨지지 않는다. 대체된 이력: 1c 핀 `5ac1d028f5`(핀 브랜치 `45394e5`, `syjn99/prysm`에서 얻을 수 없음), 1c 컴파일러 Go 1.26.3. 수정 3의 값(위 문장의 Go 1.26.3과 ELF)은 바뀌지 않는다.

## 6. 규칙 (요약, 전문은 fv/AGENTS.md)

`sszgen/`·`ssz/`·Kraken·gohashtree·`fv/<project>/upstream` 수정 금지. 해시는 계약. `sorry`/`axiom`/`native_decide`/`bv_decide` 금지. 한 번에 Lean 빌드 하나. 삭제가 추가보다 낫다. 세션 끝에 in-review와 한 줄 comment.
