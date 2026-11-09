# gen/x4: 명세 문장과 증명의 생성 (X4)

Desc와 Go 배치에서 정리 문장을, 기계어 지시 목록에서 증명을 만든다.
대상은 Go 1.26.3 ELF의 수작업 타입이다. Prysm 타입과 Go 1.26.10에 대해서는 아무것도 주장하지 않는다.
게이트 1c 통과가 아니다.

## 1. 파일

| 파일 | 무엇 |
| --- | --- |
| `x4gen.py` | 생성기. Desc는 `gen1c/emit.accept`(검사기 결과, sha256, SPEC)로만 받는다. 출력은 `lean/Gen1cX4/<T>.lean`(라이브러리 `Gen1cX4`, `lakefile.toml` 끝의 블록) |
| `compare.py`, `pairs-*.json` | 문장 비교: `∀ [Host], <obl>_stmt`와 손 정리의 타입이 정의상 같은지(`isDefEq`, 투명도 all) |
| `negative.py` | 부정 시험: 기계어 한 줄을 바꾼 사본으로 지정 정리를 다시 돈다. 대조군은 바꾸지 않은 사본 |
| `axioms.py` | `#print axioms`를 프로그램으로 판정(`propext`, `Classical.choice`, `Quot.sound`만) |
| `lean/Gen1cX4/Support.lean` | 생성 증명이 쓰는 보조정리(손으로 씀, 생성 아님) |
| `results/` | 커밋된 결과 |

## 2. 생성 규칙 (고정 크기, uint·bool 필드)

- 문장: 입력 조각 `b<i>`(SSZ 오프셋, 너비), 수신자 조각 `c<i>`(Go 오프셋, `gen/wit/src/layout.json`), 경로의 레이블 가설, 길이 가설, bool 값 가설.
- 증명: 지시 하나마다 `estep`·`kunfold`, 그리고 종류별 블록(스필 저장, 입력 적재, 수신자 저장, rip 적재, `cmp`, 조건 점프, `xor`, `retq`).
  조건 점프는 경로의 모드(수용, 길이 거부, bool 거부)에서 결과를 정하고, 불가능한 갈래를 조건 종류별 조각으로 닫는다.
- 손 증명의 정형 조각을 따른다(`Fk/ScAccept.lean`, `Fk/FvSmall.lean`, `Fk/ScRejectBool.lean`). 출처는 코드 주석에 있다.

## 3. Scalars 조각 (첫 조각)

`results/attempts-scalars.json`, `compare-scalars.json`, `negative-scalars.json`, `axioms-scalars.json`.

| 의무 | 상태 |
| --- | --- |
| size | 생성 증명 통과, 문장 SAME(`sc_size_main`) |
| accept | 생성 증명 통과(시도 2), 문장 SAME(`sc_accept_main`) |
| reject r2 bool | 생성 증명 통과(시도 2), 문장 SAME(`sc_reject_bool_main`) |
| reject r1 size | 3회 실패, 막힘. 분류: 생성 틀의 자동화 한계(`ecancel`) |
| marshal, 조합 | 이번 세션에서 시도하지 않음 |
