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
| `run_checks.sh` | gate 안 검사 실행기: build, 비교, 공리, 부정 시험을 메모리 캡 아래 돌리고 첫 실패 코드로 끝난다(리뷰 r5 S4) |
| `axioms.py` | `#print axioms`를 프로그램으로 판정(`propext`, `Classical.choice`, `Quot.sound`만) |
| `lean/Gen1cX4/Support.lean` | 생성 증명이 쓰는 보조정리(손으로 씀, 생성 아님) |
| `results/` | 커밋된 결과 |

## 2. 생성 규칙 (고정 크기, uint·bool 필드)

- 문장: 입력 조각 `b<i>`(SSZ 오프셋, 너비), 수신자 조각 `c<i>`(Go 오프셋, `gen/wit/src/layout.json`), 경로의 레이블 가설, 길이 가설, bool 값 가설.
- 증명: 지시 하나마다 `estep`·`kunfold`, 그리고 종류별 블록(스필 저장, 입력 적재, 수신자 저장, rip 적재, `cmp`, 조건 점프, `xor`, `retq`).
  조건 점프는 경로의 모드(수용, 길이 거부, bool 거부)에서 결과를 정하고, 불가능한 갈래를 조건 종류별 조각으로 닫는다.
- 무엇이 생성이고 무엇이 손 글인가(리뷰 r5 S2): 지시 하나마다의 단계(`estep`·`kunfold`·`kat`와 적재·저장 블록, 레이블 번호, 주소 식, 점프 결과)는 `.S` 지시 목록과 Desc·배치에서 만든다. 갈래를 닫는 조각과 마무리 조각은 손 증명의 글을 너비·가설 이름·번호만 바꿔 담은 것이다(`Fk/ScAccept.lean`, `Fk/ScRejectBool.lean`, `Fk/ScReject.lean`, `Fk/ScMarshal.lean`, `Fk/ComposeSc.lean`, `Fk/FvSmall.lean`, `Fk/LuMarshal.lean`, `Fk/LuReject.lean`). 리뷰 측정: Scalars accept 생성 전술 146줄 중 130줄이 손 증명에 글자 그대로 있다. 그래서 이것은 "손 증명을 Desc·지시 목록에 맞춰 틀로 재구성한다"이다. 새 명령어나 새 갈래에는 새 손 조각이 필요하다.
- 문장은 Desc와 배치에서 만들지만, 꼴은 손 정리의 문장을 본뜬 것이다(SAME 비교가 그것을 확인한다).

## 3. Scalars 조각 (첫 조각)

`results/attempts-scalars.json`, `compare-scalars.json`, `negative-scalars.json`, `axioms-scalars.json`.

| 의무 | 상태 |
| --- | --- |
| size | 생성 증명 통과, 문장 SAME(`sc_size_main`) |
| accept | 생성 증명 통과(시도 2), 문장 SAME(`sc_accept_main`) |
| reject r2 bool | 생성 증명 통과(시도 2), 문장 SAME(`sc_reject_bool_main`) |
| reject r1 size | 설계 1은 3회 실패(`ecancel`; 시도 2·3은 시도 1에 한 줄을 더하거나 `try`로 감싼 땜질이었다. 접근은 같았다). 설계 2(`Fk/ScReject.lean`의 `h_mem'` 재배열과 `sym`/`kstep` 틀)로 생성 증명 통과, 문장 SAME(`sc_reject_size_main`) |
| marshal | 생성 증명 통과(시도 1), 문장 SAME(`sc_marshal_main`) |
| 조합 | 생성 증명 통과(시도 1, 생성한 accept·marshal 위), 문장 SAME(`sc_unmarshal_then_marshal`). 전 전제 증인 `Gen1cX4.WitScComp`(gen/wit 출력을 생성 정리로 다시 겨눔) |

## 4. ListU64 조각 (부분)

`results/attempts-listu64.json`, `compare-listu64.json`, `negative-listu64.json`, `axioms-listu64.json`.
틀은 `Fk/LuMarshal.lean`(size)과 `Fk/LuReject.lean`(짧은 길이, 첫 오프셋)의 조각을 따른다. 보조정리 `Gen1cX4.off4`는 손으로 다시 증명했다(`Fk.lu_off4`와 같은 문장).

| 의무 | 상태 |
| --- | --- |
| size | 생성 증명 통과(시도 1), 문장 SAME(`lu_size_main`) |
| reject r1 짧은 길이 | 생성 증명 통과(시도 1), 문장 SAME(`lu_reject_short_main`) |
| reject r2 첫 오프셋 | 생성 증명 통과(시도 1), 문장 SAME(`lu_reject_offset_main`) |
| reject r3 정렬, r4 한도 초과 | 시도하지 않음(fmt.Errorf 호출 틀 필요) |
| accept(0·1·16), marshal(growslice), 조합 | 시도하지 않음(루프 틀 필요) |
