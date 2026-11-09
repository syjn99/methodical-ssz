# gen/wit: 증인 생성기 (X3)

fix3의 `lean/tools/wit` 생성기를 이 생성기 트리에서 돈다. `lean/Fk`에는 쓰지 않는다.
증명이 아니다. 게이트 1c 통과가 아니다.

## 1. 파일

| 파일 | 무엇 |
| --- | --- |
| `src/` | `lean/tools/wit`의 바이트 사본(fix3 stage A `d9cdb40`, `src/SOURCES.sha256`). `wgen.py`만 `write`가 다르다 |
| `config.json` | 설정: 호출 57개(생성기, 인수), 모듈 75개와 정리(`src/README.md` 표). `run.py config`가 쓴다 |
| `run.py` | `run.py gen <out>`: 호출을 모두 돌리고 출력과 `lean/Fk/<이름>`을 바이트로 비교한다(`regen.json`) |
| `goval_lean.py` | Go 값 검사를 Lean 술어로 낸다(`GoValCheck.lean`, 대조군 `GoValControl.lean`) |
| `normalize.py` | 원자 정규화: `(N : BitVec 64)`, `BitVec.ofNat 64 N` → `(N#64)` |
| `test_wit.py` | 경계 대조군(기호 길이, `lean/Fk`, 비지 않은 출력, 정규화) |
| `results/` | 커밋된 결과 |

## 2. `wgen.write`의 차이

- 출력은 `$GEN_WIT_OUT/<이름>`이다. 실제 경로가 `lean/Fk` 아래이면 거부한다.
- 블록에 길이를 모르는 조각이 있으면 거부한다(기호 길이; REPORT 7.3). 판정은 `src/goval.py`의 `Mem`이다.
- 쓴 이름을 `$GEN_WIT_OUT/.written`에 적는다.
- 생성기는 `../link/out/norm/*.S`를 읽는다. 그래서 cwd는 `fv/kraken/lean`이다(읽기만).

## 3. Go 값 검사(Lean)

- 사실: `src/goval.py`와 같다(슬라이스 머리, 객체 크기·정렬, bool 바이트, errorString itab의 형식 단어, 초기화된 오류 전역, Go 객체 서로소, `s_mem` 조각이 객체 하나 안 또는 모든 객체 밖).
- 결합: 생성 파일이 `lean/Fk/<이름>`과 바이트가 같고 `block`에 매개변수가 없으면, 수마다 Lean 정의(`Fk.<Wit>.s0`의 레지스터, `Fk.<Wit>.block`의 단어·바이트)와 `rfl`로 맞춘다.
- 술어: `Gen1c.GoVal.sliceOk`, `objOk`, `boolOk`, `pairwiseDisjoint`, `chunksOk`(Bool, `rfl`).
- 배치의 출처: `[]uint64`의 원소 크기 = 포함한 `abi.Type` uint64의 `Size_`(`eszU64_abi`, `Fk.Data.uint64Type_size_kind`). `*errors.errorString` 기술자 = 포함한 바이트(`errorStringPtrType_abi`; 블록 안 56바이트 = `Fk.Data.errorStringPtrType`, `rfl`). 구조체 크기·정렬(Scalars 24 등)은 `src/layout.json`(Go `unsafe.Sizeof`/`Alignof`)이다. 그 구조체들의 `abi.Type`은 포함되어 있지 않다.

## 4. 원자 정규화의 한계

- `def mem`과 `have H : Eq ((block …` 줄은 바꾸지 않는다. `wit_split`(fix3 `Fk.WHost`)이 그 철자를 본다.
- 정규화한 75개 파일은 모두 Lean에서 따로 돌아간다(run `logs/63`, `results/wit-norm.json`: 원자 810개, 바뀐 파일 65개). 첫 시도(괄호 없음, `mem`·`H` 줄까지 바꿈)는 표본 4개 중 1개만 통과했다. 정규화는 생성 출력의 기본이 아니다. 기본 출력은 `lean/Fk`와 바이트가 같다.
