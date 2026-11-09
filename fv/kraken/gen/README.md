# gen: phase1c 생성기와 도구

1c(증명 생성기와 Prysm Fulu 전수)의 코드다. 증명은 아직 없다. 게이트 1c 통과가 아니다.
Prysm 결과는 `../prysm/`에 있다. 환경과 gate 규칙은 run 디렉터리의 브리프를 따른다.

## 1. 디렉터리

| 경로 | 무엇 | 단계 |
| --- | --- | --- |
| `invtool/` | 생성기 앞단의 IR을 JSON으로(임시 Prysm 트리에서 빌드) | P1 |
| `prysm-gen.sh`, `prysm-elf.sh`, `keepalive.py` | 생성, IR, Go 1.26.10 ELF | P1 |
| `inventory.py`, `gendiff.py`, `mnemonics.py`, `kparse/`, `types_md.py` | 목록, diff 분류, 명령어 통계, Kraken 파서 실행, `TYPES.md` | P1 |
| `obligations.py` | Go 소스의 오류 반환 지점 열거 | P2 |
| `frozen/` | 고정 목록 `THEOREMS.json`, `ASSUMPTIONS.json`(생성기가 쓰지 않는다) | P2 |
| `desc/` | `Desc` 생산기와 시험 | P3 |
| `desccheck/` | 독립 `Desc` 검사기(Lean, EthLib 함수 실행) | P3 |
| `gen1c/` | 생성기 골격, include 어댑터 하나 | P4 |

## 2. 산출물 형식

모든 JSON에 `schema` 키가 있다.

| 산출물 | 형식 | 정의 |
| --- | --- | --- |
| Desc | `fvphase1c.desc/1` | `desc/producer.py` 머리 주석. EthLib `Desc` 항 + 머리 배치 주장 |
| 정리 문장 | Lean `def <obl>_stmt [Host] : Prop` (`namespace Gen1c.<T>`) | `gen1c/emit.py`. 증명·`sorry` 없음. 지금 틀은 고정 크기 타입의 size뿐이다 |
| 증인 설정 | `witness.json` | 가변 필드마다 길이 0·1·최대. 가변 원소 리스트는 안쪽 길이 규칙을 붙인다 |
| 부정 사례 | `negative.json` | 변이, 지정 정리, 기대 실패, 대조군. 지금은 형식만(X4에서 실행) |
| 데이터 파일 | `<id>.data`(include API v1) | `gen1c/include_adapter.py`만 API 이름과 문법을 안다 |
| 의무 목록 | `fvphase1c.theorems/1` | `frozen/THEOREMS.json` |
| 허용 가정 | `fvphase1c.assumptions/1` | `frozen/ASSUMPTIONS.json` |
| 매니페스트 | `fvphase1c.gen-manifest/1` | API 버전, 입력 해시, 타입별 파일, 데이터 항목(오프셋, 코드 참조 여부) |

include API: `api_version` 1, status `committed`(fix3 `427708e`). 사본 `gen1c/include-api-v1.json`.
버전이 바뀌면 `gen1c/include_adapter.py`만 고친다. `check_api`가 다른 버전을 거부한다.

## 3. 규칙

- 생성기는 `lean/Fk`, `link/`, `gen/frozen/`에 쓰지 않는다. `emit.py`가 쓰기 전에 검사한다(`gen1c/test_emit.py`의 대조군).
- fix3가 승인되기 전에는 `lean/Fk`·`link/` 코드를 생성하지 않는다. 출력은 run 디렉터리의 scratch·artifacts다.
- Python은 표준 라이브러리만, `python3 -I`로 돈다. Go·Lean 실행은 모두 gate 안에서 한다.

## 4. 시험

| 시험 | 명령 | 결과 파일 |
| --- | --- | --- |
| Desc 검사기 양성·음성 | `desc/test_desc.py prepare/evaluate` + gate `DescCheck.lean` | `desc/results/desc-test.json` |
| 생성기 골격 | `gen1c/test_emit.py prepare/evaluate` + gate `Compare.lean` | `gen1c/results/gen-test.json` |
