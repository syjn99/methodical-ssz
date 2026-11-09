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
| 정리 문장 | Lean `def <obl>_stmt [Host] : Prop` (수작업 `namespace Gen1c.Hand.<T>`, Prysm `Gen1c.Prysm.<패키지 끝 두 마디>.<T>`) | `gen1c/emit.py`. 증명·`sorry` 없음. 지금 틀은 고정 크기 타입의 size뿐이다 |
| 증인 설정 | `witness.json` | 가변 필드마다 길이 0·1·최대. 가변 원소 리스트는 안쪽 길이 규칙을 붙인다 |
| 부정 사례 | `negative.json` | 변이, 지정 정리, 기대 실패, 대조군. 지금은 형식만(X4에서 실행) |
| 데이터 파일 | `<id>.data`(include API v2, 형식은 v1과 같다) | `gen1c/include_adapter.py`만 API 이름과 문법을 안다 |
| 의무 목록 | `fvphase1c.theorems/1` | `frozen/THEOREMS.json` |
| 허용 가정 | `fvphase1c.assumptions/1` | `frozen/ASSUMPTIONS.json` |
| 매니페스트 | `fvphase1c.gen-manifest/1` | API 버전, 입력 해시, 타입별 파일, 데이터 항목(오프셋, 코드 참조 여부) |

include API: `api_version` 2, status `committed`(fix3 `b6c32c3`, 리뷰 전). 사본 `gen1c/include-api-v2.json`, v1 사본은 이력.
버전이 바뀌면 `gen1c/include_adapter.py`만 고친다. `check_api`가 다른 버전을 거부한다.

## 3. 규칙

- 생성기는 `lean/Fk`, `link/`, `gen/frozen/`에 쓰지 않는다. `emit.py`가 쓰기 전에 검사한다(`gen1c/test_emit.py`의 대조군).
- fix3가 승인되기 전에는 `lean/Fk`·`link/` 코드를 생성하지 않는다. 출력은 run 디렉터리의 scratch·artifacts다.
- Python은 표준 라이브러리만, `python3 -I`로 돈다. Go·Lean 실행은 모두 gate 안에서 한다.

## 4. 시험

| 시험 | 명령 | 결과 파일 |
| --- | --- | --- |
| Desc 검사기: 원본 144(닫힌 세계), 대조군, 리뷰 변이 재생(r1 20, r2 32, r3 40), 목록 시나리오(리뷰 t01–t13, 내 것, 틀린 수작업 Desc마다 add/replace) | `desc/test_desc.py prepare` → gate `desc/run_desccheck.sh` → `desc/test_desc.py evaluate` | `desc/results/desc-test.{json,md}` |
| emit 경계: 모든 시나리오를 `emit.accept`로, 리뷰 E1–E7, 내 탈출 시도 x01–x16 | `gen1c/test_boundary.py <desc-work> <out>` | `gen1c/results/boundary.{json,md}` |
| 생성기 골격: 대조군, 데이터 교차 검사, 문장 비교 | `gen1c/test_emit.py prepare <work> <desc-work>` → gate `Compare.lean` → `evaluate` | `gen1c/results/gen-test.json` |
| 고정 목록 재현 | `frozen/test_frozen.py <repo-root> <scratch>` | 종료 코드 |
| 완료표: 실제 + 대조군 | gate `complete/run_complete.sh` → `complete/table.py` | `complete/results/` |
| Prysm 시험 | gate `prysm-tests.sh` (종료 코드 = `prysm_tests_classify.py` 판정) | `prysm/tests/` |

## 5. Desc 검사기와 emit 경계

- 검사기(`desccheck/DescCheck.lean`)는 닫힌 세계다. 기대 열쇠 집합 = 검사기 표 9개 + 작업 트리의 `prysm/inventory.json`의 135개(sha256을 결과에 적는다). 생산기 출력에서 오지 않는다. 원본은 이 집합과 정확히 같아야 한다. 인벤토리 열쇠는 Prysm 패키지 둘 아래에만 있어야 한다(자체 검사).
- 검사기는 해석 전에 파일 크기(1 MiB)와 괄호 중첩 깊이(64)를 본다(`bounds`). 최상위 키 9개가 모두 있어야 한다(`required-keys`, `reference`는 null 가능). Prysm Desc는 인벤토리와 맞추고, 위임 container 필드(와 리스트·벡터 원소)는 피호출 타입의 인벤토리 항목과 재귀로 맞춘다. 예외 열쇠 둘(v1alpha1 `Checkpoint`, `AttestationData`)은 `Fv1.cpDesc`·`Fv1.adDesc`와 이름 빼고 같아야 한다(`exception-shape`).
- 결과는 JSON 파일 하나다(`fvphase1c.desccheck-result/1`, Lean JSON 인코더가 쓴다). 파일마다 경로, 내용의 sha256(EthLib SHA-256), 열쇠, 상태(SPEC/NONE), PASS/FAIL, 실패 검사가 있고 전체 `verdict`가 있다. 사람용 로그는 출력 가능한 ASCII 밖의 문자를 이스케이프한다.
- `gen1c/emit.py`는 이 결과 파일만 읽는다(로그를 읽지 않는다). 받는 조건: 결과가 strict JSON, `verdict` OK, 목록 수준 발견 없음, 인벤토리 sha256 = 작업 트리 파일 = 고정 목록의 핀(`THEOREMS.json` `sources_sha256`); 열쇠마다 original 기록 정확히 하나; 읽은 바이트의 sha256 = 그 기록; 모드에 맞는 상태(hand_case = 표 열쇠 + SPEC, prysm = 수작업 아닌 열쇠 + NONE + 고정 목록 행 있음). `--types`(pkg.Type)는 필수다. Desc는 한 번 읽고 그 바이트를 해시하고 해석한다. Desc 모양(최상위 키 9개, `fixed_size`는 자연수나 null)을 본다. 형식이 틀린 입력은 모두 `SystemExit`(거부)로 끝난다. 출력은 `<out>/<package의 /를 _로>/<Type>/`이고 같은 타입 이름 둘은 오류다. `--out`은 없거나 비어 있어야 한다(합치지 않는다).

위협 모델:
- 막는 것: 수작업 9타입의 생산기·IR 결함(명세 대조), 잘못 붙은·떠도는·빠진·중복된 Desc 파일, 유사 문자 이름, JSON 해석 차이(중복 키, 실수 표기), emit 경계의 낡은·섞인 결과 파일(sha256 결합, verdict, 인벤토리 해시).
- 막지 않는 것: 인벤토리와 맞는 Prysm 135타입의 틀린 모양(리스트 한도와 같은 바이트 수 안의 비트 길이는 인벤토리에 없다)(오프라인 독립 명세가 없다. 일관성만 본다), 손으로 위조한 결과 파일(서명이 없다), 일부러 틀리게 커밋한 인벤토리.
