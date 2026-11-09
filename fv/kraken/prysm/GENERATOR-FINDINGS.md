# GENERATOR-FINDINGS: 생성기 698c202와 Prysm ab15ff70 (phase1c)

생성기는 고치지 않았다. 재현 입력만 적는다. 상류 PR은 사용자가 만든다.
목록은 넷이다. 섞지 않는다.

## 1. 새 생성기 결함

### D1. IR에서 중첩 container의 필드 키가 필드 이름이 아니라 container 이름이다

- 위치: `sszgen/representer.go` `FieldParser.expand`의 `case *types.Struct:` 분기. `container.Append(f.name, rep)`.
  `f.name`은 바깥 정의의 이름(예: `Checkpoint`)이다. 필드 이름은 `field.Name()`이다.
  위쪽 최상위 경로(`ParseTypeDef`)는 `f.name`이 필드 이름이라 맞다. 중첩 경로만 틀리다.
- 최소 재현(gate 로그 `logs/09-repro-ir-keys.log`, 출력 사본 run 디렉터리 `artifacts/repro-ir-attestationdata.go.txt`):

  ```sh
  # methodical-ssz 워크트리 루트, Go 1.26.10
  ssz-698c202 ir --output=/tmp/ir.go --type-names=AttestationData \
      github.com/OffchainLabs/methodical-ssz/fv/kraken/target/prysm
  ```

  기대: `Source`의 `Checkpoint` 필드 키가 `Epoch`, `Root`.
  실제: `{Key: "Checkpoint", Value: &types.ValueOverlay{Name: "Epoch", ...}}, {Key: "Checkpoint", Value: &types.ValueVector{Size: 32, ...}}`.
- 영향: 이번 출력 코드에는 영향이 없다(관찰). 렌더러는 중첩 container를 항상 그 타입의 메서드 호출로 위임한다(`render/marshal.go` `marshalOp.Container`, `render/unmarshal.go` `unmarshalOp.Container`).
  영향을 받는 것: `ssz ir` 출력, `testutil.RenderIntermediate`, IR을 읽는 도구(예: 1c의 `Desc` 생성기).
  1c 도구는 위임 필드 아래를 자르므로(`gen/inventory.py reduce`) 이 키를 쓰지 않는다.
- 판정: 결함(IR 한정). 출력 코드 결함이 아니다. 심각도 낮음(추측 아님: Fulu 출력 diff 232블록이 모두 알려진 커밋 셋으로 설명된다).

### 관찰(결함으로 세지 않음)

- O1. 로그의 `Generating methods for /StatusV2`처럼 패키지 이름이 비어 있다(`logs/03-prysm-gen.log`).
  `sszgen/importer.go`의 `packages.Config.Mode`에 `NeedName`이 없어서 `PkgPath`가 빈 문자열이다(소스 읽기로 본 원인).
  출력 파일은 스모크 실행과 바이트가 같다. 출력에 영향이 없다.
- O2. 손 작성 위임: Prysm `consensus-types/primitives`의 `Slot`, `Epoch`, `ValidatorIndex`, `Gwei`, `CommitteeIndex`는 SSZ 메서드를 손으로 작성했다.
  생성 코드는 이 필드를 그 메서드로 위임한다(예: `StatusV2.MarshalSSZTo`의 `c.FinalizedEpoch.MarshalSSZTo(dst)`).
  `Slot.MarshalSSZTo`는 새 슬라이스를 만든 뒤 `append`한다. `UnmarshalSSZ` 오류는 `fmt.Errorf("%d")`다.
  생성기 동작은 설계대로다. 그러나 1c 증명은 생성되지 않은 Go 코드 5개 타입(함수 24개)의 명세가 필요하다(`TYPES.md` 5절).
  기존 축약 Prysm 타입(`fv/kraken/target/prysm`)은 메서드 없는 지역 `Slot`을 써서 이 경로가 없다.

## 2. 생성기 변경 호환성: 오류 문구 시험 회귀 셋 (인용)

출처: `/workspace/agent-runs/prysm-fv-pin-smoke/REPORT.md` 6절, 재현 `repro/partsmetadata-bitlist-limit.sh`, 로그 `logs/63`(새 출력), `logs/70`(기준선).

- `consensus-types/blocks`: `TestMarshalPartsMetadata/available_too_large`, `/requests_too_large`, `TestPartialDataColumn_PartsMetadata/marshal_error_due_max_bitlist_size`.
- 원인: `280b752`. 인코더가 Bitlist를 바이트 길이가 아니라 `ssz.ValidateBitlist(x, 4096)`(비트)로 검사한다. 너무 큰 입력은 여전히 거부된다. 오류 문구만 시험 기대와 다르다.
- 분류: 생성기 결함이 아니다. 생성기 변경의 호환성 문제다. 시험은 약화하지 않았고 고치지 않았다.
- 이 세션의 재실행: 문서 끝 "재실행 결과"를 본다.

## 3. minimal 태그의 기준선 실패 (인용, 2절과 별개)

출처: 스모크 REPORT 6절, 로그 `logs/64`·`71`, `logs/66`·`73`.

- `consensus-types/blocks` `-tags minimal`: 시험 파일 컴파일 실패. 커밋된 파일(기준선)에서도 같다.
- `encoding/ssz/detect` `-tags minimal`: `TestByState` panic. 기준선에서도 같다.
- 생성 코드와 무관하다. 새 출력이 있든 없든 같다.

## 4. 생성기 밖의 도구 빈틈 (Kraken·변환기 요청 후보)

- K1. `%riz`: GNU objdump는 `%r12` 기준 주소의 SIB 바이트를 `0x10(%r12,%riz,1)`로 적는다. Kraken 런타임 파서는 `unknown register: riz`로 거부한다.
  I의 생성 함수 13개가 이 때문에 파싱되지 않는다(`go1.26.10/kparse.json`). `%riz`를 지운 진단 사본은 모두 파싱된다(`go1.26.10/kparse-riz-diag.json`).
  주소는 `(%r12)`와 같다. 처리 위치는 `link/conv.py`의 정규화 또는 Kraken 파서다. 둘 다 이 스트림의 경로가 아니다. 제안은 run 디렉터리 `OUTBOX.md`에 있다.
- K2. `bsr`: `ssz.ValidateBitlist`에만 있다(기존 Kraken 요청과 같다).

## 재실행 결과

이 세션은 8개 설정(phase0..fulu, engine)을 다시 생성한 트리에서 스모크와 같은 시험 명령을 돌렸다.
스모크는 fulu 두 파일만 바꿨다. 그래서 다시 돌렸다. 원본은 `tests/prysm-tests.json`, 로그 사본은 `tests/prysm-tests-1{0,1}-log.txt`다.

| 패키지 | 프리셋 | 결과 |
| --- | --- | --- |
| `proto/prysm/v1alpha1` (`-run 'Fulu\|PartialDataColumns'`) | mainnet, minimal | 통과 |
| `consensus-types/blocks` (스모크 `-run`) | mainnet | 실패: 2절의 하위 시험 3개 |
| `consensus-types/blocks` (스모크 `-run`) | minimal | 시험 빌드 실패(3절과 같다) |
| `encoding/ssz/detect` (스모크 `-run`) | mainnet | 통과 |
| `encoding/ssz/detect` (스모크 `-run`) | minimal | `TestByState` panic(3절과 같다) |
| 네 패키지 전체(`-run` 없음) | mainnet | `v1alpha1`, `engine/v1`, `detect` 통과. `blocks`는 2절의 3개만 실패 |

- 실패한 하위 시험은 2절의 셋뿐이다. 새 실패는 0개다(`failed_subtests_not_in_smoke_known_3` = []).
- 첫 전체 실행(`logs/10`)은 내 스크립트의 `head`가 출력을 잘라 rc 141이었다. `logs/11`이 그것을 대체한다.
- 이 세션은 기준선(커밋된 파일)을 다시 돌리지 않았다. 3절의 "기준선에서도 같다"는 인용이다.
- spec `ssz_static` 시험, Bazel 시험, 다른 Prysm 패키지는 돌리지 않았다.
- 리뷰 phase1c-r1 S7: 위 실행은 `go test -p 2`였다. 규칙은 `-p 1`이다. `gen/prysm-tests.sh`(`-p 1`, `set -o pipefail`, 출력 전체 보관)로 같은 7개 명령을 다시 돌렸다(run `logs/28`). 결과가 같다: 실패한 하위 시험은 2절의 셋뿐이고 minimal 실패 둘도 같다. 원본 `tests/prysm-tests-p1.json`, 요약 `tests/prysm-tests-p1-summary.txt`. 이것이 위 표의 근거를 대체한다.
- 리뷰 phase1c-r2 N4: `gen/prysm-tests.sh`의 종료 코드는 이제 커밋된 분류기 `gen/prysm_tests_classify.py`의 판정이다(알려진 실패만이면 0). 분류기를 `logs/28`의 출력에 적용했다: 판정 "only known failures", 예상 밖 0(`tests/prysm-tests-p1-classified.json`). 알려지지 않은 실패를 넣은 대조군은 1로 끝난다. Prysm 시험 자체는 다시 돌리지 않았다(출력 7개는 `logs/28`의 것).
