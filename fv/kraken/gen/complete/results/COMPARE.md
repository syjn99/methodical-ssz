# P5: REPORT 2절 게이트 표의 재생성과 칸별 비교

입력은 해석된 Lean 선언뿐이다(`Complete.lean`, gate 로그 run `logs/24-complete.log`, 사본 `complete-log.txt`).
역할은 고정 목록(`gen/frozen/THEOREMS.json`)에서 온다. 증인은 "증명 항이 주 정리를 쓰고 타입에 `Host` 바인더가 없는 선언"이다.
계약은 등록부의 상수가 가설에 나타나는지로 본다. 함수 명세 계약은 그것을 결론으로 갖는 선언의 계약까지 전파한다.
재생성 표: `gate-table.md`. 수치와 칸: `gate-table.json`.

## 1. 수치

- 해석된 이름 60개(주 정리 55, 조합 3, `sc_spec_rejects_bool`, 부정 시험 지정 `fv_iter`). 모두 해석된다.
- 증인이 있는 이름 58개. 없는 둘: `bv_unmarshal_then_marshal`(REPORT도 "증인 없음"), `fv_iter`(주 정리 아님).
- 기계 비교 칸 54개: 같음 48, 다름 6. 비교하지 않은 칸 18개(증인 칸은 자유 문장, Go 값은 Lean에서 유도 불가).

## 2. 다른 칸과 원인

| 타입 | 칸 | 손 표 | 재생성 | 원인 |
| --- | --- | --- | --- | --- |
| ListC | 거부 경로 | 5/9 | 5/10 | Go 소스의 오류 반환은 10곳이다. 손 표는 원소 오프셋 초과(`totalVarBytes < endOffset`, 루프 안)를 세지 않았다. 손 표의 누락이다 |
| AttestationData | 거부 경로 | 1/1 | 1/3 | Go 소스에는 `Source`·`Target` 하위 오류 두 곳이 있다. 기계어에는 없다: P4 매니페스트에서 `"Source: %w"`, `"Target: %w"`를 디코더 기계어가 참조하지 않는다(인라인 후 도달 불가). 손 표는 기계어 기준, 고정 목록은 Go 소스 기준이다. 이 두 의무는 "기계어에서 도달 불가"를 보이는 형태가 필요하다(X4 결정 사항) |
| ListU64 | 추상 모델 | growslice 포함 | growslice 없음 | `GrowsliceC`는 `lum_grow_site`(별도 정리, 증인 `WitLuG`)의 가설이다. 주 정리 `lu_marshal_main`의 가설에는 없다. 재생성 규칙은 주 정리만 본다. 손 표가 더 넓다 |
| BitVec | 추상 모델 | fmt, newobject | + makeslice | `bv_accept_main`의 가설에 `MakesliceC`가 있다. 손 표의 누락이다 |
| Nested | 추상 모델 | newobject + 함수 명세 | + makeslice | `LuUAccC`를 결론으로 갖는 `lu_uacc_holds`가 `MakesliceC`를 가정한다. 함수 명세 아래 계약의 전파(REPORT 7절 4)다. 손 표는 전파하지 않았다 |
| BitVec | 수용 방향 | 양방향(1바이트) | EthLib→기계어(link `bv_unmarshal_accept_machine`) | 재생성 규칙은 EthLib 링크의 존재만 본다. "양방향"은 정리 문장을 읽어야 하는 주장이다. 기계 비교 밖 |

## 3. 한계

- 증인 칸(빈·1·최대)은 비교하지 않았다. 증인 선언 수만 낸다.
- 사후 칸은 크기 정리의 메모리 동일성만 기계 비교한다. 나머지 분류(정확, R + True, R 없음)는 표에 내지만 손 표와 문장 비교는 하지 않았다.
- 부정 시험은 `negative/RESULT`의 지정 이름을 해석해 잇는다. 이 세션은 부정 시험을 다시 돌리지 않았다(인용).
- 데이터 파일 칸: fix3의 데이터 include가 아직 승인되지 않았다. 지금은 include API가 대체할 손 상수(`blFmtB`, `luTW` 등)의 사용만 `data_consts`로 낸다.
