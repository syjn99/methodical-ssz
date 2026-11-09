# P5: REPORT 2절 게이트 표의 재생성과 칸별 비교

입력은 해석된 Lean 선언뿐이다(`Complete.lean`, `run_complete.sh`; 마지막 실행: fix3 FINAL(`93b63cd`) 위 rebase 뒤 run `logs/84`(retest-93b63cd의 complete 단계), 사본 `complete-log.txt`).
역할은 고정 목록(`gen/frozen/THEOREMS.json`)에서 온다. 증인은 "증명 항이 주 정리를 쓰고, 타입에 `Host` 바인더가 없고, 구체 `Host` 인스턴스를 쓰는 선언"이다(3절).
계약은 등록부의 상수가 가설에 나타나는지로 본다. 함수 명세 계약은 그것을 결론으로 갖는 선언의 계약까지 전파한다.
재생성 표: `gate-table.md`. 수치와 칸: `gate-table.json`.

## 1. 수치

- 해석된 이름 68개(rebase 전 65). 더한 셋: `lc_reject_offset_order_main`(fix3 새 주 정리, ListC r8), `sc_reject_bool_err`(fix3, Scalars bool 거부의 오류 값 정리), `lcl_order`(fix3 부정 시험 `lcorder`의 지정 이름). 모두 해석된다. 환경의 `*_main` 56 = 입력 56(전 55).
- 증인이 있는 이름 59개(전 58). `lc_reject_offset_order_main`(`WitLcO`)과 `sc_reject_bool_err`(`WitScRB`)가 더해졌다. `sc_reject_bool_main`은 직접 증인을 잃었다(아래 2절).
- 기계 비교 칸 54개: 같음 48, 다름 6(전과 같은 수, 다른 칸 구성은 바뀜). 비교하지 않은 칸 18개.
- 데이터 상수: fix3 `Fk.Data`의 항목을 환경에서 읽는다(`<id>`, `<id>_addr`; 38개) + `StaticBox` = 39(`COMPLETE-DATA 39`). 손 목록은 없앴다(`luTW`는 fix3에서 `intType_addr`로 바뀌어 없어졌다).
- 부정 시험: 변이가 명령을 바꾸지 않는 사례(`'X' -> 'X'`)는 대조군이다. 부정 시험으로 세지 않는다(`control`, `lcorderctl`).

## 1b. fix3 FINAL 뒤 (rebase 2)

- 해석된 이름 68 → 71(`lc_reject_item_main`, `lu_reject_short_frame`, `lcl_itemerr`), 증인 있음 59 → 60, 환경 `*_main` 56 → 57, 데이터 상수 39 → 41(`lcFmtItems`, `lcFmtItems_addr`).
- 비교 54칸: 같음 48 → 47, 다름 6 → 7. 새 차이 하나: ListU64 거부 경로 손 4/4, 재생성 3/4. `lu_reject_short_frame`(fix3 새 정리)이 r1 행에 대응되었는데 직접 증인이 없다(함수 명세 `lu_urej_short_holds`가 쓴다). 재생성 규칙(행의 정리마다 직접 증인)은 이것을 닫힘으로 세지 않는다. Scalars의 `sc_reject_bool_err`와 같은 꼴이다.
- ListC: 거부 경로 6/10 → 7/10(`lc_reject_item_main`, 증인 `WitLcI`), 손 표도 7/10으로 같다. 부정 시험 규칙을 고쳤다: 대조군은 RESULT의 PASS 행이다(`lcitemsctl`의 변이 `$0x9` → `$9`는 같은 값의 다른 철자라 앞의 "같은 글자" 규칙이 놓쳤다). 그래서 ListC 부정 시험은 같음이다.

## 2. 다른 칸과 원인

| 타입 | 칸 | 손 표 | 재생성 | 원인 |
| --- | --- | --- | --- | --- |
| ListU64 | 거부 경로 | 4/4 | 3/4 | rebase 2 뒤 새 차이. `lu_reject_short_frame`에 직접 증인이 없다(1b절) |
| Scalars | 거부 경로 | 2/2 | 1/2 | rebase 뒤 새 차이. fix3에서 `WitScRB`의 `sc_reject_bool_runs`가 `sc_reject_bool_err`를 쓴다. `sc_reject_bool_main`은 `sc_reject_bool_err`의 증명 안에서만 쓰이고 직접 증인이 없다. 재생성 규칙(행의 정리마다 직접 증인)은 이것을 닫힘으로 세지 않는다. `err`의 가설이 `main`의 가설을 포함하는지는 기계로 보지 않았다 |
| FixedVec | 부정 시험 | control, loop | loop | 규칙: 대조군(RESULT의 PASS 행; `control`)은 부정 시험이 아니다. 손 표는 그것을 부정 시험으로 적는다(ListC의 `lcorderctl`은 적지 않는다) |
| AttestationData | 거부 경로 | 1/1 | 1/3 | Go 소스에는 `Source`·`Target` 하위 오류 두 곳이 있다. 기계어에는 없다: P4 매니페스트에서 `"Source: %w"`, `"Target: %w"`를 디코더 기계어가 참조하지 않는다(인라인 후 도달 불가). 손 표는 기계어 기준, 고정 목록은 Go 소스 기준이다. 이 두 의무는 "기계어에서 도달 불가"를 보이는 형태가 필요하다(X4 결정 사항) |
| ListU64 | 추상 모델 | growslice 포함 | growslice 없음 | `GrowsliceC`는 `lum_grow_site`(별도 정리, 증인 `WitLuG`)의 가설이다. 주 정리 `lu_marshal_main`의 가설에는 없다. 재생성 규칙은 주 정리만 본다. 손 표가 더 넓다 |
| Nested | 추상 모델 | newobject + 함수 명세 | + makeslice | `LuUAccC`를 결론으로 갖는 `lu_uacc_holds`가 `MakesliceC`를 가정한다. 함수 명세 아래 계약의 전파(REPORT 7절 4)다. 손 표는 전파하지 않았다 |
| BitVec | 수용 방향 | 양방향(1바이트) | EthLib→기계어(link `bv_unmarshal_accept_machine`) | 재생성 규칙은 EthLib 링크의 존재만 본다. "양방향"은 정리 문장을 읽어야 하는 주장이다. 기계 비교 밖 |

rebase 전에 다르던 두 칸은 이제 같다: ListC 거부 경로(fix3가 손 표를 6/10으로 고쳤고 재생성도 6/10), BitVec 추상 모델(fix3가 손 표에 makeslice를 더했다; OUTBOX 002에서 알린 두 칸).

## 3. 한계

- 주 정리 목록의 교차 검사: `Complete.lean`이 Fk 모듈의 `*_main` 정리를 환경에서 세어 입력과 비교한다. 다르면 실패한다.
  run `logs/27`, `logs/35`, rebase 뒤 `logs/54`(`run_complete.sh`: 실제 rc 0이고 대조군 rc가 0이 아닐 때만 gate 종료 코드 0): 환경 56 = 입력 56. 대조군(입력에서 `cp_size_main`을 뺌)은 오류로 끝난다(`mains-check-log.txt`).
- 계약 등록부는 고정 14개다(`Complete.lean` `registry`). 등록부에 없는 새 계약은 표에 나타나지 않는다. "같음 48칸"은 이 등록부와 키워드 대응(`table.py`) 수준의 비교다.
- 증인 규칙: 증명 항이 주 정리를 쓰고, 타입에 `Host` 바인더가 없고, 구체 `Host` 인스턴스를 쓰는 선언(리뷰 뒤 마지막 조건을 더했다. 명세 수준 보조정리 `Fv1.lu_spec_rejects`가 증인으로 잘못 세어졌다).
- 입력 65개 = 앞의 60 + `*_spec_accepts_iff` 다섯(고정 목록 `reject_complete`의 부분 대응). 앞의 60줄은 바뀌지 않았다.

- 증인 칸(빈·1·최대)은 비교하지 않았다. 증인 선언 수만 낸다.
- 사후 칸은 크기 정리의 메모리 동일성만 기계 비교한다. 나머지 분류(정확, R + True, R 없음)는 표에 내지만 손 표와 문장 비교는 하지 않았다.
- 부정 시험은 `negative/RESULT`의 지정 이름을 해석해 잇는다. 이 세션은 부정 시험을 다시 돌리지 않았다(인용).
- 데이터 파일 칸: fix3 stage A가 승인됐다. `data_consts`는 `Fk.Data` 항목의 사용이다. 데이터 파일과 `Fk.Data`의 대응은 `gen/gen1c/test_include.py`가 본다(`results/include-check.json`).
