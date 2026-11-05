# 1b 재검사 (Claude Fable, 2026-11-05 13:46–13:55)

대상: ssz-fv-phase1b 4e37f2e (8f3faff + 53 커밋). 절차: REPORT-1b.md 14절.

## 재현 결과

| 검사 | 결과 |
| --- | --- |
| `lake clean` 뒤 `lake build` | 성공, 678 jobs, 13:46:14 → 13:49:40 (3분 26초), 최대 메모리 229 MB(time -l) |
| `tools/axioms.sh` | 종료 0. 생성한 AXIOMS.txt가 커밋본과 같음(598줄). `TOTAL 597 NONSTANDARD 0` |
| `sorry`/`admit`/`native_decide`/`bv_decide`/`axiom` 검색(Fk, Fv1) | Axioms.lean의 주석 한 줄만. `Fk/Bytes.lean`의 `bv_decide` 3곳은 사라짐(a813744) |
| `link/check.py` | PASS all. BUNDLE sha256 `1e921671…906c` = 보고서 |
| `link/check.py --selftest` | 기대대로 실패·통과 |
| `negative/run.sh` | 변이 3개 FAIL(지정 정리 안에서), 대조군 PASS = 보고서 |
| `go test ./fv/kraken/semtest/` | ok(cached) |
| `sszgen/`, `ssz/` 변경 | 없음(`git diff --stat 8f3faff..HEAD`) |

## 보고서와 다른 점

- 없음. 수치(정리 597, 명령어 2751, 번들 해시)가 모두 같다.

## 내가 더 본 것

1. **F2의 생성기 원인 확인.** `sszgen/render/marshal.go:349` `tmplGenerateMarshalValueList`가 `len({{.FieldName}}) > {{.MaxSize}}`를 쓴다. bitlist에서 FieldName은 바이트 배열이고 MaxSize는 비트 한도다. 생성된 `fv/kraken/target/types1b.ssz.go:338`이 `len(c.B) > 2048`이다. 생성기 버그 맞다. fastssz도 같은지는 확인 못 함.
2. **증인이 하나뿐.** `Fk/Witness.lean`의 `lu_accept_runs`만 전제 동시 만족을 증명한다. AttestationData 수용(계약 8개), BitL 수용(계약 3개, `ValidateBitlistC` 포함), Nested(함수 명세 2개), ListC(newobject + 함수 명세)는 증인이 없다. 계약 모양(`MakesliceC`, `MemmoveC`, `NewobjectC`)은 힙 조각을 `Heap avail`로 따로 두고 프레임 `F`와 서로소로 만들어서 평가 세션의 모순은 피했다. 그래도 동시 만족은 증명이 아니라 판단이다. astra에 전수 검사를 요청했다(항목 1).
3. **`MemmoveC`는 r14 보존을 말하지 않는다.** `MakesliceC`, `NewobjectC`는 r14를 돌려준다. memmove 뒤에 r14(Go g 포인터)를 쓰는 경로가 있으면 전제가 부족하다. AttestationData 정리가 어떻게 넘겼는지 astra 검토 대상.
4. **이견 8(Prysm 배치).** 정리는 Prysm 바이너리의 기계어가 아니다. 보고서 판정 문장 "Prysm 2타입"에는 이 단서가 없다. 판정 절(0절)에 넣어야 한다.
5. **하드웨어 대조 미실행.** 조건 C15, B4는 x86-64 Linux 기계가 있어야 한다. 이번에도 arm64 호스트라 스크립트만 있다.

## 판정(재검사 기준)

재현 가능. 보고서 수치는 정확하다. 게이트 1 "조건부"에 동의하되, 증인 부재(2)와 Prysm 배치 단서(4)를 조건에 더한다. astra 결과를 기다린다.

## 추가 (14:35, astra 리뷰 뒤)

astra 판정: 조건부, 게이트 1 미통과. 필수 수정 12개. 내가 확인한 것:

1. **발견 1(P0, `GrowsliceC` 모순) 재현.** `Review1b.lean`을 1b 빌드 위에서 `lake env lean`으로 돌렸다. 3.7초. `growslice_false`, `bl_accept_main_preconditions_false`, `bl_unmarshal_accept_spec_k_preconditions_false`, `lum_grow_site_preconditions_false` 모두 표준 공리 3개만 쓴다. `Fk/BlAccept.lean:85`가 `GrowsliceC`를 가설로 받는다. BitL 수용 정리 2개와 growslice 지점 정리 1개는 공허하다. 내 재검사(위)는 이것을 놓쳤다. 계약 하나하나의 모순 가능성을 Lean으로 시험하지 않고 모양만 봤기 때문이다. 평가 세션 때와 같은 실수다.
2. **발견 2(P1, `fmt.errorf`) 확인.** Go 1.26.3 `src/fmt/errors.go`: 내부 `errorf`는 인수가 없고 `%`가 없으면 nil을 돌려주고, 공개 `Errorf`가 `errors.New`를 부른다. `FmtErrorfC`는 항상 `rax ≠ 0`을 요구하므로 ListC 거부 3경로(`zero`, `past`, `tail`)는 실제 분기를 증명하지 않는다.
3. **발견 3(P1, 링크 검사) 확인.** `link/check.py:299`: 원본 명령어가 `conv.NORM`(nop 정규화 목록)에 있으면 새 바이트를 디코딩하지 않고 `padding`으로 기록한다. nop 자리를 `retq`로 바꿔도 PASS다. 원본에 그런 변이는 없지만 검사가 그것을 막지 못한다.
4. 발견 4(증인 부재, 결론에서 프레임·r14 누락)는 내 재검사 2·3항과 같다. astra가 정리별 표로 넓혔다.
5. fastssz v1.0.0도 bitlist 한도를 바이트 길이에 적용한다(astra 코드 확인, 실행 시험 없음). F2는 fastssz 유래 버그일 가능성이 있다.

판정 변경: 게이트 1 **미통과**에 동의한다. 세션 자평 "조건부 통과"는 철회해야 한다. 다만 BitL 수용과 growslice 지점을 뺀 나머지 정리(ListU64, FixedVec, BitVec, Nested, ListC, Checkpoint, AttestationData의 수용·마샬·크기·거부)에서는 모순을 찾지 못했다. 증인이 없을 뿐이다. Kraken 접근은 유지한다.
