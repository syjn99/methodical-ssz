# 1b-fix 재검사 (Claude Fable, 2026-11-05 20:56–21:15)

대상: ssz-fv-phase1b-fix 694f129 (32c0bdc + 12 커밋). 세션 in-review 17:59(감시기가 상태 필드 이름을 잘못 봐서 20:56에 알았다).

## 재현 결과

| 검사 | 결과 |
| --- | --- |
| `lake clean` 뒤 `lake build` | 성공, 20:56:49 → 21:00:15 (3분 26초) |
| `tools/axioms.sh` | 종료 0. AXIOMS.txt 커밋본과 같음(755줄). `TOTAL 754 NONSTANDARD 0` |
| 금지 전술·선언 검색(Fk, Fv1) | 없음(Axioms.lean 주석만) |
| `link/check.py` | PASS all, 검사 (a)–(g). 번들 `b71c1c11…b7c3` = 보고서 |
| `--selftest` | 9개 기대대로(새 사례: all.S 불일치, SHash 오래됨 포함) |
| `negative/run.sh` | 7개 기대대로(offset, maxlen, loop, gsnum, nilerr FAIL, control PASS, nopret 링크 FAIL). 종료 코드가 결과 줄에 찍힘 |
| `go test ./fv/kraken/semtest/` | ok |
| `review/Review1b.lean` 회귀 | 오류 5개로 정교화 실패(새 계약 서명). `review1b_input_excluded`가 `newLen = 2^63` 입력이 새 전제(힙 예산 ≤ maxAlloc)에 걸림을 증명 |

## 계약 일관성 (지난번에 빠뜨린 검사)

모순 시도 대신, 세션이 둔 모델 정리의 결론 형태를 확인했다. 각 모델 정리는 구체 Host에서 계약 그 자체를 결론으로 가진다(모든 `S`에서):
- `rt_growslice : GrowsliceC bumpHeap ty 1 S` (Fk/RtCopy.lean)
- `rt_errorf_nil : FmtErrorfNilC S`, `rt_errorf : FmtErrorfC Heap S` (Fk/RtErr.lean)
- `rt_memmove : MemmoveC S` (Fk/RtCopy.lean)
- `bump_makeslice1 : MakesliceC bumpHeap ty 1 S`, `bump_newobject24 : NewobjectC bumpHeap ty 24 S` (Fk/BumpMore.lean)

계약을 만족하는 구현이 있으므로 계약은 모순이 아니다. 주 정리 전제의 동시 만족은 증인 정리가 보인다. `ad_accept_runs`(WitAd), `ne_accept_runs`(WitNe0/1/16), `cp_marshal_runs`(WitCpM), `fv_accept_runs`, `bv_accept_runs`, `lu_accept_runs`가 각각 해당 주 정리 이름을 실제로 참조한다(grep). 증인이 주 정리의 전제를 약화된 사본이 아니라 그대로 쓰는지는 astra 항목 2에 맡겼다.

`rt_growslice`는 `esz = 1`만 다룬다. ListU64 마샬의 growslice 지점(`esz = 8`)은 `growslice_call_runs`가 따로 있다(n = 1, 257). 확인했다.

## 보고서와 다른 점

없음. 수치가 모두 같다.

## 판정(재검사 기준)

세션 자평 "조건부, 게이트 1 미통과"에 동의한다. 리뷰의 P0·P1 세 가지는 고쳐졌다. 남은 것은 세션이 표(9.3, 13절)에 정직하게 적었다: BitL·ListC 수용 증인, 인코더·거부 정리 증인, 스택 조각 보존. 1c 설계 입력 5개(10.2절)는 타당해 보이며, 특히 "기호 길이 대신 고정 길이 증인"은 측정에 근거한다.

## 추가 (21:45, astra 리뷰 뒤)

astra 판정: 조건부, 게이트 1 미통과(세션 자평과 같음). 새 False 도출 없음. 내가 확인한 것:

1. **발견 1(P1, B0 스택 좌표) 재현.** `Review1bFixB0.lean`을 vcgen 툴체인으로 돌렸다(4초, 표준 공리). `funspec … at s`의 `s`는 호출 전 상태이고 `push64`가 rsp를 8 줄이므로, 첫 저장 `mov %rbx,0x10(%rsp)`의 목적지는 호출 전 `rsp + 8`이다. 1b-fix가 쓴 `rsp + 16`은 틀렸다. astra는 자신의 1b 리뷰 권고(+16)도 철회했다. 결론 "vcgen은 main에 남는다"는 유지되지만 수치(14/16)는 다시 재야 한다.
2. **발견 2(P2, SHash 검사 우회) 확인.** `link/check.py:273`이 `SHash.lean` 파일 전체에서 정규식으로 해시를 모은다. 주석에 해시를 두고 `Fk.sHash := []`로 바꿔도 통과한다. 실제 정의 값을 읽도록 고쳐야 한다.
3. **astra가 더 강하게 확인한 것.** 계약 7개(Makeslice, Memmove, Growslice, Newobject 32, FmtErrorfNil, FmtErrorf, ConvT64)를 한 Host에서 동시에 만족하는 정리를 만들었다(`Review1bFix.lean`, 표준 공리). 증인 10개가 주 정리를 약화 없이 직접 적용함을 표로 확인했다. AttestationData 수용의 계약 3종 8호출 공동 만족을 인정했다. `nextSliceCap` 세 분기가 Go 1.26.3과 맞음을 확인했다.
4. **남은 신뢰 항목(발견 3·4).** 런타임 모델은 계약이 모순이 아님을 보이는 것이지 Go 구현의 정교화가 아니다. `FmtErrorfC`·`ConvT64C`의 인수 유효성·boxed 값·정상 종료는 형식 전제에 없다. 스택 조각·입력·수신자 그래프를 결론에서 돌려주지 않아 후속 호출 조합이 막힌다. `NewobjectC 16` 모델과 ListC 오류 경로 증인, `lum_grow_site` 증인, BitL 모델이 없다.
5. 문서 정정(발견 5): CONTRACTS.md의 오래된 "모델 없음" 행, 9.3절의 `bv_marshal_main` 누락, "주 정리 10개"는 고유 이름 8개 + 실행 증인 선언 10개.

판정: 세션 자평과 astra 판정에 동의한다. 조건부, 게이트 1 미통과. 1b 리뷰의 P0·P1은 해결됐고, 남은 것은 범위(증인·결론 보존)와 신뢰 항목의 구체화다. astra 필수 수정 1·2·6·7(정리)과 3·4·5(게이트 1 잔여)는 생성기 수정 뒤 재증명 세션 브리프에 넣는다.
