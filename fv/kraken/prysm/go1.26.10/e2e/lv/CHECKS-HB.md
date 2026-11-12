# CHECKS-HB: HB의 남은 검사 (선언 drift, 부정 시험, HbLoop2 시간)

`REPORT-HB.md`에서 N이던 검사 셋이다. 독립 리뷰를 받지 않았다.

## 1. 선언 drift (X)

- 기준 `6a78c591`, 뿌리 E2e, E2eAd, E2eScal. T3의 `decl-drift-lv-t3.txt`와 같은 방법이다.
- 기준 덤프는 LV 작업의 기준 덤프를 다시 썼다(sha256 `96f2fb34…`). 다시 만들지 않았다.
- 머리 덤프: `decl_dump.lean`, 모듈 240개(E2eList, E2eHb 포함), exit 0, 83 s (로그 38).
- 결과: `SUMMARY base=5007 head=5007 drift=0 allowed=0` (로그 39). 파일 `decl-drift-hb.txt`.
- 대조군: 머리 덤프 사본의 형식 해시 하나를 바꿨다. exit 1, `drift=1` (로그 40).
- 이 대조군은 비교기만 시험한다. 덤프 생성기는 시험하지 않는다.
- E2eList는 뿌리에 없다. `git diff 1b5f524 --diff-filter=M`이 바뀐 기존 파일로 `lakefile.toml`만 보인다.

## 2. 부정 시험 (X)

- 사례 `negcases-hb.json`, 실행기 `gen/e2e/lvnegative.py`(바꾸지 않음). exit 0, 56 s (로그 41).
- 결과 `negative-hb.json`: 10개 중 10개 통과. control_pass 3, inside 7.

| 사례 | 종류 | 대상 정리 | 결과 |
| --- | --- | --- | --- |
| `hb-control-reject`, `-iter1`, `-accept` | 대조 | 거부, 한 바퀴, 수용 | control_pass |
| `hb-stmt-size524289` | 문장 크기 상수 | `hb_e2e_reject_size_main` | inside |
| `hb-size524289` | 코드 크기 상수 | `hb_e2e_reject_size_main` | inside |
| `hb-loopbound8191` | 루프 상한 | `hb_iter1` | inside |
| `hb-elem31` | 원소 크기(memmove 수) | `hb_iter1` | inside |
| `hb-shl6` | 원소 크기(색인 shift) | `hb_iter1` | inside |
| `hb-stmt-heap` | 수용 사후조건 힙 양 | `hb_e2e_accept_main` | inside |
| `hb-stmt-len8191` | 수용 사후조건 len 칸 | `hb_e2e_accept_main` | inside |

- 코드 변이는 그 지시어를 단계로 밟는 모듈에 겨눈다. 수용 모듈은 루프 정리를 가져오므로 코드 변이의 대상이 아니다.

## 3. HbLoop2가 HbLoop1보다 느린 원인 (X, 프로파일)

프로파일러(로그 42, 43)에서 HbLoop2의 13.4 s 중 12.9 s가 커널 형식 검사다.
그 시간은 `hb_iter2` 한 선언에 있다(로그 44: 그 정리만 남긴 사본에서 12.8 s).
elaboration, `simp`, 전술 실행 시간은 두 모듈이 비슷하다(약 0.7–0.9 s, 1.3 s).
배제한 후보: 레이블 조회(`klabel`, 색인 26–154에서 82–155 ms, 로그 48), 높은 색인의 `List.drop`(10 ms 미만, 로그 47), `k + 132 + 1 = k + 133`의 `rfl`(`omega`로 바꿔도 12.8 s, 로그 46).
원인: 원천 주소 식 `bf + (rax <<< 5) * 1 + 262144 = bf + 262144 + ofNat (32 * i)`를 닫는 `laddr`(omega) 증명이다.
그 식만 떼어낸 정리의 커널 검사가 12.2 s다. 상수 262144가 없는 같은 꼴은 15.6 ms다(로그 51).
`omega`가 만든 증명 항을 커널이 검사할 때 큰 상수에서 비용이 커지는 것으로 보인다. 그 안의 단계는 측정하지 않았다.
