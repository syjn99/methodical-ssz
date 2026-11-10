# 생성기 변경 기록 (홀드아웃 오염 기록)

이 파일은 `gen/scal/scalgen.py`의 변경을 적는다.
변경마다 홀드아웃을 연 전인지 후인지 적는다.
홀드아웃 형은 `HOLDOUT-MARKER.json`에 있다.

## 1. p2dec 문장 동일성 (감사 AU-08) — 홀드아웃을 열기 전

- 시점: 2026-11-10, 커밋 `4581b8f`. `scal/HOLDOUT-OPENED`는 없다. S3는 시작하지 않았다.
- 변경 전: p2dec는 문장을 고정 텍스트로 냈다. 증명은 `rootdec_seg`에 모든 인수를 넘겼다. 그래서 문장에 거짓 전제를 더해도 빌드되었다(감사의 M1 변이, 종료 0).
- 변경 후: 코드 전제 `k`, `hk`, `hf`만 콜론 앞에 둔다. 나머지는 콜론 뒤의 `∀ …, …` 하나다. 증명은 `exact E2eScal.rootdec_seg … hA hB hl`이고 뒤에 인수가 없다.
- 이 변경이 검사하는 것: 콜론 뒤의 문장과 보조정리 인스턴스의 형이 정의상 같은지다.
- 정정(리뷰 fix-r1 M2): 콜론 앞에 더한 전제는 이 변경으로 잡히지 않는다. 증명이 그 전제를 쓰지 않으면 빌드된다(`rv-gad-extra-before`, 오류 없음). 이 절의 이전 문장 "커널이 문장과 보조정리 인스턴스의 형을 검사한다"는 그만큼 틀렸다. 2절이 고친다.
- 같은 명제: 선언 덤프에서 두 생성 정리의 형 해시가 바뀌지 않았다(gate 작업 254와 260, `decl_drift` 변동 0). 해시는 구조 해시이고 묶음 이름을 보지 않는다.
- 입력: 개발 집합만 썼다. AttestationData와 Checkpoint 디코더의 `.S`, 그 두 형의 IR 항목이다.
- 다시 만든 파일: `lean/E2eScal/GenAdDec.lean`, `lean/E2eScal/GenCpDec.lean`. `regen_check.sh` 결과는 SAME이다.
- 부정 시험: `scal-gad-stmt-extra`, `scal-gcp-stmt-extra`(거짓 전제 `(1 : Nat) = 2`를 더함)가 정리 안에서 실패한다(작업 258, 259).

## 2. 전체 문장의 종류 검사 (리뷰 fix-r1 M2, S1, S2) — 홀드아웃을 열기 전

- 시점: 2026-11-10, 커밋 `094e51e`. `scal/HOLDOUT-OPENED`는 없다. S3는 시작하지 않았다. 홀드아웃 파일은 열지 않았다.
- 문제: 1절의 검사는 콜론 뒤만 본다. p1 모드는 `--same-as` 손 정리가 없으면 문장 검사가 없다. 홀드아웃 형에는 손 정리가 없다.
- 새 손 모듈 `lean/E2eScal/Kind.lean`: 고정된 문장 종류 `u64DecAcceptKind C`, `rootDecSegKind C j1 j2 dR dB dS fP fL fC src`(`abbrev`).
- `u64DecAcceptKind_of`, `rootDecSegKind_of`는 각 종류를 보조정리 `u64dec_accept`, `rootdec_seg`에서 증명한다. 그래서 종류의 본문은 보조정리 결론과 커널에서 맞춰진다.
- `lean/E2eScal/KindAnchor.lean`: `sl_kind_anchor`, `ci_kind_anchor`. P1 종류가 검토된 손 정리 `E2eAd.sl_unmarshal_accept_main`, `E2eAd.ci_unmarshal_accept_main`의 선언 형 전체와 같다.
- 생성기 변경: 생성 정리 `t`마다 바로 뒤에 `t_kind : ∀ (h : Host), type_of% (@t h) = <종류> …`를 낸다. 증명은 `with_reducible rfl`이다.
- `@t h`의 형은 콜론 앞과 뒤의 묶음을 모두 포함한다. 그래서 어느 자리에 전제를 더하거나 빼거나 바꿔도 `t_kind`가 실패한다. 손 정리가 필요 없다.
- 이 검사가 보지 않는 것: 종류에 넘긴 매개변수(지시 번호, 변위, 오프셋)가 그 Go 형에 맞는지다. 맞지 않으면 증명의 코드 사실이 성립하지 않아 빌드가 실패한다. 이것은 증명의 성질이고 `t_kind`의 성질이 아니다.
- 생성 증명의 마지막 줄은 `with_reducible exact …`다. 결론의 상수가 틀리면 `Int.toBytes`를 펼치지 않고 바로 실패한다(S2: 이전 300초 벽시계 초과, 지금 1.4초).
- `gen/e2e/negative.py`: 정리 바로 뒤의 `theorem <t>_kind`를 변이 파일과 사례 범위에 넣는다.
- 입력: 개발 집합만 썼다. 1절과 같은 `.S` 세 개와 IR 항목 두 개다.
- 다시 만든 파일: `GenCi.lean`, `GenAdDec.lean`, `GenCpDec.lean`. `regen_check.sh` 세 번 모두 SAME이다(gate 작업 294). 생성 정리의 형 해시는 바뀌지 않았다. 선언 변동은 새 선언 11개뿐이다(`allow-fixr1.txt`, 작업 293).
- 부정 시험(사례 묶음마다 gate 작업 하나, 작업 288–291): 콜론 앞 전제 추가 `scal-gad-stmt-extra-before`, `scal-gcp-stmt-extra-before`, `scal-gci-stmt-extra-before`, 맨 앞 추가 `scal-gad-stmt-extra-first`, `scal-gci-stmt-extra-first`, 전제 삭제 `scal-gad-stmt-drop`, 결론 상수 `scal-gad-stmt-literal`, 종류 인수 `scal-gad-kind-arg`. 모두 사례 범위 안에서 실패한다.
- 콜론 앞 추가 변이 다섯 개의 오류는 모두 `_kind` 줄에만 있다. 정리 자체는 그 변이로도 빌드된다. 그래서 이 검사가 그 변이를 잡는 유일한 장치다.
- 결과 파일 `negative-result.json`: 28/28(대조 6, 정리 안 실패 22).

## 3. 평가 세션의 0단계 (리뷰 fix-r2 N1, N2, N3) — 홀드아웃을 열기 전

- 시점: 2026-11-10, 평가 세션. `scal/HOLDOUT-OPENED`는 아직 없다. 홀드아웃 파일은 열지 않았다.
- 방법 고정: 커밋 `56dfc27`, `Kind.lean` 블롭 `3c9b95b1…`, `scalgen.py` 블롭 `78e3339b…`.
- 이 단계는 생성기, 보조정리, 종류를 바꾸지 않는다.
- N1: `gen/e2e/negative.py`가 첫 오류 `Unknown option`, `Case tag … not found`를 `wrong_target`으로 분류한다. 목록은 완전하지 않다.
- N2: `gen/scal/kindcheck.py`는 읽는 쪽의 검사다. 생성 정리마다 `_kind` 줄의 우변이 고정 종류인지 본문으로 검사한다.
- N2 한계: `_kind` 줄은 생성기 출력이다. 퇴화한 우변도 Lean에서 빌드된다. 그래서 이 검사가 필요하다.
- N2 한계: 종류 매개변수가 Go 형에 맞는지는 보지 않는다. 그것은 증명의 코드 사실로만 검사된다.
- N3(a): 실패한 빌드 뒤에는 다음 통과를 믿기 전에 `stale_olean.py`를 돌린다.

## 4. 홀드아웃 H1 평가 (열린 뒤) — 평가 세션

- 연 시각: 2026-11-10T17:53:24Z (`scal/HOLDOUT-OPENED`, 커밋 `fc8749c`).
- 생성기, 보조정리, 종류는 바꾸지 않았다. `kindcheck.py`는 `Kind.lean` 블롭이 고정값임을 확인했다.
- 생성기는 형마다 한 번 돌렸다. ValidatorIndex `p1`(작업 299), BeaconBlockHeader `p2dec`(작업 312).
- 날것 출력 `GenVi.lean`, `GenBhDec.lean`은 고치지 않고 커밋했다. 손 수정은 0줄이다. 둘 다 그대로 빌드되었다.
- 열린 뒤에 더한 손 파일: `BhCode`, `ViSpec`, `WitVi`, `BhHead`, `BhAccept`, `BhReject`, `BhSpec`, `BhSpecK`, `WitBhA`, `WitBhR`.
- 이 손 파일은 대부분 개발 집합 손 증명의 글을 고친 것이다(`AdHead`, `AdReject`, `AdSpecK`, `WitAdA`, `WitAdR`, `Spec`, `WitCi`).
- 열린 뒤에 더한 도구: `gen/e2e/bhlink.py`(`adlink.py`의 글), `gen/e2e/bhdiff.py`와 Prysm 임시 트리의 `fve2e/bhcheck`.
- 이 도구는 생성기가 아니다. 증명 문장을 만들지 않는다.
- 열린 뒤에 더한 증거 파일(리뷰 s4-r1 S5): `lean/E2eScal/BhSpecChecker.lean`(`descterm.py` 출력), `gen/scal/AxiomsScal.lean`의 손 목록 추가, `gen/scal/negcases-holdout.json`.
- 이 증거 파일은 방법을 바꾸지 않는다. 생성기, 보조정리, 종류, 분류기는 같다.
- 한계: `bh/link/norm`은 Lake `input_dir`가 아니다. lakefile 변경은 승인이 필요해서 하지 않았다.
- 결과와 한계는 `RESULT.json`에 있다.

## 5. 세션 10 (INBOX 020) — 열린 뒤

- 생성기, 보조정리, 종류, 템플릿은 바꾸지 않았다. 템플릿 변경 제안도 없다.
- 더한 손 파일: `BhReject.lean`의 정리 둘, `WitBhU`, `ViReject`, `WitViR`. 개발 집합 손 증명의 글에서 코드 상수만 바꿨다.
- 더한 증거 파일: `negcases-holdout.json`의 사례 15개, `AxiomsScal.lean`의 손 목록 7개.
- 인코더 (iii)은 손 증명으로 시도했고 증명하지 못했다. 초안은 저장소에 넣지 않았다.
- 문서 변경: `BhSpecChecker.lean` 머리 주석(선언 덤프 같음), `README.md`, `gen.sh`(홀드아웃 명령 두 줄; 생성기 변경이 아니다).
