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

## 6. 세션 11 (INBOX 021) — 열린 뒤

- 생성기, 보조정리, 종류, 템플릿은 바꾸지 않았다.
- 저장소에 Lean 파일을 더하지 않았다. T-9 시도는 모두 실행 디렉터리의 임시 파일이다.
- 증거 파일 변경: `negative-holdout.json`에서 약한 사례 하나를 합계에서 뺐다(리뷰 s5-r1 S1). `axioms-gate.json`을 현재 SHA의 출력으로 바꿨다.

## 7. 홀드아웃 H2 평가 (세션 13, INBOX 023) — 열린 뒤

- 연 시각: `scal/HOLDOUT-OPENED`의 `H2.opened_utc`(커밋 `7a5ea61`). 그 전에는 Eth1Data 자료를 열지 않았다.
- 범위: `Eth1Data.UnmarshalSSZ`와 `MarshalSSZTo` 빠른 경로. `SizeSSZ`는 뺐다(AU-09 노출).
- 이 세션은 H1 파일을 읽을 수 있었다. H1 경험에서 독립이 아니다.
- 생성기, 보조정리, 종류, 템플릿, 분류기는 바꾸지 않았다.
- 생성기는 한 번 돌렸다(`p2dec`, 작업 393). 종료 코드 2, 출력 0바이트다.
- 기록: `e1/gen-e1dec.raw.txt`(명령, 종료 코드, stderr 원문). 빈 `GenE1Dec.lean`은 라이브러리에 넣지 않았다.
- 순서(리뷰 h2-r1 S1): 기록 파일은 02:02:50Z에 썼다. 커밋 `a9918d4`는 02:04:40Z다.
- 그 사이에 `E1Seg0.lean`을 쓰고 빌드했다(작업 394, 02:04:30Z–02:04:33Z).
- 그래서 "원 출력을 손 수정 전에 커밋한다" 규칙은 커밋 순서로만 지켜졌다. 작업 순서로는 지켜지지 않았다.
- 영향은 없다. 고칠 생성 출력이 없다.
- 원인: DepositRoot의 memmove 출처가 `buf + 0`이다. 코드에 `add $src,%rbx`가 없다.
- 고정 템플릿 `rootDecMid`는 이 지시어를 요구한다. 생성기는 첫 필드에서 멈추고 BlockHash도 내지 않는다.
- 제안(하지 않음): `rootDecMid`에 출처 0의 변형을 두고 `p2dec`가 `add`가 없는 블록을 받게 한다.
- 이 제안은 방법 변경이다. 이 평가에서는 하지 않았다. 생성기 적용 범위는 이 형에서 0/2 필드다.
- DepositCount의 인라인 읽기(지시 47–49)에는 방법의 템플릿이 없다(리뷰 h2-r1 S2).
- 그래서 제안한 변형이 있어도 생성기는 두 루트 구간(지시 13–36, 50–74)만 덮는다.
- 손 증명으로 대신한 부분(복사한 글):
  - `E1Seg0.lean`: `rootdec_seg`의 문장과 증명 글에서 `add` 단계를 지운 것. 고정 방법의 일부가 아니다.
  - BlockHash 구간: 고정 `rootdec_seg`를 손으로 인스턴스화했다(`GenBhDec`의 생성 글 형태를 복사).
  - `E1Accept`(`BhHead`, `BhAccept`의 글), `E1Reject`(`BhReject`), `E1Spec`(`BhSpec`), `E1SpecK`(`BhSpecK`), `WitE1A`(`WitBhA`), `WitE1R`(`WitBhR`).
- 열린 뒤에 더한 손 파일: `E1Code`, `E1Desc`, `E1Seg0`, `E1Accept`, `E1Reject`, `E1Spec`, `E1SpecK`, `WitE1A`, `WitE1R`.
- 생성 파일: `E1SpecChecker.lean`(`descterm.py` 출력, 머리 주석에 경로 한 줄을 더함).
- 검사기 json `e1/prysm_v1alpha1.Eth1Data.desc.json`의 출처(리뷰 h2-r1 S3): 다른 실행의 리뷰어 임시 디렉터리에서 복사했다.
- 그것은 리뷰 phase1c-r5의 임시 사본 `desc/orig/`다. 이 저장소 밖에 있다.
- sha256 `6064a3dc…782b`는 `gen/desc/results/main.result.json` 기록 74(`Eth1Data`, PASS)와 같다(세션 14에서 다시 셈).
- 손 Desc(`E1Desc.lean`, 커밋 `c43359b`)는 검사기 Desc를 만들거나 출력하기 전에 커밋했다.
- 열린 뒤에 더한 도구: `gen/e2e/e1link.py`(`bhlink.py`의 글), `gen/e2e/e1diff.py`(`bhdiff.py`의 글), Prysm 임시 트리의 `fve2e/e1check`.
- 열린 뒤에 더한 증거 파일: `gen/scal/negcases-h2.json`, `AxiomsScal.lean`의 손 목록 15개와 import 셋.
- 세션 14(리뷰 h2-r1 S6)에서 부정 시험 2건을 더했다: `e1-rc-stmt-size`, `e1-witr-stmt-len`. 둘 다 정리 안에서 실패했다(작업 432, 433).
- `kindcheck.py`는 돌리지 않았다. 검사할 생성 정리가 없다.
- 인코더(`MarshalSSZTo`)의 스택 검사는 `lea -0x8(%rsp),%r12; cmp 0x10(%r14),%r12; jbe` 꼴이다(T-9와 같다).
- INBOX 023 3단계에 따라 시도하지 않았다. 예산은 사용자 결정을 기다린다.
- 한계: `e1/link/norm`은 Lake `input_dir`가 아니다. lakefile 변경은 승인이 필요해서 하지 않았다.

## 8. SG-1 확장 (두 홀드아웃을 연 뒤) — 개발 작업, 홀드아웃 아님

- 언제: 2026-11-11, 기준 커밋 `48b74b6` 뒤. H1과 H2를 모두 연 뒤다.
- 무엇: 출처 오프셋 0의 32바이트 디코드 구간을 생성기가 받게 했다.
- 새 Lean 파일: `P2DecZ.lean`(템플릿 `rootDecMidZ`, 보조정리 `rootdec_seg_z`), `KindZ.lean`(종류 `rootDecSegZKind`).
- `rootdec_seg_z`는 손 파일 `E1Seg0.lean`의 글을 일반화했다. 정의와 증명 글은 이름만 다르다.
- `Kind.lean`, `P2Dec.lean`, 기존 정리의 문장은 바꾸지 않았다. `decl_drift`는 ADDED 19개만 보인다.
- `scalgen.py p2dec`: 버퍼 다시 읽기 다음 지시어로 꼴을 고른다. 형 이름이나 필드 이름은 보지 않는다.
- `add $X,%rbx`면 기존 꼴이다. `mov $0x20,%ecx`면 오프셋 0 꼴이다. 다른 것은 불일치다.
- 필드 규칙: 필드마다 따로 맞춘다. 한 필드의 실패가 뒤 필드의 검사를 막지 않는다.
- 출력은 완전하거나 없다. 일부만 맞으면 종료 코드 3이고 stdout은 비어 있다.
- `--partial-out`을 주면 맞은 필드만 파일에 쓴다. 파일 머리에 `PARTIAL OUTPUT`과 빠진 필드를 적는다.
- 어느 필드도 맞지 않거나 구간이 겹치면 종료 코드 2이고 아무것도 쓰지 않는다.
- `kindcheck.py`: `rootDecSegZKind`(인자 8개)를 받는다. `KindZ.lean`이 고정 blob일 때만 받는다.
- 오염: Eth1Data는 이 확장의 개발 자료다. 확장은 Eth1Data의 `.S`를 보고 만들었다.
- 그래서 Eth1Data 결과는 홀드아웃 결과가 아니다. 새 홀드아웃 형은 정하지도 열지도 않았다.
- 위 §4–§7의 H1, H2 결과는 확장 전의 결과다. 그대로 둔다.
- 확장 전 기록: 고정 생성기(blob `78e3339`)의 Eth1Data 실행은 종료 코드 2, 0/2 필드다(`a9918d4`, 승인 `48b74b6`).
- 이 기록은 역사적 부정 결과로 남는다. `gen/scal/p2dec_test.py`가 같은 결과를 다시 낸다.
- 확장 뒤: 새 생성기는 Eth1Data에서 2/2 루트 필드를 낸다(`GenE1Dec.lean`, 손대지 않은 출력).
- DepositCount의 인라인 읽기에는 여전히 템플릿이 없다.
- 회귀: GenCi, GenVi, GenAdDec, GenCpDec, GenBhDec를 새 생성기로 다시 만들었다. 모두 바이트가 같다.
- 시험: `scal/sg1-gen-test.json`(10/10), `scal/negative-sg1.json`(7/7). 일반화 주장은 이 시험의 범위만이다.

## 9. T-9 스트림 (사용자 지시, 2026-11-11) — 열린 뒤

- 생성기, 보조정리, 종류, 템플릿은 바꾸지 않았다. `Fk/*`와 계약도 바꾸지 않았다.
- 이 작업은 손 증명이다. 생성기 결과가 아니다. 홀드아웃 주장에 넣지 않는다.
- 작성 세션은 H1과 H2의 파일과 T-9 기록을 읽었다. 독립 표본이 아니다.
- 더한 Lean 파일: `StackGuard.lean`, `BhEncHead.lean`, `BhEncRoots.lean`, `BhEncMain.lean`, `BhSpecM.lean`, `WitBhM.lean`.
- `BhEncHead.lean`의 A1, A2 본문은 세션 11의 임시 파일 `Split3.lean`에서 왔다. 가드 분기와 길이 목표 두 곳을 고쳤다.
- `WitBhM.lean`은 `E2e/WitCpM.lean`의 글이다. `BhSpecM.lean`은 `E2e/CpSpecM.lean`의 글이다.
- 더한 증거 파일: `gen/scal/negcases-t9.json`, `scal/negative-t9.json`, `gen/e2e/bhmdiff.py`, `bh/bhmcheck-main.go.txt`, `bh/differential-enc*.json`.
- `AxiomsScal.lean`에 이름 11개를 더했다. `axioms-gate.json`을 현재 트리의 출력으로 바꿨다.
- 제안(하지 않음): 인코드 템플릿을 이 세 루트 블록 꼴에 맞추는 변경. `scalgen.py`와 `Kind.lean`은 그대로다.

## 10. 세션 15 통합 (INBOX 027) — 열린 뒤

- T9 스트림과 SG1 스트림을 이 브랜치에 병합했다. 새 증명, 생성기 변경, 템플릿 변경은 없다.
- 두 스트림이 모두 이 파일에 8절을 더했다. SG-1 Lean 주석이 8절을 가리키므로 SG-1이 8절이다. T-9는 9절이 됐다.
- `kindcheck.py`를 바꿨다(리뷰 sg1-r1 S2). `PARTIAL OUTPUT` 머리가 있는 파일을 거부한다. 읽는 쪽 검사기의 변경이다.
- 이 변경은 생성기 출력, 종류, 보조정리를 바꾸지 않는다. 기존 생성 파일 6개는 그대로 PASS다.
- `gen/scal/negcases-sg1.json`에 사례 8건을 더했다(리뷰 sg1-r1 S3). `rootdec_seg_z`와 BlockHash 구간을 겨눈다.

## 11. 홀드아웃 H3 평가 — 열린 뒤

- 연 시각: `scal/HOLDOUT-OPENED`의 `H3.opened_utc`(커밋 `782a41b`, 2026-11-11T04:26:30Z).
- 방법 고정: 커밋 `dda707c`. 고정 기록의 blob 7개와 `lean/E2eScal` 트리 id를 다시 셌다. 모두 같다.
- 형: `v1alpha1.BlobIdentifier`(Z 부류), `v1alpha1.DepositMessage`(N 부류). 범위는 `UnmarshalSSZ`뿐이다.
- 평가 세션은 생성기, 종류, 템플릿 보조정리를 만들지 않았다. H1, H2, SG-1, T-9 파일은 읽을 수 있었다.
- 생성기, `kindcheck.py`, `Kind*.lean`, 템플릿 보조정리 모듈, `Fk/*`, 계약, 기존 문장은 바꾸지 않았다.
- 생성기는 형마다 한 번 돌렸다(작업 11, 12). 둘 다 종료 0이고 stderr는 비어 있다.
- 원 출력 `GenBiDec.lean`, `GenDmDec.lean`은 손대지 않고 커밋했다(`936446b`). 손 수정은 0줄이다.
- `kindcheck.py`는 두 파일 모두 PASS다(작업 13). 두 파일은 그대로 빌드됐다(작업 14).
- 생성기 적용 범위: BlobIdentifier 필드 2개 중 1개, DepositMessage 필드 3개 중 1개.
- 생성기는 32바이트 `[]byte` 필드만 읽는다(`scalgen.py` `ir_roots`). 그래서 48바이트 PublicKey를 보지 않는다.
- 인라인 uint64 읽기(Index, Amount)에는 방법의 템플릿이 없다. 이것은 H3 전에 적은 한계다.
- 손 보조정리: 새 H3 모듈 `DmSeg0.lean`(`E2eScal.H3.bytes48dec_seg_z`).
- 그 글은 `rootDecHead`, `rootDecMidZ`, `rootdec_seg_z`의 글에서 `32`를 `48`로 바꾼 것이다. 고정 방법의 일부가 아니다.
- 손 파일과 원본 글: `BiAccept`, `DmAccept`(`E1Accept`), `BiReject`, `DmReject`(`E1Reject`), `BiSpec`, `DmSpec`(`E1Spec`).
- 계속: `BiSpecK`, `DmSpecK`(`E1SpecK`), `WitBiA`, `WitDmA`(`WitE1A`), `WitBiR`, `WitDmR`(`WitE1R`), `BiDesc`, `DmDesc`, `H3Code`.
- 두 수용 정리는 생성 구간 정리를 그대로 부른다(`bi_dec_BlockRoot_seg`, `dm_dec_WithdrawalCredentials_seg`).
- 생성 파일: `BiSpecChecker.lean`, `DmSpecChecker.lean`(`descterm.py` 출력, 머리 주석에 경로 한 줄을 더함).
- 검사기 json의 출처: phase1c-r5 리뷰의 임시 사본 `desc/orig/`다(H2와 같다). sha256은 `main.result.json` 기록과 같다.
- 손 Desc(`11babc9`)는 검사기 Desc를 만들거나 출력하기 전에 커밋했다.
- 열린 뒤에 더한 도구: `gen/e2e/h3link.py`(`e1link.py`의 글), `gen/e2e/h3diff.py`(`e1diff.py`의 글), `h3/h3check-main.go.txt`.
- 열린 뒤에 더한 증거 파일: `gen/scal/negcases-h3.json`, `AxiomsScal.lean`의 손 목록 87개와 import 8개.
- 이 도구와 증거 파일은 방법을 바꾸지 않는다.
- 제안(하지 않음) P-H3-1: 인라인 uint64 읽기 템플릿.
- P-H3-1의 꼴은 `mov dB(%rsp),%rcx; mov src(%rcx),%rcx; mov %rcx,f(%rdx)`이다. 두 형에서 같다.
- 제안(하지 않음) P-H3-2: 구간 템플릿의 크기를 매개변수로 하고 `ir_roots`가 48바이트 벡터도 읽게 한다.
- P-H3-2가 있으면 PublicKey 구간(지시 13–36)이 생성 대상이 된다. 이 평가에서는 하지 않았다.
- 두 제안은 방법 변경이다. 그래서 그 필드는 생성기가 덮지 않은 것으로 보고한다.
- 한계: `h3/link/norm`은 Lake `input_dir`가 아니다. lakefile 변경은 승인이 필요해서 하지 않았다.
- 정정(통합 INT2, 리뷰 h3-r1 S1): 읽기 A3는 큐레이터가 후보 목록을 본 뒤에 정했다.
- 그때 누구도 방법 코드를 열지 않았다. 출처는 저장소 밖의 컨트롤러 확인 파일이다.
- 다른 읽기(전이적 필드)에서는 N 부류가 `ProposerSlashing`이다. 그 읽기는 쓰지 않았다.
- 읽기 A1을 글자 그대로 읽으면 후보가 없다. 확인된 A1은 `HOLDOUT-OPENED`의 좁은 읽기다.
- 정정(h3-r1 S2): 기존 파일 `gen/scal/AxiomsScal.lean`을 늘렸다(+97줄, −0줄). 공리 손 목록이고 방법 파일이 아니다.
- 정정(h3-r1 S3): `BiSpecChecker.lean`, `DmSpecChecker.lean`은 "Do not edit" 파일이다. 손으로 머리 한 줄을 더했다.
- 그 머리는 `descterm.py`의 고정 디렉터리를 적는다. 파일은 그곳에 없고 `e2e/h3/`에 있다.
- 정정(h3-r1 S6): 검사기 json은 다른 리뷰의 임시 사본에서 왔다. 기록과는 sha256으로만 묶인다. 저장소만으로는 다시 만들 수 없다.

## 12. 통합 INT2 (H3와 ENC 병합) — 열린 뒤

- H3 `75166e4`(리뷰 h3-r1 승인)와 ENC `ad15fbc`(리뷰 enc-r1 승인)를 `--no-ff`로 병합했다.
- 병합 커밋은 `500571c`(H3)와 `c10daf9`(ENC)다. 새 증명, 생성기 변경, 문장 변경은 없다.
- ENC는 H3 형의 코드를 쓰지 않는다. ENC 작성자는 `h3/` 파일 이름과 gate 기록 5개만 보았다(리뷰 enc-r1 S5).
- 생성기 재실행: 통합 검사로 `regen_check.sh`를 scratch에 돌렸다. H3 평가의 생성기 실행 수(형마다 한 번)에 넣지 않는다.

## 13. GEN2 보조정리 작업 (단위 G2-L) — H3 뒤, 개발 작업, 홀드아웃 아님

- 이 작업은 H3 평가와 통합 INT2, INT3 뒤에 했다. 기준 커밋은 `71161fa`다.
- BlobIdentifier와 DepositMessage는 이제 개발 자료다. 이 두 형으로 홀드아웃 주장을 하지 않는다.
- 작성 세션은 새 Fable 세션이고 직접 작성자다. 이 세션은 생성기를 만들지 않았다.
- 이 세션은 세 디코더의 `.S`, 손 증명, 생성 파일, H3 기록을 모두 읽었다.
- 새 모듈만 더했다: `SegN`, `KindN`, `SegNRel`, `U64Inline`, `KindU64`, `Gen2Examples`, `Compose`, `Gen2ComposeEx`.
- 기존 `.lean` 파일, `scalgen.py`, `kindcheck.py`, `gen.sh`, H3 생성 파일과 H3 기록은 바꾸지 않았다.
- 증명 생성기는 그대로다. 그래서 생성기 적용 범위(SG-2)는 바뀌지 않았다.
- `SegN.lean`과 `KindN.lean`의 글은 임시 스크립트가 `P2Dec.lean`, `P2DecZ.lean`, `Kind.lean`, `KindZ.lean`에서 만들었다.
- 그 스크립트는 크기 `32`를 매개변수 `n`으로 바꾼다. 스크립트는 커밋하지 않았다.
- `Gen2Examples.lean`도 임시 스크립트로 썼다. 이것은 `scalgen.py`의 출력이 아니다. 손 예시로 센다.
- 인라인 uint64 꼴은 세 자리에서 먼저 읽었다. 임시 레지스터가 다르다: Eth1Data는 rsi, 나머지 둘은 rcx다.
- P-H3-1의 글(§11)은 rcx만 적는다. 그 글은 H3의 두 형에만 맞다.
- L1의 크기는 32, 48, 96뿐이다. 96바이트 자리는 개발 자료에 없다. 96은 실제 코드에서 확인하지 않았다.
- L2의 레지스터는 12개다. 관측한 것은 rsi와 rcx 둘이다. 수신자는 rdx여야 한다.
- L3은 조각 셋과 예시 하나다. 구간 목록을 받는 일반 결합기는 없다. 프레임은 `0x20`만 다룬다.
- 일반성 주장은 없다. 다른 형으로 옮겨지는지는 측정하지 않았다.
- 더한 증거 파일: `gen/scal/negcases-gen2.json`. `gen/e2e/negative.py`는 바꾸지 않았다.
- 공리 게이트는 임시 JSON으로 돌렸다. 커밋된 `axioms-gate.json`은 바꾸지 않았다.
- 독립 리뷰는 아직 없다.

## 14. GEN2 생성기 작업 (단위 G2-G) — H3 뒤 생성기 변경, 개발 작업, 홀드아웃 아님

- 이 작업은 H3 평가 뒤에 증명 생성기 `gen/scal/scalgen.py`를 바꿨다. 기준 커밋은 `6c62a49`다.
- 작성 세션은 새 Opus 세션이다. 보조정리(단위 G2-L)는 쓰지 않았다. 리뷰도 하지 않는다.
- 입력은 개발 자료뿐이다: Eth1Data, BlobIdentifier, DepositMessage의 `.S`, IR, 손 증명, 생성 파일.
- BlobIdentifier와 DepositMessage는 GEN2의 표본 안 자료다. H4 전까지 홀드아웃 주장은 없다.
- 무엇이 바뀌었나: `p2dec --gen2` 선택 모드를 더했다. 기본 모드의 출력은 글자 그대로 같다.
- `--gen2`는 IR의 모든 필드를 분류한다. 바이트 벡터 32, 48, 96과 인라인 uint64만 덮는다.
- 32바이트 필드는 옛 정리 글을 쓴다. 48, 96은 `bytesdec_seg(_z)`, uint64는 `u64dec_inline_seg`를 쓴다.
- 다른 필드는 "not covered: 이유"로 보고한다. 정리를 추측하지 않는다.
- `--gen2 --compose`도 더했다. 모든 필드가 덮이면 수용 정리 전체를 쓴다.
- 합성 정리의 문장 검사는 손 정리와의 `_type` 항등식뿐이다. 그 정리에 대한 종류(kind)는 없다.
- 손 정리가 없는 형(홀드아웃)에서는 합성 문장을 검사할 것이 없다. 이것은 열린 틈이다.
- 생성기는 형마다 한 번 돌렸다(작업 05, 11). 원 출력은 손대지 않고 먼저 커밋했다.
- 새 파일만 썼다: `Gen2E1Dec`, `Gen2BiDec`, `Gen2DmDec`, `Gen2BiAccept`, `Gen2DmAccept`, `Gen2E1Accept`.
- H3 원 출력 `GenBiDec.lean`, `GenDmDec.lean`과 H3 기록은 바꾸지 않았다.
- 옛 생성기 명령 8개의 출력은 바이트가 같다(`regen_check.sh` SAME, 작업 02, 17).
- `kindcheck.py`는 새 종류 셋을 고정 blob과 함께만 받는다. `_type` 항등식은 "identity-checked"로 따로 보고한다.
- 보조정리 모듈은 바꾸지 않았다. 리뷰 g2l-r1의 판정은 APPROVE이고 필수 수정은 없다.
- 96바이트 필드는 개발 자료에 없다. 48바이트 add 꼴은 합성 `.S`의 글 검사만 했다. 커널 검사는 아니다.
- 일반성 주장은 없다. 독립 리뷰는 아직 없다.

## 15. GEN2 수정 작업 (단위 G2-F) — H3 뒤 두 번째 생성기 변경, H4 고정 전, 개발 작업

- 리뷰 g2g-r1의 판정은 REQUEST_CHANGES다. 필수 수정 둘은 문서다. 증명 결함은 없었다.
- 이 작업은 H3 뒤 두 번째 생성기 변경이다. H4를 위해 생성기를 고정하기 전에 했다.
- 작성 세션은 새 Opus 세션이다. G2-G와 G2-L을 쓰지 않았다. 리뷰도 하지 않는다.
- 14절 정정(리뷰 S4): "형마다 한 번" 앞에 scratch 시험 실행이 있었다(G2-G 작업 01, 09).
- 커밋된 실행은 작업 05와 11이다. scratch 출력은 커밋하지 않았다.
- 바뀐 것: `kindcheck.py`의 `_type` 규칙. 합성 정리에만 받고, 오른쪽이 생성 이름이면 거부한다.
- 바뀐 것: `--gen2 --partial-out` 파일은 유효한 Lean 모듈이다. `kindcheck.py --partial`은 종료 3을 준다.
- 바뀐 것: `--compose`에 `--same-as`가 없으면 `UNCHECKED STATEMENT` 표시를 쓴다. `--same-as-prop`을 더했다.
- 입력은 개발 자료뿐이다. BeaconBlockHeader(H1 형)도 이제 GEN2의 표본 안 자료다.
- `Gen2BhDecPartial.lean`은 생성기를 한 번 돌린 원 출력이다(작업 05). 같은 명령의 scratch 시험이 앞섰다(작업 02).
- 기본 모드와 커밋된 생성 파일은 바뀌지 않았다: `regen_check.sh` 15/15 SAME(작업 13).
- 일반성 주장은 없다. 독립 리뷰는 아직 없다.

## 16. 홀드아웃 H4 평가 — 열린 뒤

- 연 시각: `scal/HOLDOUT-OPENED`의 `H4.opened_utc`(커밋 `9d338fa`, 2026-11-11T08:53:45Z).
- 방법 고정: 커밋 `eacf0fb`. 고정 기록의 blob 15개와 `lean/E2eScal`, `lean/Fk` 트리 id를 다시 셌다. 모두 같다.
- 형: `v1alpha1.Deposit_Data`(A 부류), `v1alpha1.PendingPartialWithdrawal`(B 부류). 범위는 `UnmarshalSSZ`뿐이다.
- 평가 세션은 GEN2 생성기, 검사기, 종류, 보조정리를 만들지 않았다. 이전 단위의 파일은 읽을 수 있었다.
- 밝힌 유사성(H4-A5): Deposit_Data는 DepositMessage에 96바이트 Signature를 더한 형이다. 필드 3개는 표본에 가깝다.
- 손 Desc(`2daf204`)는 검사기 Desc를 출력하기 전에 커밋했다.
- 손 문장 `H4.dd_accept_stmt`, `H4.pw_accept_stmt`(`d7e3304`)는 생성기를 돌리기 전에 커밋했다.
- 손 문장은 IR `go_fields`, SSZ 배치, `.S`의 프레임 사실, Bi/Dm/E1/Bh 손 정리의 꼴에서 썼다.
- 링크 표는 손 문장 전에 만들었다. 문장이 `.S`의 프레임 사실을 써야 했다. 생성기는 돌리지 않았다.
- 생성기 (S)와 (C)는 형마다 한 번씩 돌렸다(작업 12, 13, 16, 17). 다른 선택으로 다시 돌리지 않았다.
- 원 출력 `Gen2DdDecPartial.lean`, 요약 JSON 둘, stderr 기록 셋은 손대지 않고 먼저 커밋했다(`43a0847`, `76b66ba`).
- 손 수정 줄은 0이다. stderr 하나(Deposit_Data (S))에는 실행 디렉터리 경로가 있어 커밋하지 않았다.
- `scalgen.py`, `kindcheck.py`, `Kind*.lean`, 보조정리 모듈, `Fk/*`, 계약, 기존 문장은 바꾸지 않았다.
- 새 손 보조정리: `H4.bytes32dec_seg_nop`(`DdSegNop.lean`). `bytesdec_seg`(n = 32)의 글에 `nop` 한 단계를 더했다.
- 그 글은 임시 스크립트가 `SegN.lean`에서 만들었다. 스크립트는 커밋하지 않았다. 방법의 일부가 아니다.
- 열린 뒤 더한 도구: `gen/e2e/h4link.py`(`h3link.py`의 글), `gen/e2e/h4diff.py`(`h3diff.py`의 글), `h4/h4check-main.go.txt`.
- 열린 뒤 더한 증거 파일: `gen/scal/negcases-h4.json`, `AxiomsScal.lean`의 import 7개와 손 목록 46개.
- 검사기 json은 phase1c-r5 리뷰의 임시 사본에서 왔다. sha256은 `main.result.json` 기록과 같다.
- `DdSpecChecker.lean`, `PwSpecChecker.lean`은 `descterm.py` 출력이다. 머리에 경로 한 줄을 손으로 더했다(H3와 같다).
- 제안(하지 않음) P-H4-1: 32바이트 구간 머리에서 `callq runtime.makeslice` 앞의 `nop`을 허용한다.
- P-H4-1이 있으면 Deposit_Data의 WithdrawalCredentials(지시 47–72)가 생성 대상이 된다.
- 제안(하지 않음) P-H4-2: 인라인 uint64 읽기의 다른 꼴을 읽는다.
- 그 꼴은 `mov 0x8(%rbx),%r8; mov %r8,0x10(%rax)`이다. 두 기준 레지스터를 앞의 다른 지시가 다시 읽는다.
- 제안(하지 않음) P-H4-3: 위임 overlay 필드(호출)를 기존 함수 명세 `ViUAccC`, `EpUAccC`로 덮는 구간 템플릿.
- 세 제안은 방법 변경이다. 그래서 해당 필드는 생성기가 덮지 않은 것으로 보고한다.
- 도구 한계: `negative.py`의 코드 변이는 그 모듈 안의 이름만 바꾼다.
- 문장이 다른 모듈의 `abbrev`이면 대조군도 실패한다(`dd-acc-control`, 작업 46). 그 네 사례는 철회했다.
- 한계: `h4/link/norm`은 Lake `input_dir`가 아니다. lakefile 변경은 승인이 필요해서 하지 않았다.
- 일반성 주장은 없다. 독립 리뷰는 아직 없다.

## 17. 통합 INT4 (GEN2와 H4 병합) — 리뷰 뒤 정정

- 위 절의 글은 고치지 않는다. 이 절은 덧붙인 정정이다.
- 13–16절의 "독립 리뷰는 아직 없다"는 다음 리뷰로 대체한다.
- g2l-r1 APPROVE(`6c62a49`), g2g-r1 REQUEST_CHANGES(`cd47028`, 문서만), g2f-r1 APPROVE(`eacf0fb`), h4-r1 APPROVE(`fae7d6f`).
- 16절 정정(리뷰 h4-r1 S2): 평가자는 `dd_accept_stmt`를 쓰기 전에 `Gen2DmAccept.lean`을 읽었다.
- 그 파일은 형제 개발 형 DepositMessage의 생성 합성 정리다. 다른 형의 파일이라 허용된다.
- 결과 (C)는 두 형 모두 거부했다. 그래서 어떤 항등식 결과도 이 읽기에 의존하지 않는다.
- 16절 정정(S1): 덮은 필드 3개 중 PublicKey와 Amount는 표본에 가깝다. 표본 밖은 Signature 하나다.
- 덮지 못한 WithdrawalCredentials는 표본에 가까운 32바이트 꼴이다. 패딩 `nop`에서 실패했다(SG-3).
- 15절 정정(리뷰 g2f-r1 S5): 15절의 작업 번호 01, 02, 05, 09, 11, 13은 그 세션의 gate 작업이다.
- 그 로그는 저장소에 없다. 번호는 이름표일 뿐이다. 저장소 안의 증거는 커밋된 출력과 `regen_check.sh` 결과다.
- 16절 정정(S7): 선택 기록의 A2 다른 읽기를 `scal/HOLDOUT-OPENED`의 `H4.review_h4_r1_correction`에 더했다.
- 통합 검사의 `regen_check.sh`는 `Gen2DdDecPartial.lean`의 생성기 명령도 두 번 다시 돌렸다(scratch).
- 이것은 H4 실행이 아니다. H4의 "형마다 한 번" 규칙은 평가 세션에 대한 것이다. 결과는 SAME이다.
- 제안(하지 않음)은 그대로다: P-H4-1, P-H4-2, P-H4-3, 합성 문장의 종류(kind).
- g2f-r1 S1–S4(`kindcheck.py` 변경)도 제안(하지 않음)이다. H4 고정 뒤라 바꾸지 않았다.
- 일반성 주장은 없다. 통합 INT4 자체의 리뷰는 아직 없다.
