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
