# 재증명 수정 2 재검사 (Claude Fable, 2026-11-06 08:34–09:00)

대상: `syjn99/ssz-fv-reprove-fix2` tip `7152188`(시작 `28ea489`, 커밋 8개). 읽기 전용. 로그: `review-reprove-fix2-claude-verify.log`, `review-reprove-fix2-claude-mutations.log`, `review-reprove-fix2-claude-lean.log`, 검사 파일 `ReviewReproveFix2.lean`.

## 1. 재현 수치

| 항목 | 보고서 | 재검사 | 일치 |
| --- | --- | --- | --- |
| 깨끗한 빌드(`lake clean` 뒤) | 856 jobs 성공 | 성공, 08:34:57–08:38:53 | 예 |
| AXIOMS.txt | TOTAL 1583 NONSTANDARD 0 | 같은 파일(바이트 동일), 1583/0 | 예 |
| AXIOMS-ALL.txt | 8028 NONSTANDARD 0 | 같은 파일, 8028/0 | 예 |
| 금지 전술(sorry/axiom/native_decide/bv_decide) | 없음 | 주석 두 줄만 | 예 |
| goval | 79 파일, 위반 0, 미검사 2 | 79/0/2 (WitCpM dst 기호 길이, 1a Witness.lean) | 예 |
| layout.json | layout.go 출력 | `GOROOT=$(go env GOROOT) go run`으로 재생성, 바이트 동일(2803). Scalars 24/8, E 오프셋 16 | 예 |
| 링크 검사 | PASS all (a)–(h) | PASS all, 번들 dbee1642… | 예 |
| 자기 시험 | 24 기대대로 | 24 기대대로(실패 23 + 통과 1) | 예 |
| ELF | 9c850c97…c501 변화 없음 | 같음 | 예 |
| 부정 시험 | 16 기대대로 | 16 기대대로(08:39:38–08:49:53), 새 변이 scrbword·blrity 지정 정리에서 실패, 대조군 PASS. 실행 뒤 워크트리 clean | 예 |
| go test semtest | PASS | `-count=1`: ok  	github.com/OffchainLabs/methodical-ssz/fv/kraken/semtest	0.458s | 예 |
| tools/RegressFix2.lean | 오류 없음, 공리 표준 | 오류 0, 선언 19개 표준 공리 | 예 |
| 리뷰 파일 회귀 | ReviewReproveFix 실패 둘, Astra 실패 넷, SHash 통과 | 오류 줄 3(원인 둘: Joint 인수, bv_errstr), 4, 0 | 예 |
| 주 정리 / 증인 선언 / Wit 파일 | 55 / 80(고유 59) / 79 | 55 / 59 고유 / 79 | 예 |

B0(vcgen)는 이 워크트리에서 실행할 수 없었다(`unknown module prefix 'Kraken'`, vcgen 의존성 미빌드). 세션도 B0를 주장하지 않았다.

## 2. 링크 검사 변이 (linkmut3, 보고서 밖 사본)

astra 우회 5개 전부 FAIL로 바뀜:

| 변이 | 결과 |
| --- | --- |
| A1 SHash 해시 문자열 안 `/-x-/` | FAIL (f) 원문 불일치(4행) |
| A2a·A2b `blFmtB` 뒤 `|>.map`(같은 줄, 다음 줄) | FAIL (g) 정의가 리터럴 하나가 아님 |
| A3 사용 위치 공백 둘 + 527 | FAIL (g) ELF 바이트 불일치 |
| A4 Go 호출 두 개를 "C: %w"로, 원본은 주석 | FAIL (g) go/parser 리터럴 없음 |
| A5a·A5b Wit 파일에 `[Host]` 정리 / 일반 def로 99999 | FAIL (g) 미검사 참조(역할 theorem / witness) |

새 변이 8개: N1 SHash 끝 주석 FAIL, N2 `-- "` 주석 뒤 527 FAIL, N3 문자 리터럴 `'"'` 뒤 527 FAIL, N5 `+ (526 : Nat)` FAIL(unparsed), N6 `/- -- -/` 뒤 999 FAIL, N8 `"\""` 문자열 + 주석 + 999 FAIL. PASS 둘은 정당: N4(두 호출 중 하나만 `"B: " + "%w"`로 바꿈, 다른 호출의 리터럴이 남고 ELF 검사가 바이트를 고정), N7(Lean 중첩 블록 주석 안의 999는 Lean에서도 주석).

## 3. Go 값 검사기 변이 (WitScA)

G1 bool 2 → "bool byte > 1". G2 패딩 제거 → 객체가 블록 밖. G3 수신자 0x1002c → 블록 밖(정렬 검사보다 먼저 걸림). G4 cap 15 < len 16 → "len > cap". G5 수신자 0x10020 → 슬라이스 데이터와 겹침. 다섯 모두 검출. G6 `layout.json`의 Scalars 크기를 16으로 손으로 바꾸고 패딩을 빼면 goval은 통과한다. 검사기가 `layout.json`을 신뢰하고 링크 검사는 이 파일을 고정하지 않는다(F-1).

## 4. Lean 검사 (`ReviewReproveFix2.lean`, 오류 0)

- `Joint S ty blFmtB vblRO VblMsg luFmtTooBig luTW`와 `Joint S ty bvFmtJ bvRO BvMsg luFmtMis luTW`(정리가 쓰는 인수 그대로)를 `joint_models`로 닫음. `Joint S ty [] (fun _ => True) (fun _ _ _ => True) [] 0`도 닫힌다: 모델은 메시지 바이트를 읽지 않으므로 어떤 RO·MsgIn에도 만족한다. 계약은 MsgIn과 RO를 묶지 않는다. 묶음은 호출자 인스턴스의 몫이다(F-2).
- rodata 셋(5743+13 ≤ 13272, 13272+21 ≤ 33605)과 blFmtB(526+5 ≤ 5743)는 서로 떨어져 있다. `vblRO`는 분리 결합으로 만족 가능하다.
- `VblMsg` 세 rodata 경우가 각 메시지를 담고, `%d` 경우는 128 이하. rodata 경우는 `hm = []`.
- `bl_reject_invalid_main` 예산 16640 ≥ 8192 + 5 + 128 + 8192 = 16517.
- `sc_spec_rejects_bool`을 구체 입력(마지막 바이트 2)에 적용. 경계 1은 전제 밖.
- `BoxIn`: 5는 정적 표, 300은 힙 8바이트.
- `#print axioms` 29개(joint_models, 새 거부·조합·사후조건 정리, 증인 14개) 전부 표준.

## 5. 소견

- F-1 (경미) `layout.json`은 goval의 입력이고 손으로 바꿀 수 있다. 재현 절차가 재생성하지만 링크 검사나 자기 시험이 고정하지 않는다. 1c 입력 13(실행 기록에 묶기)에 포함할 것.
- F-2 (설계, 신뢰 항목) `FmtErrorfWC`는 `MsgIn sp msg hm`이 메시지 바이트를 `RO` 또는 `hm` 안에 둔다는 것을 요구하지 않는다. 현재 인스턴스(VblMsg+vblRO, BvMsg+bvRO)는 그 조건을 만족하지만 CONTRACTS.md 1e 신뢰 항목에 "호출자가 MsgIn ⇒ 바이트 ∈ RO ∨ hm을 보장한다"가 없다. 추가할 것.
- F-3 (문서됨) `bl_reject_invalid_main` 결론은 `rax ≠ 0`과 프레임 보존뿐이다. 오류 객체(itab·e)는 없다. Scalars 거부(`rax = e0, rbx = e1`)보다 약하다. CONTRACTS 1e가 적고 있다.
- F-4 (경미) 보고서 X10 "ReviewReproveFix 실패 둘"은 오류 줄 셋(원인 둘)이다. 수치 표기만.
- F-5 (범위) X8c(ListC 원소 오프셋 순서) 미수행과 `ne_marshal_main` R 손실, 크기 정리 11개의 프레임은 보고서 0절이 막는 조건으로 적었다. 자평과 같다.

## 6. astra 전 판정

조건부. 게이트 1 미통과(세션 자평과 같다). 필수 수정 1·2·3·6·8은 변이와 수치로 닫힘을 확인했다. 4·5는 계약이 실제 호출 모양으로 좁혀졌고 남은 것은 신뢰 항목(F-2 포함)이다. 7은 부분. "완료 단위 전부 충족" 타입 Scalars·ListU64는 6요소 기준으로 성립한다(조합 증인 포함). 거부 경로 2/3.

## 7. astra 리뷰(09:12) 발견 재현

| astra 발견 | 재현 | 결과 |
| --- | --- | --- |
| 1 역할 분류: `[h : Host]` def가 `(z 1).At (go_string._+99999)`를 둠 | astra 파일 그대로(WitScM) | PASS all = 재현(버그). 내 단순 변형(`[h : Host]` theorem의 등식, 바인더 `blFmtB` 가림)은 "place-unknown"으로 FAIL. 우회는 검사기가 아는 배치 형식(`(z n).At`)을 쓸 때 열린다 |
| 2 (h) `luTW := (…+49184).toBitVec + 8` | sed 변이 | PASS all = 재현(버그). 정의 앞부분만 읽는다 |
| 4 오류 증인: `WitScRB.block` 첫 두 워드 0, `sc_reject_bool_runs` 결론 `rax = 0` | 소스 확인(`WitScRB.lean:42`, `:87`) | 재현. `sc_reject_bool_main`은 `rax = e0`만 말하고 `e0 ≠ 0`을 요구하지 않는다. 내 §5 F-3과 같은 종류(오류 객체 비nil 미명세) |
| 5 크기 정리 분류 | `AdSpec.lean:18–21`(`st.data.dmem = s.dmem`), `ScSize.lean:10`(rax만) | 재현. 보고서 X7 표의 "R 없음 7개"는 메모리 동일성 결론이고, 프레임 미달은 `sc_size_main` 하나다 |
| 3 Go 파서 지역 `fmt` 가림 | 미재현(astra 로그 `reprove-fix2-mut-go-fmt-shadow.log` 수용) | — |

## 8. 최종 판정

조건부. 게이트 1 미통과(세션 자평, astra, 나 셋이 같다). astra 필수 수정 8개 중 1·2·4·5를 재현했다. 3은 로그로 수용했다. 내 소견 F-1(layout.json 고정)은 astra 5와, F-2(MsgIn–RO 묶음은 호출자 책임)는 astra 3절과 겹친다.

astra 의견 "1c 개발은 지금 시작할 수 있다. 검사기 보강(1–5)과 남은 수작업 기준 사례(6–7)를 1c 첫 작업으로 고정한다"에 동의한다. 이유: 1·2·3은 검사기 수정이고 1c X1·X2(자동 완료표, 증인 생성기 통합)와 같은 코드를 만진다. 별도 수정 3 세션보다 1c X0로 흡수하는 쪽이 중복이 적다. 단 1c의 첫 in-review 완료 조건에 필수 수정 1–5의 자기 시험을 넣는다.
