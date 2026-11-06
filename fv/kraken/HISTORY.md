# HISTORY: Kraken x64 세션 이력

세션마다 한 단락이다. 시각은 IST 커밋 시각이다. 에이전트 시간이고 사람 시간이 아니다.
옛 보고서(`REPORT-1b*.md`)와 리뷰 증거(로그, json, 변이 사본)는 git 이력에 있다.
리뷰 증거는 커밋 `28ea489`(재증명 수정)와 `0ef30e3`(재증명 수정 2)에 있다. 그 전 세션의 증거는 각 리뷰 커밋에 있다.
리뷰 본문은 `review/*.md`에 남는다.

## 1. 평가 (2026-11-04 21:30 – 11-05 00:40)

커밋 `c60e0d2..1f95206`, 리뷰 `8f3faff`.
MiniRV 대신 Kraken x64(main `6064eec`)를 쓸 수 있는지 평가했다.
K0: Lean 4.35.0에서는 Kraken 파서가 빌드되지 않는다. nightly-2026-09-21에서 Kraken과 EthLib SSZ 폐포가 빌드된다(332 s).
K1: `link/conv.py`가 objdump를 레이블 어셈블리로 바꾼다. 9개 함수가 런타임 파서를 통과한다.
K2–K4: Scalars 거부·수용·크기·인코더, ListU64 루프와 수용 경로를 증명했다. 정리 57개.
`kstep`은 큰 맥락에서 `grind` 시간 초과로 끝났다. 그래서 단계 보조정리와 매크로 439줄(`Step`, `Labels`, `Flags`, `Block`, `Bytes`)을 만들었다.
비용: Scalars 거부 24분, ListU64 수용 61분. 같은 일이 1a MiniRV에서 약 4시간 걸렸다(학습 효과 포함). Fk 빌드 19.7 s.
판정은 "조건부 가능"이었다.
astra 리뷰: `lu_accept_main`이 공허하다(계약 `hms`가 모든 `cnt`와 프레임에 양화되어 전제가 모순). ValidateBitlist에 Kraken이 모르는 `bsr`가 있다.
K5 하드웨어 대조는 Docker가 응답하지 않아 하지 못했다.

## 2. 1b (2026-11-05 06:13 – 13:44)

커밋 `8f3faff..4e37f2e`, 리뷰 `9ff7c73`.
대상을 9개 타입으로 늘렸다: BitVec, Nested, ListC, BitL, Prysm v7.1.8 축약 Checkpoint·AttestationData.
크기, 인코더 빠른 경로, 디코더 수용·거부, EthLib 왕복 정리를 만들었다. 정리 597개.
`MakesliceC`를 힙 조각 형식으로 고쳐 `lu_accept_main`을 다시 증명했다. 증인 `lu_accept_runs`(n = 0, 1, 16).
링크 검사 `link/check.py`를 만들었다(27개 함수, 2751개 명령어).
발견 F1(BitVec 패딩 비트 수용), F2(BitL 인코더가 바이트를 셈). `semtest/f12_test.go`가 재현한다.
B0: vcgen 갈래를 평가했고 main에 남기로 했다(`vcgen/B0.md`).
자평은 "게이트 1 조건부 통과"였다.
astra 리뷰가 기각했다: `GrowsliceC`가 모순이라 BitL 수용 셋이 공허했다. 인수 없는 `fmt.errorf`는 nil을 돌려주므로 ListC 거부 계약이 틀렸다. 링크 검사가 의미가 바뀐 명령어를 통과시켰다.

## 3. 1b-fix (2026-11-05 14:42 – 17:59)

커밋 `32c0bdc..694f129`, 리뷰 `f452384`.
`GrowsliceC`에 입력 범위와 예산을 넣고 모델 `rt_growslice`를 증명했다.
fmt를 `FmtErrorfNilC`(인수 0개, rax = 0)와 인수 있는 계약으로 나눴다.
링크 검사에 (f) SHash와 (g) 형식 상수를 더했다.
주 정리 10개와 계약 호출 1개에 전제 증인을 만들었다.
B0 명세의 필드 오프셋을 고쳐 다시 쟀다.
수치: 704 jobs, AXIOMS 754, 자기 시험 9, 부정 시험 7.
자평은 "조건부, 게이트 1 미통과"였다.
astra 리뷰: B0 spill 좌표가 틀렸다(`rsp + 16`이 아니라 호출 전 `rsp + 8`). SHash 검사에 새 우회가 있다. 전체 전제의 비공허성과 조합 가능한 사후조건이 없다.

## 4. 재증명 (2026-11-05 23:01 – 11-06 01:28)

커밋 `2d0150b..440e079`, 리뷰 `df024af`.
생성기 수정 `698c202`(F1, F2, G1–G3, H1)를 병합한 `2d0150b` 위에서 다시 증명했다. 새 ELF `9c850c97…c501`.
F1·F2는 거부 정리가 됐다. `ssz.ValidateBitvector`는 계약이 아니라 기계어 정리가 됐다.
G3가 지운 첫 오프셋 `> size` 분기는 옛 ELF에도 없었다. 지울 기계어 정리가 없었다.
수치: 804 jobs, AXIOMS 1296/6648, 자기 시험 10. 주 정리 53개 중 48개에 직접 증인.
astra 리뷰: 링크 검사 우회 둘, 실제 Go 상태와 다른 증인, 실패하는 Go 회귀 시험. 필수 수정 7개.

## 5. 재증명 수정 (2026-11-06 02:09 – 03:25)

커밋 `df024af..813a86a`, 리뷰 `28ea489`.
남은 주 정리 넷과 `lum_grow_site`에 증인을 만들었다. 모든 주 정리 53개에 증인이 있다.
`goval.py`(Go 값 검사)를 만들었다. `%w` 호출을 `FmtErrorfWC`로 옮겼다. 제한 없는 `FmtErrorfC`를 지웠다.
`joint_models`가 계약 10개를 한 Host·한 힙에서 만족한다.
B0에 레이블 불변식을 넣어 다시 쟀다: VC 20, 닫힘 3, 열림 17.
수치: 830 jobs, AXIOMS 1432/7334, 자기 시험 14, 부정 시험 14, 증인 파일 69, goval 위반 0.
자평은 "게이트 1 조건부 통과"였다.
astra 리뷰가 기각했다: SHash 검사가 문자열 안 주석에 뚫린다. 형식 상수 검사가 접미 식과 공백에 뚫린다. Scalars의 Go 객체는 16이 아니라 24바이트다. fmt 계약 범위, rodata 메시지, ListC 안쪽 리스트, 사후조건, 게이트 표. 필수 수정 8개.

## 6. 재증명 수정 2 (2026-11-06 06:51 – 08:33)

커밋 `28ea489..7152188`, 리뷰 `0ef30e3`.
필수 수정 8개 중 6개를 완료했다. #7(사후조건)은 부분이다.
(f)를 생성 원문 비교로, (g)를 역할 분류와 Go 파서(`golits.go`)로 바꿨다. (h) 런타임 데이터 검사를 더했다.
`layout.go`가 gc amd64 배치를 `layout.json`에 쓴다. goval이 크기·정렬·패딩·bool·겹침을 본다.
fmt를 `FmtErrorfWC`(`%w`)와 `FmtErrorfDWC`(`%d %w`)로 나눴다. `ConvT64C`에 상자 내용을 넣었다. ValidateBitlist 메시지를 rodata(`vblRO`)에 두었다.
새 거부 정리: `sc_reject_bool_main`, `bl_reject_invalid_main`. ListC 비어 있지 않은 원소 증인 6개. 조합 증인 WitLuComp, WitScComp.
ListC 원소 오프셋 순서 거부는 하지 않았다.
수치: 856 jobs, AXIOMS 1583/8028, 자기 시험 24, 부정 시험 16, 증인 파일 79, goval 79/0/2.
astra 리뷰: 역할 분류가 Host 바인더와 이름 가림을 구분하지 못한다. (h)가 접미 식과 다른 포인터 타입을 받는다. Go 파서가 지역 `fmt`를 표준 패키지로 본다. 오류 증인이 유효한 Go 오류 인터페이스가 아니다. 크기 정리 분류가 틀렸다(일곱은 메모리 동일성). Scalars·ListU64의 "타입 전체 완료"를 철회했다. 필수 수정 8개.
그 뒤 `DIRECTION.md`(`3548e9d`)가 (f)(g)(h)를 Lake `input_file`과 ELF 데이터 include로 바꾸기로 정했다.

## 7. 정리 (2026-11-06)

커밋 `3548e9d..`(이 세션).
코드·주석·보고서·아티팩트를 줄였다. 주 정리·증인·계약의 문장, 대상 Go 코드, ELF, link/out의 `.S`·objdump·nm, 부정 시험, 자기 시험은 바꾸지 않았다.
보고서 여섯을 `REPORT.md`(현재 상태)와 이 파일로 합쳤다. `COST.md`를 지웠다(평가 세션 비용은 1절).
게이트 표에 astra 수정 2 8절 정정을 반영했다.
