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

## 7. 정리 (2026-11-06 09:30 – 19:58)

커밋 `3548e9d..`(브랜치 `syjn99/ssz-fv-cleanup`).
코드·주석·보고서·아티팩트를 줄였다. 주 정리·증인·계약의 문장, 대상 Go 코드, ELF, link/out의 `.S`·objdump·nm, 부정 시험, 자기 시험은 바꾸지 않았다.

- 보고서 여섯을 `REPORT.md`(현재 상태)와 이 파일로 합쳤다. `COST.md`를 지웠다(평가 세션 비용은 1절). 게이트 표에 astra 수정 2 8절 정정을 반영했다.
- `review/`: 로그·json·txt·변이 사본 68개를 지웠다. 현재 서명으로 빌드되지 않는 회귀 블록과 파일 셋(`Review1b.lean`, `ReviewB0CountAstra.lean`, `ReviewFixB0CountAstra.lean`)을 지웠다. 남은 Lean 파일 11개는 오류 없이 돈다.
- 아티팩트: `link/out/raw/*.S` 30개(check.py가 읽지 않음), vcgen 로그 9개, `goval-result.txt`, `regress-fix2.log`, `link/out/SELFTEST`, `link/out/FUNCS.md`를 지우고 생성물을 `.gitignore`에 넣었다.
- 미사용 보조 정리 16개를 의존성 폐포로 찾아 지웠다: `bva_s40`, `bva_s48`, `bva_slot'`, `bva_nat`, `bva_rbx`, `bvm_o`, `bvm_one`, `bvr_a`, `bvr_sc`, `bvr_sc'`, `Fk.sep_drop`, `cpm_slot`, `Fk.spill_sep`, `f88`, `f120`, `Keep1.refl`. `rtvbl_16`은 rfl 보조정리라 남겼다.
- 증인 생성기: `wgen.py` 공통 함수와 표 `ALL` 하나로 74개 파일을 다시 만든다. 재생성 결과는 커밋된 파일과 바이트 단위로 같다. 생성기 없는 파일은 `WitAd`, `WitCp`, `WitCpM`, `WitFv`, `Witness`다. 증명 골격(`hk_*`, `hf_*`, 블록 분할)을 `WHost.lean`의 정리 넷과 매크로 `wit_split`으로 옮겼다.
- `Fk/*.lean` 주석에서 세션 표식과 과거 상태 문장을 지웠다. 파일 머리 docstring은 5줄 이하다.
- `fv/AGENTS.md`를 규칙만 남겨 76줄로 줄였다.

검사(기준선 → 정리 뒤):

| 검사 | 기준선 | 정리 뒤 |
| --- | --- | --- |
| `lake build` | 856 jobs | 856 jobs |
| AXIOMS 정리 | 1583, NONSTANDARD 0 | 1571, NONSTANDARD 0 (−16 삭제, +4 `WHost` 정리) |
| AXIOMS 모든 선언 | 8028, NONSTANDARD 0 | 7975, NONSTANDARD 0 (증인 골격 보조 선언 −26, 삭제 정리와 그 보조 선언 −27) |
| 링크 검사 | PASS | PASS. ELF sha256 `9c850c97…c501`, `norm/*.S`·objdump·nm·`Code.lean` 불변. BUNDLE은 `AXIOMS.txt` 변경으로 바뀐다 |
| 자기 시험 | 24 | 24 |
| 부정 시험 | 16 | 16 기대대로(대조군 PASS, 변이 15개 지정 정리에서 FAIL) |
| goval | 79/0/2 | 79/0/2 |
| `go test ./fv/kraken/semtest/` | ok | ok |
| `RegressFix2.lean`, 리뷰 Lean 파일 | 일부 실패 | 모두 오류 없음 |

크기(git이 추적하는 파일):

| 범위 | 파일 전 → 후 | 줄 전 → 후 | 용량 전 → 후 |
| --- | --- | --- | --- |
| `lean/Fk/*.lean` | 148 → 148 | 27,733 → 26,269 | 1,820K → 1,688K |
| 그중 `Wit*.lean` | 79 → 79 | 9,645 → 8,596 | 740K → 640K |
| `lean/tools/wit` | 34 → 31 | 3,679 → 3,164 | 304K → 244K |
| `link` 전체 | 72 → 40 | 33,812 → 27,326 | 3,820K → 3,588K |
| `review` | 96 → 23 | 10,612 → 3,857 | 948K → 304K |
| `vcgen`(`.lake` 제외) | 17 → 8 | 2,583 → 388 | 192K → 44K |
| 보고서 md | 11 → 6 | 2,267 → 586 | 244K → 68K |
| `fv/AGENTS.md` | 1 → 1 | 167 → 76 | 8K → 8K |
| `fv/kraken` 전체 | 434 → 311 | 85,757 → 66,598 | 7,712K → 6,372K |

## 8. 메모리 최적화 memopt (2026-11-09 20:31 – 21:27)

커밋 `86fd060..509faff`(브랜치 `syjn99/ssz-fv-memopt`). 보고서는 `memopt/REPORT.md`다.
9.69 GiB Linux 환경에서 `lake build`가 `Fk.WitLcM4x16`에서 OOM으로 실패했다.
원인은 `u64v0`–`u64v3`의 `by decide`다. elaboration이 `u64Bytes`를 계산하고, 네 증명이 동시에 돈다.
`wlcm.py`의 증명 한 줄을 `simp [u64Bytes, uintBytes]`로 바꾸고 증인 셋을 재생성했다. 명제는 바꾸지 않았다.
수치: `WitLcM4x16` 단독 peak 13.01–13.27 GiB → 1.42 GiB(macOS 48 GiB). 9.69 GiB 컨테이너에서 원본 단독은 OOM kill, 수정본 전체 빌드는 856 jobs 성공(`memory.peak` 7.41 GiB).
inspector diff는 `u64v` 공리 7줄(`propext`, `Quot.sound`)뿐이다. AXIOMS 1571/7975, NONSTANDARD 0. 회귀는 모두 성공했다.
판정은 "조건부"다. 사용자 머신 재현이 남았다.
독립 리뷰(gpt-6-astra, `253a84a`)도 조건부였다. 선언 290개의 `Expr.equal` 대조에서 assertion 약화는 없었다.
리뷰의 P1(8.2절 재현에서 캐시 재사용)과 P2 두 건(`run.sh` 종료 코드, `gen.py` 원본)은 브랜치 끝 커밋에서 고쳤다.

## 9. 수정 3 링크 재설계 (2026-11-09 15:15 – 17:25 UTC, fix3 스트림)

링크 검사의 Lean·Go 소스 정규식을 지우고 같은 보증을 Lake 입력과 ELF 데이터 include로 얻었다.
X1: `lakefile.toml`의 `Fk` `needs`에 `input_dir` 셋을 등록했다. 실험(대조군 Built 0, 1바이트 변경 시 `Fk.Code` 재빌드와 지정 정리 실패, 복원)을 거쳐 SHash와 검사 (f)를 지웠다.
X2: `link/data.py`와 `data_include`로 22개 항목을 include했다. 손 상수 12개를 바꾸고 검사 (g)(h)·역할 분류·`golits.go`를 지웠다. 새 검사 (f)는 데이터 파일 = ELF다. 자기 시험은 24개에서 10개다.
X3: `sc_reject_bool_err`(전제 `e0 ≠ 0`, 결론 rax ≠ 0)를 더했다. 증인 18개의 오류 전역을 초기화된 값으로, `%w` 증인 5개의 타입 기술자를 ELF 바이트로 바꿨다. goval이 둘을 검사한다.
X4: `sc_size_main` 메모리 동일, `sc_marshal_main` r14, `ne_marshal_main` R, ListC 죽은 스택 `lcStk`.
X5: 계약 `FmtErrorfDDC`·모델·`joint_models`(11개), 루프 보조 정리 `lcl_order`, 진입부터의 `lc_reject_offset_order_main`(첫 쌍), 증인 `WitLcO`, 부정 시험 lcorder와 대조군. 처음에는 비용 추정만으로 미루었다가 오케스트레이터 결정에 따라 했다. 원소 오류 전달("Items: %w")은 시작하지 않았다.
X6: 게이트 표 정정(크기 동일 여덟, BitVec makeslice, ListC 5/10(X5 뒤 6/10), 미검사 종류별 집계).
X7(최종 코드 `f45903c`): 차가운 프로젝트 빌드 863 jobs, 공리 1627/8287 NONSTANDARD 0, 검사 PASS, 자기 시험 10, 부정 시험 18, goval 80/0/2, go test PASS.
철회: `review/ReviewSHashFixAstra.lean`(대상 삭제), `bool_two_returns_nil` 예시(지적이 닫혀 `bool_two_returns_error`로 바꿈).

## 10. 수정 3 리뷰 반영 (2026-11-09 17:55 – 20:05 UTC, fix3 스트림)

리뷰 fix3-r1은 REQUEST_CHANGES(M1–M4)였다.
Stage A(`d9cdb40`, 리뷰 r2 APPROVE): `data.py`가 추적 파일과 같은 출력을 낸다(`# text` 줄 삭제, `data.py --check` 추가). REPORT 8절을 그대로 도는 블록으로 다시 썼다. 삭제로 닫은 astra 1–3의 신뢰 한계를 적었다. 두 읽기기의 줄 규칙을 맞췄다.
Stage B(M4): ListU64 짧은 입력 거부의 함수 명세(`LuURejShortC`, 기계어에서 유도), 원소 오류 전달 정리 `lcl_itemerr`·`lc_reject_item_main`, include 항목 `lcFmtItems`(API v3, 더하기만), 증인 `WitLcI`, 부정 시험 lcitems와 다시 빌드하는 대조군.
`WitLcI` 첫 빌드는 커널 OOM kill이었다. 그 뒤 RSS 감시(5 GiB)를 두고 진단했다: 마지막 정리의 `exact h`가 남은 `emp` 프레임 때문에 분리 논리곱을 정의상 펼쳤다. 두 번째 시도는 2.74 GiB로 빌드됐다.
리뷰 fix3-r3은 stage B(`f9e2bc3`)를 APPROVE했다. 판정은 조건부(게이트 1 미통과)로 남는다. 마지막 커밋은 문서만 고쳤다(수치, 메모리 전제, 알려진 한계).

## 11. 1c 생성기와 Prysm 목록 (2026-11-09 15:14 – 23:27 UTC, phase1c 스트림)

Prysm `ab15ff70`(slice + `ssz-size`)을 생성기 `698c202`로 다시 생성하고 Go 1.26.10으로 새 실험 ELF를 만들었다(P1, 목록 135개, 범위 안 132개).
고정 목록(정리 3676개 + 손 사례 134행)과 허용 가정 목록을 먼저 커밋했다. 독립 Desc 검사기는 리뷰 r1–r3에서 세 번 고쳤고 r3 뒤 설계를 닫힌 세계와 내용 결합 결과로 바꿨다(r4 승인).
fix3 승인 뒤 rebase 두 번. P7: 증인 생성기(76/76 바이트 같음, Go 값 Lean 술어). P8(X4): 손 사례 9개 타입의 손 주 정리 58개를 생성기로 다시 만들었다. Scalars·ListU64·ListC는 지시 걷기·루프 틀, 나머지 여섯은 손 모듈에서 읽는 고정 틀이다. 모두 문장 SAME, Lean 통과, 공리 표준만, 변이가 지정 정리 안에서 실패했다. 생성 증명의 88–100%는 손 증명과 같은 글이다.
X5: Go 1.26.10 링크 표 (a)–(f) PASS. Prysm 132개 타입 중 46개의 size만 증명됐다. 디코더·인코더는 틀이 맞지 않아 모두 거부됐다(손 작성 primitives 호출 2, 틀 없음 132).
X6: `conv.py --norm`의 `%riz` 규칙(Go 1.26.3 번들 그대로), `check.py`의 10바이트 명령어 읽기 결함 수정, 이 보고서 10절.
리뷰: phase1c-r1…r7(r4 이후 모두 APPROVE, 권장 수정 반영). 메모리: 모든 Lean 작업은 gate + 메모리 캡, 커널 OOM 0.

## 12. 실제 Prysm Checkpoint 종단 증명 (2026-11-10 01:17 – 02:40 UTC, prysm-e2e 스트림)

phase1c 체크포인트 `6e82ae24` 위에서 새 Lean 라이브러리 `E2e`와 이름공간 `prysm/go1.26.10/e2e/`를 만들었다.
호출 그래프와 `-m=2` 근거로 Epoch 메서드의 인라인 여부를 확정했다. 링크 표 7개 함수, 데이터 항목 10개, 검사 (a)–(f) PASS.
consensus-specs에서 손 Desc를 쓰고 검사기 Desc와 맞췄다. Go 1.26.10 런타임 소스를 다시 읽었다(바뀐 계약 없음, 계획서의 growslice 변경 기술은 `moveSliceNoCap`의 변경이었다).
Epoch 디코더 수용을 함수 명세로 증명하고 Checkpoint 디코더 수용·크기 거부·도달 불가 경로·명세 정렬, 인코더 빠른 경로, 합성을 증명했다.
디코더 정리는 6 GiB 프로세스 상한에서 두 번 죽었다(커널 OOM 아님). 마지막 레지스터 목표의 `trivial`/`rfl`이 원인이었다. 정리를 둘로 나누고 닫는 전술을 바꿨다.
부정 시험 30/30, 공리 23개 표준, Go 차분 47건 일치. 인코더 거부, growslice 경로, Epoch 거부는 하지 않았다.
리뷰 e2e-r1(9bad532)은 합성 정리가 디코더를 실행하지 않음을 찾았다(M1, FINDINGS R-1). 이름을 `cp_e2e_marshal_decoded_receiver`로 바꾸고 E5를 미완료로 고쳤다. INBOX 004에서 인코더 거부, 인코더 명세 정렬, 증인 있는 size, Epoch 거부, Go 값 술어를 증명했다.
세션 2에서 M1의 진짜 합성 `cp_e2e_unmarshal_then_marshal`(디코더 진입 → 인코더 반환, 출력 = dst ++ 입력 40바이트)과 한 Host 증인 `WitCpC`를 증명했다(첫 시도, 증인은 구문 수정 1회). 부정 시험 11/11. 이어서 인코더 growslice 경로 `cp_e2e_marshal_grow_main`(첫 지점, `GrowsliceC` esz 1)과 증인 `WitCpG`(len 30, cap 36)를 증명했다(정리 4회 실행: 길이 부등식의 UInt64/BitVec 형태, 탐침 1회; 증인 첫 시도). 부정 시험 9/9. 리뷰 S1–S9를 처리했다(S2는 문구 유지). 전체 부정 시험 73/73(사례별 900초 제한), 공리 49개 표준, Go 차분 48건 불일치 0.

2026-11-10 prysm-e2e 세션 4: A3(실제 AttestationData 디코더 수용, 크기 거부, 도달 불가 래핑 4개, 명세 정렬, 증인)을 `8cba8b4`로 증명했다. 그 뒤 INBOX 009에 따라 A4를 멈추고 Checkpoint 인코더의 남은 용량 경우를 증명했다: 첫 지점이 맞고 둘째가 자라는 경우, 첫 지점이 자라는 모든 경우(둘째 growslice 호출 진입까지), growslice 뒤 거부, 경우 덮기 두 개. 첫 성장 뒤 둘째 성장의 나머지 실행은 `GrowsliceC` 형식이 두 호출을 잇지 못해서 막혔다(T-7, OUTBOX 007). 기존 정리 문장은 바꾸지 않았다.

2026-11-10 prysm-e2e 세션 5 (INBOX 010, 리뷰 e2e-r3 REQUEST_CHANGES 처리): M1 `cp_e2e_marshal_grow_any_sharp`(첫 성장 뒤: 반환, 둘째 growslice를 지나 반환, 또는 남은 힙이 예산보다 작은 둘째 호출 진입), M2 프레임을 적은 덮기 정리 2개와 증인 `WitCpWF`·`WitCpWRF`, S1 `GoValW`, S3–S6 기록 수정, FINDINGS 역사 색인, 확장성 단계 S0 기준선(`scal/BASELINE.json`)을 커밋했다. 기존 정리 문장은 바꾸지 않았다. T-7의 남은 영역은 사용자 결정 전까지 막힘(차분만)이다. S2는 부분 수행이다. A4와 S1 단계는 시작하지 않았다.

2026-11-10 prysm-e2e 세션 10 (INBOX 020, 리뷰 s4-r1 APPROVE 뒤): S1–S6 문서 수정과 NF-12 부정 시험 4건을 더했다. BeaconBlockHeader 디코더의 오류 감싸기 두 곳 도달 불가와 ValidatorIndex 길이 거부를 증명했다. BeaconBlockHeader 인코더 빠른 경로는 구간 A의 메모리 사후조건을 닫지 못했다. 시도 3회 한도에서 멈췄다(T-9, memcap 종료 4회).

2026-11-11 prysm-e2e 세션 11 (INBOX 021, 리뷰 s5-r1 APPROVE 뒤): S1–S5 기록 수정과 NF-13…NF-15를 더했다. T-9를 진단했다. memcap 종료의 원인은 Lean 커널의 메모리였다. 구간 A를 A0(스택 가드), A1, A2로 나누자 A1, A2, 합성에서 커널 메모리 실패가 없었다(세션 12 정정: 닫혔다고 적었지만 `sorryAx`에 의존했다). A0의 커널 검사는 한도 안에서 닫지 못했다. T9-PLAN 한도(시도 6회)에서 멈췄다.

2026-11-11 prysm-e2e 세션 12 (INBOX 022, 리뷰 s6-r1 REQUEST_CHANGES 처리): 기록만 고쳤다. Lean 파일은 바꾸지 않았다. 세션 11의 "A1, A2, 합성이 닫혔다"는 틀렸다. 리뷰의 `#print axioms` 실행에서 셋 다 `sorryAx`에 의존했고, 합성은 커널이 거부한 A0 변형에도 의존했다. 커널 메모리 장애가 A0에 있다는 위치는 유효하다. §12 첫 단락, 세션 4, 세션 10 항목의 "도달 불가" 증명은 조건부 건너뜀이다. 모든 입력에서의 도달 불가는 호출 대상 명세와 함께일 때만 성립한다(NF-15). FINDINGS에 과정 규칙 P-1(임시 결과의 닫힘은 `#print axioms`로 판정)과 P-2(작업 명령은 Lean 종료 코드로 끝남)를 더했다.

2026-11-11 prysm-e2e 세션 13 (INBOX 023, 홀드아웃 H2 평가): `7a5ea61`에서 `v1alpha1.Eth1Data`를 열었다. 고정 생성기 `p2dec`의 한 번 실행은 종료 2로 출력 없이 멈췄다(SG-1, 오프셋 0의 DepositRoot). 생성기 적용 범위는 0/2 필드다. 디코더 수용, 크기 거부, 명세 정렬, 코덱 동등, 증인을 손으로 증명했다(공리 표준). 인코더는 T-9와 같은 스택 가드 머리라서 시도하지 않았다. 생성기, 종류, 보조정리, 템플릿은 바꾸지 않았다. 이 세션은 `REPORT.md`를 고치지 않았다.

2026-11-11 prysm-e2e 세션 14 (INBOX 024, 리뷰 h2-r1 REQUEST_CHANGES 처리): 기록만 고쳤다. Lean 파일은 바꾸지 않았다. `REPORT.md` 11절의 "H2를 열지 않았다"를 지우고 H2 결과와 한계를 더했다(M1). `CONTAMINATION.md` 7절, FINDINGS SG-1, `RESULT.json`을 고쳤다(S1–S3). 부정 시험 2건을 더했다(S6, 27/27).

2026-11-11 T-9 스트림 (사용자 지시, 새 예산; 기준 `48b74b6`, 브랜치 `claude/ssz-fv-t9-fable`): 새 Fable 세션이 증명을 직접 썼다. 진단 1회로 원인을 정했다. 스택 가드 분기를 `simp`와 `omega`로 닫은 증명은 5 GiB 한도 아래에서 커널 검사에 실패한다. 기계 문맥이 없는 `BitVec` 명제에서도 같다. 비용이 큰 부분 항은 프로파일하지 않았다. 리터럴 2^64 − 32가 원인이라는 것은 추론이다(리뷰 t9-r1 문구). 보조정리 `E2eScal.lea_cmp_be_false`(변경 없는 `Fk.cmp_be_false` 위)로 닫았다. 여섯 구간과 합성으로 `bh_e2e_marshal_main`(빠른 경로만)을 증명했다. 증인, 명세 정렬, 부정 시험 36건, Go 차분 21건, 공리 게이트를 더했다. 시도 5회(실패 2회: 반환 주소 식의 범위 가정 누락, 명세 따름정리의 `⋆` 결합 방향과 import 누락). `Fk/*`, 계약, 생성기, 종류, 템플릿, ELF, 도구 체인은 바꾸지 않았다. growslice 분기와 길이 거부는 범위 밖이다. 독립 리뷰는 아직 없다.

2026-11-11 SG-1 스트림 (사용자 지시; 기준 `48b74b6`, 브랜치 `claude/ssz-fv-sg1`): 두 홀드아웃을 연 뒤의 개발 작업이다. 오프셋 0 디코드 구간의 템플릿 `rootdec_seg_z`와 종류 `rootDecSegZKind`를 더했다. `scalgen.py p2dec`가 오프셋 0 꼴을 받게 했다. 확장된 생성기는 Eth1Data 루트 필드 2개 중 2개를 낸다(`GenE1Dec.lean`). Eth1Data는 이 확장의 개발 자료이고 표본 안이다. 확장 전 H2 결과(고정 생성기, 종료 2, 0/2 필드)는 역사적 결과로 남는다. H1과 H2의 결과는 바뀌지 않았다. 리뷰 sg1-r1이 `da3f233`을 승인했다.

2026-11-11 prysm-e2e 세션 15 (INBOX 027, 통합): T9 스트림(`154944e`)과 SG1 스트림(`da3f233`)을 `--no-ff`로 병합했다(`e56063c`, `63ef3b9`). 충돌은 두 스트림이 고친 기록과 목록에만 있었다. 두 쪽을 모두 남겼다. Lean, 생성기, 시험 파일은 각 스트림의 바이트와 같다. 병합 트리에서 빌드, 공리 게이트, 세 갈래 선언 비교, 재생성 검사, 종류 검사, 두 스트림의 부정 시험을 다시 돌렸다. 리뷰 t9-r1, sg1-r1, h2-r2의 고칠 항목을 기록과 시험에 반영했다. 독립 리뷰는 아직 없다.

2026-11-11 기준 기록 단위 (리뷰 int-r1 고칠 항목 R1–R5): 날짜가 있는 이전 단락은 고치지 않고 정정을 더한다.
T9 스트림은 리뷰를 받았다(t9-r1 승인, `154944e`).
통합도 리뷰를 받았다(int-r1 승인, `c3c56a1`).
T9 스트림 단락과 세션 15 단락의 "독립 리뷰는 아직 없다"는 이 점에서만 대체된다.
`scal/RESULT.json`의 H1 시점과 H2 시점 문장에 "역사적" 표시를 더했다. 수치는 바꾸지 않았다.
`StackGuard.lean` 설명문을 기록된 원인으로 고쳤다. 정리와 증명은 바꾸지 않았다.
다른 기계로 옮길 기준 문서 `prysm/BASELINE.md`를 더했다.

2026-11-11 ENC 스트림 (사용자 지시; 기준 `dda707c`, 브랜치 `claude/ssz-fv-enc-reuse`): 새 Fable 5.2 세션이 직접 작성했다.
재사용 블록 `E2eScal.enc32_call`(memmove 호출)과 `E2eScal.enc_reject_tail`(길이 거부 꼬리)을 더했다.
BeaconBlockHeader 루트 블록 세 개를 `enc32_call`로 다시 증명했다. 문장은 기존과 `rfl`로 같다. 기존 모듈은 고치지 않았다.
`Eth1Data.MarshalSSZTo`의 빠른 경로, 명세 따름정리, 증인을 증명했다.
BeaconBlockHeader 길이 거부 세 곳과 증인을 증명했다. 전제는 `len + 112 ≤ cap`이다.
여러 지시어의 인코드 템플릿은 자리 6곳에 공통으로 맞지 않는다(FINDINGS ENC-1). 호출 앞 구간은 자리마다 손으로 밟았다.
시도 10회(실패 4회), 진단 3회, gate 646초다. 첫 작업에서 옮겨 온 `.lake`의 두 모듈이 낡아서 `lake build E2eScal`을 한 번 돌렸다. `P2EncCp`는 다시 빌드되지 않았다.
gate는 스트림 이름 `enc`를 받지 않았다. 작업은 스트림 `prysm-e2e`와 표지 `enc:`로 돌렸다.
부정 시험은 33건 중 32건이 설계대로다. 1건은 작성자가 대상 정리를 잘못 지정했고 통과로 세지 않는다.
공리 게이트는 PASS다(선언 3813개). 선언 차이는 ADDED 330, CHANGED 0, REMOVED 0이다.
증명하지 않은 것: growslice 분기, morestack 경로, 용량이 작은 길이 거부, Eth1Data 길이 거부, Go 값 술어.
독립 리뷰는 아직 없다. 원격에 쓰지 않았다.
