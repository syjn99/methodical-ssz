# 재증명 재검사 (Claude Fable 5.1), 2026-11-06 01:29–01:50

대상: `syjn99/ssz-fv-reprove` tip `440e079`(시작 `2d0150b`, 커밋 18개).
방법: 깨끗한 빌드, 공리 두 범위, 금지 전술, 링크 검사와 자기 시험, 부정 시험 전체 실행, Go 시험, 계약·전제의 모순 시도(Lean), 옛·새 기계어 비교.
스크립트 `verify-reprove.sh`, 로그 `verify-reprove.log`, Lean 파일 `ReviewReprove.lean`(오류 0).

## 1. 수치 재현 (보고서 0절과 비교)

| 항목 | 보고서 | 재검사 |
| --- | --- | --- |
| `lake clean && lake build` | 804 jobs 성공 | 성공, 3분 34초, 최대 254 MB |
| `AXIOMS.txt` | TOTAL 1296 NONSTANDARD 0 | 같음. 커밋본과 바이트 동일 |
| `AXIOMS-ALL.txt` | TOTAL 6648 NONSTANDARD 0 | 같음. 커밋본과 동일 |
| `sorry`/`admit`/`native_decide`/`bv_decide`/`axiom` | 0 | 0 (주석 2줄만) |
| `link/check.py` | PASS (a)–(g) | PASS all, BUNDLE 3b9e61bf… |
| 자기 시험 | 10개 기대대로 | 10개 기대대로("주석에만 해시" 포함) |
| ELF sha256 | 9c850c97…c501 | 같음 |
| 부정 시험 | 10개 기대대로 | 10개 기대대로. 변이 8개가 지정 정리에서 실패, 대조군 PASS, `nopret`은 (d)에서 실패 |
| 고유 주 정리 `*_main` | 53 | 53 |
| 실행 증인 `*_runs` | 57 | 57(파일 56개, `Witness.lean`에 2개) |
| `go test ./fv/kraken/semtest/` | 언급 없음 | **FAIL 2개**(아래 3절) |

## 2. 모순 시도와 전제 만족 가능성 (`ReviewReprove.lean`)

모두 Lean으로 닫혔다(`lake env lean`, 오류 0).

1. `lum_grow_site`(증인 없음): 레지스터·예산 전제(`rdx = rcx + 4`, `rcx ≤ rdi < rdx`, `2·nextSliceCap + 8192 ≤ avail ≤ maxAlloc`)가 `rcx = rdi = 0, rdx = 4`에서 함께 성립한다.
2. `lc_accept_main`(증인 없음): 리스트 전제(`hgs`, `hend`, `hfirst`, `hparts`)가 빈 ListU64 하나(`tl = [4,0,0,0] ++ [4,0,0,0]`, T = 8)에서 함께 성립한다. `hnexts`는 공허하게 참. 전제 모순은 없다. 증인이 없는 이유는 비용이지 모순이 아니다.
3. `blValid` 경계를 EthLib `unpackDelimited (some 2048)`에 대해 확인: `[1]` 유효, `[0]`·`[]` 무효, 2047비트(256바이트, 마지막 255) 유효, 2048비트(257바이트, 마지막 1) 유효, 2049비트(마지막 3) 무효, 258바이트 무효. 보고서 R4·`bl_marshal_rejects_overlong`과 일치.
4. `ValidateBitlistC` 결론의 두 절(`rax = 0 ↔ blValid`, `¬blValid → rax = itab`)은 `itab ≠ 0`(`Regress.hit`)으로 양립한다.
5. `Joint S ty`(8계약 공동 만족) `not_joint_false` 재확인.

손으로 확인한 것:

- `bv_spec_accepts_iff`는 EthLib `deserialize bvDesc`(`bvDesc = .container ["j"] [.bitVector 4]`, Fv1)를 쓴다. 지역 재정의가 아니다.
- `blValid_iff`는 EthLib `unpackDelimited`를 직접 펼친다. `highestBit`는 256개 값 `decide`.
- 유도 명세 `VbvAccC`·`VbvPadC`는 `vbv_acc_holds`·`vbv_pad_holds`로 기계어 정리에서 나온다. 가정이 아니다.
- 증인 `WitBvR`은 `bv_reject_padding_main`을 그대로 적용하고 `vbv_pad_holds`(실제 코드)와 `rt_errorf_nil`·`bump_newobject16`을 한 Host에서 쓴다. `WitBl1/257`은 `bl_accept_main`을 `blValid_iff`로 얻은 전제와 함께 그대로 적용한다. `WitVbv`·`WitBv`·`WitBlR`·`WitLcE`도 주 정리를 약화 없이 적용한다.
- `ssz.ValidateBitvector.S`에 `bsr` 없음(0건). `ssz.ValidateBitlist.S`에만 있다.
- 옛 반례 정리 `bv_padding_counterexample`·`bl_marshal_overlong`은 코드에서 사라졌다(주석 언급만).

## 3. 발견

**F-1 (필수). `fv/kraken/semtest/f12_test.go`가 고친 생성기와 모순된다.**
`TestF1BitvectorPadding`은 "디코더가 0x10을 받는다", `TestF2BitlistByteLimit`은 "인코더가 258바이트를 받는다"를 단언한다. 둘 다 이제 실패한다(`F1 not reproduced: decoder rejects 0x10: J: bitvector padding bits are not zero`, `F2 not reproduced: encoder rejects: B: unexpected number of bytes, got 258 but found 257`). 보고서 8절 재현 목록에 `go test`가 없고, 보고서는 semtest를 언급하지 않는다. 고칠 것: 두 시험을 거부 단언으로 뒤집고(F1: 0x10 거부·0x0f 수용, F2: 258바이트 거부·257바이트 수용), 주석의 `bv_padding_counterexample`·`bl_marshal_overlong` 참조를 `bv_reject_padding_main`·`bl_marshal_overlong_rejected`로 바꾼다. 8절 재현에 `GOROOT=$(go env GOROOT) go test ./fv/kraken/semtest/`를 더한다.

**F-2 (경미). 보고서 수치는 모두 재현됐다.** 부정 시험 `bvnochk`의 재조준(이견 7)은 타당하다. 처음 변이가 수용 경로에도 있는 명령이었으므로 "지정 정리 밖에서 먼저 실패"가 맞다.

**F-3 (확인). R5 "G3는 기계어를 바꾸지 않았다".** ListU64·BitL·Nested·ListC 디코더의 옛(`f452384`)·새 `.S`를 비교했다. 명령어 수 175·124·142·395 같고 니모닉 순서가 같다. 차이는 `go_string._` 오프셋(+40)과 레지스터 이름뿐이다.

## 4. 판정 (Claude)

조건부. 게이트 1 미통과는 보고서의 자평과 같다. 남은 것은 보고서 0절 조건 1–5에 F-1을 더한 것이다.
astra 검토(`review-reprove-gpt6.md`) 뒤 확정한다.

## 5. astra 검토(02:04) 뒤 재현과 정정

astra 필수 발견 7개 중 기계적으로 재현할 수 있는 것을 사본(`scratchpad/linkmut`)에서 재현했다.

| astra 발견 | 재현 | 결과 |
| --- | --- | --- |
| 1. (f)가 SHash 정의 뒤의 식을 보지 않음 | `Fk.sHash` 정의 끝에 ` \|>.take 0` 추가 후 `check.py` | **PASS all**(번들 해시 불변). 재현됨 |
| 2. (g)가 `blFmtB`를 검사하지 않음 | `blFmtB` 첫 바이트 66→67 | **PASS all**. 재현됨. 대조군 `vbvFmt` 첫 바이트 변경은 (g) FAIL |
| 4. `WitBlR` 용량 0 < 길이 257 | `WitBlR.lean:105-107` 헤더 바이트 읽음 | cap 워드 `(0 : BitVec 64)`, len 257. 확인됨. 정리에 `len ≤ cap` 전제가 없어 증인은 전제를 정확히 만족하지만 Go 값이 아니다 |
| 5. semtest F1·F2 | 1절 F-1과 같음 | 같음 |
| 3·6·7 | 문서·범위 판단 | 동의. 특히 R5 문구: 니모닉 열은 같지만 피연산자·저장 순서는 다르다(ListC rdi/rbx 저장 순서, BitL 레지스터). 내 3절 F-3도 "니모닉 순서"까지만 확인한 것이므로 같은 정정을 받는다 |

정정: `ReviewReprove.lean` 48행의 `… → True` 예시는 아무것도 보이지 않는다(astra 지적). 4절의 양립성 근거는 49행 `hit`(itab ≠ 0)뿐이다.
또한 내 2절 1·2항은 수치·리스트 전제의 만족 가능성만 보인다. 전체 Host·메모리 전제를 한 상태에서 인스턴스화한 증인이 아니다.

## 6. 최종 판정 (Claude, astra 검토 반영)

조건부. 게이트 1 미통과(세션 자평·astra와 같음).
다음 세션(재증명 수정)에 넣을 것: astra 필수 수정 1–7(링크 검사 (f) 정의 전체 검사와 `.take 0` 자기 시험, (g)에 `blFmtB`, semtest 거부 단언, `WitBlR` 용량, 오류 인터페이스 적용 조건, CONTRACTS 오래된 행과 "1–7 처리" 문구, G3 문구와 B0 불변식) + 게이트 잔여 1–3(ListC 수용·마샬·크기와 Nested 크기와 `lum_grow_site` 증인, 빈·1·최대, Nested·Checkpoint·AttestationData 부정 시험).
