# ATTEMPTS: LV 시도 기록

한 줄에 한 사실을 적는다.
시도 한도는 의무 하나당 3회다.
명령과 종료 코드의 표는 `STEPS.tsv`에 있다. 로그는 로컬 작업 디렉터리의 `logs/`에 있고 커밋하지 않는다.

## 환경 (U1 시작 시)

- 호스트: darwin/arm64. x86-64 기계어는 실행하지 않는다.
- ELF는 계획 담당이 Docker(linux/arm64)에서 다시 만들었다. sha256 `c6403c02…911e`, build ID, objdump·nm sha256이 `build-ids.txt`와 같다.
- 무거운 작업 게이트: 작업 지시가 정한 `heavy.py`(잠금, 로그, 상한 40960 MB, 시간 상한).
- 레포의 `gen/tools/memcap.py`는 `/proc`가 필요하다. macOS에는 없어서 쓰지 않았다.
- `link/check.py`는 LLVM 도구를 `shutil.which`로 찾고 없으면 `xcrun --find`로 찾는다.
- 이 장비의 `llvm-objdump`와 `clang`은 Xcode의 Apple LLVM 21.0.0이다. 이전 실행의 LLVM과 판이 다를 수 있다.

## U1 링크

- `lvlink.py callgraph`: 세 함수(T1, T2, T3), 분류 안 된 호출 0, 빠진 함수 0. 결과 `lv/callgraph.json`.
- 생산자 `Desc` 출력: 세 v1alpha1 파일의 sha256이 `gen/desc/results/main.result.json`의 기록과 같다. 결과 `lv/desc/`.
- 세 함수 링크, 시도 1(로그 05): `conv.py`가 exit 1로 끝났다. 출력 디렉터리 `norm/`이 없었다. 설정 실수다(wrong-target).
- 세 함수 링크, 시도 2(로그 06–08): `conv.py` exit 0. 새 `.S` 셋은 계획 담당의 scratch 사본과 바이트가 같다.
- 같은 시도의 `check.py`는 exit 1이다. (a), (b), (c), (e), (f)는 PASS다.
- 실패는 (d)다. clang이 T3 `.S` 19행 `lea 0xffffff1c(%rdi),%rdx`를 거부했다.
- clang 오류: `displacement 4294967068 is not within [-2147483648, 2147483647]`.
- 그 피연산자는 GNU objdump가 변위 −228을 32비트 부호 없는 수로 쓴 것이다.
- 다른 커밋된 `.S`(e2e, ad, h4, Go 1.26.3)에는 이런 변위가 없다(`grep 0xffffff`).
- 원인 분류: 도구 빈틈. `conv.py`의 변위 표기와 이 장비의 Apple clang 21.0.0이 맞지 않는다.
- 이전 링크 검사가 쓴 LLVM 판은 확인하지 않았다.
- Kraken이 이 피연산자를 −228로 읽는지 4294967068로 읽는지 확인하지 않았다. T3 증명 전에 확인해야 한다.
- 결정: 커밋하는 링크 셋은 T1, T2뿐이다. `lvlink.py`에 `--t3` 선택을 두었다.
- T1·T2 링크(로그 09–12): filter, conv, data, check 모두 exit 0. `lv/link/RESULT`의 끝은 `PASS all`이다.
- 묶음 해시: `BUNDLE sha256 5c1666068e5d37550b3ac967e27d22c2038814a4163ee6a234cec3075a5e744f`.
- (d)의 DIFF 6줄은 모두 padding(`nop` 정규화)이다. 그 밖의 차이는 0이다.
- `lvSliceType.data`의 abi.Type: Size_ = 24, Kind_ = 23(slice). 바이트를 직접 읽어 확인했다.

## U3 문장

- 손 `Desc`(`E2eList/Desc.lean`)를 쓴 뒤에 생산자 `Desc`를 출력했다. 두 term은 필드 이름만 다르다.
- 작업 지시가 본으로 든 `E2eScal.H5.sm_accept_stmt`는 레포에 없다(`git grep` 결과 0). 대신 `E2eScal.H4.dd_accept_stmt`를 본으로 썼다.
- `lakefile.toml`에는 `input_dir` 둘(`lv_norm_S`, `lv_data`)과 `lean_lib` `E2eList`만 덧붙였다. 기존 항목은 바꾸지 않았다.
- 새 데이터 읽개 `lv_data_include`(`E2eList/Include.lean`)는 `E2e/Include.lean`의 글이다. `gen/e2e/lvcheck_include.py`가 SAME 넷, exit 0을 냈다.
- 문장 모듈 빌드(로그 13, 14): `E2eList.StmtSa` exit 0, 12.5 s, `E2eList.StmtSc` exit 0, 8.3 s. 오류 0이다.
- `E2eList` 모듈의 경고는 쓰지 않은 변수 이름 린터와 `module` 권고뿐이다. 문장은 증명이 없는 `def … : Prop`이라 이름이 쓰이지 않는다.
- `lake build --no-build E2e E2eAd E2eScal E2eList.StmtSa E2eList.StmtSc`(로그 15): exit 0, `All targets up-to-date (998 jobs)`.
- `E2eList/*.lean`에 `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, `maxHeartbeats`, `maxRecDepth`가 없다(`grep` exit 1).
- 측정 방법: `heavy.py`의 벽시계와 1초 표본 RSS 합. n = 1.

## 증명 단위

### T1 크기 거부 `sa_e2e_reject_size_main : sa_reject_size_stmt`

- 시도 1(로그 16): exit 0. `DdReject.lean`의 증명 글에 지시어 번호(88–93)만 바꿨다.
- `maxHeartbeats`, `maxRecDepth` 설정 없이 통과했다. 본의 `set_option`은 옮기지 않았다.

### T2 크기 거부 `sc_e2e_reject_size_main : sc_reject_size_stmt`

- 시도 1(로그 17): exit 0. 지시어 번호(30–35)와 틀 크기 48(`sub $0x30`)만 바꿨다. 설정 없이 통과했다.

### T1 구간 보조정리 `E2eList.Seg`

- 시도 1(로그 18): exit 0. `bytesdec_seg_z64`(SegN의 지역 매크로 글, n = 64)와 `bytes96dec_seg_nop`(`DdSegNop` 글, 32 → 96).
- 본의 `set_option maxHeartbeats 16000000`/`4000000`을 옮기지 않았다. 기본 한도에서 통과했다.

### T1 수용 `sa_e2e_accept_main : sa_accept_stmt`

- 시도 1(로그 20): exit 1. 마지막 `ecancel`이 실패했다.
- 원인: `bytesdec_seg_z64`의 사후조건은 `Int.toBytes 8 (OfNat.ofNat n)` 꼴이다. 문장의 `Int.toBytes 8 64`와 구문이 다르다.
- 고침: 생성된 `Gen.dd_g2dec_PublicKey_seg`처럼 크기 64를 글자로 쓴 감싼 보조정리 `sa_bits_seg`를 더했다. 증명은 `with_reducible exact bytesdec_seg_z64 64 rfl …`이다.
- 시도 2(로그 21): exit 0. 설정 없이 통과했다.

### T1 명세 다리 `E2eList.SaSpec`와 명세 정리 셋 `SaSpecK`

- 시도 1(로그 22): exit 1. `psa_serialize`에 목표 `64 + z.size < 4294967296`가 남았다. 둘째 `simp`에 `hz`가 없었다.
- 시도 2(로그 23): exit 0. 둘째 `simp`에 `hz`를 더했다.
- EthLib의 `packBits_unpackBits`(패딩 전제는 512 = 8·64라 비어 있다)와 `unpackBits_packBits`를 그대로 썼다.
- `SaSpecK`(로그 24): `sa_e2e_accept_spec_k`, `sa_e2e_reject_size_spec`, `sa_e2e_reject_complete`. 시도 1에 exit 0.

### T1 손 `Desc` = 생산자 `Desc` (판정 1)

- 새 스크립트 `gen/e2e/lvdescterm.py`가 `lv/desc/`의 생산자 파일을 Lean으로 옮긴다(`SaSpecChecker.lean`, `ScSpecChecker.lean`).
- `SaDescEq.lean`(로그 25): `prysmSaDesc_checker`(이름만 다름, `rfl`), `prysmSaDesc_deserialize_checker`(받는 입력과 값이 같다). 시도 1에 exit 0. 커널 검사(K)다.

### T1 증인 `WitSaA.sa_accept_runs`

- 시도 1(로그 26): exit 1. `whnf`에서 기본 한도 200000 heartbeats를 넘었다.
- 프로파일(로그 27, scratch 사본, `profiler true`, 한도를 올려 끝까지 돌렸다): `simp` 둘이 7.03 s와 2.08 s다. 선언의 `simp` 합은 9.16 s다.
- 원인: 메모리 전제를 닫는 `simp`가 조각 22개짜리 분리 논리식을 `sep_comm`, `sep_comm_l`로 정렬한다.
- 조치: `set_option maxHeartbeats 16000000 in`을 `sa_accept_runs` 한 선언에만 둔다. 값은 본 증인 `WitDdA.dd_accept_runs`와 같다. 이전 값은 기본 200000이다.
- 시도 2(로그 28): exit 0. 입력 셋(0, 대표값, 0xff)에 대한 `example` 셋도 통과했다.

### 시도의 셈 (판단)

- 한 시도는 한 증명 전략이다. 같은 전략 안에서 오류 메시지를 보고 고친 빌드는 같은 시도의 개발 단계로 센다.
- 그래서 빌드 로그 수와 시도 수는 다르다. 모든 빌드는 `STEPS.tsv`에 있다.
- 증명 중간 목표를 볼 때 `sorry`를 쓰지 않았다. 증명을 덜 끝낸 채 빌드하고 오류의 미해결 목표를 읽었다.

### T2 루프 보조 `E2eList.ScLemmas`

- 로그 29–31: exit 1, 1, 0. 원인 1: `⋆`는 왼쪽 결합이라 `sep_assoc` 정리가 끝에 필요했다. 원인 2: `simp`가 `take ++ getElem :: drop`을 다시 `pks`로 접었다. `rw [List.flatten_append, List.flatten_cons]`로 바꿨다.

### T2 한 바퀴 `sc_iter`와 루프 `sc_loop`, `sc_exit` (시도 1)

- 로그 32–40: 한 전략(불변식 `ScInv i`, DESIGN 4.1)의 개발 단계다. 로그 40에서 `sc_iter`가 exit 0이 됐다.
- 막힌 곳 1(로그 35–36): memmove 전제의 `ecancel` 실패. 원인: `pks[i]`의 경계 증명 항이 두 곳에서 구문이 달랐다. `generalize hE : pks[i] = e`로 고쳤다.
- 막힌 곳 2(로그 38–39): 경계 검사 가지. `Int.ofBytes (Int.toBytes 8 512) = 512`를 `decide`로 넣고 `omega`로 닫았다.
- `runtime.panicBounds` 가지(지시어 63 `jae`)는 매 바퀴 증명으로 막았다. 전제로 막지 않았다(판정 7).
- 로그 41–42: `sc_exit`, `sc_loop`(j에 대한 귀납). `eventually_mono` 이름이 없어서 `eventually_trans`와 `Eventually.done`으로 바꿨다. exit 0.
- 설정(`maxHeartbeats`, `maxRecDepth`) 없이 통과했다.

### T2 수용 `sc_e2e_accept_main : sc_accept_stmt` (시도 1)

- 로그 43: `sc_agg_seg`(크기 48을 글자로 쓴 `bytesdec_seg 48` 감쌈, src 24576). exit 0.
- 로그 44–52: 머리(손 단계), 루프, AggregatePubkey, 포인터 꼬리, 꼬리(손 단계)의 개발 단계다. 로그 52에서 exit 0.
- 막힌 곳: `bv_omega`/`kaddr`가 `Width.W64.bits`를 풀지 못했다. `Width.bits`를 넣은 `laddr` 매크로를 썼다.
- 막힌 곳: `MakesliceC`의 `rbx ≤ cnt`에 `decide`를 쓰면 기대형에 자유 변수가 있다고 거부된다. `Nat.le_refl _`로 닫았다.
- 설정 없이 통과했다. `#print axioms`(로그 53): `sc_iter`, `sc_loop`, `sc_e2e_accept_main` 모두 `[propext, Classical.choice, Quot.sound]`.

### T2 명세 다리 `E2eList.ScSpec`와 명세 정리 셋 `ScSpecK`, `Desc` 같음 `ScDescEq`

- Vector[Bytes48, 512]는 원소마다 펼치지 않는다. 48바이트 벡터의 임의 목록에 대한 보조정리(`serializeEach_bv48`, `assemble_inline_ok`, `concatParts_v48`)를 썼다.
- EthLib의 `headOf_inline`, `bodiesOf_inline`, `concatParts_size`, `concat_fixed_slices`를 그대로 썼다.
- 시도 1(로그 54–56): 개발 단계 셋. 원인: `serializeEach`, `Value.allFit`의 빈 목록 경우가 `rfl`로 줄지 않았다. 덩어리 크기 증명에 `i < 512`가 없었다(`toV48`로 바꾸고 `List.map_congr_left`로 경계를 넣었다). 로그 56에서 exit 0.
- `ScSpecK`, `ScDescEq`(로그 57): 시도 1에 exit 0.

### T2 증인 모델 `E2eList.BumpT` (판정 2)

- 한 Host에는 `runtime.makeslice`가 하나뿐이다. T2 증인에는 `MakesliceC … lvSliceType_addr 24 S`와 `MakesliceC … e2eU8Type_addr 1 S`가 함께 필요하다.
- 그래서 esz 24만의 모델(`bump_makeslice` 꼴)은 `bump_makeslice1`과 한 Host에 둘 수 없다.
- 조치: `BumpAllocT.S`는 `BumpAlloc1.S`에 형식 단어 비교 하나를 더했다. rax가 `type__+337600`이면 24·cnt, 아니면 cnt를 민다.
- 정리 둘: `bump_makeslice_t24`(esz 24), `bump_makeslice_t1`(형식 단어가 `lvSliceType_addr`가 아니면 esz 1). 증명 글은 `bump_makeslice1`이다.
- 시도 1(로그 58–62): 개발 단계. 원인: 분기 조건의 `omega`가 레이블 산술을 풀지 못했다. `BitVec.sub_add_cancel`과 `BitVec.sub_self`로 닫았다. 로그 62에서 exit 0.
- 이 모델은 비공허성 근거일 뿐이다. Go `makeslice`는 `et.Size_`를 읽는다. 이 모델은 주소 하나와 비교한다.

### T2 증인 `WitScA.sc_accept_runs`

- 시도 1(로그 63): `u8_ne_slice`의 보조 이름이 없었다(`BitVec.add_sub_cancel_left`). 로그 64: `bv_omega`로 바꿔 exit 0. 증인 본문은 첫 빌드부터 통과했다.
- `maxHeartbeats 16000000`을 이 선언 하나에만 둔다. 설정 없는 scratch 사본(로그 65)은 `whnf`에서 기본 한도를 넘었다(`simp` 2.3 s 뒤). 원인은 T1 증인과 같다(로그 27).
- 입력 셋(0, 대표값, 0xff)의 `example` 셋이 통과했다. 각 입력은 48바이트 덩어리 512개다.

## 검증 (작업 지시 6절)

- 전체 빌드(로그 67): `lake build E2eList` exit 0, 682 jobs. `--no-build E2e E2eAd E2eScal E2eList`(로그 68): exit 0, `All targets up-to-date (1035 jobs)`.
- 공리 게이트(로그 69): 새 파일 `gen/e2e/lvaxioms_gate.py`(기존 `axioms_gate.py`를 import, ROOTS에 `E2eList`, 손 목록에 `gen/e2e/AxiomsLv.lean`). PASS, 선언 5632, 정리 4684, 손 목록 462, 비표준 0, `sorryAx` 0. 결과 `lv/axioms-gate-lv.json`. 기존 `axioms-gate.json`은 덮어쓰지 않았다.
- 공리 게이트 대조군(로그 79–82): 저장소 밖 scratch 모듈 `E2eList.Planted`(`sorry` 정리 하나)를 넣었다. FAIL, `sorryAx ['E2eList.Planted.planted_sorry']`. 결과 `lv/axioms-gate-lv-plant.json`. 넣은 `.olean`은 바로 지웠다.
- 로그 79: `lake env lean -o`가 exit 1. 원인: 원천 파일이 루트 디렉터리 밖이다(wrong-target). 로그 81에서 `--root`를 주어 다시 했다.
- 로그 80: exit 2. 원인: 첫 `LEAN_PATH` 항목에 `E2eList` 디렉터리가 있으면 Lean이 다른 `E2eList` 모듈도 거기서 찾는다(wrong-target). 로그 82에서 빈 경로와 빌드 디렉터리 안의 임시 `.olean`으로 다시 했다.
- 선언 drift: 기준 `6a78c591…`을 `git archive`로 scratch에 풀고 현재 `.lake`를 복제(APFS clone)했다. 기준 트리의 `--no-build E2e E2eAd E2eScal`이 exit 0이었다(로그 70).
- 한계: 기준의 `.olean`은 기준 트리에서 따로 만든 것이 아니다. Lake 추적이 원천과 입력이 같다고 판단한 것이다.
- 로그 72: `decl_drift.py`가 exit 2로 거부했다(덤프의 roots가 다르다). 로그 73–74: 같은 roots(E2e, E2eAd, E2eScal)로 현재 트리를 다시 덤프했다. drift 0, base 5007 = head 5007.
- `E2eList` 선언은 새 root라서 drift 비교 밖이다. (리뷰 r1 S3로 아래 줄을 고쳤다. 처음 쓴 "622"는 틀린 셈이었다.)
- 다시 센 값(로그 69의 덤프와 기준 덤프의 이름 비교): 새 줄 625개, 기준에서 사라진 줄 0개. 625개 중 434개가 `E2eList.`로 시작한다. 623개가 이름에 `E2eList`를 가진다(`_private.E2eList.…`, `_aux_E2eList_…` 포함).
- 나머지 2개는 `E2e.Data.e2eU8Type_addr.eq_1`과 `commandLv_data_include_`다. 앞의 것은 `E2eList` 모듈(`WitScA.u8_ne_slice`의 `simp only [E2e.Data.e2eU8Type_addr]`)이 `E2e.Data` 이름공간에 자동으로 만든 등식 보조정리다. 뒤의 것은 새 명령 `lv_data_include`의 구문 종류 이름이다. 둘 다 추가다. 기존 선언을 바꾸지 않는다.
- drift 대조군(로그 75–78): scratch 기준 사본의 `E2eScal.WitBhU.s0`에 `0 + 0`을 심었다. drift exit 1, `CHANGED E2eScal.WitBhU.s0 value`. 파일을 되돌리고 그 모듈을 다시 빌드했다.
- 스킬 `SKILL.md`는 "`decl_dump.lean`의 Kraken 트리 첫 실행은 따로 게이트된 단위"라고 적는다. 이 실행이 그 첫 실행이다. 대조군으로 검사가 실패할 수 있음을 보였다.
- 부정 시험(로그 83–84): 새 파일 `gen/e2e/lvnegative.py`(기존 `negative.py`를 import; 문장 모듈을 펼쳐 넣고, memcap 없이 프로세스 그룹으로 시간 제한). 경우 `lv/negcases-lv.json`, 결과 `lv/negative-lv.json`.
- 결과: 18개 중 17개 통과(control_pass 4, inside 13). `lv-sa-bitslen63`은 outside다. 오류가 주 정리 앞의 `sa_bits_seg`에 있다. 그 뒤 같은 변이를 `sa_bits_seg`에 겨눈 경우 `lv-sa-bitslen63-seg`를 더했다(inside). 첫 결과는 그대로 둔다.
- stale 검사(로그 85): `stale_olean.py` exit 0, flagged 0.
- Go 차분 시험: 실행하지 않았다. Prysm Go 빌드 환경(계획 담당의 Docker)과 새 Go 하네스가 필요하다. 이 장비는 arm64라서 실행해도 x86-64 ELF의 증거가 아니다.

## T3 변위 확인 (판정: 증명 없이 값만)

- 로그 66: scratch `.S`의 `lea 0xffffff1c(%rdi),%rdx`를 Kraken `include_x64_rt`로 읽고 `#print`했다. 결과 `disp := ↑4294967068`. 같은 파일의 `lea -0xe4(%rdi),%rdx`는 `disp := ↑(-228)`다.
- 기계는 32비트 변위를 부호 확장한다(−228). 그래서 이 표기를 Kraken에 그대로 주면 다른 주소를 계산한다. 실행 증거(X)다.
- 커밋된 다른 `.S`에는 `0xffffff..(%` 꼴이 없다(`git grep`, 결과 0).

## 리뷰 r1 수정 (`fbf729a` 리뷰)

### 로그

- 번호 붙은 로그(`logs/NN-*.log`)와 `heavy.py` 기록(`.json`)은 로컬 작업 디렉터리에만 있다. 커밋하지 않았다.
- 보고서가 기대는 줄을 아래에 그대로 옮긴다(경로는 줄였다).
- 로그 08(`check.py`, T3 포함): `FAIL clang: <tmp>/re.S:738:18: error: displacement 4294967068 is not within [-2147483648, 2147483647]` 다음 줄 `  lea 0xffffff1c(%rdi),%rdx`.
- 로그 26(`WitSaA` 시도 1): `error: E2eList/WitSaA.lean:87:0: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached`.
- 로그 27(프로파일): `simp took 2.08s`, `simp took 7.03s`, 누계 `simp 9.16s`.
- 로그 65(`WitScA`, 설정 없는 scratch 사본): `WitScANoHb.lean:97:0: error: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached`, 앞서 `simp took 2.3s`.
- 로그 66(T3 변위): `disp := ↑4294967068`(`lea 0xffffff1c(%rdi),%rdx`)와 `disp := ↑(-228)`(`lea -0xe4(%rdi),%rdx`).

### M1: `maxRecDepth`

- 원인을 기록하지 않은 `set_option maxRecDepth 100000`이 `E2eList/WitSaA.lean:26`과 `E2eList/WitScA.lean:27`에 있었다. 증인 본(`WitDdA.lean`)에서 옮긴 줄이다.
- `WitSaA.lean:26`의 줄을 지웠다. 로그 86: `lake build E2eList.WitSaA` exit 0.
- `WitScA.lean:27`의 줄을 지우고 빌드했다. 로그 87: exit 1. 오류 4개는 모두 `maximum recursion depth has been reached`이고 첫 `example`(125행)과 셋째 `example`(131행)의 `by simp`에 있다. `sc_accept_runs`와 둘째 `example`은 통과했다.
- 원인: `List.replicate 512 …`(512개 원소 목록)의 길이와 원소 길이를 `simp`로 보일 때 기본 재귀 한도를 넘는다.
- 조치(r1): `set_option maxRecDepth 100000 in`을 그 두 `example`에만 두었다. 파일 `E2eList/WitScA.lean`, 126행과 134행(r1에 "127행"이라 쓴 것은 틀렸다), 값 100000. 로그 88은 docstring 앞뒤 순서 때문에 구문 오류(wrong-target)였다. 로그 89에서 exit 0.
- 이 조치는 리뷰 r2 M1에서 바뀌었다. 아래 "리뷰 r2 수정"을 본다. 지금 `E2eList`에는 `maxRecDepth` 설정이 없다.

### S5: `lakefile.toml`

- `input_dir` `lv_lean_S`(path `E2eList`, `.S`만)를 덧붙이고 `E2eList`의 `needs`에 더했다. `e2e_ad_lean_S`와 같은 꼴이다. 다른 항목은 바꾸지 않았다.
- 로그 90: `lake build E2eList` exit 0, 683 jobs(`needs`가 바뀌어 라이브러리 전체를 다시 빌드했다). 로그 91: `--no-build E2e E2eAd E2eScal E2eList` exit 0, 1036 jobs.

### S4: 부정 시험 추가

- `gen/e2e/lvnegative.py`에 `inline`(펼칠 모듈 목록)을 더했다. `Desc.lean`과 `Defs.lean`을 펼쳐 `Desc`를 변이한다. 이전 경우는 그대로 돈다.
- 더한 경우: `lv-sc-rej-control`, `lv-sc-rej-errword`(T2 크기 거부), `lv-sa-desc-control`, `lv-sa-desc-sig95`, `lv-sc-desc-control`, `lv-sc-desc-n511`(크기 변이, 첫 대상 `*_fixedSize`), `lv-sa-desc-kind`, `lv-sc-desc-kind`(같은 크기의 종류 변이, 대상 `psa_toValue_fits`, `psc_toValue_fits`).
- 로그 92, 93: 더한 8개 모두 통과. 로그 94: 전체 26개를 새 실행기로 다시 돌렸다. 25개 통과(control_pass 7, inside 18), 1개 outside(`lv-sa-bitslen63`, 이전 기록과 같다).

### 다시 돌린 검사

- 공리 게이트(로그 95): PASS, 선언 5632, 정리 4684, 손 목록 462, 비표준 0, `sorryAx` 0. 결과 `lv/axioms-gate-lv-r1.json`. 이름 집합은 로그 69와 같다.
- `STEPS.tsv`의 71, 76번 줄에 있던 작업 디렉터리 경로를 `<scratch base copy>`로 바꿨다(S1).

## 리뷰 r2 수정 (`d169e4b` 리뷰)

### M1: `maxRecDepth` 제거

- `WitScA.lean`의 `set_option maxRecDepth 100000 in` 두 줄(126행, 134행)과 그 원인 주석을 지웠다.
- 첫째와 셋째 `example`의 `(by simp) (by simp)`를 항 증명으로 바꿨다: `List.length_replicate`와 `fun e he => by rw [List.eq_of_mem_replicate he]; exact List.length_replicate`. 리뷰어가 쓴 변형과 같은 생각이다.
- 시도 1(로그 97): `lake build E2eList.WitScA` exit 0. `E2eList/*.lean`에 `maxRecDepth`가 없다(`grep`, 결과 0).

### S5: 빈 줄

- `WitSaA.lean`, `WitScA.lean`의 `namespace` 뒤 겹친 빈 줄을 하나로 줄였다.

### S1: `maxHeartbeats` 문턱값

- 리뷰어가 잰 값(리뷰 r2, 리뷰어 실행): `WitSaA.sa_accept_runs`는 200000과 400000에서 `whnf` 실패, 1000000에서 통과. `WitScA.sc_accept_runs`는 200000, 400000, 1000000에서 실패, 2000000에서 통과.
- 값을 낮췄다: `WitSaA` 16000000 → 2000000, `WitScA` 16000000 → 4000000(리뷰어 통과 값의 두 배). 두 값은 이 작업자의 빌드에서 통과했다(로그 96, 97, 98).
- 이 작업자는 문턱값 자체를 다시 재지 않았다. 문턱값은 리뷰어가 잰 값이다. 두 파일의 설정 옆 주석에 같은 내용을 적었다.

### 다시 돌린 검사

- 로그 98: `lake build E2eList` exit 0, 683 jobs, 벽시계 19.9 s(WitSaA 13 s, WitScA 17 s).
- 로그 99: `lake build --no-build E2e E2eAd E2eScal E2eList` exit 0, 1036 jobs up to date.
- 로그 100: 공리 게이트 PASS, 선언 5632, 정리 4684, 손 목록 462, 비표준 0, `sorryAx` 0. 결과 `lv/axioms-gate-lv-r2.json`. 게이트 덤프는 r1 덤프(로그 95)와 바이트가 같다(`cmp`).
- 로그 101–102: 기준 roots(E2e, E2eAd, E2eScal)의 현재 덤프는 리뷰 전 덤프(로그 73)와 바이트가 같다(`cmp`). `decl_drift.py` 기준 대 현재: exit 0, `SUMMARY base=5007 head=5007 drift=0 allowed=0`.
- 바뀐 것은 `example`과 설정과 주석뿐이다. `example`은 선언을 만들지 않는다. 그래서 덤프가 같은 것은 기대와 맞다.

## LV-1 수정 (사용자 승인, `link/conv.py`만)

- 변경(`93b3f2a`): `--norm`에서 메모리 변위가 정확히 8자리 16진수이고 최상위 비트가 켜져 있고 바로 뒤에 `(%`가 오면 부호 있는 꼴로 쓴다. 예: `0xffffff1c(%rdi)` → `-0xe4(%rdi)`.
- 즉치값(`$0x…`), 분기 대상, `%rip` 피연산자는 바꾸지 않는다. 기본+색인 꼴 `(%r,%r,s)`도 덮는다.
- `selftest()`에 경우 다섯을 더했다: `--norm`에서 바꿈, `--norm` 없이 안 바꿈, `$0xffffff1c` 즉치값 안 바꿈, 양수 `0x7fffffff(%rax)` 안 바꿈, 기본+색인 꼴 `0x80000000(%rsi,%rcx,8)` 바꿈. `conv.py`는 실행할 때마다 selftest를 먼저 돈다. 로그 104, 109, 106의 실행이 모두 exit 0이다.
- 시도 1에 통과했다.

### 검증

- (a) 로그 103(옛 `conv.py`, `29683a8`), 104(새 `conv.py`): 전체 objdump와 nm을 scratch 두 곳에 `--norm`으로 바꿨다. 둘 다 exit 0, 함수 파일 641개와 `all.S`.
- 로그 105(집계만, `.S` 내용은 열지 않았다): 바뀐 파일 104개, 바뀐 줄 161개. 바뀐 모든 줄은 변위 토큰만 다르다(스크립트로 옛 줄에 같은 치환을 해서 새 줄과 비교, 불일치 0).
- (b) 새 출력에 감싼 꼴(`0x[89a-f][0-9a-f]{7}\(%`)은 0개다. 옛 출력은 161개다.
- (c) 로그 106: 이 ELF에서 `--norm`으로 만든 커밋된 셋 7개(`e2e/link`, `e2e/ad/link`, `e2e/bh/link`, `e2e/e1/link`, `e2e/h3/link`, `e2e/h4/link`, `e2e/lv/link`)를 커밋된 `target.objdump`에서 새 `conv.py`로 scratch에 다시 만들었다. 37개 파일(`all.S` 포함)이 커밋된 파일과 바이트가 같다.
- 로그 107: `target.objdump`가 커밋되지 않은 `prysm/go1.26.10/link/norm`은 전체 변환과 비교했다. 함수 파일 136개가 같고, `all.S`의 함수 블록 136개가 같다.
- `opt-r1/link`은 다른 ELF(`3ef7ac89…`)라서 비교하지 않았다.
- 보류 평가 타입의 `.S`는 열거나 출력하지 않았다. 스크립트의 바이트 비교와 개수만 셌다.
- (d) T3 링크(로그 108–111, scratch): `lvlink.py filter --t3` exit 0, `conv.py --norm` exit 0, `lvlink.py data --t3` exit 0, `check.py` exit 0.
- `check.py` 결과: (a) 함수 3개 PASS(T3 253 명령어, 1197바이트). (b) 28줄 PASS. (c) PASS(레이블 49개). (d) PASS: 473 명령어, 461개 바이트 같음, encoding 0, padding 12. (e) PASS(522 지시어). (f) 9개 파일 PASS. `PASS all`, 묶음 해시 `393eade69a88fd79e6b6a6a50a09387cb3e5892ebe8777e8933b5f6742954e0d`.
- T3을 `lv/link`에 넣으면 그 디렉터리의 `RESULT`, `all.S`, `target.objdump`가 바뀐다. 그래서 새 형제 디렉터리 `lv/link-t3/`에 커밋했다(`dc7bd56`). `git diff dfc8b93 -- lv/link`은 비어 있다.
- `lv/link-t3/`의 T1, T2 `.S`와 데이터 파일은 `lv/link`의 것과 같다. T3 `.S`는 이전 시도(로그 06)의 것과 19행의 변위 토큰만 다르다.
- (e) 로그 113: 새 T3 `.S` 19행 `lea -0xe4(%rdi),%rdx`를 Kraken `include_x64_rt`로 읽고 `#print`했다. `disp := ↑(-228)`. 로그 112는 내가 20행을 잘못 골라서 비교 대상이 아니었다(wrong-target).
- (f) selftest: 위 실행마다 먼저 돌았고 통과했다.
- T3 정규화 `.S`의 호출 집합: `fmt.errorf` 3, `AttestationData.UnmarshalSSZ` 1, `runtime.convT64` 2, `runtime.gcWriteBarrier2` 4, `runtime.makeslice` 2, `runtime.memmove` 1, `runtime.morestack_noctxt.abi0` 1, `runtime.newobject` 4, `runtime.panicBounds` 3. 279줄.
- T3의 Lean 문장이나 증명은 시작하지 않았다.

## T3 설계와 문장

- 새 파일: `E2eList/IncludeIa.lean`(`lv_data_include` 글의 사본, 접두사 `lvt3`, 경로 `lv/link-t3/data`), `gen/e2e/lvt3check_include.py`(SAME 넷, exit 0), `CodeIa.lean`, `DataIa.lean`, `DefsIa.lean`, `StmtIa.lean`.
- `lakefile.toml`: `input_dir` 둘(`lv_t3_norm_S`, `lv_t3_data`)을 덧붙이고 이 가지에서 만든 `E2eList`의 `needs`에 더했다. 다른 항목은 바꾸지 않았다. 사용자 결정 목록에 올린다.
- 로그 114: `lake build E2eList.StmtIa` exit 1. `NewobjectC`는 `Fk.FunSpecs`에 있다(import 빠짐).
- 로그 115, 116: exit 0. 로그 117: `lake build E2eList` exit 0, 705 jobs. 로그 118: `--no-build E2e E2eAd E2eScal E2eList` exit 0, 1048 jobs.
- `StmtIa.lean`의 문장 글은 scratch 생성 스크립트로 썼다(같은 프레임 글을 반복하지 않게). 스크립트는 커밋하지 않았다. 결과 Lean 파일이 문장이다.
- 새 파일에 `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, `maxHeartbeats`, `maxRecDepth`가 없다(`grep` exit 1).

## T3 증명

### U1: P1 `ia_e2e_reject_size_main`, P2 `ia_e2e_reject_offset_main` (시도 1)

- 로그 119–123: 한 전략의 개발 단계다. 막힌 곳 셋.
- 1. `simp only [E2e.errSize_addr_eq] at … ⊢`와 `simp only [UInt64.size] at *`가 재귀 한도에 닿았다. 목표와 `hk`를 건드리지 않게 바꿨다(`dsimp only`, 이름 붙인 가설에만 `simp`).
- 2. `kat`의 `simp`가 279개 지시어의 프로그램 글자(`IaUnmarshal`)를 펼치며 기본 `maxRecDepth`(512)에서 멈춘다(로그 123, 첫 `kat`).
- 측정(로그 124): 1024, 2048, 4096 모두 그 오류가 사라졌다. 남은 오류는 P2의 미완성 가지뿐이었다. 그래서 값은 1024다. 두 정리 각각에 `set_option maxRecDepth 1024 in`을 두고 옆에 원인을 적었다.
- 3. P2의 `jne` 안 갈림 가지: 32비트 값 `ofInt 32 (ofBytes off)`가 228이면 `off = iaOff`다. `toBytes_ofInt_ofBytes`와 `isLt`로 닫았다(로그 125–127은 이름과 산술 정리의 개발 단계).
- 로그 128: `lake build E2eList.IaReject` exit 0.

### U2: T3 명세 다리 `IaSpec`, P1·P2 명세, 거부 경우 (시도 1)

- `IaSpec.lean`: `pia_serialize`, `pia_roundtrip`, `pia_accepted_is_enc`, `iaChecks`(Go 검사 넷의 순서), `pia_spec_accepts_iff`, `pia_spec_rejects`. 목록 쪽은 Go 1.26.3 ListU64 보조정리(`serializeEach_u64`, `inl_*`, `luElems`, `u64Bytes_luElems`), 데이터 쪽은 `E2e.pad_*`, 결합은 EthLib `extract_join`을 썼다.
- 로그 129–133: 한 전략의 개발 단계다. 막힌 곳: 목록 `assemble`의 크기 조건(`h8`), `Desc.isFixed`가 펼쳐지지 않음(`rfl` 사실 넷을 `simp`에 줌), Mathlib 없는 `set`, 배열 결합.
- 로그 134: `IaSpecR.lean`의 `ia_e2e_reject_size_spec`, `ia_e2e_reject_offset_spec`, `ia_e2e_reject_cases` exit 0. 설정 없이 통과했다.

### U3: P4, P5 (멈춤)

- 증명을 시작하지 않았다.
- 고정 문장 `ia_reject_misaligned_stmt`, `ia_reject_toobig_stmt`에 전제 `e0 ≠ 0`이 없다.
- 지시어 103–106(P4)과 66–69(P5)는 `test %rcx,%rcx; je`다. e0 = 0이면 itab+8을 읽지 않고 인수 단어가 0이다. `FmtErrorfDWC`는 그 단어가 `ity`이기를 요구한다.
- Kraken `Host` 배치는 임의라서 itab 레이블이 0일 수 있다. 그래서 문장 그대로는 증명할 수 없다고 판단했다.
- 계획 담당에게 보고했다. 새 이름과 판정을 기다린다.

### U4: P3 수락 `ia_e2e_accept_main` (시도 1)

- 새 파일: `E2eList/IaLoop.lean`(`ia_iter`, `ia_exit`, `ia_loop`), `E2eList/IaAccept.lean`(보조정리 12개와 `ia_e2e_accept_main : ia_accept_stmt`).
- `ia_iter`는 한 바퀴다. panicBounds 셋(155 `ja`, 159 `jb`, 164 `jb` 안 갈림 → 165)이 안 갈림을 증명한다. 가정하지 않는다.
- `ia_loop`는 남은 바퀴 수 `j`에 대한 재귀다(`i + j = n`). n = 0은 `j = 0, i = 0`이다.
- 데이터 호출은 `E2eAd.ad_e2e_accept_main`으로 닫았다. 피호출자 진입 rsp는 x − 184, scratch는 `Sd`다.
- 로그 135–140: `IaLoop`. 첫 빌드부터 통과했다. `maxRecDepth`를 빼면 `ia_iter`(로그 136), `ia_exit`(로그 139)의 첫 `kat`이 재귀 한도에서 멈춘다. 그래서 둘 다 1024를 두고 원인을 적었다.
- 로그 141–145, 152, 155–183: `IaAccept`의 개발 단계다. 한 전략(손 단계 + 계약 + 루프 + 피호출자)이다. 막힌 곳은 아래와 같다.
- 1. `sar $0x3f`는 미정의 플래그를 남긴다. `kshl64 63`으로 닫았다. `and`의 AF는 `intro _`로 닫았다.
- 2. 로그 147, 148, 152, 153: `c + -228`에 `simp [BitVec.toNat_add]; omega`를 쓰면 커널이 "deep recursion"으로 멈춘다. 각 실행은 235–309 s, 표본 RSS 16–20 GiB였다. 로그 153은 그 한 줄만으로 90 s 시간 초과다(exit 124).
- 그래서 `ia_sub228`(`BitVec.sub_eq_add_neg`, `toNat_sub_of_le`)로 바꿨다. 3.1 s다(로그 154). 상수 둘은 `toNat` simp 집합으로 증명했다(로그 151). `decide`는 쓰지 않았다.
- 3. 로그 158–160: 지시어 35 뒤 `ecancel`이 "maximum recursion depth"로 멈췄다. 2048과 8192에서도 같았다. 그래서 한도 문제가 아니라고 판단했다.
- 원인 추정: 지시어 34가 메모리에 쓴 원시 `sar`/`and` 식에서 AC 정규화가 끝나지 않는다. 그 식을 `generalize`로 이름 `P`, `C`, `Q`로 바꾸자 사라졌다(로그 161). 한도는 1024로 되돌렸다.
- 4. 로그 172–174: 피호출자 사후조건의 단어 둘(저장된 rbp, rdi 스필)이 내가 쓴 같은 꼴의 항과 구조적으로 맞지 않았다. 원자별 시험(로그 173)으로 찾았다. `generalize`로 이름 `vb`, `v4`를 붙였다. 둘 다 존재 양화된 프레임 안에만 남는다.
- 5. 로그 175, 176: `makeslice` 사후조건의 `replicate (1 * 96)`. `Nat.one_mul`로 닫았다. 옛 값을 `_`로 둔 저장 둘이 하트비트를 다 썼다. 명시 값으로 바꿨다.
- 6. 로그 181, 182: 최종 메모리. `memmove` 사후조건의 원본 주소가 `132 + rbx`다. 원자별 시험으로 찾았다.
- 로그 183: exit 0.
- 측정(로그 184, 185): `maxRecDepth`를 빼면 지시어 0의 `kat`이 멈춘다. `maxHeartbeats` 400000은 `whnf` 시간 초과, 800000과 1200000은 통과다. 값은 통과 값의 두 배인 1600000이다. 옵션 옆에 원인과 문턱을 적었다.
- 로그 186, 187: `lake build E2eList.IaLoop E2eList.IaAccept` exit 0. 로그 187은 `ia_exit`의 쓰지 않는 이름을 `_hn`으로 바꾼 뒤다.
- 두 파일에 `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`가 없다(`grep` 결과 없음).
- 로그 147, 148은 scratch 파일(`lake env lean`)이다. 그 RSS 값은 이 커밋의 증명과 관계없다.

### U5: P3 명세 `ia_e2e_accept_spec` (시도 1)

- 새 파일: `E2eList/IaSpecA.lean`. `pia_accepted_is_enc`로 `g`를 얻고 `ia_e2e_accept_main`을 n = `g.idx.length`로 쓴다. `E2eAd/AdSpecK.lean`의 글이다.
- 로그 188: `lake build E2eList.IaSpecA` exit 0. 설정 없이 통과했다.

### U6: Desc 같음 `prysmIaDesc_deserialize_checker` (시도 1)

- `python3 gen/e2e/lvdescterm.py prysm/go1.26.10/e2e/lv/desc/prysm_v1alpha1.IndexedAttestation.desc.json iaCheckerDesc > lean/E2eList/IaSpecChecker.lean`, exit 0.
- 생산자 파일의 sha256은 `91e4d752…`다. `gen/desc/results/main.result.json`의 IndexedAttestation 행(`PASS`)과 같다.
- 새 파일: `E2eList/IaDescEq.lean`. 중첩 컨테이너는 `E2e.serializeFields_congr`와 `E2e.prysmAdDesc_serialize_checker`로 닫았다.
- 로그 189: `lake build E2eList.IaDescEq` exit 0. 설정 없이 통과했다.

### U3 판정 (2026-11-12)

- 계획 담당이 `_nz` 문장을 승인했다. 사용자도 명시적으로 동의했다(계획 담당의 전달).
- 빈틈, 선례(`Fk/LuRejectCall.lean`의 `lu_reject_misaligned_main`, 전제 `e0 ≠ 0`과 `e0 = itab`), 실제 ELF 값(`0xd28520`, `lv/link-t3/RESULT` 검사 (b))은 `STATEMENTS-T3.md` 5절에 적었다.
- 정정된 전제는 고정 문장보다 강하다. 원래 넷은 N이다(쓴 그대로는 증명할 수 없다).

### U7: P3 증인 `WitIaA.ia_accept_runs` (모든 n ≤ 2048)

- 새 파일: `E2eList/BumpAllocT3.S`, `E2eList/BumpNewT3.S`, `E2eList/BumpT3.lean`, `E2eList/WitIaA.lean`.
- `BumpAllocT3`는 형 단어로 갈린다. `type__+387456`(uint64)이면 8·cnt, 아니면 cnt만큼 늘린다. `BumpNewT3`는 `type__+1464512`(AttestationData)이면 96, 아니면 72다. 오프셋은 `lv/link-t3/data`의 파일에서 왔다.
- 두 `.S`는 기존 Lake `input_dir` `lv_lean_S`(`E2eList/`의 모든 `.S`)에 든다. lakefile은 바꾸지 않았다.
- 로그 190: `BumpT3` exit 0. 정리 넷(`bump_makeslice_t3_1`, `_t3_8`, `bump_newobject_t3_72`, `_t3_96`)은 설정 없이 통과했다.
- 메모리 배치: 입력을 블록의 끝에 두었다. 그래서 `ib`의 길이가 다른 주소를 바꾸지 않는다. 힙은 16816바이트(8·2048 + 432)로 고정했다.
- 전략 1(로그 191, 192): `WitScA` 글 그대로. 로그 192는 실패다. `maxHeartbeats 64000000`에서 `whnf` 시간 초과, 1471 s, 표본 RSS 2.75 GiB. 계획 담당 판정: 이 값을 다시 올리지 않는다.
- 진단(로그 193–197): `wit_split`만으로 기본 한도에서 멈춘다(로그 193). `ib = []`이면 통과한다. 기호 길이 `ib`(또는 불투명 `L`)이면 멈춘다(로그 194, 196). `iaOff` 펼침은 관계없다. 진단 출력(로그 195)은 Nat `HAdd`/`HMul` 펼침 약 392000회를 보인다.
- 전략 2(로그 196): 길이를 변수 `L`로 일반화했다. 실패.
- 전략 3(로그 198–214): `ib`를 먼저 명시 재작성 하나로 떼어 낸다. 그 측면 조건은 `block.length = 17616`과 `hib`로 직접 증명한다. 나머지 블록에는 리터럴 길이만 남는다. 분할은 18 s가 되었다.
- 레지스터 사실 넷은 `simp [cs0]` 대신 `show`와 `UInt64.toNat_ofNat_of_lt'`로 증명했다(로그 202, 205).
- 닫는 단계로 `ecancel`을 시도했다(로그 204–208). 원자 36개를 하나씩 시험하면 모두 맞는다(로그 207). 전체는 실패하고 전술 내부 PANIC 56개가 나온다. 깊이 8192도 같다(로그 208). Kraken은 고치지 않는다(도구 경계). 그래서 `WitScA`의 AC `simp` + `exact`로 돌아갔다.
- 측정: `maxHeartbeats` 3000000, 4000000 실패(로그 211). 5000000 통과(로그 211). 6000000, 8000000, 12000000, 16000000 통과(로그 209, 210). 값은 통과 값의 두 배인 10000000이다.
- 측정: 파일 수준 `maxRecDepth`. 기본값과 1024는 호스트 사실(884개 지시어 프로그램의 `rfl`/`decide`)에서 멈춘다(로그 212). 2048은 통과한다.
- 예시 셋: n = 0(`ib = []`), n = 1, n = 2048(`List.replicate (8 * 2048) 0xff`). 길이 증명은 `List.length_replicate` 항이다. `decide`와 큰 리터럴은 쓰지 않았다.
- 로그 214: `lake build E2eList.WitIaA` exit 0, 68.8 s, 표본 RSS 2.73 GiB(파일 전체, n = 2048 예시 포함).
- 판정: 일반 n 증인은 K다. 대체 경로(구체 n 증인만)는 쓰지 않았다.

### U3: P4 `ia_e2e_reject_misaligned_nz`, P5 `ia_e2e_reject_toobig_nz`, 두 명세 (시도 1)

- 문장은 `_nz` 넷이다(`714989f`에서 고정). 새 파일: `E2eList/IaRejectCall.lean`, `E2eList/IaSpecRNz.lean`.
- 증명은 `Fk.lu_reject_misaligned_main`의 글이다. 머리 0–26은 `IaAccept.lean`과 같다.
- `je`(105, 68)는 `he0nz`로 반박한다. itab 단어 읽기의 주소만 `he0`로 바꾼다(`load_step_at`). 처음에는 `rw [he0]`가 사후조건의 `e0`까지 바꾸었다(로그 225–227의 원자별 시험으로 찾음).
- P5의 `jg`(30) 갈림은 새 보조정리 `ia_jg2048_true`로 보였다.
- 로그 216–231: 한 전략의 개발 단계다. 막힌 곳: `movups` 주소 꼴, `at_app`의 기준 주소를 명시해야 함, `Int.toBytes_length`가 기본 `simp` 집합에 없음, `StaticBox C`를 `SB`로 되돌리기.
- 측정(로그 233): 두 정리에서 `maxRecDepth`를 빼면 첫 `kat`이 멈춘다. 1024는 통과한다(로그 231, 232).
- 로그 234: `lake build E2eList.IaRejectCall E2eList.IaSpecRNz` exit 0. 하트비트 설정은 없다.

### U3 증인: `WitIaR.ia_misaligned_runs`(P4), `WitIaR.ia_toobig_runs`(P5) (시도 1)

- 새 파일: `E2eList/WitIaR.lean`. `Fk/WitLuMa.lean`의 글이다. 그 파일을 만든 생성기는 저장소에 없다. 배치는 scratch 스크립트로 계산했다(커밋하지 않음).
- `e0`는 itab 레이블 주소 0x1012b다(0이 아님). `he0`는 `label_itab`으로, `he0nz`는 `decide`로 보였다.
- 계약은 `Fk.RtErr`의 `rt_convT64`, `rt_errorf_dw`로 닫았다. 틀 `R`은 `fun _ => True`다(`sep_true`, 선례와 같음).
- P4: len = 229(상자는 정적 표의 1). P5: len = 228 + 8 · 2049(상자는 힙).
- 막힌 곳(로그 236–243): 기호 꼴 차이(`66560#64`), `zmms`가 든 `decide` 목표, `bumpHeap`을 만든 뒤 한 가설에 모든 원자가 없음(선례처럼 명시 목록 `H2`를 `ecancel`로 증명), `sep_emp` 재작성이 `sep_true`의 틀 변수를 `emp`로 묶음.
- 측정(로그 245): `maxRecDepth`가 없으면 호스트 사실에서 멈춘다. 1024는 통과한다. 하트비트 설정은 없다.
- 로그 246: `lake build E2eList.WitIaR` exit 0, 26.0 s, 표본 RSS 5.56 GiB.

### U8: T3 검증

- 로그 247, 252: `lake build E2eList` exit 0(252는 765 jobs, 100.1 s, 표본 RSS 7.71 GiB. T3 모듈이 다시 빌드됨).
- 로그 248, 254: `lake build --no-build E2e E2eAd E2eScal E2eList` exit 0(254는 1080 jobs).
- 공리 게이트: 새 손 목록 `gen/e2e/AxiomsLvT3.lean`(T3 이름 23개)과 새 감싸개 `gen/e2e/lvt3axioms_gate.py`(`lvaxioms_gate.py`의 글, `LISTS`에 두 목록). selftest PASS, 손 목록 이름 485.
- 로그 249, 255: PASS. 선언 6402, 정리 5341, 손 목록 485, 빠짐 0, 비표준 0, `sorryAx` 0. 결과: `axioms-gate-lv-t3.json`(로그 255).
- 선언 drift(로그 250, 기준 `6a78c591`, 뿌리 E2e, E2eAd, E2eScal): 0 (5007 = 5007). 결과: `decl-drift-lv-t3.txt`.
- 부정 시험: `negcases-lv-t3.json`의 8개. 로그 251은 대조군 하나가 실패했다. `IaAccept`가 `IaReject`를 통해 `StmtIa`를 두 번 가져와서다(실행기가 문장 모듈을 펼친다).
- 그래서 `iaaddr` 매크로를 새 모듈 `E2eList/IaAddr.lean`으로 옮겼다. `IaAccept`는 `IaAddr`와 `StmtIa`를 직접 가져온다. 정리 문장은 바뀌지 않았다.
- 로그 253: 8개 모두 통과(대조군 2, inside 6). 결과: `negative-lv-t3.json`.
- 경우: 크기 문장 227/228(`< 229`), 크기 코드(`cmp $0xe5,%rcx`), 오프셋 바이트(`cmp $0xe5,%rdx`), 정렬(`test $0xf`), 2048 한계(`cmp $0x7ff`), 수락 사후조건(`Heap (avail - (8 * n + 431))`).
- 링크: `git diff dc7bd56 -- lv/link-t3 lv/link`는 비어 있다. 링크 검사는 다시 돌리지 않았다(입력이 같다).
- 실행하지 않은 것: 기준 트리의 별도 빌드, 게이트 대조군, drift 대조군, `stale_olean.py`, Go 차분 시험, 하드웨어 대조.
