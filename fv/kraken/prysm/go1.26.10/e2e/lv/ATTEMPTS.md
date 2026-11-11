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
