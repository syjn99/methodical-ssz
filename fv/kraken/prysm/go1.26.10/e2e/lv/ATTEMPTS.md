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
