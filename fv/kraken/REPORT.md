# REPORT: Kraken x64 평가

기준: 브랜치 `syjn99/ssz-fv-kraken`, 시작 c60e0d2. Kraken `6064eecbb730a1152aa6ed891a155d3a92a4f298`(main, 2026-11-02). Lean `nightly-2026-09-21`. EthLib 8621856. Go 1.26.3, `GOOS=linux GOARCH=amd64 CGO_ENABLED=0 -tags purego -trimpath`. ELF 식별자는 `link/out/build-ids.txt`. 작성 2026-11-05.

이 문서의 시각은 IST, 에이전트(Claude Opus 5.5) 시간이다. 사람 시간이 아니다.

## 1. 판정

**조건부 가능.** 1b 이후를 MiniRV 없이 Kraken x64(main) 위에서 할 수 있다. 조건은 2절이다.

근거: 이 세션은 Kraken main의 x64 의미론과 프로그램 논리(`Eventually`, `step1`, `Host`, 분리 논리 `⋆`, `ecancel`) 위에서 다음을 증명했다. 모든 정리는 `propext`, `Classical.choice`, `Quot.sound`만 쓴다(`AXIOMS.txt`). `sorry`는 없다.

| 정리 | 대상(amd64 기계어) | 내용 | 1a 대응 |
| --- | --- | --- | --- |
| `sc_reject_size_main` | Scalars.UnmarshalSSZ | len ≠ 16이면 `ssz.ErrSize`의 두 단어(전역)를 반환 | `sc_reject_size` |
| `sc_accept_main` | Scalars.UnmarshalSSZ | len = 16, bool 바이트 ∈ {0,1}이면 수신자 필드 5개 = 입력 조각, nil 반환 | `sc_accept` |
| `sc_unmarshal_accept_spec_k` | 위 | EthLib `deserialize scDesc bs = .ok v`이면 수신자 = `g`의 Go 배치, `g.toValue = v` | `sc_unmarshal_accept_spec` |
| `sc_size_main` | Scalars.SizeSSZ | 16 반환 | `sc_size` |
| `sc_marshal_main` | Scalars.MarshalSSZTo | `len + 16 ≤ cap`이면 dst에 16바이트를 붙이고 `(ptr, len+16, cap, nil)` 반환. 스택 검사, `push`/`pop` 포함 | `sc_marshal` |
| `sc_marshal_spec_k` | 위 | 쓴 바이트 = EthLib `serialize scDesc g.toValue` | `sc_marshal_spec` |
| `lu_iter`, `lu_exit`, `lu_loop` | ListU64.UnmarshalSSZ 원소 루프 | 불변식과 귀납. 경계 검사 2개가 `panicBounds`로 가지 않음 | `lu_loop_body`, `lu_loop` |
| `lu_accept_main` | ListU64.UnmarshalSSZ | 수용 경로 전체: 스택 검사, 입력 검사 4개, `makeslice` 호출(계약 가설), 쓰기 장벽 전역 읽기, 루프, 반환. 수신자 = (p, n, n), p의 배열 = 입력 원소 | `lu_accept` |

증명하지 않은 것: ListU64 수용의 EthLib 연결 정리(`lu_accept_main`에서 1a의 `Transfer` 틀로 바로 만들 수 있다. 시간 관계로 하지 않았다), FixedVec 전체, ListU64 인코더와 거부 경로, 모든 `growslice` 경로, K5 대조(3.5절).

판정의 주된 근거:
- 운영 아키텍처(x86-64)의 실제 Go 컴파일러 산출물을 그대로 다뤘다. 9개 함수 모두 파싱되고 의미론에 없는 명령어가 없었다(K1).
- 1a에서 MiniRV로 한 일의 핵심 세 가지(직선 경로, 데이터 의존 루프, 외부 호출 계약)를 모두 Kraken 위에서 재현했다. 비용은 1a보다 작거나 비슷했다(4절).
- 조건부인 이유: Kraken main의 증명 자동화(`kstep`)는 우리 함수 크기에서 쓸 수 없었다. 단계 보조정리와 매크로 439줄을 우리 쪽에서 만들었다. 하드웨어 대조를 이 호스트에서 돌리지 못했다. Sail 연결이 없다.

## 2. 조건 목록: MiniRV 없이 1b(bitvector, bitlist, 중첩 container, List[container], Prysm 타입)를 Kraken x64에서 하려면 무엇이 필요한가

분류: **래퍼** = 우리 쪽 Lean 코드로 된다. **기여** = Kraken에 고치거나 더하는 것이 맞다(이 세션은 PR을 만들지 않는다). **전제** = 계약 또는 정리의 전제로 둔다.

| # | 필요한 것 | 분류 | 상태와 근거 |
| --- | --- | --- | --- |
| C1 | Host 안 조각의 한 지시어 단계, 적재·저장 단계, 주소 정규화(`estep`, `load_step`, `store_step`, `kunfold`, `kat`) | 래퍼 (기여 후보) | 완료 `Fk/Step.lean`. main의 `kstep`은 `straightlineStep` 목표용이고, 맥락이 커지면 안의 `grind`가 시간 초과로 끝난다(TOOLS.md). vcgen 브랜치가 이것을 대신할 수 있다(C14) |
| C2 | 레이블 해석: `label l = Host.addrOf (k + j)` | 래퍼 (기여 후보) | 완료 `Fk/Labels.lean`. 전제는 "함수의 레이블이 Host에서 함수 앞에 나오지 않는다"(`LabelsFresh`). 링크 수준 사실이다 |
| C3 | 정교화기 `include_x64`의 조건 코드 `g, ge, nl, nle, s, ns, o, no, p, np` | 기여 (지금은 래퍼) | `Parser/Syntax.lean`의 `declare_affixes cc`와 `Elab.lean`의 `evalCondCodeSuffix`에 줄 추가. 지금은 `include_x64_rt`(런타임 파서 + `ToExpr`) |
| C4 | 다바이트 nop(`nopl (%rax)`, `data16 nop`) 파싱 | 기여 (지금은 래퍼) | 변환기 `--norm`이 `nop`으로 바꾼다. Kraken 레이아웃이 추상이라 의미 차이는 없다 |
| C5 | mutable 전역 읽기(`ssz.Err*`, `runtime.writeBarrier`) | 전제 | 완료(3.2절). 전역을 레이블 주소의 메모리 조각으로 두고 값을 전제로 둔다. 쓰기는 1a·1b SSZ 코드에 없다 |
| C6 | 외부 호출 계약(`makeslice`, `growslice`, `memmove`, `convT64`, `newobject`, `fmt.errorf`, `gcWriteBarrier2`) | 전제 (계약 형식은 래퍼) | `makeslice` 하나로 형식을 시험했다(3.3절). 나머지는 같은 틀이다. 1a `CONTRACTS.md`의 표를 그대로 옮길 수 있다 |
| C7 | Go 런타임 전제: 스택 가드(`r14+16`의 `stackguard0` < rsp), 쓰기 장벽 꺼짐, X15 = 0, `panicBounds` 도달 불가 | 전제 | 스택 가드와 쓰기 장벽은 완료. X15(`movups %xmm15` 오류 경로)는 실행하지 않았다. `panicBounds`는 분기 정리로 도달 불가를 보였다 |
| C8 | 데이터 의존 루프 | 래퍼 | 완료(`Fk/LuLoop.lean`, `Fk/Block.lean`). 블록 분할 + 한 바퀴 + 귀납 |
| C9 | 분기 조건과 주소 산술을 독립 보조정리로 두기 | 래퍼 | 완료 `Fk/Flags.lean`. 맥락 안에서 `simp; omega`로 닫으면 커널이 깊은 재귀를 보고한다(64비트 큰 리터럴). 1a 발견 5와 같은 현상이다 |
| C10 | `ecancel`의 원자 비교가 복잡한 값 항을 펼치지 않게 하기 | 기여 (지금은 래퍼) | 지금은 계산 값을 `generalize`로 변수로 바꾼다. Kraken 쪽 수정 후보: 원자 비교를 reducible 투명도로 |
| C11 | `kstep`이 부가 목표의 `grind` 시간 초과를 잡기 | 기여 | 시간 초과는 런타임 예외라서 `try … catch`가 잡지 못한다. `tryCatchRuntimeEx` 또는 `grind` 설정 상한 |
| C12 | 1b 코드의 새 명령어 | 기여 또는 우회 | 런타임 파서에 없음: `bsr`, `lzcnt`, `tzcnt`, `popcnt`, `bt`, `xchg`, `cqo`, `div`, `rep movs`, `pxor`, `xorps`, `movq xmm↔gpr`. 있음: `movsx`, `cmov`, `setcc`, `imul`, `or`, `movups`. bitlist 검증의 `bits.Len8`은 표(rodata) 조회라서 C5 방식으로 된다. `bits.Len64`는 GOAMD64=v1에서 `bsr`, v3에서 `lzcnt`다. 1b 대상을 빌드해서 확인해야 한다(미확인) |
| C13 | `growslice` 경로(인코더의 용량 부족) | 전제 + 래퍼 | 1a와 같은 조합 문제다. append 지점별 보조정리 + 계약. 이 세션은 하지 않았다 |
| C14 | vcgen 브랜치(sgraf812/kraken `vcgen`, a4cce2e, nightly-2026-10-29) 평가 | 결정 사항 | Hoare 삼중항, `FunSpec`(함수 명세), 점프·루프·호출 예제가 있다. C1, C2, C6의 래퍼를 대신할 수 있다. 툴체인이 다르다. 1b 전에 반나절 평가를 권한다 |
| C15 | 하드웨어 대조 | 전제(신뢰) | 이 호스트(arm64)에서 실행하지 못했다(3.5절). x86-64 Linux 기계 또는 CI가 필요하다 |
| C16 | 툴체인 | 결정 사항 | Kraken은 nightly를 따른다. v4.35.0에서는 파서가 빌드되지 않는다(K0). 1b는 Kraken의 nightly에 맞춰 올린다. EthLib SSZ 폐포는 nightly에서 빌드된다 |

## 3. 항목별 결과

### 3.1 K0 툴체인

(a) v4.35.0 + Kraken: 의미론, WP, 전술은 빌드된다. 파서만 실패한다(`SyntaxAffixed.lean:86: Unknown identifier mkMarkdownDocComment`). (b) nightly-2026-09-21 + EthLib SSZ 폐포: 성공(332 s, 1.38 GB). 1단계 명세 파일 4개가 수정 없이 빌드된다. (c)는 필요 없었다. TOOLS.md K0.

### 3.2 K1 대상, 변환기, mutable 전역

- `link/conv.py`가 objdump `-gnu`의 AT&T 열을 레이블 어셈블리로 바꾼다. 9개 함수 모두 런타임 파서를 통과한다(패딩 정규화 뒤). 정교화기는 `jg`/`jge`가 있는 4개 함수를 거부한다(C3). 함수별 표는 TOOLS.md K1.
- **mutable 전역.** Kraken README는 "Mutable globals (bss and data)"를 제외 범위로 적었다. 실제 의미론에서 `sym(%rip)` 적재는 `label "sym"` 주소의 데이터 메모리(부분 맵) 적재다. `label`은 Host 프로그램에서 그 레이블 지시어를 찾고, 없으면 −1이다. 그래서 다음과 같이 다룬다.
  - 정리를 Host에 대해 일반적으로 진술하고, 전제에 `label "ssz.ErrSize"` 주소의 분리 조각(두 단어)을 둔다. 값은 전제(1a의 `hinit`와 같은 역할)다.
  - `runtime.writeBarrier`도 같다. 전제: 그 4바이트 = 0(쓰기 장벽 꺼짐).
  - 분리 논리가 전역과 다른 영역(입력, 수신자, 스택)의 겹침을 배제한다.
  - 한계: 실제 바이너리의 전역 주소와 Host 레이블 주소가 같다는 것은 링크 수준 사실이다. 정리 안에서 증명하지 않는다. 쓰기(전역 갱신)는 다루지 않았다. SSZ 코드에는 없다.
- 결론: 읽기 전용으로 쓰는 전역은 "분리된 기호 메모리 + 전제"로 충분하다. Kraken 수정은 필요 없다.

### 3.3 K2–K3 Scalars, 런타임 호출, 쓰기 장벽, 스택 검사

| 항목 | Kraken에서 둔 방식 | 1a(`CONTRACTS.md`) |
| --- | --- | --- |
| 스택 검사 `cmp 0x10(%r14),%rsp; jbe morestack` | 전제: `r14+16`의 조각 값 `guard` < rsp(또는 rsp − 8). 분기 정리로 `morestack` 쪽이 불가능함을 보인다 | 전제 P1, 같은 내용 |
| `runtime.growslice` | 빠른 경로 전제 `len + 16 ≤ cap`로 호출 분기를 타지 않음을 보인다 | 같다 |
| `runtime.makeslice` | 정리의 가설 `hms`: 반환 주소 칸과 S바이트 스택 여유를 받으면 반환 주소로 돌아오고, rsp + 8, 프레임 F 보존, 반환 rax에 0 블록. 모든 Host에 대해 진술한다 | `makesliceC H 8` (havoc 기반 계약 실행) |
| 쓰기 장벽 | 전역 조각 = 0 전제. 코드가 플래그를 실제로 읽고 분기한다 | `noBarrier` 전제, 같다 |
| 오류 전역 | 레이블 조각 + 값 전제 | `hinit`, 같다 |

차이: 1a는 계약을 기계 모델 안의 표(`rtOf H`)로 실행했다. Kraken에서는 계약이 정리의 가설이다. 호출 지점에서 `eventually_trans`로 잇는다. havoc 색인 문제(1a 발견 7)가 없다. 계약 결과가 경로를 고르면 결과에 대한 사례 분석으로 다룬다.

### 3.4 K4 루프

Kraken main에는 루프 예제가 없다(`p3_correct`는 `sorry`). 그러나 `Eventually`와 `eventually_trans`만으로 1a와 같은 방법(한 바퀴 보조정리 + 귀납)이 그대로 된다. `lu_iter`(19개 명령어, 약 9분과 함께 `lu_loop`)가 그 근거다. 불변식의 메모리는 Kraken의 `At_append_sep`로 블록을 나누고 합쳐 표현했다.

발견: 루프 경계 검사가 비교하는 `rcx`는 `cap(buf) − 4`(슬라이스 용량)이다. 처음 불변식의 `rcx = 8n`은 틀렸다. 앞부분 코드를 읽고 `8n ≤ rcx`로 고쳤다(70451e6).

### 3.5 K5 대조

실행하지 못했다. Kraken 하드웨어 대조는 x86-64에서 정적 ELF를 직접 실행한다. 이 호스트는 arm64 macOS다. Docker amd64 에뮬레이션은 Docker 데몬이 응답하지 않아 시험하지 못했다. qemu 사용자 모드는 macOS에 없다. 에뮬레이션으로 돌린다 해도 비교 대상은 qemu다. 하드웨어가 아니다. TOOLS.md K5.

## 4. 비용 비교 (1a MiniRV 대 Kraken main)

| | 1a MiniRV | Kraken main |
| --- | --- | --- |
| 첫 함수(도구 학습 포함) | ListU64 디코더 수용 약 4시간 | Scalars 거부 24분 |
| Scalars 디코더(수용 + 거부) | 약 7분(틀 복사 뒤) | 36분 |
| Scalars 인코더 빠른 경로 | 약 25분 | 약 17분 |
| ListU64 루프 | 약 30분 | 약 9분 |
| ListU64 디코더 수용 전체 | 약 4시간 | 약 61분 |
| 자동화 | 명령어마다 생성한 `rw [run_at …]; rv_norm` | `kat`(한 지시어 + 정규화), `load_step`/`store_step`, `ecancel`. `kstep`은 작은 맥락에서만 |
| 자체 기반 코드 | 의미론(MiniRV), 디코더, 계약 실행기, Sail 대응 | 단계 보조정리와 매크로 439줄. 의미론은 Kraken |
| 증명 빌드 | 62 s | 19.7 s, 1.7 GB |
| `lu_accept` 전제 | 레지스터, 입력 바이트, cap, P1, ra 짝수, 쓰기 장벽, 힙 크기, 5개 영역 `Sep` | 분리 조각 17개(`⋆`로 서로소), 스택 가드, len·cap, `makeslice` 계약, 레이블 신선성, 쓰기 장벽 칸 = 0 |

한계: 이 세션은 1a의 방법을 알고 시작했다. 시간 차이의 일부는 학습 효과다. COST.md.

## 5. 1a에서 옮길 것과 버릴 것

| 1a 산출물 | 처리 | 이유 |
| --- | --- | --- |
| EthLib 명세(`SpecScalars`, `SpecList`, `Transfer`, Desc 표, 오류 대응 표) | **옮김** (이미 `fv/kraken/lean/Fv1`) | 아키텍처와 무관하다 |
| 0단계 `Fv/Spec.lean`의 바이트 보조정리 | **옮김** (이미) | `SpecScalars`가 쓴다 |
| `SpecFixed`, `SizeSpec` | EthLib 부분만 옮김 | 크기 정리가 MiniRV를 끌어온다 |
| 계약 표(`CONTRACTS.md`)와 분류 (a)(b)(c) | **옮김** | 내용은 같다. 형식만 Kraken 가설로 |
| 루프 방법(구간, 한 바퀴, 귀납, 분리) | **옮김** | K4에서 그대로 재현했다 |
| 링크 검사, qemu 대조, 부정 사례 절차 | **옮김** (amd64용으로 다시 만들어야 함) | 절차는 같다. 링크 검사는 `conv.py` 출력과 ELF 대조로, 대조는 x86-64 기계에서 |
| 대상 타입, 드라이버 | **옮김** (이미 `fv/kraken/target`, `cmd/p1bin`) | |
| MiniRV 의미론과 모든 MiniRV 증명(`fv/phase1/lean/Fv1`의 기계어 정리, `fv/phase0/lean/Fv`) | **버림** | Kraken 의미론으로 대체 |
| 0.5단계 Sail 작업(`stepD_refines`, Sail 명령어 정리, Sail C 대조) | **버림** | riscv64 전용. x86 Sail 연결은 Kraken 쪽 계획이다 |
| riscv64 빌드 설정(`rva20u64`) | **버림** | |

## 6. Kraken에 없어서 필요한 것 (요약)

| 범주 | 항목 | 기여 / 래퍼 |
| --- | --- | --- |
| 명령어·파서 | 정교화기 조건 코드(C3), 다바이트 nop(C4), 1b 후보 명령어(C12) | 기여 |
| mutable 전역 | 읽기 전용 전역 = 레이블 조각 + 전제(C5) | 래퍼(필요 없음) |
| 외부 호출 계약 | 계약 가설 형식(C6). main에 함수 명세 장치가 없다. vcgen 브랜치에 `FunSpec`이 있다 | 지금 래퍼, vcgen 채택 시 Kraken |
| 루프 | main에 예제·보조정리 없음(C8). `Eventually`로 된다 | 래퍼 |
| 분기 가지 타기 | main 예제에 없음. 레이블 해석(C2), 한 지시어 단계(C1) | 래퍼, 기여 후보 |
| 자동화 규모 | `kstep` 안 `grind` 시간 초과 미포착(C11), `ecancel` 원자 펼침(C10) | 기여 |
| 커널 | 큰 리터럴 산술의 깊은 재귀(C9) | Lean 쪽. 래퍼로 우회 |

## 7. 신뢰 기반 문구 제안

> 기계어 정리는 Kraken x64 의미론(Kraken `6064eec`) 위의 정리다. Kraken의 x64 의미론은 Intel SDM을 참조해 손으로 쓴 것이다. Kraken 팀은 이 의미론을 실제 x86-64 하드웨어와 비교하는 대조 테스트로 검증한다. 이 프로젝트는 그 대조를 우리 함수에 대해 아직 실행하지 않았다. MiniRV 때의 "명령어 단위 Sail 일치 증명"에 해당하는 것은 Kraken에 아직 없다. Sail x86 모델과의 연결은 Kraken 쪽 계획이다. 외부 함수(Go 런타임)는 정리의 가설(계약)이고, 전역 변수의 값과 스택 가드는 정리의 전제다.

## 8. Kraken 관리자(Nic)에게 물을 질문

1. 1b(수천 명령어 규모)를 하려면 main과 sgraf812의 `vcgen` 브랜치 중 어느 쪽에서 시작해야 하는가? `vcgen`이 main에 합쳐질 예정과 툴체인 계획은?
2. `vcgen` 브랜치의 `FunSpec`은 Go ABIInternal(레지스터 인수, 대부분 호출자 저장, r14 = g, X15 = 0) 같은 비표준 호출 규약을 받는가? `CallingConvention`에 SysV, Win64만 있다.
3. README의 "Mutable globals 제외"는 의미론에서 무엇을 뜻하는가? 우리는 전역을 레이블 주소의 분리 조각으로 두었다. 이 방식이 의도와 맞는가? 데이터 섹션 레이블을 Host에 두는 권장 방법이 있는가?
4. 정교화기 `include_x64`의 조건 코드에 `g/ge/s/o/p` 계열이 빠진 것은 의도인가? 런타임 파서에는 있다.
5. `kstep`이 부가 목표의 `grind` 시간 초과를 잡지 못한다. 알려진 문제인가? 큰 분리 맥락에서 권장하는 방식은?
6. `ecancel`이 원자를 `isDefEq`로 비교하다가 복잡한 값에서 재귀 한도에 닿는다. reducible 투명도로 바꿀 계획이 있는가?
7. 하드웨어 대조를 외부 사용자가 자기 함수에 대해 돌리는 권장 방법이 있는가(메모리 상태 비교 포함)? `StateSummary`는 지금 레지스터와 플래그만 비교한다.
8. `bsr`, `lzcnt`, `popcnt`, `bt`, `div`, `rep movs`, `xorps`/`pxor`를 추가할 계획이 있는가? 기여를 받는다면 CONTRIBUTING의 AI 공개 규칙 외에 필요한 절차는?
9. Sail x86 연결의 일정과 범위는?

## 9. 이견

1. **`kstep` 대신 자체 단계 보조정리.** 브리프는 `kstep`, `grind`, `vcgen`의 자동화 정도를 재라고 했다. `kstep`을 먼저 썼다(거부 경로의 저장, 비교, 분기). 두 번째 rip 적재에서 `kstep` 안 `grind`가 시간 초과로 끝났고, 수용 경로에서는 저장 하나에서도 끝났다(TOOLS.md). 그 뒤 `kunfold` + `load_step`/`store_step`으로 바꿨다. `vcgen`은 main에 없다.
2. **main만 평가했다.** README는 1만 명령어 증명이 `vcgen` 브랜치에 있다고 적었다. 브리프가 지정한 6064eec(main)로 했다. `vcgen` 브랜치는 구조만 읽었다(C14).
3. **`include_x64` 대신 `include_x64_rt`.** 정교화기를 먼저 시도했고 4개 함수에서 `jg`/`jge`로 실패했다. 두 파서가 모두 받는 5개 함수에서 결과가 같음을 확인했다.
4. **패딩 nop 정규화.** 런타임 파서가 `nopl (%rax)`, `data16 nop`을 거부한다. `nop`으로 바꿨다. Kraken은 지시어 크기를 추상으로 두므로 의미가 같다.
5. **K5 미실행.** Docker 데몬 무응답. Docker Desktop을 재시작하지 않았다(다른 세션 영향).
6. **레이블 신선성 전제.** 레이블 주소를 실제 바이너리에서 증명하지 않고 "Host에서 함수 앞에 같은 레이블이 없다"를 전제로 두었다.
7. **사후조건의 프레임.** 수용·인코더 정리의 메모리 사후조건은 이름 붙인 조각과 `⋆ True`다. 나머지 메모리가 그대로라는 것은 말하지 않는다. 1a도 이름 붙인 객체만 말했다.
8. **EthLib 연결의 형태.** 1a와 같이 기계 전제를 `bs = enc g`인 `g`에 대해 받는다(`P : ∀ g, bs = scEncode g → …`).
9. **자기 완결 재배치.** 사용자 지시로 명세 파일, 대상 타입, 드라이버를 `fv/kraken` 아래로 복사했다. Lean 코드는 그대로이고 주석만 고쳤다. c60e0d2 이후 커밋은 `fv/kraken` 밖을 건드리지 않는다.

## 10. 재현

```sh
fv/kraken/link/build.sh                                  # ELF, objdump, 변환 (저장소 루트에서)
cd fv/kraken/lean && lake build                          # 모든 정리 (nightly-2026-09-21)
lake env lean --run scripts/ParseCheck.lean ../link/out/norm/target.*.S
lake env lean scripts/Axioms.lean                        # = ../AXIOMS.txt
```
