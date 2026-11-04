# TOOLS: Kraken 평가 도구 기록

날짜: 2026-11-04. 호스트: macOS arm64, 18코어, 48 GB. 시간은 `/usr/bin/time`의 real 값, 메모리는 최대 RSS다.

## 버전

| 항목 | 값 |
| --- | --- |
| Kraken | `6064eecbb730a1152aa6ed891a155d3a92a4f298` (2026-11-02, upstream tip과 같다) |
| Lean (`fv/kraken/lean`) | `nightly-2026-09-21` (4.36.0-nightly, commit ca39d2bc) |
| EthLib | 8621856 (git 의존성, SSZ 폐포만 import) |
| Go | 1.26.3 |

## K0 툴체인

브리프의 순서 (a) → (b) → (c)대로 시험했다.

| 시도 | 시각 | 결과 | 첫 오류 | 시간, RSS |
| --- | --- | --- | --- | --- |
| (a) v4.35.0 프로젝트(`k0a/`), Kraken git 의존성 | 21:41 | **부분.** `Kraken.X64.Semantics`, `OmniSemantics`, `WP`, `Tactics`, `SeparationTactics`, `X64.Sep`은 빌드된다. 파서(`Kraken.X64.Parser`)와 그것을 쓰는 예제는 빌드되지 않는다. | `Kraken/SyntaxAffixed.lean:86:57: Unknown identifier mkMarkdownDocComment` (4.35.0에 없는 Lean API) | 의미론만 9 s, 1.3 GB. 전체 시도 7 s에 실패 |
| (b) nightly 프로젝트(`k0b/`), Kraken + EthLib SSZ 폐포 | 21:46 | **성공.** Kraken 전체(파서, 예제 포함)와 Transfer.lean이 쓰는 EthLib 증명 모듈 5개가 빌드된다. | 없음 (경고만: 모듈 시스템 권고, `dif_pos` 폐기 예정) | 332 s (nightly 설치와 패키지 복제 포함), 1.38 GB |
| (b) 이어서: 1단계 명세 재사용(`lean/`) | 21:53 | **성공.** `Fv.Spec`(0단계), `Fv1.SpecScalars`, `Fv1.SpecList`, `Fv1.Transfer`를 원래 위치에서 수정 없이 빌드한다(`srcDir`). | 없음 | 22 s |
| (c) | | 시도하지 않음. (b)가 되었다. | | |

결정: `fv/kraken/lean`은 nightly-2026-09-21 단일 툴체인이다. EthLib 연결이 가능하다.

참고: 1단계 `Fv1.SpecFixed`는 `Fv1.SizeSpec → Fv1.Size → MiniRV`를 끌어온다. 그래서 재사용 대상에서 뺐다. FixedVec 명세가 필요하면 그 부분만 옮겨 적는다.

lake 주의: `rev = "6064eec"`(짧은 해시)는 `fatal: couldn't find remote ref`로 실패한다. 전체 해시를 쓴다.

## K1 대상과 변환

| 항목 | 값 |
| --- | --- |
| 빌드 | `GOOS=linux GOARCH=amd64 CGO_ENABLED=0 go build -tags purego -trimpath ./fv/kraken/cmd/p1bin` (`link/build.sh`) |
| 대상 | `fv/kraken/target` (1단계 대상 타입의 복사본, 생성 파일 sha256 `26eda6b6…e096`) |
| ELF sha256 | `link/out/build-ids.txt` (재배치 뒤 `bd3cb698…2a7a`). 9개 함수의 어셈블리는 재배치 전후로 같다(레이블이 함수 안 상대 오프셋이다) |
| 변환기 | `link/conv.py`: objdump `-gnu`의 AT&T 주석 열 → 레이블 어셈블리. 절대 점프는 `L_<함수>_<오프셋>` 또는 기호 이름, `disp(%rip)`은 `기호+오프셋(%rip)`. `--norm`은 패딩 `nopl (%rax)`, `data16 nop`을 `nop`으로 바꾼다 |
| 기호 | Go `nm`은 타입 기술자를 크기 0인 `type:*` 하나로 묶는다. 그 안의 주소는 앞의 가장 가까운 기호 + 오프셋(`type__+48128`)으로 적는다 |

### 파서 결과 (9개 함수)

| 함수 | 명령어 | 런타임 파서(원본) | 런타임 파서(`--norm`) | `include_x64` 정교화기 | 외부 기호 |
| --- | --- | --- | --- | --- | --- |
| Scalars.SizeSSZ | 2 | 통과 | 통과 | 통과 | |
| Scalars.MarshalSSZTo | 122 | 통과 | 통과 | 통과 | growslice, morestack, type |
| Scalars.UnmarshalSSZ | 28 | 통과 | 통과 | 통과 | ErrSize, ErrInvalidSerialization |
| FixedVec.SizeSSZ | 2 | 통과 | 통과 | 통과 | |
| FixedVec.MarshalSSZTo | 91 | `data16 nop` 1곳 거부 | 통과 | `jge` 거부 | growslice, memmove, morestack, ErrBytesLength |
| FixedVec.UnmarshalSSZ | 75 | `data16 nop` 1곳 거부 | 통과 | `jge` 거부 | makeslice, memmove, gcWriteBarrier2, writeBarrier, panicBounds, morestack, ErrSize |
| ListU64.SizeSSZ | 4 | 통과 | 통과 | 통과 | |
| ListU64.MarshalSSZTo | 83 | `nopl (%rax)` 1곳 거부 | 통과 | `jg` 거부 | growslice, morestack, ErrListTooBig |
| ListU64.UnmarshalSSZ | 175 | `nopl (%rax)` 5곳 거부 | 통과 | `jg` 거부 | makeslice, convT64, newobject, fmt.errorf, gcWriteBarrier2, writeBarrier, panicBounds, morestack, Err 4개, itab, go_string |

- 두 파서가 모두 받는 5개 함수에서 두 파서의 결과 항은 같다(`Fk/Code.lean`, `decide`).
- 정교화기 `include_x64`의 조건 코드 목록(`Parser/Syntax.lean`의 `declare_affixes cc`)에 `g, ge, nl, nle, s, ns, o, no, p, np`가 없다. 런타임 파서와 의미론에는 있다. 우리 쪽 정교화기 `include_x64_rt`(`Fk/Include.lean`)가 런타임 파서 결과를 Kraken이 파생한 `ToExpr`로 항으로 만든다.
- 의미론에 없는 명령어는 없었다. 증명에서 실행한 형태: `mov`(8/16/32/64, imm, mem), `movzbl`, `movzwl`, `lea`(SIB 포함), `cmp`, `cmpl`/`cmpb`(mem, imm), `test`, `add`, `sub`, `inc`, `neg`, `and`, `xor`, `shl`, `shr`, `sar`, `push`, `pop`, `call`, `ret`, `jmp`, `jcc`(ne, a, be, ae, b, ge, g, e), `nop`. 오류 경로의 `movups %xmm15`는 Kraken에 있다(`AvxOperation.movups`). 실행하지 않았다.

## K2–K4 증명 도구

Kraken main의 증명 자동화(`kprologue`, `sym => kstep`)는 처음부터 직선으로 실행하는 `straightlineStep` 목표용이다. 이 스냅샷의 x64 예제에는 점프를 실제로 타는 증명과 루프 증명이 없다(`p3_correct`는 `sorry`). `Program.wp`(Host 안 조각의 WP)는 정의와 건전성 정리만 있다. 그래서 다음을 우리 쪽에서 만들었다(`Fk/`). Kraken 의미론과 프로그램 논리(`Eventually`, `step1`, `Host`, `Mem`, `⋆`, `ecancel`)는 그대로 쓴다.

| 파일 | 내용 | 줄 |
| --- | --- | --- |
| `Step.lean` | `estep`(Host 안 한 지시어, `Host.eventually_of_interp` 사용), `load_step`/`store_step`(Kraken `load_sep`/`store_sep`, 새 메모리는 새 변수), 주소 정규화 보조정리, 매크로 `kunfold`, `kat`, `kshl64`, `kaddr` | 154 |
| `Labels.lean` | 레이블 해석: `label l = Host.addrOf j`(Host에서 처음 나오는 `.label l`), `LabelsFresh`, 매크로 `klabel` | 104 |
| `Flags.lean` | 분기 조건과 주소 산술의 독립 보조정리 | 111 |
| `Block.lean` | 배열 블록 분할(`At_append_sep`), 부호 비교 | 44 |
| `Bytes.lean` | 저장 값 = 입력 바이트, 프레임 약화 | 26 |

증명 모듈 깨끗한 재빌드: 19.7 s, 최대 RSS 1.7 GB. 정리 57개, 모두 `propext`, `Classical.choice`, `Quot.sound`만 쓴다(`AXIOMS.txt`).

## 막힌 오류와 대응

| 증상 | 원인 | 대응 |
| --- | --- | --- |
| `kstep` 안에서 `(deterministic) timeout at «grind tactic execution»` | `kstep`이 분리 논리 부가 목표를 `grind`로 닫으려 한다. 맥락이 크면 끝나지 않는다. 시간 초과는 런타임 예외라서 `kstep`의 `try … catch`가 잡지 못한다 | `kstep`을 쓰지 않고 `kunfold` + `load_step`/`store_step` |
| `ecancel: could not automatically solve goal` (주소 같음) | 주소 정규형 차이: `rsp + 16#64` 대 `rsp + 16`, `ofInt 64 (x.toInt + 16)` 대 `x + 16` | 정규화 보조정리(`ofInt_toInt_add`, `ofInt_sib`, `rip_addr'`), 또는 주소 등식을 따로 증명하고 `rw` |
| `ecancel` 실패 (값 같음) | 저장 값의 폭 인수가 `Width.W64.bits`로 남았다(`@BitVec.toInt Width.W64.bits x`). 표시는 같다 | 새 메모리 사실마다 `simp only [Width.bytes, Width.bits]` |
| `maximum recursion depth` at `apply estep (isInfixAt_drop hk 44)` | 193개 원소 리터럴 리스트의 `List.drop 44`를 정의 펼침으로 계산 | `simp only [List.drop_succ_cons]`로 계산(`kat`) |
| `maximum recursion depth` (레이블 부가조건) | `decide`/`rfl`로 `p[43]?`, `take 43`의 `contains`를 증명한 항 | `simp only [List.getElem?_cons_succ, …]`(`klabel`) |
| `ecancel` 안 `simp`의 `maximum recursion depth` | 조각 값이 복잡한 식(`ushiftRight (-4 + rcx) 3`)이면 원자 비교의 `isDefEq`가 펼치다가 깊어진다. 조각 수는 원인이 아니었다(12개로 줄여도 같았다) | 계산 값을 `generalize`로 새 변수로 |
| `bv_omega` 안 `simp`의 `maximum recursion depth` | `bv_omega`는 모든 가설을 `simp`한다. 큰 분리 사실이 있으면 깊어진다 | 목표만 보는 `kaddr` 또는 독립 보조정리 |
| `(kernel) deep recursion detected`, 검사 8–9분 | (1) 64비트 리터럴(2^64 − 8 등)을 포함한 식을 `simp; omega`로 닫은 증명 항. (2) `[].At x = [].At y`를 `rfl`로 닫은 항(`ExtHashMap.ofList` 펼침) | 분기 조건·주소 산술을 맥락이 작은 독립 보조정리로(`Flags.lean`), `rfl` 대신 `simp [List.At]`. 이분 탐색은 시간 제한 120–200 s로 했다 |
| `omega`가 같은 식을 맥락 안에서는 증명하지 못함 | 확인하지 않았다(맥락 밖 독립 보조정리로는 통과) | 독립 보조정리(`call_slot`, `pop_slot`, `ret_slot`) |
| `store_step_at`(주소 등식형)의 `apply`가 SIB 주소에서 재귀 한도 | 확인하지 않았다 | 주소를 먼저 `rw [show … by bv_omega]`, 그다음 `store_step` |
| `bv_decide` | `Lean.ofReduceBool` 공리를 끌어온다 | `toNat` + `omega`로 바꿨다 |

## K5 대조

| 시도 | 결과 |
| --- | --- |
| Kraken 하드웨어 대조(`Kraken/X64/Test/asm_tests.py`) | 실행하지 않았다. 이 하네스는 테스트 `.S`를 `as`/`ld`로 정적 ELF로 만들어 x86-64에서 직접 실행하고 `krakenrunner_x64` 결과와 비교한다. 호스트는 arm64 macOS다 |
| Docker `--platform linux/amd64` (qemu-user 에뮬레이션) | 2026-11-05 00:00경 Docker 데몬이 응답하지 않았다. `docker run`, `docker images`가 300 s 안에 끝나지 않았다. `timeout 30 docker version`은 출력 없이 끝났다. 다른 세션이 Docker를 쓸 수 있으므로 Docker Desktop을 재시작하지 않았다 |
| `qemu-x86_64` | 이 호스트에 없다(macOS용 qemu에는 사용자 모드가 없다) |
| 함수 전체 대조 | 하지 않았다(위의 이유) |

에뮬레이션으로 돌린다 해도 비교 대상은 하드웨어가 아니라 qemu다. 보고할 때 구별해야 한다.
