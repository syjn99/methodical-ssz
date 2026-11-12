# REPORT-ENC: 첫 가변 길이 인코더 손 증명 (ENC)

**판정: 조건부.**

조건:

1. 런타임 호출은 계약 가설이다(`MemmoveC`, `GrowsliceC`). Go 런타임 기계어의 정교화 증명은 없다.
2. 늘림 경로는 자리 1에서 한 번 늘리는 경우(G)만 K다. 그 밖의 늘림 경우(G*)는 N이다.
3. RT 거부는 처음 두 자리가 늘지 않는 경우만 K다.
4. 전제 `guard + 8 < rsp`가 morestack 경로를 막는다. 이 함수에는 쓰기 장벽 호출이 없다.
5. 디코드 뒤 인코드의 합성은 N이다. 이 타입의 디코더 증명이 레포에 없다.
6. Go 차분 시험, x86-64 실행 대조, 부정 시험(변이)은 실행하지 않았다.
7. 독립 리뷰는 아직 없다. 모든 K는 작성자의 빌드 결과다.

## 1. 대상과 핀

| 항목 | 값 |
| --- | --- |
| 대상 | `(*v1alpha1.DataColumnsByRootIdentifier).MarshalSSZTo` (`fulu.ssz.go:1754`), 지시어 118개, 명령어 107개 |
| 타입 | `block_root` Bytes32, `columns` List[uint64, 128] |
| 기준 커밋 | `1b5f524` (`claude/ssz-fv-list-vector-20261112`) |
| 브랜치 | `syjn99/ssz-fv-enc` |
| ELF sha256 | `c6403c02a110ffd6fe6d31a3c89cd395ac457b5d62e60e2e611b8ab9a8dd911e` |
| Kraken | `6064eecbb730a1152aa6ed891a155d3a92a4f298` |
| EthLib | `862185680cf23ccf54d44eb25b63b26c5020597b` |
| Lean | `4.36.0-nightly-2026-09-21` |
| 호스트 | darwin/arm64. 무거운 작업은 `heavy.py`(상한 40960 MB)로 하나씩 돌렸다 |
| 모델 | 구현 `claude-opus-5-5` |

선정 이유는 `SELECTION-ENC.md`에 있다.
설계는 `DESIGN-ENC.md`에 있다.
명령, 종료 코드, 시간, RSS는 `STEPS-ENC.tsv`에 있다. 로그는 로컬에만 있다.

## 2. 의무별 결과 (K 커널 검사, X 실행만, N 미증명 또는 미실행)

| 의무 | 결과 | 종류 | 정리 또는 파일 |
| --- | --- | --- | --- |
| 1 선정 | `DataColumnsByRootIdentifier` | X | `SELECTION-ENC.md`, `callgraph-enc.json` |
| 1 IndexedAttestation 확인 | `AttestationData.MarshalSSZTo`는 호출이다. 인라인되지 않았다. 제외 | X | `callgraph-enc.json` |
| 2 링크 (a)–(f) | PASS all, 묶음 `f7cdf5e5…` | X | `link-enc/RESULT` |
| 3 설계 | 경로, 불변식, 쓰는 바이트 | — | `DESIGN-ENC.md` |
| 4 고정 문장 | 8개, 증명 전 커밋 `abd42d8` | — | `lean/E2eEnc/StmtEnc.lean` |
| 5 F 용량 충분 | K | K | `dc_e2e_marshal_fast_main : dc_marshal_fast_stmt` (`Fast.lean`) |
| 5 F 명세 | K | K | `dc_e2e_marshal_spec : dc_marshal_spec_stmt` (`SpecM.lean`) |
| 5 G 자리 1 늘림 | K | K | `dc_e2e_marshal_grow_main : dc_marshal_grow_stmt` (`Grow.lean`) |
| 5 G 명세 | K | K | `dc_e2e_marshal_grow_spec : dc_marshal_grow_spec_stmt` (`SpecG.lean`) |
| 5 RB 길이 거부 | K | K | `dc_e2e_reject_bytes_main : dc_reject_bytes_stmt` (`Reject.lean`) |
| 5 RT 초과 거부 | K | K | `dc_e2e_reject_toobig_main : dc_reject_toobig_stmt` (`Reject.lean`) |
| 5 RB, RT 명세 | K | K | `dc_e2e_spec_reject_bytes`, `dc_e2e_spec_reject_toobig` (`Spec.lean`) |
| 5 명세 다리 | K | K | `pdc_serialize`: `serialize prysmDcDesc g.toValue = .ok (pdcEnc g)` |
| 5 루프 | K | K | `dc_iter`, `dc_exit`, `dc_loop` (`Loop.lean`), `dc_tail` (`Tail.lean`) |
| 5 G* 그 밖의 늘림 | 문장 없음 | N | 7절 |
| 5 RT, 늘리는 경우 | 문장 없음 | N | 처음 두 자리가 늘면 문장 밖이다 |
| 6 F 증인 | n = 0, 1, 128 | K | `WitF.dcf_runs_n0`, `dcf_runs_n1`, `dcf_runs_n128` |
| 6 G 증인 | n = 0, 1, 128 (len 3321, cap 3352) | K | `WitG.dcg_runs_n0`, `dcg_runs_n1`, `dcg_runs_n128` |
| 6 RB 증인 | 모든 bl ≠ 32 (예: 0, 31, 33) | K | `WitR.RB.dcrb_runs` |
| 6 RT 증인 | n = 129 | K | `WitR.RT.dcrt_runs` |
| 7 합성 | 디코더 수용 명세가 없다 | N | — |
| 8 `lake build E2eEnc` | exit 0, 636 jobs | X | 로그 63 |
| 8 `--no-build` 전체 | E2e E2eAd E2eScal E2eList E2eEnc: exit 0, 1102 jobs | X | 로그 64 |
| 8 공리 게이트 | PASS, 선언 6582, 정리 5482, 손 목록 483, 비표준 0, sorryAx 0 | X | `axioms-gate-enc.json` (로그 65) |
| 8 게이트 대조군 | 심은 `sorry`로 FAIL(기대대로) | X | `axioms-gate-enc-plant.json` (로그 59) |
| 8 금지 단어 grep | `E2eEnc/*.lean`에 없음. `AxiomsEnc.lean`의 주석 "axiom check"만 걸린다 | X | — |

공리 게이트는 새 파일 `gen/e2e/encaxioms_gate.py`다.
기존 `axioms_gate.py`와 `lvaxioms_gate.py`를 import한다. ROOTS에 `E2eEnc`, 손 목록에 `AxiomsEnc.lean`을 더한다.
심은 대조군의 `.olean`은 빌드 디렉터리에 잠시 두고 바로 지웠다.

## 3. 계약 인스턴스

| 지시어 | 피호출자 | 인스턴스 | 쓰는 정리 |
| --- | --- | --- | --- |
| 23 | `runtime.growslice` (자리 1) | `GrowsliceC Heap E2e.Data.e2eU8Type_addr 1 S` | G |
| 36 | `runtime.memmove` | `MemmoveC S`, n = 32 | F, G, RT |
| 49, 94 | `runtime.growslice` (자리 2, 3) | 같은 꼴 | 없음. F와 G는 안 갈림을 증명한다 |
| 112 | `runtime.morestack_noctxt.abi0` | 전제 `guard + 8 < rsp` | 모두 |

- 새 계약 꼴은 없다. 원소 크기는 1이다. 모델 `rt_growslice`(esz 1)가 그대로 맞았다.
- 형식 단어 `type__+387072`는 Checkpoint 인코더의 단어와 같다(`enclink.py data`가 확인).
- 데이터 읽개(`*_data_include`)는 새로 만들지 않았다. 문장은 기존 이름과 레이블을 쓴다.

## 4. 장애물 목록

### 4.1 계약 꼴과 모델

- 없는 계약 꼴은 없었다. F, G, RB, RT 모두 기존 꼴로 닫혔다.
- G*는 계약 때문에 막힌 것이 아니다. 증명 설계의 문제다(7절).

### 4.2 Kraken 명령어

- 새 명령어 빈틈은 없었다.
- `add $-0x80,%rsp`, `sub $-0x80,%rsp`는 −128로 읽혔다.
- `movl $0x24,-0x4(%rbx,%rax,1)`(32비트 즉시값, SIB 주소)는 `Int.toBytes 4 (BitVec.truncate 32 36)`로 읽혔다.
- 32비트 `xor`(`xor %esi,%esi` 등)는 정의되지 않은 AF를 만든다. 매번 `intro _`가 필요했다.
- `mov ssz.X(%rip)` 읽기에서 `ecancel`이 실패한 적이 있다. 원인은 앞 단계의 잘못 나눈 조각이었다(로그 32–36). 도구 결함이 아니다.

### 4.3 루프와 증명 크기

- 루프 한 바퀴 안에서 `omega`로 주소와 비교 사실을 바로 닫으면 커널이 무거워졌다.
- 로그 11: 작성자가 340 s 뒤 lean을 죽였다. 표본 RSS 최대 16.7 GiB다. 결과는 통과가 아니다.
- 로그 12: 증명을 잘라 다시 돌렸다. 188 s, 20.4 GiB, `dc_iter`에서 커널 깊은 재귀 오류다.
- 고침: 주소와 비교 사실을 기계 문맥 밖의 작은 보조정리로 옮겼다(`dc_addr`, `dc_room`, `dc_rbx`, `dc_inc`, `dc_idx`).
- 그 꼴은 Go 1.26.3 `Fk/LuMarshal.lean`(`lum_addr`, `lum_room`)의 꼴이다. 고친 뒤 `Loop` 빌드는 6.2 s다.
- 무거운 부분의 정확한 항은 프로파일하지 않았다. "omega 증명 항이 원인"은 추론이다.
- 주 정리에는 `maxHeartbeats`, `maxRecDepth` 설정이 없다.

### 4.4 증인 비용

| 증인 | `maxHeartbeats` | `maxRecDepth` | 측정 |
| --- | --- | --- | --- |
| `WitF` 셋 | 4000000 | `dcf_runs_n128`만 20000 | heartbeats: 200000, 1000000 실패, 4000000 통과(로그 40–42). recDepth: 512, 2000 실패, 20000 통과(로그 60–62) |
| `WitG` 셋 | 4000000 | 20000 | heartbeats: 1000000 실패, 4000000 통과(로그 45, 46). recDepth: 위와 같다 |
| `WitR.RT` | 4000000 | 기본값 | 200000, 1000000 실패, 4000000 통과(로그 49–51) |
| `WitR.RB` | 기본값 | 기본값 | — |

- 프로파일: 증인 하나에 `simp` 10–12 s다. 메모리 전제를 `sep_comm`으로 정렬하는 단계다(LV 로그 27과 같은 원인).
- `WitR.RT`의 `simp`는 2.5 s다. 나머지 heartbeats를 쓰는 `whnf`는 더 나누지 않았다.
- `maxRecDepth`의 원인은 프로파일하지 않았다. 긴 상수 목록(`z k`)이 의심이다. 사실로 확인하지 않았다.
- 본으로 복사한 파일 전체 `maxRecDepth 100000`은 측정 뒤 지웠다(`566c09d`).

### 4.5 시간과 메모리 (heavy.py, n = 1, 표본 RSS는 그룹 합의 상한 추정)

| 모듈 | 모듈 시간 | 벽시계 | RSS |
| --- | --- | --- | --- |
| StmtEnc | 3.4 s | 8.3 s | 1.93 GiB |
| Loop | 4.2 s | 6.2 s | 2.08 GiB |
| Tail | 6.2 s | 8.3 s | 2.28 GiB |
| Fast | 4.4 s | 6.2 s | 2.02 GiB |
| Spec, SpecM | 3.2 s, 3.4 s | 8.3 s | 0.94 GiB |
| Grow | 6.0 s | 8.3 s | 2.25 GiB |
| SpecG | 3.5 s | 5.2 s | 0.95 GiB |
| Reject | 6.9 s | 9.4 s | 2.16 GiB |
| WitF | 63 s | 91.7 s (WitF, WitG 함께) | 3.44 GiB |
| WitG | 90 s | 위와 같다 | 3.44 GiB |
| WitR | 20 s | 20.8 s | 2.05 GiB |

새 Lean 줄: Code 18, Defs 47, StmtEnc 338, Loop 203, Tail 270, Fast 92, Grow 179, Reject 310, Spec 53, SpecM 32, SpecG 36, WitF 140, WitG 185, WitR 142.
새 스크립트: `enclink.py` 99줄, `encaxioms_gate.py` 38줄, `AxiomsEnc.lean` 32줄.

## 5. 디코더 증명에서 다시 쓴 것과 못 쓴 것

다시 쓴 것:

- 루프 증명의 뼈대: `E2eList.IaLoop`의 `ia_iter`, `ia_exit`, `ia_loop` 꼴(남은 바퀴 수에 대한 재귀).
- `Fk.block_split`, `E2eList.jge_false512`, `E2eScal.lea_cmp_be_false`(N = 8), `Fk.add8_neg8`.
- 명세 쪽: `Fv1.serializeEach_u64`, `Fv1.inl_*`, `Fv1.u64Bytes_size`, `E2eList.pia_serialize`의 증명 순서.
- 계약 모델과 증인 Host: `rt_memmove`, `rt_growslice`, `bumpHeap`, `Fk.WHost`(`mkHost`, `wit_split`).
- 증인 본: `E2e.WitCpM`, `E2e.WitCpG`, `E2e.WitCpMR`.

못 쓴 것:

- 디코더 루프 불변식은 "앞 i개 ++ 0"이다. 인코더는 "앞 i개 ++ 옛 내용"이다. 그래서 `enc_split`, `enc_join`을 새로 썼다.
- 디코더의 머리·꼬리 구간 보조정리는 쓸 곳이 없었다. 인코더는 읽기보다 쓰기가 많다.
- RT는 `dc_tail`의 29–54 지시어 증명 글을 복사했다. 갈림이 꼬리 중간(55)에 있어서다.
- 디코더 Data/Include 읽개는 필요 없었다. 이 함수의 전역은 레이블 주소뿐이다.

## 6. 더한 신뢰 항목

- `MemmoveC`, `GrowsliceC`는 가설이다. 모델 증명은 비공허성 근거일 뿐이다(`CONTRACTS.md` 3절).
- 손 `Desc`(`prysmDcDesc`)와 consensus-specs의 같음은 판단이다. 생산자 `Desc`와의 대조는 하지 않았다(N).
- 증인 오류 단어(`0x10e8`, `0x2b`)는 대역 값이다. 실제 값은 런타임 초기화가 정한다.
- RT 경로는 거부 전에 dst의 남는 용량에 36바이트를 쓴다. 사후조건이 그것을 적는다. Go 의미대로이며 결함 후보로 보지 않았다.

## 7. G* (임의 자리 늘림): 막힌 이유

- 자리 2나 루프의 어느 바퀴에서도 growslice가 불릴 수 있다. 늘림 횟수는 경로마다 다르다.
- 늘릴 때마다 옛 블록이 계약의 사후조건에 남는다. 그래서 사후조건에 존재 술어(쓰레기 블록)가 필요하다.
- 힙 예산 전제도 늘림 횟수에 따라 정해야 한다. 각 늘림이 `2·nc + 8192`를 요구한다.
- 루프 불변식은 블록 포인터와 용량을 존재 변수로 두어야 한다. 한 바퀴 정리는 두 갈래(맞음, 늘림)가 된다.
- 계약 꼴은 충분하다. 막힌 것은 문장 설계와 시간이다. 이번 단위에서 문장으로 쓰지 않았다.

## 8. 실행하지 않은 검사

| 검사 | 상태 |
| --- | --- |
| Go 차분 시험 | 실행하지 않음 |
| x86-64 하드웨어 대조 | 실행하지 않음. 호스트는 arm64다 |
| 부정 시험(변이, `lvnegative.py` 꼴) | 실행하지 않음 |
| 선언 drift(`decl_drift.py`) | 실행하지 않음. 기존 파일은 lakefile 덧붙임 말고 바꾸지 않았다 |
| 생산자 `Desc` 대조 | 실행하지 않음 |
| stale 검사 | 실행함, exit 1, 518개 표시(로그 66). `.lake`를 APFS 복제해서 기존 산출물의 mtime이 원천보다 오래다. E2eEnc 산출물 22개는 AFTER(표시 기준 뒤에 씀)다. 죽인 빌드(로그 11)의 모듈 `E2eEnc.Loop`는 로그 13, 14에서 다시 빌드했다 |

## 9. 커밋

`70cf11f`(선정, 링크), `abd42d8`(문장, 설계), `6f39561`(루프), `f679153`(꼬리), `441b9cc`(F), `d9d6c4f`(명세), `208254f`(G), `26731a2`(G 명세), `38773d1`(거부), `4630633`(WitF), `d74fe38`(WitG), `8af7614`(WitR), `566c09d`(설정 정리, 게이트), 그리고 이 보고서의 커밋.

## 10. 시도 셈

- 한 시도는 한 증명 전략이다. 같은 전략 안의 오류 수정 빌드는 개발 단계로 셌다(LV와 같은 해석).
- 루프(의무 5): 시도 1(기계 문맥 안의 `omega`)은 로그 11, 12에서 실패했다. 시도 2(작은 보조정리)가 통과했다.
- 나머지 의무는 시도 1에서 통과했다. 한도(3회)에 닿은 의무는 없다.
- 개발 중 목표를 볼 때 `sorry`를 쓰지 않았다. 덜 끝낸 증명을 빌드하고 미해결 목표를 읽었다.
