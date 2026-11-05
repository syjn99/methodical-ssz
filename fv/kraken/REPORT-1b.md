# REPORT-1b: 1단계 이정표 1b (Kraken x64)

기준: 브랜치 `syjn99/ssz-fv-phase1b`, 시작 `syjn99/ssz-fv-kraken`. Kraken `6064eec`(main), Lean `nightly-2026-09-21`, EthLib `8621856`, Go 1.26.3, `GOAMD64=v1`(TOOLS.md "고정 버전"). 작성 2026-11-05. 시각은 IST 에이전트 시간이다. 사람 시간이 아니다.

## 0. 판정

**게이트 1: 부분 통과.** 6개 타입 종류 중 4개(bitvector, 중첩 container, Prysm 2타입)는 인코더, 디코더(수용과 거부), 크기 정리가 모두 통과한다. bitlist는 모두 통과하지만 핵심 검사가 계약(`ValidateBitlistC`) 뒤에 있다. List[container]는 크기와 디코더 거부만 통과한다. 디코더 수용과 인코더는 증명하지 않았다(12절).

- 정리 500개. `sorry` 0개. 모든 정리가 `propext`, `Classical.choice`, `Quot.sound`만 쓴다(`AXIOMS.txt`, `lean/tools/axioms.sh`).
- 링크 검사(`link/check.py`): 27개 함수 + `ssz.ValidateBitlist`, 2751개 명령어. 바이트 대응, 경계, 전역 주소, 레이블 신선성, 재조립 모두 PASS. 번들 sha256 `9c92e9fd…ffc`(`link/out/RESULT`).
- 발견 2개. **F1**: BitVec 디코더가 패딩 비트가 선 바이트를 받는다. **F2**: BitL 인코더의 길이 검사가 비트가 아니라 바이트를 센다. 둘 다 Lean 정리이고 Go 시험(`semtest/f12_test.go`)으로 재현된다(5.2절).
- 하드웨어 대조는 실행하지 않았다(이 호스트는 arm64). 스크립트만 있다(`semtest/run.sh`).

## 1. 정정: 평가 세션의 `lu_accept_main`

REPORT.md 1절은 `lu_accept_main`을 "수용 경로 전체"로 표시했다. 그 판은 공허했다. 계약 가설 `hms`가 모든 `cnt`와 모든 프레임 `F`에 양화되어 전제를 동시에 만족하는 상태가 없었다(astra, `review/ReviewKraken.lean`의 `lu_accept_preconditions_false`). 그 완료 표시를 철회했다(REPORT.md 1절에 정정 문단).

수정(B2.0):
- `MakesliceC Heap ty esz S`(`Fk/Contracts.lean`): 사전조건에 런타임 힙 조각 `Heap avail`, 타입 인수 `rax = ty`, `len ≤ cap = cnt`, `esz·cnt ≤ avail`을 둔다. 사후조건의 0 블록은 `Heap`에서 떼어낸다. 그래서 블록은 반환 슬롯, 스택, `F`와 서로소다.
- `bump_makeslice`(`Fk/Bump.lean`): 범프 할당기 기계어(`Fk/BumpAlloc.S`)가 이 계약을 만족한다.
- `lu_accept_runs`(`Fk/Witness.lean`): 구체 Host 하나에서 `lu_accept_main`의 모든 전제를 증명한다. n = 0, 1, 16.
- `lu_accept_main`을 새 계약으로 다시 증명했다(b6da965).

## 2. B0: vcgen 브랜치 평가

**main에 남는다.** 상세는 `vcgen/B0.md`.
- vcgen(sgraf812/kraken `a4cce2e`, `nightly-2026-10-29`)은 EthLib SSZ 폐포와 함께 빌드된다(262 s, 1.78 GB).
- Go ABIInternal은 `CallingConvention` `⟨[.rsp, .r14], …⟩`로 표현된다.
- `sc_accept_main`을 `funspec`으로 다시 증명해 보았다. 명령어 명세 5개를 우리 쪽에서 더했다. 그 뒤 검증 조건 16개 중 12개가 `kfinish`로 닫히지 않았다(저장 뒤 적재의 `isSome`, 분기 대상 불변식).
- 채택하면 메모리 모델(`Mem.Mapped`/`loadInt`)이 달라져 기존 증명을 다시 써야 한다. vcgen은 main에 합쳐지지 않았고 의미론 파일이 main과 159줄 다르다.

## 3. B1: 링크 수준 검사

`link/check.py`(검사 (a)–(d))와 `link/conv.py`(실패 조건 강화). 결과 `link/out/RESULT`, 자기 시험 `link/out/SELFTEST`.

| 검사 | 내용 | 결과 |
| --- | --- | --- |
| (a) | 함수마다 ELF `.symtab` 주소·크기 = objdump 범위, 바이트 = ELF 파일 바이트, `llvm-objdump` 독립 디코딩의 명령어 경계 = objdump, `.S` 레이블 = 명령어 주소 | 28개 함수 PASS |
| (b) | 전역·외부 기호(`ssz.Err*`, `runtime.writeBarrier`, `type__+…`, 런타임 함수)의 주소와 섹션 | PASS |
| (c) | `LabelsFresh`: `all.S`(실제 Host 배치)에서 함수 레이블이 유일 | PASS |
| (d) | `.S`를 `clang --target=x86_64-linux-gnu`로 원래 주소에 다시 조립한 바이트 = ELF 바이트 | 2751개 중 2702개 같음, 49개는 패딩 nop(표: RESULT의 `DIFF (d) … padding` 줄) |
| 번들 | ELF sha256 하나로 `.S` 28개, `Code.lean`, `AXIOMS.txt`, RESULT를 묶는다. 해시는 마지막 PASS 줄 뒤에 찍는다 | `9c92e9fd…ffc` |

`conv.py`는 이제 다음에서 실패한다: `//`가 없는 objdump 행, 주소 틈, 명령어 중간을 가리키는 분기, 이름 정리 충돌. 자기 시험 6개(명령어 하나 삭제, 즉치값 변경, 레이블 이동, `//` 없는 행, 전역 오프셋 변경, 변경 없는 사본)가 모두 기대대로 실패·통과한다.

## 4. B2: 1a 잔여

| 항목 | 결과 | 정리 |
| --- | --- | --- |
| B2.0 makeslice 계약, 증인 | 완료 | 1절 |
| B2.1 ListU64 수용의 EthLib 연결 | 완료 | `lu_unmarshal_accept_spec_k` |
| B2.2 FixedVec | 크기, 마샬 빠른 경로, 수용, 거부 완료 | `fv_size_main`, `fv_marshal_main`, `fv_accept_main`, `fv_reject_size_main`, `*_spec_k` |
| B2.3 ListU64 거부 전부, 오류 대응 | 4경로 완료. EthLib는 "4개 Go 검사가 모두 통과 ⟺ 받음" | `lu_reject_short_main`, `lu_reject_offset_main`, `lu_reject_toobig_main`, `lu_reject_misaligned_main`, `lu_spec_accepts_iff` |
| B2.4 ListU64 마샬, 왕복 3타입 | 완료 | `lu_marshal_main`, `sc_roundtrip`, `lu_roundtrip`, `fv_roundtrip` |
| B2.5 growslice | 한 지점(ListU64 마샬의 오프셋 append) 증명. 나머지 지점 추정은 11절 | `GrowsliceC`, `lum_grow_site` |
| B2.6 CONTRACTS.md | 완료(1b 표 추가). havoc 색인 문제가 Kraken 가설 형식에서 생기지 않음을 3절에 적었다 | |
| B2.7 부정 사례 | 변이 3개가 지정 정리의 변이 지시어에서 실패, 대조군 통과(`negative/RESULT`) | 표는 아래 |
| B2.8 `dst[:len]` 보존 | 모든 마샬 정리의 사후조건에 `pre` 조각 | |

| 변이 | 위치 | 지정 정리 | 결과 |
| --- | --- | --- | --- |
| 오프셋 상수 4 → 8 | `target.ListU64.UnmarshalSSZ.S:15` | `lu_accept_main` | FAIL `LuAccept.lean:114` |
| 길이 검사 `jg` 제거 | `…UnmarshalSSZ.S:28` | `lu_reject_toobig_main` | FAIL `LuRejectCall.lean:187` |
| 루프 경계 4 → 3 | `target.FixedVec.UnmarshalSSZ.S:47` | `fv_iter` | FAIL `FvLoop.lean:50` |
| 대조(같은 지시어로 바꿈) | 같음 | `fv_iter` | PASS |

변이는 지시어 수를 바꾸지 않는다. Kraken 배치는 추상이라 주소를 다시 만들 필요가 없다. 그래서 첫 PC 보조정리에서 깨지지 않고 변이 지시어에서 깨진다.

## 5. B3: 1b 범위

### 5.1 게이트 1 자평 (타입 종류별)

| 종류 | 타입 | 크기 | 인코더(빠른 경로) | 디코더 수용 | 디코더 거부 | EthLib 왕복 | 부정 입력 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| bitvector | BitVec (Bitvector4) | `bv_size_main` | `bv_marshal_main` | `bv_unmarshal_accept_spec_k` | `bv_reject_size_main` + `bv_reject_spec` | `bv_roundtrip` | 빈 값·초과 거부 증명. 패딩 비트는 Go가 받음(F1) |
| bitlist | BitL (Bitlist[2048]) | `bl_size_main` | `bl_marshal_main` | `bl_unmarshal_accept_spec_k` (**`ValidateBitlistC` 뒤**) | 짧음·오프셋: `bl_reject_*_main`. 검증 실패: 계약 뒤, 오류 경로 미증명 | `bl_roundtrip` | 빈 값·최대 수용 증명. 초과는 EthLib 거부만(`bl_spec_rejects`) |
| 중첩 container | Nested | `ne_size_main` (L ≠ nil) | `ne_marshal_main` | `ne_unmarshal_accept_spec_k` | 짧음·오프셋: `ne_reject_*_spec`. 피호출자 오류 감싸기 경로 미증명 | `ne_roundtrip` | `ne_spec_accepts_iff`로 EthLib 쪽 전부 |
| List[container] | ListC (List[ListU64, 4]) | `lc_size_main` + `lc_size_eq` | **없음** | **없음** | 5경로: `lc_reject_{short,offset,tail,zero,past}_spec`. 정렬 오류·원소 수 초과(convT64)와 루프 안 오프셋 검사 미증명 | `lc_roundtrip`(EthLib만) | 빈 값, 오프셋 0·작음·큼 증명. 정렬 안 됨은 EthLib 쪽만 |
| Prysm | Checkpoint | `cp_size_main` | `cp_marshal_spec_k` | `cp_unmarshal_accept_spec_k` | `cp_reject_size_main` + `cp_reject_size_spec` | `cp_roundtrip` | 길이 ≠ 40 전부 |
| Prysm | AttestationData | `ad_size_main` | `ad_marshal_main` + `ad_marshal_bytes` | `ad_unmarshal_accept_spec_k` | `ad_reject_size_main` + `ad_reject_size_spec` | `ad_roundtrip` | 길이 ≠ 128 전부 |

모든 수용 정리의 형태(1a와 같음): "EthLib `deserialize d bs = .ok v`이면 Go 값 `g`가 있고 `g.toValue = v`, `bs = enc g`이며, 그 `g`의 입력 조각으로 기계어가 nil을 반환하고 수신자가 `g`의 Go 배치를 담는다". 인코더 정리: "수신자가 `g`의 Go 배치를 담으면 `dst[len:]`에 `enc g`의 바이트를 쓰고 `dst[:len]`을 보존한다", `serialize d g.toValue = .ok (enc g)`.

부정 입력 표(빈 값, 최소, 최대, 초과, 오프셋 0·작음·큼·정렬 안 됨)와 각 줄의 정리: `semtest/cases.why`. 디코더 오류 대응표: SPEC.md 3절.

### 5.2 발견

**F1 (BitVec 패딩 비트).** `BitVec.UnmarshalSSZ`는 1바이트를 그대로 받는다. EthLib는 상위 4비트(패딩)가 선 바이트를 `paddingBits`로 거부한다.
- Lean: `bv_spec_rejects_padding : deserialize bvDesc #[0x10] = .error .paddingBits`, `bv_padding_counterexample`(기계어가 0x10을 받아 nil을 반환).
- Go: `semtest/f12_test.go` `TestF1BitvectorPadding` 통과.

**F2 (BitL 길이 검사 단위).** `BitL.MarshalSSZTo`는 `len(c.B) > 2048`을 검사한다. `c.B`는 구분 비트를 포함한 바이트 배열이고, SSZ 한도 2048은 비트 수다(최대 257바이트). 그래서 258~2048바이트 bitlist를 nil 오류로 인코딩한다. EthLib와 같은 타입의 디코더(`ssz.ValidateBitlist`)는 그 출력을 거부한다.
- Lean: `bl_marshal_overlong`(258바이트 `blOverlong`에서 기계어가 성공하고 `offset 4 ‖ c.B`를 쓴다 ∧ EthLib가 그 바이트를 거부), `bl_spec_rejects_overlong`, `bl_accepted_size`(EthLib가 받는 입력은 261바이트 이하).
- Go: `TestF2BitlistByteLimit` 통과.

두 발견 모두 생성기(`sszgen/`)의 문제다. 브리프에 따라 `sszgen/`, `ssz/`는 고치지 않았다.

### 5.3 B3 하위 항목

| 항목 | 결과 |
| --- | --- |
| B3.0 대상 빌드 표 | `link/out/FUNCS.md`(함수별 명령어 수, 호출, 전역). `GOAMD64=v1`을 `link/build.sh`에 고정. 런타임 파서가 거부하는 것은 `ssz.ValidateBitlist`의 `bsr %r8d,%r8d` 1줄뿐. `nopw (%rax,%rax,1)` 등 패딩 형태를 `conv.py` NORM 표에 더했다 |
| B3.1 Desc, 추상화, 오류 대응 | SPEC.md, `lean/Fv1/Spec{BitVec,Nested,ListC,Prysm,BitList}.lean` |
| B3.2 타입별 정리 | 5.1절 |
| B3.3 bitlist rodata 표 | 해당 없음. `GOAMD64=v1`에서 `bits.Len8`은 `bsr`이고 표를 읽지 않는다(SPEC.md 6절, 이견 4) |
| B3.4 ReadOffset/WriteOffset 범위 | SPEC.md 4절. 디코더 쪽은 모두 32비트 적재라서 변환이 없다(`lu_off4`, `ne_off28`, `zx_o`). 인코더 쪽 자르기는 ListC 한 곳이고 인코더가 미증명이다 |
| B3.5 Prysm 커밋 | v7.1.8 `51b5a75…`, SPEC.md 1절 |

### 5.4 함수 명세 조합 (C20)

Nested 디코더는 `Scalars.UnmarshalSSZ`와 `ListU64.UnmarshalSSZ`를 호출한다. 두 피호출자는 계약이 아니라 우리 정리에서 유도한 함수 명세로 둔다(`ScUAccC` ← `sc_uacc_holds`, `LuUAccC` ← `lu_uacc_holds`). 이를 위해 `sc_accept_main`, `lu_accept_main`의 사후조건이 rsp + 8, r14, 모든 조각(스택 칸의 새 내용 포함), 프레임 `R`을 돌려준다(dbd70cf). ListU64의 스택 사용은 블록 하나(`luFrame`)로 묶었다.

## 6. B4: 하드웨어 대조

실행하지 않았다. 이 호스트는 macOS arm64이고 x86-64 Linux 기계를 받지 않았다.

`semtest/`(README.md):
- `run.sh`: x86-64 Linux에서만 실행한다. 고정 플래그로 ELF를 다시 빌드하고 sha256이 `link/out/build-ids.txt`와 같은지 검사한다. 그 ELF를 `-test`로 실행해 `expected.txt`(Go 기준, arm64에서 생성)와 비교한다. 다른 호스트에서는 종료 코드 2로 멈춘다.
- `cases.txt` 47줄, `cases.why`(줄마다 정리).
- 한계: 메모리 상태 전체가 아니라 함수의 관찰 결과(오류 종류, 출력 바이트)만 비교한다. astra C15 지적("메모리 비교가 필요")은 남는다.

## 7. 조건표 (C1–C22)

C1–C16은 REPORT.md 2절. 1b에서 바뀐 것만 적는다.

| # | 상태 (1b) |
| --- | --- |
| C6 | 완료. 계약 8종(`MakesliceC`, `MemmoveC`, `GrowsliceC`, `ConvT64C`, `FmtErrorfC`, `NewobjectC`, `ValidateBitlistC`, 함수 명세 2개). CONTRACTS.md |
| C7 | X15 = 0은 가정하지 않는다. `movups %xmm15` 저장을 임의 값 저장으로 증명했다(`lu_reject_*`) |
| C12 | 차단 항목 확정: `bsr`(`ssz.ValidateBitlist`). 계약으로 우회. 9절 |
| C13 | 한 지점 증명. 나머지 추정 11절 |
| C14 | B0: 채택 안 함 |
| C15 | 스크립트만(6절) |

astra가 더한 조건(브리프 B4b):

| # | 조건 | 완료 기준 | 상태 |
| --- | --- | --- | --- |
| C17 | 실행 파일 연결 | ELF 바이트 전수 대응, 명령어 경계, 함수 크기, 분기 목표, 전역 주소, 외부 기호, 레이블 유일성을 하나의 검사가 확인하고, 그 결과와 `.S`·`Code.lean`·`AXIOMS.txt`를 ELF 해시 하나로 묶는다. 검사가 변이(자기 시험)에 실패한다 | **완료**(3절). 남은 것: 크기 0 기호(`type:*`) 안 주소의 소유 범위는 증명하지 않는다 |
| C18 | 계약 비공허성 | 계약마다 크기 범위와 런타임 자원을 명시하고, 계약을 만족하는 실행 증인과 전제 전체를 동시에 만족하는 구체 상태를 Lean 정리로 둔다 | **부분.** `makeslice`만 증인 2개(`bump_makeslice`, `lu_accept_runs`). 나머지 7개 계약은 같은 형식이지만 증인이 없다 |
| C19 | 실제 호출 조건 | 정리마다 유효 주소, 접근 권한, 별칭 정책, 스택 가드, GC(쓰기 장벽) 조건을 적고, 실제 Go 호출자가 보장하는지 한 줄로 판단한다 | **부분.** 각 파일 머리말과 CONTRACTS.md 4절에 적었다. 접근 권한은 Kraken `Effects.All`이 검사하지 않는다. 쓰기 장벽 0은 일반 호출의 보장이 아니다(빠른 경로 전제) |
| C20 | 함수 조합 | 사후조건이 입력·접두사·프레임·rsp·r14를 돌려주고, 한 함수 정리를 다른 함수 증명에서 호출 명세로 쓴 예가 있다 | **완료**(5.4절, Nested 디코더) |
| C21 | 명세와 범위 | 타입마다 Desc·추상화·오류 대응, 크기·인코더·디코더 완료표, EthLib 연결 | **부분.** 5.1절 표. ListC 인코더·디코더 수용, 감싼 오류 경로가 남는다 |
| C22 | 검사 민감도 | 입력 누락을 실패로 처리하고, 의미 변이가 지정 정리에서 실패하고, 주소만 바뀐 사례가 통과한다 | **완료.** `conv.py` 실패 조건, `check.py --selftest`, `negative/` |

## 8. 신뢰 기반 문구 (REPORT.md 7절 갱신)

> 기계어 정리는 Kraken x64 의미론(AeneasVerif/kraken `6064eec`) 위의 Lean 정리다. 대상은 Go 1.26.3(`GOAMD64=v1`)이 만든 ELF의 기계어이고, ELF와 Lean 입력의 대응은 `link/check.py`가 바이트 단위로 검사한다(ELF sha256 하나로 묶음). Kraken의 의미론은 Intel SDM을 참조해 손으로 쓴 것이다. 이 프로젝트는 우리 함수에 대해 하드웨어 대조를 아직 실행하지 않았다. Go 런타임 함수(`makeslice`, `memmove`, `growslice`, `newobject`, `convT64`, `fmt.Errorf`)와 `ssz.ValidateBitlist`는 정리의 가설(계약)이다. 그중 `makeslice`만 계약을 만족하는 구현과 전제의 동시 만족을 증명했다. bitlist의 검증 규칙은 `ValidateBitlist` 계약에 들어 있고 기계어로 증명하지 않았다. 전역 변수의 값(오류 값, 쓰기 장벽 꺼짐)과 스택 가드는 정리의 전제다. 정리는 빠른 경로(용량 충분, 포인터 필드가 nil이 아님)를 다룬다.

## 9. Kraken 요청 목록 (사용자가 Kraken 팀(Nic)에 요청)

| 범주 | 항목 | 이유와 근거 |
| --- | --- | --- |
| 명령어 | `bsr` (32/64비트) | `ssz.ValidateBitlist`의 `bits.Len8`(`GOAMD64=v1`). 없어서 bitlist 핵심 검사를 계약으로 뒀다 |
| 명령어 | `lzcnt` | 같은 코드의 `GOAMD64=v3` 형태 |
| 명령어(후보) | `tzcnt`, `popcnt`, `bt`, `xchg`(레지스터), `cqo`, `div`, `rep movs`, `pxor`, `xorps`, `movq xmm↔gpr` | REPORT.md C12. 1b 대상에서는 나오지 않았다 |
| 파서 | 다바이트 nop(`nopl (%rax)`, `nopw (%rax,%rax,1)`, `data16 nop` 등) | 지금은 `conv.py`가 `nop`으로 정규화한다(49곳) |
| 파서 | 정교화기 `include_x64`의 조건 코드 `g, ge, nl, nle, s, ns, o, no, p, np` | 지금은 런타임 파서 + `ToExpr`(`include_x64_rt`) |
| 자동화 | `kstep`이 부가 목표의 `grind` 시간 초과를 잡기 | REPORT.md C11 |
| 자동화 | `ecancel`의 원자 비교: `Width.W64.bits` 폭 인수가 다른 같은 항, 큰 리터럴(`-8`)에서 정의 동치 검사가 재귀 한도·시간 초과에 닿는다 | 우리는 `generalize`, 독립 주소 보조정리, `rw [show … by bv_omega]`로 우회한다. 이번에도 수십 곳 |
| 자동화 | 분리 논리 프레임의 결합 방향(`⋆`가 왼쪽 결합)에 무관한 `ecancel` 맞춤 | 함수 명세 조합에서 묶음 단위를 `sep_assoc`로 맞춰야 했다 |
| 자동화 | vcgen `@[spec]` 형태 추가(`movzx` 메모리 원천, 8비트 비교, 메모리 즉치 저장, base+disp 64비트 적재)와 vcgen의 main 합류 일정 | `vcgen/Vg/Specs.lean`에 증명 사본 |
| 대조 | 외부 사용자가 자기 함수에 하드웨어 대조를 돌리는 방법(메모리 상태 비교 포함) | REPORT.md 질문 7 |

## 10. sorry 목록과 공리

- `sorry`, `admit`, `native_decide`, `bv_decide`, `axiom` 선언: 없음. `Fk/Bytes.lean`의 `zx8`/`zx16`/`zx32`는 `bv_decide`(공리 `Lean.ofReduceBool`)를 썼다. 1b에서 `omega` 증명으로 바꿨다(a813744).
- `AXIOMS.txt`: Fk, Fv1, Fv 모듈의 정리 500개 전수(Lean 환경을 열거한다, `lean/tools/Axioms.lean`). 마지막 줄 `TOTAL 500 NONSTANDARD 0`. 스크립트는 표준 공리 밖의 공리가 하나라도 있으면 실패한다.

## 11. 비용

시각은 커밋 시각이다. 1b 시작은 2026-11-05 02:45.

| 구간 | 시간 | 내용 |
| --- | --- | --- |
| 02:45–06:22 | 3시간 37분 | B0(vcgen 빌드 262 s 포함), B1 |
| 06:22–06:43 | 21분 | B2.0 계약 수정, 증인, B2.1 |
| 06:43–07:06 | 23분 | B2.2 FixedVec 전체 |
| 07:06–07:24 | 18분 | B2.3 ListU64 거부 4경로와 EthLib 대응, B2.4 마샬·왕복 |
| 07:24–07:41 | 17분 | B2.5 growslice 한 지점, B2.6–B2.8 |
| 07:41–07:56 | 15분 | B3.0 대상 빌드 표, BitVec 전체와 F1 |
| 07:56–08:45 | 49분 | C20 사후조건 확장, 함수 명세 2개, Nested 디코더 수용(호출 4개 조합) |
| 08:45–08:54 | 9분 | Nested 명세, 거부 2, 크기, EthLib 동치 |
| 08:54–09:08 | 14분 | ListC 거부 5경로와 EthLib |
| 09:08–09:20 | 12분 | Checkpoint 전체 |
| 09:20–09:43 | 23분 | AttestationData 명세, BitL 마샬과 F2, BitL 수용(계약 3개) |
| 09:43–09:56 | 13분 | B4 스크립트, AXIOMS 도구, SPEC.md, ListC 크기(루프), AttestationData 수용(호출 8개) |
| 09:56–10:05 | 9분 | AttestationData 마샬(memmove 3개) |
| 10:05–10:55 | 50분 | Nested 마샬(bool 두 갈래, 인라인 루프. 정의 동치 시간 초과 진단 약 25분) |

정리 하나의 비용(커밋 간격 기준, 대략): 짧은 거부 경로 2–5분, 호출 1–3개의 수용 경로 10–15분, 호출 8개의 직선 경로 5–10분(틀 복사), 인라인 루프가 있는 인코더 15–50분.

### 남은 growslice 지점 추정 (B2.5)

growslice 경로는 마샬 함수마다 append 지점 수만큼 있다(Scalars 5, FixedVec 2, ListU64 2, BitVec 1, Nested 9, ListC 4, BitL 2, Checkpoint 2, AttestationData 7). 한 지점 증명(`lum_grow_site`)은 약 5분이었다. 지점 사이의 조합(앞 지점이 growslice를 탄 뒤 뒤 지점은 빠른 경로 등)까지 모든 경로를 덮으려면 함수마다 지점 수에 비례하는 경로 보조정리와 합류 보조정리가 필요하다. 추정: 지점당 5–10분, 합류 처리 함수당 15–30분, 전체 약 6–9시간.

## 12. 남은 것과 추정

| 항목 | 추정 |
| --- | --- |
| ListC 디코더 수용(원소 루프: 원소마다 `newobject`, `ListU64.UnmarshalSSZ` 함수 명세, 오프셋 검사, `gcWriteBarrier1` 분기) | 2–4시간 |
| ListC 인코더(인라인: 크기 합 루프, 오프셋 쓰기 루프, 원소별 인라인 ListU64 인코더의 이중 루프) | 2–4시간 |
| ListC 디코더 정렬 오류·원소 초과(convT64 + fmt.errorf, ListU64 틀 복사) | 30분 |
| 감싼 오류 경로(Nested S·L, ListC 원소, BitL 검증 실패): 피호출자의 거부 함수 명세 + `fmt.errorf` 계약 | 경로당 20–40분 |
| nil 포인터 필드 경로(`newobject`로 새 객체를 만드는 인코더·크기 경로) | 경로당 15–30분 |
| 나머지 계약의 증인(C18): memmove, growslice, newobject는 범프 할당기·바이트 복사 루프로 | 계약당 30–60분 |
| `ValidateBitlist` 기계어 증명 | Kraken에 `bsr`이 들어온 뒤 1–2시간 |
| 하드웨어 대조 실행 | x86-64 Linux 기계를 받은 뒤 30분 |

## 13. 이견

리뷰 지적(`review/claude.md`, `review/gpt6-astra.md`)과 브리프에서 벗어난 것.

1. **astra 1 (`lu_accept_main` 공허).** 맞다. 1절에서 철회하고 고쳤다. Claude 재검사 2항도 같은 이유로 틀렸다.
2. **astra 2, Claude 추가 2 (`bits.Len8`은 표가 아니라 `bsr`).** 맞다. REPORT.md C12를 정정했다. Kraken을 고치지 않는다는 결정에 따라 `ValidateBitlist`를 계약으로 뒀다(9절 요청).
3. **astra 3 (조합용 사후조건 부족).** 고쳤다. 모든 마샬 정리가 `dst[:len]`을 돌려준다. 디코더 수용 정리가 rsp + 8, r14, 스택 칸, 프레임을 돌려준다(5.4절).
4. **B3.3 rodata 표 방식을 쓰지 않음.** 먼저 확인했다: `link/out/FUNCS.md`에서 `ssz.ValidateBitlist`의 전역 참조는 없고 objdump에 `bsr`이 있다. 표가 없으므로 C5 방식(레이블 조각 + 값 전제)을 적용할 대상이 없다. 대신 함수 전체를 계약으로 뒀다.
5. **astra 4, C15 (메모리 비교 대조).** 동의한다. 이 호스트에서는 실행할 수 없다. `semtest/run.sh`는 관찰 결과만 비교한다. 메모리 상태 비교는 Kraken 대조 도구(`StateSummary`)가 레지스터와 플래그만 비교하는 한계와 같이 남는다.
6. **astra의 비용 비교 지적.** 동의한다. 평가 세션의 "61분 대 4시간"은 모순된 계약으로 얻은 값이었다. 11절의 값도 같은 에이전트가 틀을 복사한 시간이다. 독립 생산성 추정이 아니다.
7. **astra C19 (쓰기 장벽 0, 스택 가드).** 반박하지 않는다. 정리는 빠른 경로 정리이고 일반 Go 호출의 보장이 아님을 각 파일과 8절에 적었다. GC가 할당 중 표시 단계에 들어가는 경우(쓰기 장벽이 켜짐)는 증명하지 않았다.
8. **Prysm 타입의 Go 배치.** Prysm 원본 구조체에는 protobuf 필드(`state`, `sizeCache`, `unknownFields`)가 앞에 있다. 이 모듈은 Prysm에 의존하지 않으므로(go.mod가 `fv/kraken` 밖) 그 필드를 옮기지 않았다. SSZ 스키마와 생성 코드의 논리는 같지만 필드 오프셋이 다르다. 그래서 정리는 Prysm 바이너리의 기계어가 아니라 같은 생성 코드를 이 구조체로 컴파일한 기계어에 대한 것이다.
9. **`fmt.Errorf`의 `%w`를 모델하지 않음.** `FmtErrorfC`는 rax ≠ 0(nil이 아닌 오류)만 말한다. 어떤 오류를 감싸는지는 말하지 않는다. 그래서 감싼 오류 경로의 정리는 "오류를 반환한다"까지이고 Go `errors.Is`의 결과는 말하지 않는다. `semtest/expected.txt`가 그 결과(`wrap:ErrListTooBig` 등)를 기록한다.
10. **ListU64 오류 종류.** 거부 정리는 반환 오류가 어느 전역인지(ErrSize, ErrInvalidVariableOffset) 또는 nil이 아님을 말한다. EthLib의 `Err` 종류와 1:1 대응시키지 않았다. EthLib 쪽은 "거부한다"(`∃ e, … = .error e`)로만 연결했다.
11. **부정 사례 방식.** 브리프는 "주소를 다시 생성하는 템플릿"을 말했다. Kraken 배치는 지시어 크기를 추상으로 두므로 주소 재생성이 필요 없다. 변이를 `.S` 지시어 한 줄 교체로 했고 지시어 수를 유지했다. 대조군(같은 줄로 교체)이 통과함으로 확인했다.
12. **vcgen 미채택.** B0에서 시도했다(2절). 실패 내용과 시간은 `vcgen/B0.md`. 대안은 main 유지다.
13. **`bv_decide` 사용 철회.** 평가 세션의 `Fk/Bytes.lean`이 `bv_decide`를 썼다. astra는 그 정리들의 공리를 조회하지 않았다. 1b에서 표준 공리만 쓰도록 바꿨다.
14. **ListC 인코더·디코더 수용 미완료.** 브리프 순서(bitvector → 중첩 → List[container] → Prysm → bitlist)를 지켰지만 List[container]의 루프 두 개를 먼저 끝내지 않고 Prysm과 bitlist로 넘어갔다. 이유: 종류별로 최소 하나의 정리를 먼저 두어 게이트 1 표를 빈칸 없이 만들기 위해서다. ListC 수용·인코더는 12절에 남겼다.

## 14. 재현

```sh
fv/kraken/link/build.sh                       # ELF, objdump, 변환, SHash.lean (저장소 루트)
python3 fv/kraken/link/check.py fv/kraken/link/out          # RESULT, BUNDLE
python3 fv/kraken/link/check.py --selftest fv/kraken/link/out
cd fv/kraken/lean && lake build               # 모든 정리
tools/axioms.sh                               # ../AXIOMS.txt
cd ../../.. && fv/kraken/negative/run.sh <scratch>   # 부정 사례
go test ./fv/kraken/semtest/                  # F1, F2
fv/kraken/semtest/run.sh                      # x86-64 Linux에서만
```
