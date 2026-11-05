# Kraken x64 평가 재검사 (Claude Fable, 2026-11-05 00:30)

대상: `ssz-fv-kraken` tip ee39240 (c60e0d2 이후 커밋 16개, 모두 `fv/kraken` 아래만). 에이전트 판정 "조건부 가능".

## 소스로 확인한 것

1. **자기 완결성.** `git diff --stat c60e0d2..HEAD -- . ':!fv/kraken'`가 비어 있다. `fv/kraken` 안(upstream 제외)에 `phase0`, `phase1`, `MiniRV`, `rva20` 문자열이 없다(REPORT·COST·TOOLS 제외). 명세 파일은 `fv/kraken/lean/Fv1`, `Fv`로 복사됐다. main 위로 rebase 가능.
2. **정리 문장의 비공허성.** `lu_accept_main`(`Fk/LuAccept.lean:28-67`)의 전제는 길이가 명시된 분리 조각 17개(`⋆`), 스택 가드 `guard < rsp - 8`, `rcx = 4 + 8n`, `rcx ≤ rdi < 2^63`, 쓰기 장벽 4바이트 = 0, `makeslice` 계약 `hms`(모든 상태·반환 주소·프레임 `F`에 대해 양화). 결론은 `pc = ra`, `rax = rbx = 0`, 수신자 (p, n, n)와 `p`의 배열 = `bs`. 입력 `bs`, `n ≤ 16`, 레지스터는 임의. 1a의 `Sep`(mod 2^64 거리)과 달리 Kraken의 `⋆`는 조각의 서로소를 뜻하므로 astra 1a 지적 P2(nil 수신자)의 형태는 다르다. nil(rax = 0)은 여전히 배제되지 않는다. 주소 0의 조각도 분리 논리로는 가능하다. 1a와 같은 "실제 호출용 전제"의 문제이며 REPORT 이견 7이 프레임 한계를 적었다.
3. **`sc_accept_main`**(`Fk/ScAccept.lean:20-42`): 전제 `rcx = 16`, `b4 ∈ {[0],[1]}`, 레이블 신선성 2개, 분리 조각 12개. 결론은 수신자 조각 5개가 입력 조각과 같음. 적절하다.
4. **레이블 해석.** `LabelsFresh p k`(`Fk/Labels.lean:72`): Host에서 함수 앞에 같은 레이블이 없다는 전제. 링크 수준 사실이고 정리 안에서 증명하지 않는다(REPORT 이견 6). 실제 ELF와 Host 레이블 주소의 일치도 마찬가지(REPORT 3.2). 1a의 링크 검사에 해당하는 도구가 아직 없다. 1b 전에 만들어야 한다.
5. **mutable 전역.** README의 "제외"는 "모델이 전역 쓰기를 다루지 않는다"는 뜻이고, 읽기는 `label` 주소의 데이터 메모리 적재로 동작함을 에이전트가 의미론에서 확인했다. `ssz.ErrSize`와 `runtime.writeBarrier`를 레이블 조각 + 값 전제로 둔 방식은 1a의 `hinit`/`noBarrier`와 같은 강도다.
6. **자동화.** `kstep`은 큰 맥락에서 `grind` 시간 초과로 실패해 자체 `kat`/`load_step`/`store_step`(`Fk/Step.lean` 154줄 등 매크로·보조정리 439줄)으로 대체했다. 의미론은 Kraken 것이고 보조정리는 그 의미론에서 증명된 것이므로 신뢰 기반에 추가되는 것은 없다. 유지 비용은 우리 몫이다. vcgen 브랜치가 이를 대체할 수 있다(C14).
7. **K1 파서.** 9개 함수 모두 런타임 파서 통과(패딩 nop 정규화 뒤). 정교화기 `include_x64`는 `jg`/`jge` 때문에 4개 함수를 거부한다. 의미론에 없는 명령어는 없다. 1b 후보 명령어(`bsr`, `lzcnt`, `popcnt`, `bt`, `div`, `rep movs`, SSE) 중 일부는 Kraken에 없다(C12). 1b 대상을 빌드해 봐야 확정된다.
8. **비용 비교의 한계.** REPORT가 스스로 적었다. 이 세션은 1a 방법을 알고 시작했으므로 시간 차이의 일부는 학습 효과다. 그래도 ListU64 수용 전체 61분 대 약 4시간은 방법 차이를 넘는다.

## 판정에 대한 의견

- "조건부 가능"은 정확하다. 조건 16개 중 MiniRV를 되살려야 하는 것은 없다. 조건은 (a) 우리 래퍼(완료 또는 1a 틀 이식), (b) Kraken 기여(정교화기 조건 코드, nop 파싱, grind 시간 초과, 1b 명령어), (c) 전제(전역 값, 스택 가드, 외부 호출 계약), (d) 결정(vcgen 브랜치, 툴체인, 하드웨어 대조)이다.
- 사용자 기준("MiniRV를 버릴 수 있는가")으로는 **가능**이다. MiniRV 없이 세 가지 핵심(직선, 루프, 외부 호출)이 Kraken 위에서 재현됐다.
- 남는 신뢰 간극 둘: 하드웨어 대조를 우리 함수에 대해 아직 돌리지 않았다(x86-64 Linux 기계 필요). 링크 수준 검사(ELF ↔ Host 레이블·전역 주소)가 없다.

## 재현
(verify-kraken.sh 결과를 아래에 붙인다)

`verify-kraken.sh` (ee39240, 00:14):

| 검사 | 결과 |
| --- | --- |
| `link/build.sh` (amd64 재빌드, objdump, 변환) | ELF sha256 `bd3cb698…2a7a`, `build-ids.txt`와 일치. 생성 파일 sha256 `26eda6b6…e096`(1a와 같은 생성 결과). 작업 트리 변경 없음 |
| `fv/kraken/lean` 깨끗한 빌드(`.lake/build` 삭제 후) | 572 jobs, 20.5 s 통과 |
| 공리 재생성 | `AXIOMS.txt`와 정확히 일치. `sorryAx` 0. 공리는 `propext`, `Classical.choice`, `Quot.sound`뿐 |
| 파서 검사 9함수(`--norm` 뒤) | 모두 0 rejected |

결론: 에이전트 보고의 재현 가능한 부분은 모두 재현됐다. 실행하지 않은 것(K5 하드웨어 대조)은 이 호스트에서도 실행할 수 없다.

## 추가 (02:25): astra 리뷰 교차 검증

astra(gpt-6-astra) 리뷰 `review-kraken-gpt6.md`(260줄, 02:10)의 판정은 **조건부**다. 주요 발견 4개를 내가 다시 확인했다.

| astra 발견 | 내 확인 | 결과 |
| --- | --- | --- |
| 1. `lu_accept_main`의 전제가 모순(공허). `hms`가 모든 `cnt`에 양화되어 `cnt = 2^61`이면 새 블록 `8·cnt = 2^64`바이트가 모든 주소를 덮어 반환 슬롯과 서로소일 수 없다 | `fv/kraken/lean`에서 `lake env lean ReviewKraken.lean` 실행. `lu_accept_preconditions_false`(원래 정리의 전제 전부를 받아 `False`)가 3초에 통과. 공리는 `propext`, `Classical.choice`, `Quot.sound`뿐 | **확인.** `lu_accept_main`은 참이지만 공허하다. 내 재검사 2항("비공허성")은 틀렸다. 나는 조각 길이와 레지스터 전제만 봤고 계약 가설 `hms`의 양화 범위를 보지 않았다 |
| 1'. `cnt ≤ 16`만 더하면 되는가 | 아니다. `hms`는 프레임 `F`에도 양화된다. `F`를 "슬롯과 스택 밖 모든 주소를 덮는 조각"으로 잡으면 사전조건은 만족되고 사후조건의 새 블록이 들어갈 자리가 없다. `DataMem`은 `ExtHashMap (BitVec 64) UInt8`이라 그런 `F`가 존재한다 | 계약에 런타임 소유 힙 조각을 두고 새 블록을 그 안에서 떼어내는 형식이 필요하다. 1a의 `makesliceC`(힙 범위 조건)에 해당한다. 수정 뒤 빈 리스트·1개·16개의 전제 만족 증인을 남겨야 한다 |
| 2. `ValidateBitlist`의 `bits.Len8`이 `bsr`로 컴파일되어 Kraken 파서가 거부 | `kraken-bitlist-v1.objdump:21` `BSRL R8, R8`, `:8` `NOPW 0(AX)(AX*1)` 확인 | **확인.** C12는 "후보"가 아니라 bitlist의 차단 항목이다. `GOAMD64=v3`는 `lzcnt`라 역시 거부. Kraken에 `bsr` 추가(패치)가 필요하다 |
| 3. 함수 정리의 사후조건이 조합에 부족(`dst[:len]` 접두사 보존, 호출 후 `rsp`) | 정리 문장으로 확인(`ScSpec.lean:86`, `ScAccept.lean:36`). 1a 리뷰 P2와 같은 지적 | **확인** |
| 4. 링크 검사 부재. astra 자신이 임시 검사(ELF 바이트 ↔ objdump ↔ LLVM 독립 디코딩 582개 명령어, 9함수 구문 트리 일치)를 돌려 지금 9함수에서는 불일치 없음 | 로그 `review-kraken-link.log`, `review-kraken-llvm-ast.log` 존재 확인 | 1b의 B1에 그대로 넣는다. `conv.py`의 조용한 행 누락, 이름 정리 충돌은 거부로 바꿔야 한다 |

그 밖에 astra가 확인한 것: Fk 57개 정리 전수 공리 조회 표준 3개뿐(커밋된 `AXIOMS.txt`는 11개만 직접 조회), 자체 단계 보조정리는 Kraken 의미론 위의 정리(우회 아님), K0 nightly 주장 재현, `lakefile`이 `SpecList`를 빌드 대상에 넣지 않음, `build.sh`가 `GOAMD64`를 고정하지 않음, 비용표는 같은 작업의 비교가 아님(ListU64 61분은 모순 계약 기준).

## 수정된 의견

- 00:30 메모의 "사용자 기준으로는 가능"을 **철회**한다. 세 기둥 중 직선 경로(Scalars 4경로, EthLib 연결)와 데이터 의존 루프(`lu_loop`)는 선다. 외부 호출 계약을 포함한 함수 전체 수용 정리는 공허해서 증거가 없다.
- 두 리뷰 모두 **조건부**이고, 조건 중 MiniRV 복귀를 요구하는 것은 없다. 공허성은 계약 형식의 오류이지 Kraken의 한계가 아니다. 1a MiniRV에서도 같은 종류의 전제 문제(P1 nil 수신자, havoc 색인)가 있었다.
- 1b 세션의 첫 일은 `hms`를 힙 자원 형식으로 고치고 `lu_accept_main`을 다시 증명하는 것이다(추정 반나절). 그 다음 `bsr` 패치, 링크 검사.
- 삭제 결정은 사용자 몫이다. 삭제하더라도 MiniRV 브랜치 3개를 `git bundle`로 `~/Downloads`에 보관하는 단계를 `drop-minirv.sh`에 넣었다(astra: "과거 검토와 재현 자료까지 삭제할 이유는 없다").
