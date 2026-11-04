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
