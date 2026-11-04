# COST: Kraken 평가 세션 비용

에이전트(Claude Opus 5.5) 한 세션. 시각은 2026-11-04 IST, 커밋 시각 기준이다. 사람 시간이 아니다. 각 구간에는 빌드 대기와 도구 학습이 들어 있다.

## 시간표

| 구간 | 커밋 | 내용 |
| --- | --- | --- |
| 21:30–21:41 | | 문서와 Kraken 소스 읽기 |
| 21:41–21:55 | 66ce3e6 | K0 툴체인: (a) 4.35.0 실패(파서), (b) nightly 성공 |
| 21:55–21:57 | 52a866b | K1 빌드, 변환기, 두 파서 시험 |
| 21:57–22:21 | f315f64 | K2 거부 경로 (main의 `kstep` 사용법 학습 포함) |
| 22:21–22:33 | 0df83c1 | K2 수용 경로 (`kstep` 대신 자체 `load_step`/`store_step`) |
| 22:33–22:36 | a731c42, 0f1d0b0 | 레이블 해석 보조정리, EthLib `deserialize` 연결 |
| 22:36–22:55 | 8b298fe | K3 SizeSSZ, MarshalSSZTo 빠른 경로, EthLib `serialize` 연결 |

(그 사이 9eb6885: `fv/kraken` 자기 완결 재배치, 사용자 지시)

## 함수별 실측

| 정리 | 명령어 수(경로) | 시간 | 막힌 곳 |
| --- | --- | --- | --- |
| `sc_reject_size_main` | 7 | 24분 | `kstep`의 분리 목표 정규형, `kstep` 안 `grind` 시간 초과(두 번째 rip 적재) |
| `sc_accept_main` | 25 × 2 경로 | 12분 | `kstep`이 맥락이 커지자 저장 명령어 하나에서 `grind` 시간 초과. 자체 단계 보조정리로 교체 |
| `sc_unmarshal_accept_spec_k` | | 3분 | 1단계 `Transfer`를 그대로 썼다 |
| `sc_size_main` | 2 | 2분 | |
| `sc_marshal_main` | 약 45 × 2 경로 | 약 17분 | `List.drop 44`의 정의 펼침 재귀 한도, 레이블 부가조건 `decide` 재귀 한도, `Width.W64.bits` 폭 인수 불일치, SIB 주소 정규형 |
| `sc_marshal_spec_k` | | 2분 | |
