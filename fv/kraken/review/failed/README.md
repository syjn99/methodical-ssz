# 실패한 증인 시도 (재증명 R6)

| 파일 | 대상 정리 | 결과 | 시간 | 목표 |
| --- | --- | --- | --- | --- |
| `WitLuMa.lean` | `lu_reject_misaligned_main` | `s_mem`은 통과. `lu_reject_misaligned_runs`(본문 정리 적용)가 `whnf` 시간 초과 | heartbeat 400만, 91초(`lake env lean`, 2026-11-06 00:48) | 100행 정리 머리 |

같은 생성기(`tools/wit/wlur.py`)의 `toobig` 판(`Fk/WitLuTb.lean`)은 통과한다.
두 판의 차이는 오류 레이블, 형식 문자열 오프셋·길이(68), rcx(5), 마지막 전제(`hmis`)다.
원인은 확인하지 않았다(추측: `hmis`나 `hlen`의 `simp [s0]`가 레지스터 기록을 펼친다).
재현: `cd fv/kraken/lean && cp ../review/failed/WitLuMa.lean Fk/ && lake env lean Fk/WitLuMa.lean`.
