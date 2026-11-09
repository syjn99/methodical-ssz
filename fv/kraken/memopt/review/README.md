# memopt 독립 리뷰 (gpt-6-astra)

리뷰 대상은 `syjn99/ssz-fv-memopt`의 `e8f95e3`이다. 판정은 조건부다.
리뷰어가 E 경로에서 실행했다. 재실행에는 `run-lean.py`의 경로를 바꿔야 한다.
E는 세션 scratchpad의 `memopt/review` 디렉터리다. 출력 파일의 절대 경로는 그 위치를 가리킨다.

## 파일

| 파일 | 역할 |
| --- | --- |
| `REVIEW-gpt6-astra.md` | 리뷰 본문. 판정, 발견 3개, 완료 기준 10개, 필수 수정 목록 |
| `Compare.lean` | 원본과 수정본 `.olean`을 서로 다른 환경으로 읽는다. 타입과 정의 값을 `Expr.equal`로 비교한다 |
| `compare-final.txt` | `Compare.lean` 출력. 선언 290개, 외부 선언 5개, 정의 값 57개 PASS |
| `Recheck.lean` | 변경 증인의 `#print axioms`와 외부 정의의 `#print` |
| `recheck.txt` | `Recheck.lean` 출력 |
| `run-lean.py` | 원본·수정본 증인 6개씩을 별도 `-R`, `-o`로 컴파일한다. 이어서 `Recheck.lean`과 공리 두 범위를 실행한다 |
| `lean-commands.json` | `run-lean.py`가 실행한 명령, cwd, 종료 코드 |
| `static-checks.txt` | 보호 경로 diff, 증명 문자열 복원 뒤 파일 비교, 패키지 revision, ELF 해시, 생성기 재실행 |
| `log-audit.txt` | 빌드 로그의 `Built`, `Replayed`, 종료 상태 분석 |
| `evidence-crosscheck.txt` | 기록된 시간·RSS 원시값과 보고서 요약의 대조. Inspector 출력 diff |
| `wrapper-exit-test.txt` | 가짜 `docker`(exit 23)로 `lowmem/run.sh`를 실행한 결과. 발견 2의 근거 |
| `diagnostic-repro.txt` | HEAD에서 `scratch/gen.py`를 실행한 결과. 발견 3의 근거 |

## 재실행

- `run-lean.py`는 자기 디렉터리의 `orig/Fk/*.lean`, `new/Fk/*.lean`을 읽는다. 이 두 디렉터리는 커밋하지 않았다.
- 재실행하려면 `orig/`에 `86fd060`의 증인 6개를, `new/`에 현재 증인 6개를 넣는다. cwd는 `fv/kraken/lean`이다.
- `Compare.lean`은 환경 변수 `REVIEW_DIR`에 `orig/`, `new/`의 부모 디렉터리를 받는다.
- `.olean`과 `orig/`, `new/`, `regen/` 디렉터리는 커밋하지 않았다. 다시 만들 수 있다.

## 반영

발견 1–3의 반영은 `memopt/REPORT.md` 11절에 있다.
