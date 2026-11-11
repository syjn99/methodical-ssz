# FINDINGS 후보 (LV 스트림)

이 파일은 `prysm/FINDINGS.md`의 후보 목록이다.
기존 원장은 바꾸지 않았다.
ID는 안정 ID다.

| ID | 처음 본 곳 | 상태 | 증거 종류 | 내용 |
| --- | --- | --- | --- | --- |
| LV-1 | U1 링크(로그 08, 66), `9b805e0` 뒤 | 열림 | 실행(X) | 음수 변위 표기의 도구 빈틈 후보. production 결함이 아니다 |

## LV-1

- T3 `IndexedAttestation.UnmarshalSSZ`의 정규화 `.S` 19행은 `lea 0xffffff1c(%rdi),%rdx`다.
- `go tool objdump -gnu`는 32비트 변위 −228을 `0xffffff1c`로 쓴다.
- `link/conv.py`는 그 표기를 그대로 둔다.
- x86-64는 32비트 변위를 부호 확장한다. 기계의 주소는 rdi − 228이다.
- Apple clang 21.0.0은 이 줄을 거부한다(`displacement 4294967068 is not within [-2147483648, 2147483647]`).
- 그래서 `check.py` (d)가 실패했다(로그 08).
- Kraken 파서(`6064eec`)는 `disp := ↑4294967068`로 읽는다.
- `lea -0xe4(%rdi),%rdx`는 `disp := ↑(-228)`로 읽는다(로그 66).
- 이 `.S`로 증명하면 기계와 다른 주소를 다룬다.
- 커밋된 다른 `.S`에는 이 꼴이 없다(`git grep '0xffffff..(%'`, 결과 0). 기존 정리에는 영향이 없다.
- 고칠 곳 후보(하지 않음): `conv.py --norm`이 변위를 부호 있는 수로 쓴다. 또는 `check.py`에 변위 범위 검사를 더한다.
- 이전 링크 검사의 LLVM이 이 표기를 받았는지는 모른다.
