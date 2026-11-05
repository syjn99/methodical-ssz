# semtest: hardware comparison (B4)

작성 2026-11-05. 이 호스트(macOS arm64)에서는 `run.sh`를 실행하지 않았다.

## 파일

| 파일 | 내용 |
| --- | --- |
| `cases.txt` | `p1bin -test` 입력. 타입마다 빈 입력, 최소, 최대, 초과, 잘못된 오프셋(0, 작음, 큼, 정렬 안 됨). 크기와 마샬 줄도 있다. |
| `cases.why` | `U` 줄마다 그 결과를 보장하는 정리. "not proved"는 증명이 없는 경로다. |
| `expected.txt` | Go 기준 출력. `gen-expected.sh`가 만든다(아무 아키텍처). |
| `run.sh` | x86-64 Linux에서만 실행한다. 고정 플래그(`GOAMD64=v1`)로 ELF를 다시 빌드한다. sha256이 `link/out/build-ids.txt`의 값과 같은지 검사한다. 그 ELF를 `-test`로 실행하고 `expected.txt`와 비교한다. |
| `f12_test.go` | 발견 F1, F2의 Go 수준 회귀 시험(거부 단언, `GOROOT=$(go env GOROOT) go test ./fv/kraken/semtest/`, 아무 아키텍처). 수정 전 반례 시험은 커밋 `37efd44`에 있다. |

## 실행

1. x86-64 Linux 호스트에 Go 1.26.3을 설치한다.
2. 저장소 루트에서 `fv/kraken/semtest/run.sh`를 실행한다.
3. ELF 해시가 다르면 비교를 멈춘다. 이때 증명 대상과 다른 기계어다.

## 한계

- `expected.txt`는 Go 기준이다. 같은 Go 코드를 arm64에서 실행한 결과다. 정리에서 계산한 값이 아니다. `cases.why`가 각 줄과 정리를 잇는다.
- `p1bin -test`는 1b 타입의 값을 `UnmarshalSSZ`로 정한다(시험 대상 코드에 의존). 그래서 F2(258바이트 bitlist)는 `cases.txt`로 마샬할 수 없다. F2의 인코더 거부는 `f12_test.go`가 시험한다.
- `p1bin`을 바꾸면 ELF가 바뀌고 증명의 타입 주소(`type__+…`)가 바뀔 수 있다. 그래서 `p1bin`은 바꾸지 않았다.
