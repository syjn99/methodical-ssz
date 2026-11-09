# 공유 문서 변경 제안 (phase1c, rebase 뒤 적용)

INBOX 003 2번: 원칙 승인, fix3 rebase 뒤에 적용한다. 지금은 공유 문서를 고치지 않는다.
아래 문장은 그때 `DIRECTION.md` 5절과 `TOOLS.md` "고정 버전"에 넣을 초안이다.

## DIRECTION.md 5절 (1c 부분만 바꾼다)

> 1c의 Prysm 소스는 `ab15ff70c72a568c870b2de662474685a95de294`(slice + `ssz-size`)다. 고정 배열 핀과 같다고 주장하지 않는다.
> 1c의 대상 컴파일러는 Go 1.26.10이다. 새 실험 기준선이며 이름공간이 따로다(`prysm/go1.26.10/MANIFEST.md`).
> Go 1.26.3 ELF `9c850c97…c501`의 정리는 이 기계어에 옮겨지지 않는다.
> 대체된 이력: 1c 핀 `5ac1d028f5`(핀 브랜치 `45394e5`), 1c 컴파일러 Go 1.26.3. 수정 3의 값은 바뀌지 않는다.

## TOOLS.md 고정 버전 표 (행 추가)

| 항목 | 값 | 어디서 고정하는가 |
| --- | --- | --- |
| 1c Prysm 소스 | `ab15ff70c72a568c870b2de662474685a95de294`, 생성은 임시 트리에서만 | `prysm/go1.26.10/MANIFEST.md` |
| 1c Go | 1.26.10, 호스트 linux/arm64에서 linux/amd64 교차 컴파일, `GOAMD64=v1 CGO_ENABLED=0 -tags purego -trimpath` | `prysm/go1.26.10/build-ids.txt` |
| 1c ELF | sha256 `c6403c02…911e`(커밋하지 않음, 재빌드 명령은 MANIFEST) | `prysm/go1.26.10/build-ids.txt` |
